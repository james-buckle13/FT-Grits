package process

import (
	"bytes"
	"fmt"
	"grits/types"
)

type TypeEnvironment int

const (
	GAMMA TypeEnvironment = iota
	DELTA
	UNKNOWN
)

// Entry point to typecheck programs
func Typecheck(processes []*Process, assumedFreeNames []Name, globalEnv *GlobalEnvironment) error {
	errorChan := make(chan error)
	doneChan := make(chan bool)

	globalEnv.log(LOGINFO, "Initiating typechecking")

	// Running in a separate process allows us to break the typechecking part as soon as the first
	// error is found
	go typecheckFunctionsAndProcesses(processes, assumedFreeNames, globalEnv, errorChan, doneChan)

	select {
	case err := <-errorChan:
		return err
	case <-doneChan:
		globalEnv.log(LOGINFO, "Typecheck successful")
	}

	return nil
}

func typecheckFunctionsAndProcesses(processes []*Process, assumedFreeNames []Name, globalEnv *GlobalEnvironment, errorChan chan error, doneChan chan bool) {
	defer func() {
		// No error found, notify parent
		doneChan <- true
	}()

	assignTypesToProcessProviders(processes)

	// Start with some preliminary check on the labelled types
	if err := preliminaryTypesDefinitionsChecks(globalEnv); err != nil {
		errorChan <- err
	}

	// Check that function definitions are well formed
	if err := preliminaryFunctionDefinitionsChecks(globalEnv); err != nil {
		errorChan <- err
	}

	// Check that processes are well formed
	if err := preliminaryProcessesChecks(processes, assumedFreeNames, globalEnv); err != nil {
		errorChan <- err
	}

	globalEnv.log(LOGRULEDETAILS, "Preliminary checks ok")

	// At this point, we can assume that all names and functions have a type and such type is well formed

	// So, we can initiate the more heavyweight typechecking on the function's and processes' bodies

	// Typecheck function definitions
	if err := typecheckFunctionDefinitions(globalEnv); err != nil {
		errorChan <- err
	}

	globalEnv.log(LOGRULEDETAILS, "Function declarations typecheck ok")

	// Typecheck process definitions
	if err := typecheckProcesses(processes, assumedFreeNames, globalEnv); err != nil {
		errorChan <- err
	}

	globalEnv.log(LOGRULEDETAILS, "Process declarations typecheck ok")
}

// Sets a common type to all provider names
// E.g. the names a, b and c should all have the type nat:
// >    prc[a, b, c] : nat = ...
func assignTypesToProcessProviders(processes []*Process) {
	for i := range processes {
		SetTypesToNames(processes[i].Providers, processes[i].Type)
	}
}

//////////////////////////////////////////////////////
///////////////// Preliminary checks /////////////////
//////////////////////////////////////////////////////

// Ensures that labelled types are well defined
func preliminaryTypesDefinitionsChecks(globalEnv *GlobalEnvironment) error {
	// First analyse the labelled types (i.e. type A = ...)
	return types.SanityChecksTypeDefinitions(*globalEnv.Types)
}

// Perform some preliminary checks about the types in function definitions
// Ensures that types only referred to existing labelled types (i.e. recursion is used correctly). Also, ensures that there are no missing types and that types are well formed
func preliminaryFunctionDefinitionsChecks(globalEnv *GlobalEnvironment) error {
	// todo the typesToCheck need to have the modalities added

	var typesToCheck []types.SessionType

	// Analyse the function declarations types (i.e. from 'def f(x : B) : A = ...', check types A & B)
	unique := make(map[string]bool)
	for _, f := range *globalEnv.FunctionDefinitions {

		// Check for duplicate function names
		exists := unique[f.FunctionName]
		if exists {
			return fmt.Errorf("(%s) function %s uses a duplicate function name", f.Position.String(), f.String())
		}
		unique[f.FunctionName] = true

		// Check type of provider
		if f.Type != nil {
			typesToCheck = append(typesToCheck, f.Type)
		} else {
			return fmt.Errorf("(%s) function %s has a missing type of provider", f.Position.String(), f.String())
		}

		// Check parameters
		for _, p := range f.Parameters {
			if p.Type != nil {
				typesToCheck = append(typesToCheck, p.Type)
			} else {
				return fmt.Errorf("(%s) in function definition %s, parameter %s has a missing type", f.Position.String(), f.String(), p.String())
			}
		}

		// Ensure unique parameter names
		if !AllNamesUnique(f.Parameters) {
			return fmt.Errorf("(%s) in function definition %s, parameter/s %s are defined more than once", f.Position.String(), f.String(), NamesToString(DuplicateNames(f.Parameters)))
		}

		// Modify the types to set their modalities
		labelledTypesEnv := types.ProduceLabelledSessionTypeEnvironment(*globalEnv.Types)
		for i := range typesToCheck {
			types.AddMissingModalities(&typesToCheck[i], labelledTypesEnv)
		}

		// Run the actual checks on the types
		if err := types.SanityChecksType(typesToCheck, *globalEnv.Types); err != nil {
			return fmt.Errorf("(%s) type error in function definition %s; %s", f.Position.String(), f.String(), err)
		}

		// Ensure that for Γ ⊢ P :: (a : A), the declaration of independence (Γ ≥ A) holds
		succedentType := f.Type
		antecedents := f.Parameters
		if err := declationOfIndependence(antecedents, succedentType); err != nil {
			return fmt.Errorf("(%s) type error in function definition %s; %s", f.Position.String(), f.String(), err)
		}
	}

	return nil
}

// Perform similar preliminary checks on process definitions
func preliminaryProcessesChecks(processes []*Process, assumedFreeNames []Name, globalEnv *GlobalEnvironment) error {

	// Make sure that the assumed free names are unique and have an assigned type
	// These are defined using the 'assuming' keyword: assuming a : A, b : B, ...
	if !AllNamesUnique(assumedFreeNames) {
		return fmt.Errorf("in the names assumptions, the free names %s are defined more than once", NamesToString(DuplicateNames(assumedFreeNames)))
	}

	var typesToCheck []types.SessionType
	remainingAssumedFreeNames := make(map[string]bool)
	for _, fn := range assumedFreeNames {
		if fn.Type == nil {
			return fmt.Errorf("the assumed name %s has no declared type. Use 'assuming %s : T' instead", fn.String(), fn.String())
		}

		// This will be used to make sure that all declared free names are used (exactly once) by some process
		remainingAssumedFreeNames[fn.Ident] = true

		typesToCheck = append(typesToCheck, fn.Type)
	}

	// Modify the types to set their modalities
	labelledTypesEnv := types.ProduceLabelledSessionTypeEnvironment(*globalEnv.Types)
	for i := range typesToCheck {
		types.AddMissingModalities(&typesToCheck[i], labelledTypesEnv)
	}

	if err := types.SanityChecksType(typesToCheck, *globalEnv.Types); err != nil {
		return fmt.Errorf("type error when assuming name; %s", err)
	}

	// Check for uniqueness of provider names
	allProcessNames := make(map[string]bool)
	for i := range processes {
		// Check for uniqueness of provider name within the local process definition
		if !AllNamesUnique(processes[i].Providers) {
			return fmt.Errorf("(%s) in process definition %s, the providers contain duplicate names (%s)", processes[i].Position.String(), processes[i].OutlineString(), NamesToString(DuplicateNames(processes[i].Providers)))
		}

		// Check for uniqueness of provider names compared to all processes
		for _, provider := range processes[i].Providers {
			if allProcessNames[provider.Ident] {
				return fmt.Errorf("(%s) in process definition %s, the provider used (%s) is already in use by other processes. Please use a different name", processes[i].Position.String(), processes[i].OutlineString(), provider.Ident)
			}
			allProcessNames[provider.Ident] = true
		}
	}

	// make sure that there aren't any assumed names that are then defined as a process
	for name := range allProcessNames {
		if remainingAssumedFreeNames[name] {
			return fmt.Errorf("the assumed name '%s' is later defined as a process", name)
		}
	}

	// Check the types for the processes (i.e. prc[a] : A = ...)
	for i := range processes {

		// Check the provider type
		var typesToCheck []types.SessionType
		if processes[i].Type != nil {
			typesToCheck = append(typesToCheck, processes[i].Type)
		} else {
			return fmt.Errorf("(%s) process %s has a missing type of provider", processes[i].Position.String(), processes[i].OutlineString())
		}

		// Modify the types to set their modalities
		labelledTypesEnv := types.ProduceLabelledSessionTypeEnvironment(*globalEnv.Types)
		for i := range typesToCheck {
			types.AddMissingModalities(&typesToCheck[i], labelledTypesEnv)
		}

		// Run the checks
		if err := types.SanityChecksType(typesToCheck, *globalEnv.Types); err != nil {
			return fmt.Errorf("(%s) type error in process %s; %s", processes[i].Position.String(), processes[i].OutlineString(), err)
		}

		// Check also that the free names being used exist either as one of the other provider names, or as an assumed free name
		processFreeNames := processes[i].Body.FreeNames()
		// Remove provider names, since those are bound
		processFreeNames = NamesInFirstListOnly(processFreeNames, processes[i].Providers)

		for _, fn := range processFreeNames {
			assumedNameCanBeUsed, foundInAssumed := remainingAssumedFreeNames[fn.Ident]
			processNameCanBeUsed, foundInProcessNames := allProcessNames[fn.Ident]

			if !foundInAssumed && !foundInProcessNames {
				return fmt.Errorf("(%s) in process definition %s, the name %s is not defined. Use 'assuming %s : T'", processes[i].Position.String(), processes[i].OutlineString(), fn.Ident, fn.Ident)
			} else if foundInAssumed && assumedNameCanBeUsed {
				// Referring to an assumed free name
				remainingAssumedFreeNames[fn.Ident] = false
			} else if foundInAssumed && !assumedNameCanBeUsed {
				// Referring to assumed name however it is already used
				return fmt.Errorf("(%s) in process definition %s, the assumed name %s is already used elsewhere", processes[i].Position.String(), processes[i].OutlineString(), fn.Ident)
			} else if foundInProcessNames && processNameCanBeUsed {
				// Referring to a process name
				allProcessNames[fn.Ident] = false
			} else if foundInProcessNames && !processNameCanBeUsed {
				// Referring to process provider name however it is already used
				return fmt.Errorf("(%s) in process definition %s, the process name %s is already used elsewhere", processes[i].Position.String(), processes[i].OutlineString(), fn.Ident)
			}
		}

		// todo check for the declaration of independence here as well
	}

	for name, remainingName := range remainingAssumedFreeNames {
		if remainingName {
			return fmt.Errorf("the assume name %s has never been used", name)
		}
	}

	return nil
}

// Ensure that for Γ ⊢ P :: (a : A), Γ ≥ A, where A is the succedentType
func declationOfIndependence(antecedents []Name, succedentType types.SessionType) error {
	for _, antecedentName := range antecedents {
		err := declationOfIndependenceOne(antecedentName, succedentType)
		if err != nil {
			return err
		}
	}

	return nil
}

// Ensure that left ≥ right
func declationOfIndependenceOne(left Name, rightType types.SessionType) error {
	if !left.Type.Modality().CanBeDownshiftedTo(rightType.Modality()) {
		return fmt.Errorf("declaration of independence error: %s must have a stronger mode than %s", left.Type.StringWithOuterModality(), rightType.StringWithOuterModality())
	}

	return nil
}

/////////////////////////////////////////////////////////
///////////////// Initiate typechecking /////////////////
/////////////////////////////////////////////////////////

func typecheckFunctionDefinitions(globalEnv *GlobalEnvironment) error {
	labelledTypesEnv := types.ProduceLabelledSessionTypeEnvironment(*globalEnv.Types)
	functionDefinitionsEnv := produceFunctionDefinitionsEnvironment(*globalEnv.FunctionDefinitions, labelledTypesEnv)

	for _, funcDef := range *globalEnv.FunctionDefinitions {
		gammaNameTypesCtx := produceNameTypesCtx(funcDef.Parameters)
		// delta contents initiated as empty
		deltaNameTypesCtx := make(NamesTypesCtx)

		faultTolerancePromise := funcDef.FaultTolerancePromise
		providerType := funcDef.Type

		globalEnv.logf(LOGRULE, "Typechecking function definition %s\n", funcDef.String())

		err := funcDef.Body.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, nil, providerType, labelledTypesEnv, functionDefinitionsEnv, globalEnv)
		if err != nil {
			return fmt.Errorf("(%s) typechecking error in function %s; %s", funcDef.Position.String(), funcDef.String(), err)
		}
	}

	return nil
}

// Typecheck each process of the form:
// -> assuming x: B, ...
// -> prc[a] : A = P
// using the judgement as follows:
// -> x: B, ... ⊢ P :: (a : A)
func typecheckProcesses(processes []*Process, assumedFreeNames []Name, globalEnv *GlobalEnvironment) error {
	labelledTypesEnv := types.ProduceLabelledSessionTypeEnvironment(*globalEnv.Types)
	functionDefinitionsEnv := produceFunctionDefinitionsEnvironment(*globalEnv.FunctionDefinitions, labelledTypesEnv)

	for i := range processes {
		// Obtain the free name types (to be set as Gamma)
		freeNames := getFreeNameTypes(processes[i], processes, assumedFreeNames)
		gammaNameTypesCtx := produceNameTypesCtx(freeNames)
		// delta contents initiated at empty
		deltaNameTypesCtx := make(NamesTypesCtx)

		faultTolerancePromise := processes[i].FaultTolerancePromise
		providerType := processes[i].Type

		globalEnv.logf(LOGRULE, "Typechecking process %s\n", processes[i].OutlineString())

		// Run the typechecker
		// might be a good idea to set the shadowProvider name to processes[i].Providers[0] (when there is only one provider)
		err := processes[i].Body.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, nil, providerType, labelledTypesEnv, functionDefinitionsEnv, globalEnv)
		if err != nil {
			return fmt.Errorf("(%s) typechecking error in process '%s'; %s", processes[i].Position.String(), processes[i].OutlineString(), err)
		}
	}

	return nil
}

////////////////////////////////////////////////////////////////
///////////////// Syntax directed typechecking /////////////////
////////////////////////////////////////////////////////////////
/////////////////// x: B, ... ⊢ P :: (a : A) ///////////////////
////////////////////////////////////////////////////////////////

// Each form has a dedicated typechecking function.
// If a type error is found, typecheckForm returns a TypeError -- if there are no errors, the function succeeds, returning nothing

// typecheckForm uses these parameters:
// -> gammaNameTypesCtx   	<- Γ: names in infallible context to be used (in case of linearity, ...)
// -> deltaNameTypesCtz 	<- Δ: names in fallible context to be used (in case of linearity, ...)
// -> faultTolerancePromise	<- level of fault tolerance that the providing process aims to guarantee
// -> providerShadowName    <- name of the process providing on (nil when name 'self' is used instead)
// -> providerType    		<- the type of the provider (i.e. type of provider name 'self')
// -> labelledTypesEnv 		<- [read-only] keeps the mapping of pre-defined types (type A = ...)
// -> sigma           	 	<- [read-only] ∑: keeps the mapping of pre-defined function definitions (def f() : A = ...)
// -> globalEnv           	<- [read-only] contains the logging capabilities

// */-*: send w<u, v>
func (p *SendForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.to_c, providerShadowName) {
		// MulR: *
		globalEnv.log(LOGRULEDETAILS, "rule ⊗R (MulR)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be SendType
		providerSendType, sendTypeOk := providerType.(*types.SendType)

		if !sendTypeOk {
			// wrong type: A * B
			return TypeErrorf("expected '%s' to have a send type (A * B), but found type '%s' instead", p.String(), providerType.String())
		}

		expectedLeftType := providerSendType.Left
		expectedRightType := providerSendType.Right

		expectedLeftType = types.Unfold(expectedLeftType, labelledTypesEnv)
		expectedRightType = types.Unfold(expectedRightType, labelledTypesEnv)

		foundLeftType, payloadTypeEnvironment, errorLeft := consumeName(p.payload_c, gammaNameTypesCtx, deltaNameTypesCtx)

		if payloadTypeEnvironment != GAMMA {
			return TypeErrorf("expected '%s' to have an infallible payload", p.String())
		}

		foundLeftType = types.Unfold(foundLeftType, labelledTypesEnv)

		foundRightType, continuationTypeEnvironment, errorRight := consumeName(p.continuation_c, gammaNameTypesCtx, deltaNameTypesCtx)

		if continuationTypeEnvironment != GAMMA {
			return TypeErrorf("expected '%s' to have an infallible continuation", p.String())
		}

		foundRightType = types.Unfold(foundRightType, labelledTypesEnv)

		if errorLeft != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorLeft)
		}

		if errorRight != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorRight)
		}

		// The expected and found types must match
		if !types.EqualType(expectedLeftType, foundLeftType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.payload_c.String(), expectedLeftType.String(), foundLeftType.String())
		}

		if !types.EqualType(expectedRightType, foundRightType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), expectedRightType.String(), foundRightType.String())
		}

		// Set the types for the names
		p.to_c.Type = providerSendType
		p.payload_c.Type = foundLeftType
		p.continuation_c.Type = foundRightType

	} else if isProvider(p.continuation_c, providerShadowName) {
		// ImpL: -*
		globalEnv.log(LOGRULEDETAILS, "rule ⊸L (ImpL)")

		clientType, toTypeEnvironment, errorClient := consumeName(p.to_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		if toTypeEnvironment != GAMMA {
			return TypeErrorf("expected '%s' to have an infallible 'to' channel", p.String())
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be ReceiveType
		clientReceiveType, clientTypeOk := clientType.(*types.ReceiveType)

		if !clientTypeOk {
			// wrong type: A -* B
			return TypeErrorf("expected '%s' to have a receive type (A -* B), but found type '%s' instead", p.to_c.String(), clientType.String())
		}

		expectedLeftType := clientReceiveType.Left
		expectedRightType := clientReceiveType.Right

		foundLeftType, payloadTypeEnvironment, errorLeft := consumeName(p.payload_c, gammaNameTypesCtx, deltaNameTypesCtx)

		if payloadTypeEnvironment != GAMMA {
			return TypeErrorf("expected '%s' to have an infallible payload", p.String())
		}

		foundRightType, errorRight := consumeNameMaybeSelf(p.continuation_c, providerShadowName, gammaNameTypesCtx, deltaNameTypesCtx, providerType)

		expectedLeftType = types.Unfold(expectedLeftType, labelledTypesEnv)
		expectedRightType = types.Unfold(expectedRightType, labelledTypesEnv)
		foundLeftType = types.Unfold(foundLeftType, labelledTypesEnv)
		foundRightType = types.Unfold(foundRightType, labelledTypesEnv)

		if errorLeft != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorLeft)
		}

		if errorRight != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorRight)
		}

		// The expected and found types must match
		if !types.EqualType(expectedLeftType, foundLeftType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.payload_c.String(), expectedLeftType.String(), foundLeftType.String())
		}

		if !types.EqualType(expectedRightType, foundRightType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), expectedRightType.String(), foundRightType.String())
		}

		// Set the types for the names
		p.to_c.Type = clientReceiveType
		p.payload_c.Type = foundLeftType
		p.continuation_c.Type = foundRightType
	} else if isProvider(p.payload_c, providerShadowName) {
		return TypeErrorf("the send construct requires that you use the self name or send self as a continuation. In '%s', self was used as a payload", p.String())
	} else {
		return TypeErrorf("the send construct requires that you use the self name or send self as a continuation. In '%s', self was not used appropriately", p.String())
	}

	if polarityError := checkExplicitPolarityValidity(p, p.to_c, p.payload_c, p.continuation_c); polarityError != nil {
		return TypeErrorE(polarityError)
	}

	// make sure that no variables are left in gamma and delta
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

// */-*: <x, y> <- recv w; P
func (p *ReceiveForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.from_c, providerShadowName) {
		// ImpR: -*
		globalEnv.log(LOGRULEDETAILS, "rule ⊸R (ImpR)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be ReceiveType
		providerReceiveType, receiveTypeOk := providerType.(*types.ReceiveType)

		if !receiveTypeOk {
			// wrong type: A -* B
			return TypeErrorf("expected '%s' to have a receive type (A -* B), but found type '%s' instead", p.String(), providerType.String())
		}

		newLeftType := providerReceiveType.Left
		newLeftType = types.Unfold(newLeftType, labelledTypesEnv)
		newRightType := providerReceiveType.Right
		newRightType = types.Unfold(newRightType, labelledTypesEnv)

		if nameTypeExists(gammaNameTypesCtx, p.payload_c.Ident) ||
			nameTypeExists(gammaNameTypesCtx, p.continuation_c.Ident) {
			// Names are not fresh
			return TypeErrorf("variable names <%s, %s> already defined. Use unique names in %s", p.payload_c.String(), p.continuation_c.String(), p.String())
		}

		if nameTypeExists(deltaNameTypesCtx, p.payload_c.Ident) ||
			nameTypeExists(deltaNameTypesCtx, p.continuation_c.Ident) {
			// Names are not fresh
			return TypeErrorf("variable names <%s, %s> already defined. Use unique names in %s", p.payload_c.String(), p.continuation_c.String(), p.String())
		}

		if p.payload_c.Equal(p.continuation_c) {
			return TypeErrorf("variable names <%s, %s> are the same. Use unique names", p.payload_c.String(), p.continuation_c.String())
		}

		gammaNameTypesCtx[p.payload_c.Ident] = NamesType{Type: newLeftType}

		p.from_c.Type = providerReceiveType
		p.payload_c.Type = newLeftType
		p.continuation_c.Type = newRightType

		if polarityError := checkExplicitPolarityValidity(p, p.from_c, p.payload_c, p.continuation_c); polarityError != nil {
			return TypeErrorE(polarityError)
		}

		continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, &p.continuation_c, newRightType, labelledTypesEnv, sigma, globalEnv)

		return continuationError
	} else if isProvider(p.payload_c, providerShadowName) || isProvider(p.continuation_c, providerShadowName) {
		return TypeErrorf("you cannot assign self to a new channel (%s)", p.String())
	} else {
		// MulL: *
		globalEnv.log(LOGRULEDETAILS, "rule ⊗L (MulL)")

		clientType, typeEnvironment, errorClient := consumeName(p.from_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		if typeEnvironment != GAMMA {
			return TypeErrorf("expected '%s' to have an infallible 'from' channel", p.String())
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be SendType
		clientSendType, clientTypeOk := clientType.(*types.SendType)

		if !clientTypeOk {
			// wrong type, expected A * B
			return TypeErrorf("expected '%s' to have a send type (A * B), but found type '%s' instead", p.from_c.String(), clientType.String())
		}

		newLeftType := clientSendType.Left
		newLeftType = types.Unfold(newLeftType, labelledTypesEnv)
		newRightType := clientSendType.Right
		newRightType = types.Unfold(newRightType, labelledTypesEnv)

		if nameTypeExists(gammaNameTypesCtx, p.payload_c.Ident) ||
			nameTypeExists(gammaNameTypesCtx, p.continuation_c.Ident) {
			// Names are not fresh [todo check if needed]
			return TypeErrorf("variable names <%s, %s> already defined. Use unique names", p.payload_c.String(), p.continuation_c.String())
		}

		if nameTypeExists(deltaNameTypesCtx, p.payload_c.Ident) ||
			nameTypeExists(deltaNameTypesCtx, p.continuation_c.Ident) {
			return TypeErrorf("variable names <%s, %s> already defined. Use unique names", p.payload_c.String(), p.continuation_c.String())
		}

		if isProvider(p.payload_c, providerShadowName) ||
			isProvider(p.continuation_c, providerShadowName) {
			// Unwanted reference to self
			return TypeErrorf("variable names <%s, %s> should not refer to self", p.payload_c.String(), p.continuation_c.String())
		}

		gammaNameTypesCtx[p.payload_c.Ident] = NamesType{Type: newLeftType}
		gammaNameTypesCtx[p.continuation_c.Ident] = NamesType{Type: newRightType}

		p.from_c.Type = clientSendType
		p.payload_c.Type = newLeftType
		p.continuation_c.Type = newRightType

		if polarityError := checkExplicitPolarityValidity(p, p.from_c, p.payload_c, p.continuation_c); polarityError != nil {
			return TypeErrorE(polarityError)
		}

		continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

		return continuationError
	}
}

// Internal/External Choice: w.l<u>
func (p *SelectForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.to_c, providerShadowName) {
		// IChoiceR: +{label1: T1, ...}
		globalEnv.log(LOGRULEDETAILS, "rule ⊕R (IChoiceR)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be SelectLabelType
		providerSelectLabelType, selectLabelTypeOk := providerType.(*types.SelectLabelType)

		if !selectLabelTypeOk {
			// wrong type, expected +{...}
			return TypeErrorf("expected '%s' to have a select type (+{...}), but found type '%s' instead", p.StringShort(), providerType.String())
		}

		// Match branch by label
		continuationType, continuationTypeFound := types.FetchSelectBranch(providerSelectLabelType.Branches, p.label.L)

		if continuationTypeFound {
			foundContinuationType, _, errorContinuationType := consumeName(p.continuation_c, gammaNameTypesCtx, deltaNameTypesCtx)

			if errorContinuationType != nil {
				return TypeErrorf("error in %s; %s", p.String(), errorContinuationType)
			}

			if !types.EqualType(continuationType, foundContinuationType, labelledTypesEnv) {
				return TypeErrorf("type of '%s' is '%s'. Expected type to be '%s'", p.continuation_c.String(), foundContinuationType.StringWithOuterModality(), continuationType.StringWithOuterModality())
			}

			p.to_c.Type = providerSelectLabelType
			continuationType = types.Unfold(continuationType, labelledTypesEnv)
			p.continuation_c.Type = continuationType
		} else {
			return TypeErrorf("could not match label '%s' (from '%s') with the labels from the type '%s'", p.label.String(), p.String(), providerSelectLabelType.String())
		}
	} else if isProvider(p.continuation_c, providerShadowName) {
		// EChoiceL: &{label1: T1, ...}
		globalEnv.log(LOGRULEDETAILS, "rule &L (EChoiceL)")

		clientType, _, errorClient := consumeName(p.to_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be BranchCaseType
		clientBranchCaseType, clientTypeOk := clientType.(*types.BranchCaseType)

		if !clientTypeOk {
			// wrong type, expected &{...}
			return TypeErrorf("expected '%s' to have a branching type (&{...}), but found type '%s' instead", p.String(), clientType.String())
		}

		// Match branch by label
		continuationType, continuationTypeFound := types.FetchSelectBranch(clientBranchCaseType.Branches, p.label.L)

		if continuationTypeFound {
			foundContinuationType, errorContinuationType := consumeNameMaybeSelf(p.continuation_c, providerShadowName, gammaNameTypesCtx, deltaNameTypesCtx, providerType)

			if errorContinuationType != nil {
				return TypeErrorf("error in %s; %s", p.String(), errorContinuationType)
			}

			if !types.EqualType(continuationType, foundContinuationType, labelledTypesEnv) {
				return TypeErrorf("type of '%s' is '%s'. Expected type to be '%s'", p.continuation_c.String(), foundContinuationType.StringWithOuterModality(), continuationType.StringWithOuterModality())
			}

			// Type ok

			// Set types
			p.to_c.Type = clientBranchCaseType
			p.continuation_c.Type = continuationType
		} else {
			return TypeErrorf("could not match label '%s' (from '%s') with the labels from the type '%s'", p.label.String(), p.String(), clientBranchCaseType.String())
		}
	} else {
		return TypeErrorf("expected '%s' to either receive or send label on 'self', e.g. self.%s<%s> or %s.%s<self>", p.String(), p.label.String(), p.to_c.String(), p.continuation_c.String(), p.label.String())
	}

	// Ensure correct explicit polarities (if used)
	if err := checkExplicitPolarityValidity(p, p.to_c, p.continuation_c); err != nil {
		return TypeErrorE(err)
	}

	// make sure that no variables are left in gamma
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

// Case: case from_c ( branches )
func (p *CaseForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.from_c, providerShadowName) {
		// EChoiceR: &{label1: T1, ...}
		globalEnv.log(LOGRULEDETAILS, "rule &R (EChoiceR)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be BranchCaseType
		providerBranchCaseType, branchCaseTypeOk := providerType.(*types.BranchCaseType)

		if !branchCaseTypeOk {
			// wrong type, expected &{...}
			return TypeErrorf("expected '%s' to have a branching type (&{...}), but found type '%s' instead", p.StringShort(), providerType.String())
		}

		labelsChecked := make(map[string]bool)

		// Check each branch individually
		for _, curBranchForm := range p.branches {
			// Pick each branch ast and match it with its type using the label
			expectedBranchType, typeFound := types.LookupBranchByLabel(providerBranchCaseType.Branches, curBranchForm.label.L)

			// Check for duplicated labels
			if labelsChecked[curBranchForm.label.L] {
				return TypeErrorf("label '%s' in the branch '%s' is duplicated", curBranchForm.label.L, curBranchForm.StringShort())
			}

			labelsChecked[curBranchForm.label.L] = true

			if !typeFound {
				return TypeErrorf("branch labelled '%s' does not match the branches of type '%s'", curBranchForm.StringShort(), providerBranchCaseType.String())
			}

			// Set type
			curBranchForm.payload_c.Type = expectedBranchType.SessionType

			polarityError := checkExplicitPolarityValidity(p, curBranchForm.payload_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}

			// Copy gamma and delta so that each branch has its own version
			newGammaNameTypesCtx := copyContext(gammaNameTypesCtx)
			newDeltaNameTypesCtx := copyContext(deltaNameTypesCtx)

			continuationError := curBranchForm.continuation_e.typecheckForm(newGammaNameTypesCtx, newDeltaNameTypesCtx, faultTolerancePromise, &curBranchForm.payload_c, expectedBranchType.SessionType, labelledTypesEnv, sigma, globalEnv)

			if continuationError != nil {
				return continuationError
			}
		}

		if len(labelsChecked) < len(providerBranchCaseType.Branches) {
			labels := extractUnusedLabels(providerBranchCaseType.Branches, labelsChecked)

			return TypeErrorf("some labels (i.e. %s) from the type '%s' are not pattern matched in the case construct: %s", labels, providerBranchCaseType.String(), p.StringShort())
		}

		// Set type of case
		p.from_c.Type = providerBranchCaseType
	} else {
		// IChoiceL: +{label1: T1, ...}
		globalEnv.log(LOGRULEDETAILS, "rule ⊕L (IChoiceL)")

		clientType, clientTypeEnvironment, errorClient := consumeName(p.from_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.StringShort(), errorClient)
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be SelectLabelType
		clientSelectLabelType, clientTypeOk := clientType.(*types.SelectLabelType)

		if !clientTypeOk {
			// wrong type, expected +{...}
			return TypeErrorf("expected '%s' to have a select type (+{...}), but found type '%s' instead", p.StringShort(), clientType.String())
		}

		labelsChecked := make(map[string]bool)

		// Check each branch individually
		for _, curBranchForm := range p.branches {
			// Pick each branch ast and match it with its type using the label
			expectedBranchType, typeFound := types.LookupBranchByLabel(clientSelectLabelType.Branches, curBranchForm.label.L)

			// Check for duplicated labels
			if labelsChecked[curBranchForm.label.L] {
				return TypeErrorf("label '%s' in the branch '%s' is duplicated", curBranchForm.label.L, curBranchForm.StringShort())
			}

			labelsChecked[curBranchForm.label.L] = true

			if !typeFound {
				return TypeErrorf("case labelled '%s' does not match the branches of type '%s'", curBranchForm.StringShort(), clientSelectLabelType.String())
			}

			// Copy gamma and delta so that each branch has its own version
			newGammaNameTypesCtx := copyContext(gammaNameTypesCtx)
			newDeltaNameTypesCtx := copyContext(deltaNameTypesCtx)

			switch clientTypeEnvironment {
			case GAMMA:
				// curBranchForm.payload_c cannot exist in gammaNameTypesCtx
				newGammaNameTypesCtx[curBranchForm.payload_c.Ident] = NamesType{Type: expectedBranchType.SessionType}
			case DELTA:
				newDeltaNameTypesCtx[curBranchForm.payload_c.Ident] = NamesType{Type: expectedBranchType.SessionType}
			}

			// Set type
			curBranchForm.payload_c.Type = expectedBranchType.SessionType

			polarityError := checkExplicitPolarityValidity(p, curBranchForm.payload_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}

			continuationError := curBranchForm.continuation_e.typecheckForm(newGammaNameTypesCtx, newDeltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			if continuationError != nil {
				return continuationError
			}
		}

		if len(labelsChecked) < len(clientSelectLabelType.Branches) {
			labels := extractUnusedLabels(clientSelectLabelType.Branches, labelsChecked)

			return TypeErrorf("some labels (i.e. %s) from the type '%s' are not pattern matched in the case construct: %s", labels, clientSelectLabelType.String(), p.StringShort())
		}

		// Set type of case
		p.from_c.Type = clientSelectLabelType
	}

	polarityError := checkExplicitPolarityValidity(p, p.from_c)
	if polarityError != nil {
		return TypeErrorE(polarityError)
	}

	return nil
}

// Branch: label<payload_c> => continuation_e
func (p *BranchForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	return TypeErrorf("Cannot typecheck a case/receive branch directly")
}

// New: continuation_c <- new (body); continuation_e
func (p *NewForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// Cut
	globalEnv.log(LOGRULEDETAILS, "rule CUT")

	//	if isProvider(p.new_name_c, providerShadowName) || nameTypeExists(gammaNameTypesCtx, p.new_name_c.Ident) {
	//		// Names are not fresh
	//		return TypeErrorf("the cut rule requires a new variable; %s is already assigned", p.new_name_c.String())
	//	}
	_, new_name_reused := gammaNameTypesCtx[p.new_name_c.Ident]

	if !new_name_reused && nameInNames(p.new_name_c, p.body.FreeNames()...) {
		return TypeErrorf("cannot use '%s' in spawned process (%s). Try using 'self' instead.", p.new_name_c.String(), p.body.StringShort())
	}

	if new_name_reused && !nameInNames(p.new_name_c, p.body.FreeNames()...) {
		return TypeErrorf("name '%s' is reassigned before being used in the spawned process (%s).", p.new_name_c.String(), p.body.StringShort())
	}

	// When 'new' is used directly (i.e. not derived from a macro expansion), then we need to ensure
	// that the body is either a function call, or an axiomatic rule (e.g. send)
	if !p.derivedFromMacro {
		// check form of body
		if FormHasContinuation(p.body) {
			// Difficult to split gamma, so we show it as ill typed for now
			return TypeErrorf("cannot determine variable context splitting in '%s'. Expected the body to be a simple axiomatic rule (e.g. send), but found '%s'", p.StringShort(), p.body.String())
		}

		// We can infer which variables are used when typechecking p.body
		switch interface{}(p.body).(type) {
		case *CallForm:
			callForm := p.body.(*CallForm)

			// first split gamma and delta
			gammaLeftNameTypesCtx, gammaRightNameTypesCtx, deltaLeftNameTypesCtx, deltaRightNameTypesCtx, gammaDeltaErr := splitGammaAndDeltaCtx(gammaNameTypesCtx, deltaNameTypesCtx, callForm.parameters, nil, labelledTypesEnv)

			if new_name_reused {
				// re-add new name after context splitting
				gammaRightNameTypesCtx[p.new_name_c.Ident] = NamesType{Type: p.new_name_c.Type}
			}

			if gammaDeltaErr != nil {
				return TypeErrorf("error when splitting variable context in '%s': %s", p.StringShort(), gammaDeltaErr)
			}
			// Get function signature (incl. its type)
			functionSignature, exists := sigma[callForm.functionName]
			if !exists {
				return TypeErrorf("function '%s' is undefined", p.body.String())
			}

			functionSignatureType := types.CopyType(functionSignature.Type)
			functionSignatureType = types.Unfold(functionSignatureType, labelledTypesEnv)

			// Check for declaration of independence: (Γ ⪰ m)
			// Γ (gammaLeftNameTypesCtx) ⪰ m (type of p.continuation_c)
			err := declationOfIndependence(gammaLeftNameTypesCtx.getNames(), functionSignatureType)
			if err != nil {
				return TypeErrorE(err)
			}

			// Check for declaration of independence: (Δ ⪰ m)
			// Δ (deltaLeftNameTypesCtx) ⪰ m (type of p.continuation_c)
			err = declationOfIndependence(deltaLeftNameTypesCtx.getNames(), functionSignatureType)
			if err != nil {
				return TypeErrorE(err)
			}

			function := GetFunctionByName(*globalEnv.FunctionDefinitions, callForm.functionName)
			if function == nil {
				return TypeErrorf("function '%s' is undefined", p.body.String())
			}

			if function.FaultTolerancePromise < faultTolerancePromise {
				return TypeErrorf("expected fault tolerance promise of at least %d, but found %d", faultTolerancePromise, function.FaultTolerancePromise)
			}
			// Typecheck the call function
			// N.B. type checking with the original ft promise will ensure that the newly spawned process (the function being called) has a ft promise at least as strong as that of its parent, i.e. caters for k >= n check in the CUT rule
			callBodyError := p.body.typecheckForm(gammaLeftNameTypesCtx, deltaLeftNameTypesCtx, faultTolerancePromise, &p.new_name_c, functionSignatureType, labelledTypesEnv, sigma, globalEnv)

			if callBodyError != nil {
				return callBodyError
			}

			// Add new channel name to gamma
			gammaRightNameTypesCtx[p.new_name_c.Ident] = NamesType{Type: functionSignatureType}

			// typecheck the continuation body
			continuationError := p.continuation_e.typecheckForm(gammaRightNameTypesCtx, deltaRightNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			if continuationError != nil {
				return continuationError
			}

			// Set type
			p.new_name_c.Type = functionSignatureType

			// Check for declaration of independence: (m ⪰ o)
			// m (type of p.continuation_c) ⪰ p (providerType)
			err = declationOfIndependenceOne(p.new_name_c, providerType)
			if err != nil {
				return TypeErrorE(err)
			}

			polarityError := checkExplicitPolarityValidity(p, p.new_name_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}
		default:
			// The type of p.continuation_c has to be provided by the user

			// Split gamma and delta
			gammaLeftNameTypesCtx, gammaRightNameTypesCtx, deltaLeftNameTypesCtx, deltaRightNameTypesCtx, gammaDeltaErr := splitGammaAndDeltaCtx(gammaNameTypesCtx, deltaNameTypesCtx, p.body.FreeNames(), nil, labelledTypesEnv)

			if new_name_reused {
				// re-add new name after context splitting
				gammaRightNameTypesCtx[p.new_name_c.Ident] = NamesType{Type: p.new_name_c.Type}
			}

			if gammaDeltaErr != nil {
				return TypeErrorf("error when splitting variable context in '%s': %s", p.StringShort(), gammaDeltaErr)
			}

			if p.new_name_c.Type == nil {
				return TypeErrorf("expected '%s' to have an explicit type in %s", p.new_name_c.String(), p.StringShort())
			}

			// Modify the type of p.continuation_c to set its modalities
			types.AddMissingModalities(&p.new_name_c.Type, labelledTypesEnv)

			// Get type of inner provider
			err := checkNameType(p.new_name_c, labelledTypesEnv)
			if err != nil {
				return TypeErrorf("invalid type for %s in %s: %s", p.new_name_c.String(), p.StringShort(), err)
			}

			// Unfold if needed
			p.new_name_c.Type = types.Unfold(p.new_name_c.Type, labelledTypesEnv)

			// Check for declaration of independence: Γ ⪰ m && Δ ⪰ m && m ⪰ n
			err = declationOfIndependence(gammaLeftNameTypesCtx.getNames(), p.new_name_c.Type)
			if err != nil {
				return TypeErrorE(err)
			}

			err = declationOfIndependence(deltaLeftNameTypesCtx.getNames(), p.new_name_c.Type)
			if err != nil {
				return TypeErrorE(err)
			}

			// m (type of p.continuation_c) ⪰ p (providerType)
			err = declationOfIndependenceOne(p.new_name_c, providerType)
			if err != nil {
				return TypeErrorE(err)
			}

			// typecheck the body of the process being spawned
			// N.B. type checking with the original ft promise will ensure that the newly spawned process has a ft promise at least as strong as that of its parent, i.e. caters for k >= n check in the CUT rule
			bodyError := p.body.typecheckForm(gammaLeftNameTypesCtx, deltaLeftNameTypesCtx, faultTolerancePromise, &p.new_name_c, p.new_name_c.Type, labelledTypesEnv, sigma, globalEnv)

			if bodyError != nil {
				return bodyError
			}

			// Add new channel name to gamma
			p.new_name_c.Type = types.Unfold(p.new_name_c.Type, labelledTypesEnv)
			gammaRightNameTypesCtx[p.new_name_c.Ident] = NamesType{Type: p.new_name_c.Type}

			polarityError := checkExplicitPolarityValidity(p, p.new_name_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}

			// typecheck the continuation of the cut rule
			continuationBodyError := p.continuation_e.typecheckForm(gammaRightNameTypesCtx, deltaRightNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			if continuationBodyError != nil {
				return continuationBodyError
			}
		}

	} else {
		// Since it is derived from a macro, then we assume that the continuation_e is an axiomatic rule (e.g. send) instead of the body -- no macros are currently being used
		panic("todo need to handle macros -- not implemented")
	}

	return nil
}

// New: continuation_c <- spawn (body); continuation_e
func (p *SpawnForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// FalCut
	globalEnv.log(LOGRULEDETAILS, "rule FALCUT")

	_, new_name_reused := deltaNameTypesCtx[p.spawned_name_c.Ident]

	if !new_name_reused && nameInNames(p.spawned_name_c, p.body.FreeNames()...) {
		return TypeErrorf("cannot use '%s' in spawned process (%s). Try using 'self' instead.", p.spawned_name_c.String(), p.body.StringShort())
	}

	if new_name_reused && !nameInNames(p.spawned_name_c, p.body.FreeNames()...) {
		return TypeErrorf("name '%s' is reassigned before being used in the spawned process (%s).", p.spawned_name_c.String(), p.body.StringShort())
	}

	// When 'new' is used directly (i.e. not derived from a macro expansion), then we need to ensure
	// that the body is either a function call, or an axiomatic rule (e.g. send)
	if !p.derivedFromMacro {
		// check form of body
		if FormHasContinuation(p.body) {
			// Difficult to split gamma, so we show it as ill typed for now
			return TypeErrorf("cannot determine variable context splitting in '%s'. Expected the body to be a simple axiomatic rule (e.g. send), but found '%s'", p.StringShort(), p.body.String())
		}

		// We can infer which variables are used when typechecking p.body
		switch interface{}(p.body).(type) {
		case *CallForm:
			callForm := p.body.(*CallForm)

			// first split gamma and delta
			gammaLeftNameTypesCtx, gammaRightNameTypesCtx, deltaLeftNameTypesCtx, deltaRightNameTypesCtx, gammaDeltaErr := splitGammaAndDeltaCtx(gammaNameTypesCtx, deltaNameTypesCtx, callForm.parameters, nil, labelledTypesEnv)

			if new_name_reused {
				// re-add new name after context splitting
				deltaRightNameTypesCtx[p.spawned_name_c.Ident] = NamesType{Type: p.spawned_name_c.Type}
			}

			if gammaDeltaErr != nil {
				return TypeErrorf("error when splitting variable context in '%s': %s", p.StringShort(), gammaDeltaErr)
			}
			// Get function signature (incl. its type)
			functionSignature, exists := sigma[callForm.functionName]
			if !exists {
				return TypeErrorf("function '%s' is undefined", p.body.String())
			}

			functionSignatureType := types.CopyType(functionSignature.Type)
			functionSignatureType = types.Unfold(functionSignatureType, labelledTypesEnv)

			// Check for declaration of independence: (Γ ⪰ m)
			// Γ (gammaLeftNameTypesCtx) ⪰ m (type of p.continuation_c)
			err := declationOfIndependence(gammaLeftNameTypesCtx.getNames(), functionSignatureType)
			if err != nil {
				return TypeErrorE(err)
			}

			// Check for declaration of independence: (Δ ⪰ m)
			// Δ (deltaLeftNameTypesCtx) ⪰ m (type of p.continuation_c)
			err = declationOfIndependence(deltaLeftNameTypesCtx.getNames(), functionSignatureType)
			if err != nil {
				return TypeErrorE(err)
			}

			// ft promise for newly spawned process is set to 0 as it makes no difference for fallible channels
			callFaultTolerancePromise := uint64(0)

			// Typecheck the call function
			callBodyError := p.body.typecheckForm(gammaLeftNameTypesCtx, deltaLeftNameTypesCtx, callFaultTolerancePromise, &p.spawned_name_c, functionSignatureType, labelledTypesEnv, sigma, globalEnv)

			if callBodyError != nil {
				return callBodyError
			}

			// Add new channel name to delta
			deltaRightNameTypesCtx[p.spawned_name_c.Ident] = NamesType{Type: functionSignatureType}

			// typecheck the continuation body
			continuationError := p.continuation_e.typecheckForm(gammaRightNameTypesCtx, deltaRightNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			if continuationError != nil {
				return continuationError
			}

			// Set type
			p.spawned_name_c.Type = functionSignatureType

			// Check for declaration of independence: (m ⪰ n)
			// m (type of p.continuation_c) ⪰ p (providerType)
			err = declationOfIndependenceOne(p.spawned_name_c, providerType)
			if err != nil {
				return TypeErrorE(err)
			}

			polarityError := checkExplicitPolarityValidity(p, p.spawned_name_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}
		default:
			// The type of p.continuation_c has to be provided by the user

			// Split gamma and delta
			gammaLeftNameTypesCtx, gammaRightNameTypesCtx, deltaLeftNameTypesCtx, deltaRightNameTypesCtx, gammaDeltaErr := splitGammaAndDeltaCtx(gammaNameTypesCtx, deltaNameTypesCtx, p.body.FreeNames(), nil, labelledTypesEnv)

			if new_name_reused {
				// re-add new name after context splitting
				deltaRightNameTypesCtx[p.spawned_name_c.Ident] = NamesType{Type: p.spawned_name_c.Type}
			}

			if gammaDeltaErr != nil {
				return TypeErrorf("error when splitting variable context in '%s': %s", p.StringShort(), gammaDeltaErr)
			}

			if p.spawned_name_c.Type == nil {
				return TypeErrorf("expected '%s' to have an explicit type in %s", p.spawned_name_c.String(), p.StringShort())
			}

			// Modify the type of p.continuation_c to set its modalities
			types.AddMissingModalities(&p.spawned_name_c.Type, labelledTypesEnv)

			// Get type of inner provider
			err := checkNameType(p.spawned_name_c, labelledTypesEnv)
			if err != nil {
				return TypeErrorf("invalid type for %s in %s: %s", p.spawned_name_c.String(), p.StringShort(), err)
			}

			// Unfold if needed
			p.spawned_name_c.Type = types.Unfold(p.spawned_name_c.Type, labelledTypesEnv)

			// Check for declaration of independence: Γ ⪰ m && Δ ⪰ m && m ⪰ n
			err = declationOfIndependence(gammaLeftNameTypesCtx.getNames(), p.spawned_name_c.Type)
			if err != nil {
				return TypeErrorE(err)
			}

			err = declationOfIndependence(deltaLeftNameTypesCtx.getNames(), p.spawned_name_c.Type)
			if err != nil {
				return TypeErrorE(err)
			}

			// m (type of p.continuation_c) ⪰ p (providerType)
			err = declationOfIndependenceOne(p.spawned_name_c, providerType)
			if err != nil {
				return TypeErrorE(err)
			}

			// ft promise for newly spawned process is set to 0 as it makes no difference for fallible channels
			newProcessFaultTolerancePromise := uint64(0)

			// typecheck the body of the process being spawned
			bodyError := p.body.typecheckForm(gammaLeftNameTypesCtx, deltaLeftNameTypesCtx, newProcessFaultTolerancePromise, &p.spawned_name_c, p.spawned_name_c.Type, labelledTypesEnv, sigma, globalEnv)

			if bodyError != nil {
				return bodyError
			}

			// Add new channel name to delta
			p.spawned_name_c.Type = types.Unfold(p.spawned_name_c.Type, labelledTypesEnv)
			deltaRightNameTypesCtx[p.spawned_name_c.Ident] = NamesType{Type: p.spawned_name_c.Type}

			polarityError := checkExplicitPolarityValidity(p, p.spawned_name_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}

			// typecheck the continuation of the falcut rule
			continuationBodyError := p.continuation_e.typecheckForm(gammaRightNameTypesCtx, deltaRightNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			if continuationBodyError != nil {
				return continuationBodyError
			}
		}

	} else {
		// Since it is derived from a macro, then we assume that the continuation_e is an axiomatic rule (e.g. send) instead of the body -- no macros are currently being used
		panic("todo need to handle macros -- not implemented")
	}

	return nil
}

// 1 : close w
func (p *CloseForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// EndR: 1
	globalEnv.log(LOGRULEDETAILS, "rule 1R (EndR)")

	providerType = types.Unfold(providerType, labelledTypesEnv)

	if isProvider(p.from_c, providerShadowName) {
		providerUnitType, unitTypeOk := providerType.(*types.UnitType)

		if !unitTypeOk {
			return TypeErrorf("expected '%s' to have a unit type (1), but found type '%s' instead", p.String(), providerType.String())
		}

		p.from_c.Type = providerUnitType

		polarityError := checkExplicitPolarityValidity(p, p.from_c)
		if polarityError != nil {
			return TypeErrorE(polarityError)
		}
	} else {
		// Closing on the wrong name
		_, unitTypeOk := providerType.(*types.UnitType)

		if unitTypeOk {
			return TypeErrorf("expected '%s' to close on 'self' instead", p.String())
		} else {
			return TypeErrorf("expected '%s' to have a unit type (1), but found type '%s' instead", p.String(), providerType.String())
		}
	}

	// make sure that no variables are left in gamma and delta
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

// 1 : wait w; ...
func (p *WaitForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// EndL: 1
	globalEnv.log(LOGRULEDETAILS, "rule 1L (EndL)")

	// Can only wait for a client (not self)
	if isProvider(p.to_c, providerShadowName) {
		// Waiting on the wrong name
		providerType = types.Unfold(providerType, labelledTypesEnv)
		_, unitTypeOk := providerType.(*types.UnitType)

		if unitTypeOk {
			return TypeErrorf("expected '%s' to have a wait on a 'non-self' channel instead (%s is acting as self)", p.String(), p.to_c.String())
		} else {
			return TypeErrorf("expected '%s' to have a unit type (1), but found type '%s' instead", p.String(), providerType.String())
		}
	}

	clientType, typeEnvironment, errorClient := consumeName(p.to_c, gammaNameTypesCtx, deltaNameTypesCtx)
	if errorClient != nil {
		return TypeErrorf("error in %s; %s", p.String(), errorClient)
	}

	if typeEnvironment != GAMMA {
		return TypeErrorf("expected to wait on an infallible channel, instead found a fallible channel")
	}

	clientType = types.Unfold(clientType, labelledTypesEnv)
	// The type of the client must be UnitType
	clientUnitType, clientTypeOk := clientType.(*types.UnitType)

	if clientTypeOk {
		// Set type
		p.to_c.Type = clientUnitType

		polarityError := checkExplicitPolarityValidity(p, p.to_c)
		if polarityError != nil {
			return TypeErrorE(polarityError)
		}

		// Continue checking the remaining process
		continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

		return continuationError
	} else {
		return TypeErrorf("expected '%s' to have a unit type (1), but found type '%s' instead", p.to_c.String(), clientType.String())
	}
}

// fwd w u
func (p *ForwardForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// ID: 1
	globalEnv.log(LOGRULEDETAILS, "rule ID/FWD")

	if isProvider(p.from_c, providerShadowName) {
		return TypeErrorf("forwarding to self (%s) is not allowed. Use 'fwd %s %s' instead)", p.String(), p.from_c.String(), p.to_c.String())
	}

	if !isProvider(p.to_c, providerShadowName) {
		return TypeErrorf("not forwarding on self (%s). Expected forward to refer to self (fwd %s %s)", p.String(), p.from_c.String(), p.to_c.String())
	}

	clientType, _, errorClient := consumeName(p.from_c, gammaNameTypesCtx, deltaNameTypesCtx)
	clientType = types.Unfold(clientType, labelledTypesEnv)
	if errorClient != nil {
		return TypeErrorf("error in %s; %s", p.String(), errorClient)
	}

	if !types.EqualType(providerType, clientType, labelledTypesEnv) {
		return TypeErrorf("problem in %s: type of %s (%s) and %s (%s) do not match", p.String(), p.to_c.String(), providerType.String(), p.from_c.String(), clientType.String())
	}

	// Check polarities
	providerType = types.Unfold(providerType, labelledTypesEnv)
	if clientType.Polarity() != providerType.Polarity() {
		// Make sure that the polarities match
		return TypeErrorf("invalid polarities in %s: name '%s' is %s, while '%s' is %s", p.StringShort(), p.to_c.String(), types.PolarityMap[providerType.Polarity()], p.from_c.String(), types.PolarityMap[clientType.Polarity()])
	}

	// Set types
	p.to_c.Type = providerType
	p.from_c.Type = clientType

	// compare annotated polarities
	if polarityError := checkExplicitPolarityValidity(p, p.to_c, p.from_c); polarityError != nil {
		return TypeErrorE(polarityError)
	}

	// make sure that no variables are left in gamma
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

// drop w; ...
func (p *DropForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// Drop
	globalEnv.log(LOGRULEDETAILS, "rule DROP")

	// Can only wait for a client (not self)
	if !isProvider(p.client_c, providerShadowName) {
		clientType, _, errorClient := consumeName(p.client_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		if types.IsWeakenable(clientType) {
			// Set type
			p.client_c.Type = clientType

			// compare annotated polarities
			polarityError := checkExplicitPolarityValidity(p, p.client_c)
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}

			// Continue checking the remaining process
			continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

			return continuationError
		} else {
			return TypeErrorf("unable to drop %s, which is in %s mode", p.client_c.String(), clientType.Modality().FullString())
		}
	} else {
		// Wrongly dropping self
		return TypeErrorf("expected '%s' to have a drop on a 'non-self' channel instead (i.e. incorrectly dropping '%s')", p.String(), p.client_c.String())
	}
}

// f(...)
func (p *CallForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	globalEnv.log(LOGRULEDETAILS, "rule CALL")

	// Check that function exists
	functionSignature, exists := sigma[p.functionName]
	if !exists {
		return TypeErrorf("function '%s' is undefined", p.String())
	}

	// Check that the arity matches
	if len(functionSignature.Parameters)+1 == len(p.parameters) {
		// Parameters being passed include a reference to 'self' as the first element

		if !p.parameters[0].IsSelf && !(providerShadowName != nil && providerShadowName.Ident == p.parameters[0].Ident) {
			return TypeErrorf("error in %s; expected first parameter of function call to be 'self', but found '%s'", p.String(), p.parameters[0].String())
		}

		// Check type of self
		if !types.EqualType(providerType, functionSignature.Type, labelledTypesEnv) {
			return TypeErrorf("type error in function call '%s'. Name '%s' has type '%s', but expected '%s'", p.String(), p.parameters[0].String(), providerType.String(), functionSignature.Type.String())
		}

		// Check types of each parameter
		for i := 1; i < len(p.parameters); i++ {
			foundParamType, _, paramTypeError := consumeName(p.parameters[i], gammaNameTypesCtx, deltaNameTypesCtx)

			if paramTypeError != nil {
				return TypeErrorf("error in %s; %s", p.String(), paramTypeError)
			}

			expectedType := functionSignature.Parameters[i-1].Type

			if !types.EqualType(foundParamType, expectedType, labelledTypesEnv) {
				return TypeErrorf("type error in function call '%s'. Name '%s' has type '%s', but expected '%s'", p.String(), p.parameters[i].String(), foundParamType.String(), expectedType.String())
			}

			// Set types
			p.parameters[i].Type = foundParamType

			// compare annotated polarities
			polarityError := checkExplicitPolarityValidity(p, p.parameters[i])
			if polarityError != nil {
				return TypeErrorE(polarityError)
			}
		}
	} else if len(functionSignature.Parameters) == len(p.parameters) {
		// 'self' is not included in the parameters

		// Check type of self
		if !types.EqualType(providerType, functionSignature.Type, labelledTypesEnv) {
			providerName := "self"
			if providerShadowName != nil {
				providerName = providerShadowName.String()
			}

			return TypeErrorf("type error in function call '%s'. Provider '%s' has type '%s', but %s expects '%s'", p.String(), providerName, providerType.String(), p.functionName, functionSignature.Type.String())
		}

		// Check types of each parameter
		for i := 0; i < len(p.parameters); i++ {
			foundParamType, _, paramTypeError := consumeName(p.parameters[i], gammaNameTypesCtx, deltaNameTypesCtx)

			if paramTypeError != nil {
				return TypeErrorf("error in %s; %s", p.String(), paramTypeError)
			}

			expectedType := functionSignature.Parameters[i].Type

			if !types.EqualType(foundParamType, expectedType, labelledTypesEnv) {
				return TypeErrorf("type error in function call '%s'. Name '%s' has type '%s', but expected '%s'", p.String(), p.parameters[i].String(), foundParamType.String(), expectedType.String())
			}

			// Set types
			p.parameters[i].Type = foundParamType

			// compare annotated polarities
			if polarityError := checkExplicitPolarityValidity(p, p.parameters[i]); polarityError != nil {
				return TypeErrorE(polarityError)
			}
		}
	} else {
		// Wrong number of parameters
		return TypeErrorf("wrong number of parameters in function call '%s'. Expected %d, but found %d parameters", p.String(), len(functionSignature.Parameters), len(p.parameters))
	}

	// Set type
	p.ProviderType = functionSignature.Type

	// make sure that no variables are left in gamma and delta
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

// Let: let bound_var = val in continuation_e
func (p *LetForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	globalEnv.log(LOGRULEDETAILS, "rule LET")

	if nameTypeExists(gammaNameTypesCtx, p.bound_var.Ident) {
		return TypeErrorf("variable name '%s' already defined. Use a unique name", p.bound_var.String())
	}

	if nameTypeExists(deltaNameTypesCtx, p.bound_var.Ident) {
		return TypeErrorf("variable name '%s' already defined. Use a unique name", p.bound_var.String())
	}

	// adding the bound variable channel to gamma, treated as infallible since values are considered infallible
	gammaNameTypesCtx[p.bound_var.Ident] = NamesType{Type: types.NewNatType(types.DefaultMode())}

	// setting the types
	p.bound_var.Type = types.NewNatType(types.DefaultMode())

	if polarityError := checkExplicitPolarityValidity(p, p.bound_var); polarityError != nil {
		return TypeErrorE(polarityError)
	}

	continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

	return continuationError
}

// Sync: bridge_c <- sync <channels_to_be_synced>; continuation_e
func (p *SyncForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	globalEnv.log(LOGRULEDETAILS, "rule SYNC")

	if len(p.channels_to_be_synced) < 1 {
		return TypeErrorf("expected '%s' to sync at least one dependency, but found 0", p.StringShort())
	}

	// handles k > n check in the SYNC rule
	if len(p.channels_to_be_synced) <= int(faultTolerancePromise) {
		return TypeErrorf("cannot guarantee the specified fault tolerance promise as not enough dependencies being synced, required at least %d + 1 dependencies", faultTolerancePromise)
	}

	providedTypesOfSyncedChans := make([]types.SessionType, len(p.channels_to_be_synced))

	for i, fallibleChannel := range p.channels_to_be_synced {
		// Can only wait for a client (not self)
		if isProvider(fallibleChannel, providerShadowName) {
			return TypeErrorf("expected '%s' to sync a dependency, not itself ('%s' is acting as self)", p.StringShort(), fallibleChannel.String())
		}

		foundType, typeEnvironment, err := consumeName(fallibleChannel, gammaNameTypesCtx, deltaNameTypesCtx)

		if typeEnvironment != DELTA {
			return TypeErrorf("expected fallible dependency '%s' to be found in Δ but it wasn't", fallibleChannel.String())
		}

		foundType = types.Unfold(foundType, labelledTypesEnv)

		providedTypesOfSyncedChans[i] = foundType

		if err != nil {
			return TypeErrorE(err)
		}
	}

	if !allTypesBeingSyncedAreEqual(providedTypesOfSyncedChans, labelledTypesEnv) {
		return TypeErrorf("expected '%s' to sync dependencies of the same type", p.StringShort())
	}

	// if types of channels being synced are equal, then this variable is used as the type of the bridge channel
	typeOfSyncedChans := providedTypesOfSyncedChans[0]

	if !typeOfSyncedChans.IsSynchronisable() {
		return TypeErrorf("type of replicas is not synchronisable.")
	}

	if nameTypeExists(gammaNameTypesCtx, p.bridge_c.Ident) {
		return TypeErrorf("variable name '%s' already defined. Use a unique name", p.bridge_c.String())
	}

	if nameTypeExists(deltaNameTypesCtx, p.bridge_c.Ident) {
		return TypeErrorf("variable name '%s' already defined. Use a unique name", p.bridge_c.String())
	}

	// adding the infallible bridge channel to gamma
	gammaNameTypesCtx[p.bridge_c.Ident] = NamesType{Type: typeOfSyncedChans}

	// setting the types
	p.bridge_c.Type = typeOfSyncedChans
	for i := range p.channels_to_be_synced {
		p.channels_to_be_synced[i].Type = typeOfSyncedChans
	}

	combinedNamesForPolarityCheck := append(p.channels_to_be_synced, p.bridge_c)
	polarityError := checkExplicitPolarityValidity(p, combinedNamesForPolarityCheck...)
	if polarityError != nil {
		return TypeErrorE(polarityError)
	}

	continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

	return continuationError
}

// boom from_c
func (p *BoomForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {

	globalEnv.log(LOGRULEDETAILS, "rule BOOM")

	providerType = types.Unfold(providerType, labelledTypesEnv)

	if isProvider(p.from_c, providerShadowName) {
		p.from_c.Type = providerType

		polarityError := checkExplicitPolarityValidity(p, p.from_c)
		if polarityError != nil {
			return TypeErrorE(polarityError)
		}
	} else {
		// inducing a fault on the wrong name
		return TypeErrorf("expected '%s' to induce a fault on 'self' instead", p.String())
	}

	// make sure that no variables are left in gamma and delta
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}

	return nil
}

// this is a runtime construct and so does not need type-checking
func (p *SyncStateForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	return TypeErrorf("Cannot typecheck a sync state as it is a runtime construct")
}

// this is a runtime construct and so does not need type-checking
func (p *IntSyncStateForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	return TypeErrorf("Cannot typecheck an intermediate sync state as it is a runtime construct")
}

// this is a runtime construct and so does not need type-checking
func (p *ClsSyncStateForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	return TypeErrorf("Cannot typecheck a close sync state as it is a runtime construct")
}

// Split: <channel_one, channel_two> <- split from_c; P
func (p *SplitForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	globalEnv.log(LOGRULEDETAILS, "rule SPLIT")

	// Can only wait for a client (not self)
	if isProvider(p.from_c, providerShadowName) {
		return TypeErrorf("expected '%s' to have a split a client, not itself ('%s' is acting as self)", p.StringShort(), p.from_c.String())
	}

	foundType, typeEnvironment, err := consumeName(p.from_c, gammaNameTypesCtx, deltaNameTypesCtx)
	foundType = types.Unfold(foundType, labelledTypesEnv)

	if err != nil {
		return TypeErrorE(err)
	}

	// Ensure new names
	if nameTypeExists(gammaNameTypesCtx, p.channel_one.Ident) ||
		nameTypeExists(gammaNameTypesCtx, p.channel_two.Ident) {
		// Names are not fresh
		return TypeErrorf("variable names <%s, %s> already defined. Use unique names", p.channel_one.String(), p.channel_two.String())
	}

	if nameTypeExists(deltaNameTypesCtx, p.channel_one.Ident) ||
		nameTypeExists(deltaNameTypesCtx, p.channel_two.Ident) {
		// Names are not fresh
		return TypeErrorf("variable names <%s, %s> already defined. Use unique names", p.channel_one.String(), p.channel_two.String())
	}

	if p.channel_one.Equal(p.channel_two) {
		return TypeErrorf("variable names <%s, %s> are the same. Use unique names", p.channel_one.String(), p.channel_two.String())
	}

	switch typeEnvironment {
	case GAMMA:
		gammaNameTypesCtx[p.channel_one.Ident] = NamesType{Type: foundType}
		gammaNameTypesCtx[p.channel_two.Ident] = NamesType{Type: foundType} //todo not sure if i need to use CopyType
	case DELTA:
		deltaNameTypesCtx[p.channel_one.Ident] = NamesType{Type: foundType}
		deltaNameTypesCtx[p.channel_two.Ident] = NamesType{Type: foundType}
	}

	if !types.IsContractable(foundType) {
		return TypeErrorf("unable to split %s, which is in %s mode", p.from_c.String(), foundType.Modality().FullString())
	}

	// Set type
	p.from_c.Type = foundType
	p.channel_one.Type = foundType
	p.channel_two.Type = foundType

	// compare annotated polarities
	if polarityError := checkExplicitPolarityValidity(p, p.from_c, p.channel_one, p.channel_two); polarityError != nil {
		return TypeErrorE(polarityError)
	}

	// Continue checking the remaining process
	continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

	return continuationError
}

func (p *CastForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.to_c, providerShadowName) {
		// Downshift DnSR: \/
		globalEnv.log(LOGRULEDETAILS, "rule ↓R (DnSR, Cast)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be DownType
		providerDownType, downTypeOk := providerType.(*types.DownType)

		if !downTypeOk {
			// wrong type: m \/ m A
			return TypeErrorf("expected '%s' to have a downshift type (i.e. \\/), but found type '%s' instead", p.String(), providerType.String())
		}

		// Check that m1 can be downshifted to m2: m1 \/ m2
		if !providerDownType.From.CanBeDownshiftedTo(providerDownType.To) {
			// This should never happen if the type is well formed
			return TypeErrorf("the type '%s' of '%s' has an improper downshift type, i.e. '%s' cannot be downshifted to '%s'", providerDownType.String(), p.String(), providerDownType.From.String(), providerDownType.To.String())
		}

		expectedContinuationType := providerDownType.Continuation
		expectedContinuationType = types.Unfold(expectedContinuationType, labelledTypesEnv)

		foundContinuationType, _, errorContinuation := consumeName(p.continuation_c, gammaNameTypesCtx, deltaNameTypesCtx)
		foundContinuationType = types.Unfold(foundContinuationType, labelledTypesEnv)

		if errorContinuation != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorContinuation)
		}

		// Expect that the modalities match
		if !providerDownType.From.Equals(foundContinuationType.Modality()) {
			return TypeErrorf("expected mode of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), providerDownType.From.String(), foundContinuationType.Modality().String())
		}

		// The expected and found types must match
		if !types.EqualType(expectedContinuationType, foundContinuationType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), expectedContinuationType.String(), foundContinuationType.String())
		}

		// Set the types for the names
		p.to_c.Type = providerDownType
		p.continuation_c.Type = foundContinuationType
	} else if isProvider(p.continuation_c, providerShadowName) {
		// Downshift UpSL: /\
		globalEnv.log(LOGRULEDETAILS, "rule ↑L (UpSL, Cast)")

		clientType, _, errorClient := consumeName(p.to_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be UpType
		clientUpType, clientTypeOk := clientType.(*types.UpType)

		if !clientTypeOk {
			// wrong type: A /\ B
			return TypeErrorf("expected '%s' to have an upshift type (i.e. /\\), but found type '%s' instead", p.to_c.String(), clientType.String())
		}

		// Check that m1 can be downshifted to m2: m1 \/ m2
		if !clientUpType.From.CanBeUpshiftedTo(clientUpType.To) {
			// This should never happen if the type is well formed
			return TypeErrorf("the type '%s' of '%s' has an improper upshift type, i.e. '%s' cannot be upshifted to '%s'", clientUpType.String(), p.String(), clientUpType.From.String(), clientUpType.To.String())
		}

		expectedContinuationType := clientUpType.Continuation
		foundContinuationType, errorContinuation := consumeNameMaybeSelf(p.continuation_c, providerShadowName, gammaNameTypesCtx, deltaNameTypesCtx, providerType)

		expectedContinuationType = types.Unfold(expectedContinuationType, labelledTypesEnv)
		foundContinuationType = types.Unfold(foundContinuationType, labelledTypesEnv)

		if errorContinuation != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorContinuation)
		}

		// Expect that the modalities match
		if !clientUpType.From.Equals(foundContinuationType.Modality()) {
			return TypeErrorf("expected mode of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), clientUpType.From.String(), foundContinuationType.Modality().String())
		}

		// The expected and found types must match
		if !types.EqualType(expectedContinuationType, foundContinuationType, labelledTypesEnv) {
			return TypeErrorf("expected type of '%s' to be '%s', but found type '%s' instead", p.continuation_c.String(), expectedContinuationType.String(), foundContinuationType.String())
		}

		// Set the types for the names
		p.to_c.Type = clientUpType
		p.continuation_c.Type = foundContinuationType
	} else {
		return TypeErrorf("the case construct requires that you cast to 'self' or cast 'self' as the continuation. In '%s', 'self' was not used", p.String())
	}

	if polarityError := checkExplicitPolarityValidity(p, p.to_c, p.continuation_c); polarityError != nil {
		return TypeErrorE(polarityError)
	}

	// make sure that no variables are left in gamma and delta
	if err := linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx); err != nil {
		return TypeErrorE(err)
	}
	return nil
}

func (p *ShiftForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	if isProvider(p.from_c, providerShadowName) {
		// UpSR: /\
		globalEnv.log(LOGRULEDETAILS, "rule ↑R (UpSR, Shift)")

		providerType = types.Unfold(providerType, labelledTypesEnv)
		// The type of the provider must be UpType
		providerUpType, upTypeOk := providerType.(*types.UpType)

		if !upTypeOk {
			// wrong type: m /\ m A
			return TypeErrorf("expected '%s' to have an upshift type (i.e. /\\), but found type '%s' instead", p.String(), providerType.String())
		}

		// Check that m1 can be shifted to m2: m1 /\ m2
		if !providerUpType.From.CanBeUpshiftedTo(providerUpType.To) {
			// This should never happen if the type is well formed
			return TypeErrorf("the type '%s' of '%s' has an improper upshift type, i.e. '%s' cannot be upshifted to '%s'", providerUpType.String(), p.String(), providerUpType.From.String(), providerUpType.To.String())
		}

		expectedContinuationType := providerUpType.Continuation
		expectedContinuationType = types.Unfold(expectedContinuationType, labelledTypesEnv)

		if nameTypeExists(gammaNameTypesCtx, p.continuation_c.Ident) {
			// Names are not fresh
			return TypeErrorf("variable names '%s' is already defined. Use unique name in %s", p.continuation_c.String(), p.String())
		}

		if nameTypeExists(deltaNameTypesCtx, p.continuation_c.Ident) {
			// Names are not fresh
			return TypeErrorf("variable names '%s' is already defined. Use unique name in %s", p.continuation_c.String(), p.String())
		}

		p.from_c.Type = providerUpType
		p.continuation_c.Type = expectedContinuationType

		if polarityError := checkExplicitPolarityValidity(p, p.from_c, p.continuation_c); polarityError != nil {
			return TypeErrorE(polarityError)
		}

		continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, &p.continuation_c, expectedContinuationType, labelledTypesEnv, sigma, globalEnv)

		return continuationError
	} else if isProvider(p.continuation_c, providerShadowName) {
		return TypeErrorf("you cannot assign self to a new channel (%s)", p.String())
	} else {
		// DnSL: \/
		globalEnv.log(LOGRULEDETAILS, "rule ↓L (DnSL, Shift)")

		clientType, clientTypeEnvironment, errorClient := consumeName(p.from_c, gammaNameTypesCtx, deltaNameTypesCtx)
		if errorClient != nil {
			return TypeErrorf("error in %s; %s", p.String(), errorClient)
		}

		clientType = types.Unfold(clientType, labelledTypesEnv)
		// The type of the client must be DownType
		clientDownType, clientTypeOk := clientType.(*types.DownType)

		if !clientTypeOk {
			// wrong type, expected A \/ B
			return TypeErrorf("expected '%s' to have a downshift type (i.e. \\/), but found type '%s' instead", p.from_c.String(), clientType.String())
		}

		// Check that m1 can be shifted to m2: m1 \/ m2
		if !clientDownType.From.CanBeDownshiftedTo(clientDownType.To) {
			// This should never happen if the type is well formed
			return TypeErrorf("the type '%s' of '%s' has an improper downshift type, i.e. '%s' cannot be upshifted to '%s'", clientDownType.String(), p.String(), clientDownType.From.String(), clientDownType.To.String())
		}

		newContinuationType := clientDownType.Continuation
		newContinuationType = types.Unfold(newContinuationType, labelledTypesEnv)

		if nameTypeExists(gammaNameTypesCtx, p.continuation_c.Ident) {
			return TypeErrorf("variable name '%s' is already defined. Use unique names", p.continuation_c.String())
		}

		if nameTypeExists(deltaNameTypesCtx, p.continuation_c.Ident) {
			return TypeErrorf("variable name '%s' is already defined. Use unique names", p.continuation_c.String())
		}

		if isProvider(p.continuation_c, providerShadowName) {
			// Unwanted reference to self
			return TypeErrorf("variable names '%s' should not refer to self", p.continuation_c.String())
		}

		switch clientTypeEnvironment {
		case GAMMA:
			gammaNameTypesCtx[p.continuation_c.Ident] = NamesType{Type: newContinuationType}
		case DELTA:
			deltaNameTypesCtx[p.continuation_c.Ident] = NamesType{Type: newContinuationType}
		}

		p.from_c.Type = clientDownType
		p.continuation_c.Type = newContinuationType

		if polarityError := checkExplicitPolarityValidity(p, p.from_c, p.continuation_c); polarityError != nil {
			return TypeErrorE(polarityError)
		}

		continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)

		return continuationError
	}
}

func (p *PrintForm) typecheckForm(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, faultTolerancePromise uint64, providerShadowName *Name, providerType types.SessionType, labelledTypesEnv types.LabelledTypesEnv, sigma FunctionTypesEnv, globalEnv *GlobalEnvironment) *TypeError {
	// Print
	globalEnv.log(LOGRULEDETAILS, "rule PRINT")

	// Continue checking the remaining process
	continuationError := p.continuation_e.typecheckForm(gammaNameTypesCtx, deltaNameTypesCtx, faultTolerancePromise, providerShadowName, providerType, labelledTypesEnv, sigma, globalEnv)
	return continuationError
}

/////////////////////////////////////////////////////
///////////////// Fixed Environment /////////////////
/////////////////////////////////////////////////////

// FunctionTypesEnv is a fixed Environments: Set once at the beginning and only read from it
// It is represented by sigma (∑) in the type system, where it maps function names to the function type
type FunctionTypesEnv map[string]FunctionType

type FunctionType struct {
	FunctionName string
	Parameters   []Name
	Type         types.SessionType
}

func produceFunctionDefinitionsEnvironment(functionDefs []FunctionDefinition, labelledTypesEnv types.LabelledTypesEnv) FunctionTypesEnv {
	functionTypesEnv := make(FunctionTypesEnv)
	for _, j := range functionDefs {
		functionTypesEnv[j.FunctionName] = FunctionType{Type: types.Unfold(j.Type, labelledTypesEnv), FunctionName: j.FunctionName, Parameters: j.Parameters}
	}

	return functionTypesEnv
}

//////////////////////////////////////////////////////
/////////////////// Typing Context ///////////////////
//////////////////////////////////////////////////////

// NamesTypesCtx is a dynamic context used to keep track of the available names/channels (& their types)
// It maps names to their types and is represented by gamma (Γ) in the type system
type NamesTypesCtx map[string]NamesType

type NamesType struct {
	Name Name
	Type types.SessionType
}

func (namesTypesCtx NamesTypesCtx) getNames() (result []Name) {
	for _, v := range namesTypesCtx {
		result = append(result, v.Name)
	}

	return result
}

func produceNameTypesCtx(names []Name) NamesTypesCtx {
	namesTypesCtx := make(NamesTypesCtx)
	for _, j := range names {
		namesTypesCtx[j.Ident] = NamesType{Type: j.Type, Name: j}
	}

	return namesTypesCtx
}

func nameTypeExists(namesTypesCtx NamesTypesCtx, key string) bool {
	_, ok := namesTypesCtx[key]
	return ok
}

// Deep copies a map
func copyContext(orig NamesTypesCtx) NamesTypesCtx {
	copy := make(NamesTypesCtx)
	for k, v := range orig {
		copy[k] = v
	}

	return copy
}

///////////////////////////////////////////////////////
/////////////////// Error Structure ///////////////////
///////////////////////////////////////////////////////

// TypeError is the type of error when parsing a process.
type TypeError struct {
	Desc string
}

func (e *TypeError) Error() string {
	return e.Desc
}

// Create type error by formatting a string
func TypeErrorf(message string, args ...interface{}) *TypeError {
	return &TypeError{
		Desc: fmt.Sprintf(message, args...),
	}
}

// Create TypeError from a generic error
func TypeErrorE(err error) *TypeError {
	return &TypeError{
		Desc: err.Error(),
	}
}

//////////////////////////////////////////////////////
/////////////////// Util Functions ///////////////////
//////////////////////////////////////////////////////

// we check whether a channel is the provider (i.e. either self of same as the explicit provider name)
// E.g. the channel being sent to is the provider for these cases:
// -> send self<b, c>
// -> send a<b, c> (where a is the provider)
func isProvider(name Name, providerShadowName *Name) bool {
	if name.IsSelf {
		return true
	}

	if providerShadowName != nil {
		return name.Ident == providerShadowName.Ident
	}

	return false
}

// Takes a name from gamma or delta. If the name is not found, then return error
func consumeName(name Name, gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx) (types.SessionType, TypeEnvironment, error) {

	if name.IsSelf {
		return nil, UNKNOWN, fmt.Errorf("found self, expected a client")
	}

	foundNameGamma, okGamma := gammaNameTypesCtx[name.Ident]

	if okGamma {
		// If linear then remove
		delete(gammaNameTypesCtx, name.Ident)

		return foundNameGamma.Type, GAMMA, nil
	}

	foundNameDelta, okDelta := deltaNameTypesCtx[name.Ident]

	if okDelta {
		delete(deltaNameTypesCtx, name.Ident)

		return foundNameDelta.Type, DELTA, nil
	}

	// Problem since the requested name was not found in neither gamma nor delta
	return nil, UNKNOWN, fmt.Errorf("the requested name (%s) is not defined (has no type)", name.String())
}

// Takes a name from gamma or delta. If the name is 'self', then return the provider type instead of fetching it from gamma
func consumeNameMaybeSelf(name Name, providerShadowName *Name, gammaNameTypesCtx, deltaNameTypesCtx NamesTypesCtx, providerType types.SessionType) (types.SessionType, error) {
	if name.IsSelf {
		return providerType, nil
	}

	if providerShadowName != nil && providerShadowName.Ident == name.Ident {
		return providerType, nil
	}

	foundNameGamma, okGamma := gammaNameTypesCtx[name.Ident]

	if okGamma {
		// If linear then remove
		delete(gammaNameTypesCtx, name.Ident)

		return foundNameGamma.Type, nil
	}

	foundNameDelta, okDelta := deltaNameTypesCtx[name.Ident]

	if okDelta {
		// If linear then remove
		delete(deltaNameTypesCtx, name.Ident)

		return foundNameDelta.Type, nil
	}

	// Problem since the requested name was not found in the gamma or delta
	return nil, fmt.Errorf("the requested name (%s) is not defined (has no type)", name.String())
}

func stringifyContext(nameTypesCtx NamesTypesCtx) string {
	if len(nameTypesCtx) == 0 {
		return ""
	}

	var buffer bytes.Buffer

	for k := range nameTypesCtx {
		buffer.WriteString(k)
		buffer.WriteString("; ")
	}

	str := buffer.String()

	return str[:len(str)-2]
}

// Enforce linearity, i.e. ensure that there are no variables left in Gamma and Delta
func linearGammaAndDeltaContext(gammaNameTypesCtx, deltaNameTypesCtx NamesTypesCtx) error {
	// todo change to allow weakenable variables (although drop prevents this)
	if len(gammaNameTypesCtx) == 1 {
		return fmt.Errorf("linearity requires that no names are left behind, however there is one name (%s) left", stringifyContext(gammaNameTypesCtx))
	} else if len(gammaNameTypesCtx) > 1 {
		return fmt.Errorf("linearity requires that no names are left behind, however there were %d names (%s) left", len(gammaNameTypesCtx), stringifyContext(gammaNameTypesCtx))
	}

	if len(deltaNameTypesCtx) == 1 {
		return fmt.Errorf("linearity requires that no names are left behind, however there is one name (%s) left", stringifyContext(deltaNameTypesCtx))
	} else if len(deltaNameTypesCtx) > 1 {
		return fmt.Errorf("linearity requires that no names are left behind, however there were %d names (%s) left", len(deltaNameTypesCtx), stringifyContext(deltaNameTypesCtx))
	}

	// Ok, no unwanted variables left in gamma
	return nil
}

// Compares the given labels with the ones offered by the branches. Returns the unused ones
func extractUnusedLabels(branches []types.Option, labels map[string]bool) string {
	// One or more branches are not exhausted
	var labelsList []string
	for l := range labels {
		labelsList = append(labelsList, l)
	}

	uncheckedBranches := types.GetUncheckedBranches(branches, labelsList)

	var labelsNotChecked bytes.Buffer
	for i, j := range uncheckedBranches {
		labelsNotChecked.WriteString(j.Label)

		if i < len(uncheckedBranches)-1 {
			labelsNotChecked.WriteString(", ")
		}
	}

	return labelsNotChecked.String()
}

// From the gamma context, take the requested names and put them in a separate context
// The providerShadowName acts as a bound name (i.e. it should be ignored)
func splitGammaAndDeltaCtx(gammaNameTypesCtx NamesTypesCtx, deltaNameTypesCtx NamesTypesCtx, names []Name, providerShadowName *Name, labelledTypesEnv types.LabelledTypesEnv) (NamesTypesCtx, NamesTypesCtx, NamesTypesCtx, NamesTypesCtx, error) {

	var namesFoundGamma []Name
	var namesFoundDelta []Name

	for _, name := range names {

		if name.IsSelf || (providerShadowName != nil && providerShadowName.Ident == name.Ident) {
			continue
		}

		foundType, typeEnvironmentContainingName, err := consumeName(name, gammaNameTypesCtx, deltaNameTypesCtx)
		foundType = types.Unfold(foundType, labelledTypesEnv)

		if err != nil {
			return nil, nil, nil, nil, err
		}

		name.Type = foundType

		switch typeEnvironmentContainingName {
		case GAMMA:
			namesFoundGamma = append(namesFoundGamma, name)
		case DELTA:
			namesFoundDelta = append(namesFoundDelta, name)
		default: // never reached since in the case of UNKNOWN consumeName returns an error and is caught in the above condition
			return nil, nil, nil, nil, err
		}
	}

	gammaLeftNameTypesCtx := produceNameTypesCtx(namesFoundGamma)
	gammaRightNameTypesCtx := gammaNameTypesCtx

	deltaLeftNameTypesCtx := produceNameTypesCtx(namesFoundDelta)
	deltaRightNameTypesCtx := deltaNameTypesCtx

	return gammaLeftNameTypesCtx, gammaRightNameTypesCtx, deltaLeftNameTypesCtx, deltaRightNameTypesCtx, nil
}

// Ensure that a name has a type linked to it. Check for well formedness of the type.
// This is used to analyse types defined within the AST (e.g. checks type A from x : A <- new P; Q)
func checkNameType(name Name, labelledTypesEnv types.LabelledTypesEnv) error {
	if name.Type == nil {
		return fmt.Errorf("type for name '%s' was not found", name.String())
	}

	// run type related checks
	err := types.CheckTypeWellFormedness(name.Type, labelledTypesEnv)

	return err
}

// Given a process, it takes the free names and fetches their types from the assumed names or the process types
func getFreeNameTypes(process *Process, processes []*Process, assumedFreeNames []Name) []Name {
	// First prepare a map of all available names (both assumed and defined from a process)
	allAvailableNames := make(map[string]NamesType)
	for i := range processes {
		for _, provider := range processes[i].Providers {
			provider.Type = processes[i].Type
			allAvailableNames[provider.Ident] = NamesType{Name: provider, Type: processes[i].Type}
		}
	}
	for _, assumedFn := range assumedFreeNames {
		allAvailableNames[assumedFn.Ident] = NamesType{Name: assumedFn, Type: assumedFn.Type}
	}

	// Get a list of all the free names from the current process that should have a type
	processFreeNames := process.Body.FreeNames()
	// Remove provider names, since those are bound
	processFreeNames = NamesInFirstListOnly(processFreeNames, process.Providers)

	// Fetch the names/types from the collection the we created earlier
	var result []Name
	for _, processFn := range processFreeNames {
		fetchedName, found := allAvailableNames[processFn.Ident]

		// From the preliminary checks, this should always succeed
		if found {
			result = append(result, fetchedName.Name)
		}
	}

	return result
}

func nameInNames(check Name, names ...Name) bool {
	for _, curr := range names {
		if check.Equal(curr) {
			return true
		}
	}

	return false
}

// Compare annotated polarity to the (more precise) polarities inferred from the type
func checkExplicitPolarityValidity(p Form, names ...Name) error {

	for _, name := range names {
		if !name.ExplicitPolarityValid() {
			return fmt.Errorf("invalid polarities in %s, expected %s, but found %s", p.String(), types.PolarityMap[name.Type.Polarity()], types.PolarityMap[*name.ExplicitPolarity])
		}
	}

	return nil
}

// Check if all types of the channels being synced are equal
func allTypesBeingSyncedAreEqual(input []types.SessionType, labelledTypesEnv types.LabelledTypesEnv) bool {
	if len(input) <= 1 {
		return true
	}

	for i := 1; i < len(input); i++ {
		if !types.EqualType(input[0], input[i], labelledTypesEnv) {
			return false
		}
	}

	return true
}
