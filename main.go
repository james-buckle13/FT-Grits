package main

import (
	"grits/cmd"
	"grits/parser"
	"grits/process"
	"log"
	"time"
)

const development = true

func main() {
	if development {
		p := `
			// type nat = +{zero : 1, succ : nat}
			// def create_zero() : nat @ 0 = t: 1 <- new close self; self.zero<t>
			// def a_body() : nat * 1 @ 0 = z0: nat <- new (create_zero()); term: 1 <- new close self; send self <z0, term>
			// def b_body() : 1 * 1 @ 0 = term1: 1 <- new close self; term2: 1 <- new close self; send self <term1, term2> // to be used for checking type mismatch
			// def new_body(): nat * 1 @ 0 = a <- spawn (a_body()); y <- sync <a>; <z, y'> <- recv y; wait y'; term: 1 <-new close self; send self <z, term>
			// prc[a] : nat * 1 @ 1 = w <- new (new_body()); <z, w'> <- recv w; wait w'; term: 1 <-new close self; send self <z, term>
			prc[a] : nat * 1 @ 7 = term:1 <- new close self; let x = 5 in send self <x, term>
			`
		dev(p)
	} else {
		cmd.Cli()
	}
}

func dev(program string) {
	// For DEVELOPMENT only: we can run programs directly, bypassing the CLI version
	const (
		executionVersion = process.NORMAL_ASYNC
		typecheck        = true
		execute          = true
		delay            = 0 * time.Millisecond
	)
	var processes []*process.Process
	var assumedFreeNames []process.Name
	var globalEnv *process.GlobalEnvironment
	var err error

	processes, assumedFreeNames, globalEnv, err = parser.ParseString(program)

	if err != nil {
		log.Fatal(err)
		return
	}

	// globalEnv.LogLevels = []process.LogLevel{}
	globalEnv.LogLevels = []process.LogLevel{
		process.LOGINFO,
		process.LOGRULE,
		process.LOGPROCESSING,
		process.LOGRULEDETAILS,
		process.LOGMONITOR,
	}

	if typecheck {
		err = process.Typecheck(processes, assumedFreeNames, globalEnv)
		if err != nil {
			log.Fatal(err)
			return
		}
	}

	if execute {
		re, _, _ := process.NewRuntimeEnvironment()
		re.GlobalEnvironment = globalEnv
		re.Typechecked = typecheck
		re.Delay = delay

		process.InitializeProcesses(processes, nil, nil, re)
	}
}
