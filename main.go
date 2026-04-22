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
			type nat = +{zero : 1, succ : nat}
			let create_zero() : nat @ 0 = t: 1 <- new close self; self.zero<t>
			let a_body() : nat * 1 @ 0 = z0: nat <- new (create_zero()); term: 1 <- new close self; send self <z0, term>
			prc[a] : nat * 1 @ 1 = a: nat * 1 <- spawn (a_body()); b: nat * 1 <- spawn (a_body()); y <- sync <a, b>; <z, y'> <- recv y; wait y'; term: 1 <-new close self; send self <z, term>
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
		execute          = false
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
