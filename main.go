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
			def body() : nat -* (nat * 1) @ 0 = c:1 <- new close self; <x, y> <- recv self; send y <x, c>
			def send_to_repl(x : nat -* (nat * 1)): nat * 1 @ 1 = let v = 5 in send x <v, self>
			prc[q] : nat * 1 @ 1 = a <- spawn (body()); b: nat -* (nat * 1) <- spawn (boom_in self); y <- sync <a, b>; z <- new send_to_repl(y); <x, t> <- recv z; wait t; term:1 <- new close self; send self <x, term>
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
