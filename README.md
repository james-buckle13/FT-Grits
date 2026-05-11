<p align="center">
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="./assets/grits-light-text.svg">
  <img alt="Grits" width="250" height="161" src="./assets/grits-dark-text.svg">
</picture>
</p>
<!-- # Grits -->

**Grits** is a type-checker and interpreter for intuitionistic session types written in Go, based on the semi-axiomatic sequent calculus. This fork is an extension of the exisiting tool with fault tolerance constructs.

## Grammar

The full grammar accepted by our compiler is as follows:

```text
<prog> ::= <statement>*

<statement> ::= type <label> = <type>                           
              | def <label> ( [<param>] ) : <type> @ n = <term>     
              | def <label> '[' <param> ']' @ n = <term>            
              | assuming <param>                                
              | prc '[' <name> ']' : <type> @ n = <term>            
              | exec <label> ( )                               

<param> ::= <name> : <type> [ , <param> ]                       

<type> ::= [<modality>] <type_i>                                

<type_i> ::= <label>                                            
           | 1                                                 
           | + { <branch_type> }                                
           | & { <branch_type> }                                
           | <type_i> * <type_i>                                
           | <type_i> -* <type_i>                               
           | <modality> /\ <modality> <type_i>                  
           | <modality> \/ <modality> <type_i>                  
           | ( <type_i> ) 

<branch_type> ::= <label> : <type_i> [ , <branch_type> ]        

<modality> ::= r | rep | replicable                             
             | m | mul | multicast                              
             | a | aff | affine                                 
             | l | lin | linear                                 

<term> ::= send <name> '<' <name> , <name> '>'                  
        | '<' <name> , <name> '>' <- recv <name> ; <term>       
        | <name> . <label> '<' <name> '>'                       
        | case <name> ( <branches> )                            
        | <name> [ : <type> ] <- new <term>; <term>   
        | <name> [ : <type> ] <- spawn <term>; <term>         
        | <label> ( [<names>] )                                 
        | fwd <name> <name>    
        | let <name> = n in <term>                                 
        | '<' <name> , <name> '>' <- split <name>; <term>      
        | <name> <- sync '<' <name>, <name> '>'; <term>
        | close <name>                                          
        | wait <name> ; term                                    
        | cast <name> '<' <name> '>'                            
        | <name> <- shift <name> ; <term>                       
        | print <label> ; <term>                                
        | ( <term> ) 

<branches> ::= <label> '<' <name> '>' => <term> [ '|' <branches> ] 

<names> ::= <name> [ ',' <names> ]                              

<name> ::= 'self'                                               
         | <channel_name>                                       
         | <polarity> <channel_name>                            

<polarity> ::= +                                                
             | -                                                

Others:
    <label> is an alpha-numeric combination (e.g. used to represent a choice option)
    // Single line comments
    /* Multi line comments */
    whitespace is ignored
```
