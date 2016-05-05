# JFOL
### A simple Automated Theorem Prover for First-Order Logic

This Automated Theorem Prover can create proofs of arguments given to it in FOL.

It proves the tautologicity of arguments with the Resolution method, as described in _First Order Logic and Automated Theorem Proving_, by Melvin Fitting (2nd ed.). Specifically, it employs a combination of Alpha/Beta Expansion, Resolution, and General Literal Resolution deduction rules to create a Resolution proof.

This is nonstandard. Most Resolution provers simplify the input argument completely down into Conjunctive Normal Form and only apply resolution rules. JFOL simplifies each of the argument sentences only as far as reducing the set of binary connectives and converting to Skolem Normal Form, and does not combine argument sentences. This saves some simplification time for large arguments, but I mostly take this approach because it makes the proofs easy to follow with human eyes.

Theoretically, it should be able to find a proof if the argument is valid. If the argument is invalid, it may not stop trying to find a proof and run forever. Usually it will run out of options and stop.

It receives arguments from stdin, and outputs a proof (or its attempt to find one) to stdout.

## Compilation

I have only compiled and run the project under Ubuntu 15.10 and 16.04, but it should work wherever its dependencies work (see below).
Once you have the dependencies, it's a simple matter of cloning the repository and making the executable:

````
$ git clone git@github.com:pyridine/JFOL.git  
$ cd JFOL/jfol
$ make
````

If you don't want to download the whole git repository, I'd recommend you just [download the sources](https://github.com/pyridine/JFOL/archive/master.zip) and make those.

## Usage

The `jfol` script ties together the parser and the prover. You may need to `chmod +x jfol` in order to use it.
I have provided several examples of the syntax the prover accepts in `jfol/arguments`.

(If you want to see the actual syntax specification, check out `fol.waxeye`.)

Here's an example of the syntax JFOL accepts:

````
$ cat arguments/socrates 
#p
All X (Man[X] implies Mortal[X]).
Man[socrates].
#c
Mortal[socrates].
````

This is a representation of the age-old argument "All men are mortal and Socrates is a man, therefore Socrates is mortal."

Arguments consist of two sections. The first, beginning with "#p", is a list of newline-delimited premise sentences. The second, which begins with "#c", is where you write your **single** conclusion sentence.

You can pipe the argument right into jfol, which will have the following result:

(Alternatively, you could type the argument into the terminal after `./jfol <RET>`, if you're some kind of masochist...)

````
$ cat arguments/socrates | ./jfol 
1. Man[socrates]                      : Simplified Premise
2. ((not Man[X]) or Mortal[X])        : Simplified Premise
3. (not Mortal[socrates])             : Simplified Negated Conclusion
4. (not Man[X]) | Mortal[X]       2   : Disjunctive Expansion
5. (not Man[socrates])            4,3 : General Literal Resolution: [X -> socrates]  
6. -><-                           1,5 : Resolution
Proof closed!
Proof time (seconds): 0.036
````

As you can see, JFOL presents its proof as a list of numbered steps. Each step consists of a generalized disjunction of sentences expressed in a particular syntax, with `|` delimiting the disjuncts. The text to the right of the `:` describes the rule with which the step was deduced, and the numbers to the left of the `:` cite the steps with which that rule was applied.

In this example proof, the first few steps (1-3) are the premises and the negated conclusion. Steps 4-6 are JFOL's attempts at deriving a contradiction, which it reaches in step 6. I use "-><" as a meaningful substitute for the empty generalized disjunction.

I've supplied many example arguments in the `jfol/arguments` directory. Check 'em out.

## Dependencies

I am indebted to [Python 3.5](https://www.python.org/), the [Waxeye Parser-Generator 0.8.0](http://waxeye.org/), and [Chicken Scheme 4.10.0](https://www.call-cc.org/) for supplying the tools I used to create this ATP. You will need these installed to compile JFOL - although you will only need to install Waxeye if you wish to recompile the parser.
