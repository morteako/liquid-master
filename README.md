# Verification of Haskell programs using Liquid Haskell

## A guide on how to type check the programs in my thesis

This contains instructions about how to type check the programs in my thesis.
Every program is expected to type check without warnings, except where noted.

### Tested on 
`The Glorious Glasgow Haskell Compilation System, version 8.4.3`

`LiquidHaskell Version 0.8.6.0 [develop@e84189055529b3351026a44687ccfecf8ef0bd1c (Thu May 9 09:46:54 2019 -0700)]`


## Liquid Haskell
[Install Liquid Haskell](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/INSTALL.md)

Verifying a file using Liquid Haskell is done by: `liquid FILE`

Liquid Haskell will then output SAFE if the program type checks, or UNSAFE if not.

### ProofCombinators.hs

Due to some issues regarding importing the the actual
ProofCombinator-module, I just copied it and renamed it Proof (Proof.hs), and
used local versions of this module.
So, all the Proof.hs files are just copies of [ProofCombinators.hs](https://github.com/ucsd-progsys/liquidhaskell/blob/develop/include/Language/Haskell/Liquid/ProofCombinators.hs), and not my own work.

## Type checking normal Haskell

For ease of use, I will be using ghci to type check Haskell.
This is to easily enable non-exhaustiveness warnings, which are important in many 
of the examples for this thesis

This warning is enabled by the -W flag: `ghci -W`


## Chapter 3

`cd chapter3`

### 3.2.1 Termination



`liquid unsound_termination.hs`

#### Lazyness

`liquid lazy.hs`


### 3.2.1 Totality

`liquid totality_example.hs`


`ghci -W totality_example.hs`
        
        Gives non-exhaustive pattern match warning, as expected

`liquid unsound_partial.hs`

## Chapter 4

`cd chapter4`

### 4.1 Natural numbers

`cd 4.1`

#### 4.1.1 Liquid Haskell

##### Version with PLE
`liquid PeanoLH.hs`

##### Version without PLE
`liquid PeanoLHnoPLE.hs`

#### 4.1.2 Dependent Haskell

`ghci -W PeanoEq.hs`

### 4.2 - Compile time validity checking

`cd 4.2`

#### 4.2.1 Liquid Haskell

`liquid Formula.hs`

#### 4.2.2 Dependent Haskell
`ghci -W Sequent.hs`

## Chapter 5

`cd chapter5`

### Size verification
`cd size_verification`

### 5.2 - Proving the splitting theorem
`cd 5.1`

`liquid SplitDigit.hs`
