# Solving the peg game with TLA+

#### What is this?

This project contains a TLA+ specification which models the "peg game" (formally known as [triangular peg solitaire](https://en.wikipedia.org/wiki/Peg_solitaire)), and can be used to solve the game given any particular starting position.

This project contains two files:

- peggame.tla
- peggame.pdf

The `tla` file contains the specification's source code, and the `pdf` file contains the TLaTeX pretty-printed version of the specification.

#### How do I use it?

In order to use this model to solve a peg game, you will need to be familiar with TLA+ and TLA+ Toolbox.  

The way you solve a game is as follows:
- Set the initial state of the game by defining the "Init" state as desired
- Run the TLA+ model checker, adding an *invariant* that there is no winning state: `Win = FALSE`.
- When you run the model checker, it should "fail" (this is a good thing), providing all steps which led to the winning state.

![Example Results](/run.png)

## 
