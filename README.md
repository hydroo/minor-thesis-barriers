# Development and Analysis of Barrier Protocols

## About

This is a semi-organised repository of about one year of university work. During this time I:

 * surveyed existing protocols
 * surveyed actual implementations
 * invented new protocols
 * analysed/modelchecked/benchmarked some of them
 * surveyed the waters in which barriers live - how can barriers be built on shared and distributed memory architectures, an (in-depth-)look at the MPI standard and its suitability for implementing barriers

## Structure

 * /complex-lab/ is the first ~0.5 years resulting in a small, bad report and a presentation
 * / is the last ~0.5 years resulting in my minor thesis and a presentation

## Requirements

Some things in the repository need special software

 * [PRISM Model Checker](http://prismmodelchecker.org/)
 * [SPIN Model Checker](http://spinroot.com)
 * GNU C Compiler, because I used local functions/lambdas in the c programming language
 * an MPI implementation (e.g. [Open MPI](http://open-mpi.org/))

## License

Everything is licensed under the [Creative Commons Attribution-NonCommercial-ShareAlike 4.0](http://creativecommons.org/licenses/by-nc-sa/4.0) license.

If this licensing scheme is a problem for your intentions, please mail me. I don't have much experience in licensing things like the contents of this repository.

## Misc

 * Parts of this repository might be broken
 * Apologies for the presentation slides being incomplete. I'm bad at git.

## Why upload this?

 * For people interested in researching barrier protocols
 * As a portfolio entry so potential employers can see what I did and how I did it
