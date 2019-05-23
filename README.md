# Effect Parametricity Using Agda

This repository contains proofs of some results involving monads in general and effect parametricity in particular.
The effect parametricity results are based on the paper "Free Theorems Involving Type Constructor Classes" by Janis Voigtländer (2009).

The proofs are written in the extension of Agda accompanying the paper "Parametric Quantifiers for Dependent Type Theory" by Andreas Nuyts, Andrea Vezzosi and Dominique Devriese (2017), available at the [parametric branch](https://github.com/agda/agda/tree/parametric) of the Agda repository.

The files TypeSystem.agda, Source.agda, Target.agda and Primitives.agda provide the type system we work in and are taken from the repository [parametric-demo](https://github.com/Saizan/parametric-demo), but TypeSystem.agda is extended and modified to contain for instance lists and natural numbers.

The mechanization of the example worked out in the TyDe extended abstract submission can be found in the module Simplified of the file [PurityPreservation.agda](EffectParametricity/PurityPreservation.agda).

## Installing and using Agda-parametric

  If you want to type-check the code in this repository, you should be able to build and install a version of Agda-parametric as follows (note: this will replace your current Agda installation):

    git clone --single-branch --branch parametric https://github.com/agda/agda.git Agda-parametric
    cd Agda-parametric
    cp stack-8.0.1.yaml stack.yaml
    stack install

  Afterwards, you can open the file in emacs, and press C-c C-l to type-check it.
  Note: if you've previously opened Agda files in the same copy of emacs, you first need to use C-c C-x C-r to restart Agda.
