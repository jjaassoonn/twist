# Serre's Twisting Sheaf

This repo is aimed to formalise the concept of [Serre's Twisting Sheaf](https://en.wikipedia.org/wiki/Proj_construction#The_twisting_sheaf_of_Serre). But before this, we need to build some missing pieces.

## Localized Module
We need localized module, because we want the definition of quasicoherent sheaves which can be defined as locally $\tilde{M_i}$ over $\mathrm{Spec} R_i$.

So for a commutative ring $R$, a multiplicative subset $S\subseteq R$ and $R$-module $M$. We can defined the localized module $M_S$ (an $R_S$-module) to be
$$ \left\{[m, s]|[m, s]\sim[n, t]\iff\exists u\in S,u\cdot t\cdot m = u\cdot s\cdot n\right\} $$

See [src/module_localisation/bsaic.lean](src/module_localisation/basic.lean)

## Integer grading from natural number grading
Sometimes it is convinient to trade a natrual number graded algebra as an integer graded algebra by taking negative grade to be $\{0\}$. This is implemented at [src/grading/nat_to_int.lean](src/module_localisation/nat_to_int.lean). We want this because we want to shift a grading by an arbitrary $m\in\mathbb Z$.