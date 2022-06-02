# Serre's Twisting Sheaf

This repo is aimed to formalise the concept of [Serre's Twisting Sheaf](https://en.wikipedia.org/wiki/Proj_construction#The_twisting_sheaf_of_Serre). But before this, we need to build some missing pieces.

## Localized Module
We need localized module, because we want the definition of quasicoherent sheaves which can be defined as locally $\tilde{M_i}$ over $\mathrm{Spec} R_i$.

So for a commutative ring $R$, a multiplicative subset $S\subseteq R$ and $R$-module $M$. We can defined the localized module $M_S$ (an $R_S$-module) to be
$$ \left\{[m, s]|[m, s]\sim[n, t]\iff\exists u\in S,u\cdot t\cdot m = u\cdot s\cdot n\right\} $$

See [src/module_localisation/bsaic.lean](src/module_localisation/basic.lean)

## Integer grading from natural number grading
Sometimes it is convinient to trade a natrual number graded algebra as an integer graded algebra by taking negative grade to be $\{0\}$. This is implemented at [src/grading/nat_to_int.lean](src/module_localisation/nat_to_int.lean). We want this because we want to shift a grading by an arbitrary $m\in\mathbb Z$.

## Graded modules and twisting

Given a graded ring $A\cong\bigoplus_i A_i$, an $A$-module $M\cong\bigoplus_j M_j$ is said to be graded if $a_i\cdot m_j\in M_{i+j}$ for all $a_i\in A_i$ and $m_j\in M_j$. Given a graded $A$-module $M$, we can twist $M$ by $j$ to give another graded $A$-module where the $i$-th grade component $M'_j$ is defined as $M_{i+j}$. To verify this is a graded module with respect to this new grading, one needs to verify that $M\cong\bigoplus_i M'_i$ and this grading respects scalar multiplication. These are defined in [src/grading/graded_module.lean](src/grading/graded_module.lean).

## $\tilde{M}$

So given a commutative ring $R$ and $R$-module $M$, we can define a sheaf of abelian group $\tilde{M}$ on $\mathrm{Spec} R$ by asking
$$
U\mapsto \prod_{p\in U}M_p.
$$

Then this is a $\mathrm{Spec} R$-module. This is defined in [src/MSpec/basic.lean](src/MSpec/basic.lean). I called this `MSpec` for **module on spec**.