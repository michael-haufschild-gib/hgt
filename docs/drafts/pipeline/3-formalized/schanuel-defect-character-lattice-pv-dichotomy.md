# Exact character lattice and Picard--Vessiot dichotomy of Schanuel defects

- **ID:** schanuel-defect-character-lattice-pv-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** logarithmic-differential algebraicity + integral defect lattice
- **Statement:** An integral defect combination is a logarithmic derivative exactly when its
  additive linear form is algebraic over the constant field; this computes the diagonal
  Picard--Vessiot character lattice exactly.

## Goal

Test whether the defect-lattice theorem makes the hyperexponential discrepancy functions

\[
 Z_i=\frac{e^{X_i}}{Y_i}
\]

algebraically independent over the algebraic curve field.  Their logarithmic connection forms are

\[
 d\log Z_i=dX_i-d\log Y_i=-\epsilon_i.
\]

The naive full-torus conjecture is false when an integral combination of the coordinate functions
`X_i` is constant.  The exact survivor classifies every character relation.

## Gates

- [x] 0 -> 1  in-progress: conjecture, countermechanism, and exact replacement identified
- [x] 1 -> 2  fully-proven: dependency-closed equivalence proved on paper
- [x] 2 -> 3  formalized: Lean theorem verified in scratch, axiom-audited, and umbrella-wired
- [ ] 3 -> 4  publication-ready: external novelty and independent PV interpretation audit pending

## Theorem

Let `C -> L` be any characteristic-zero field extension, let `x_i,y_i in L` with `y_i != 0`, and
put

\[
 \epsilon_i=\frac{dy_i}{y_i}-dx_i\in\Omega_{L/C}.
\]

For every integral vector `m=(m_i)`, the following are equivalent:

1. there is `f in L^*` such that

\[
 \sum_i m_i\epsilon_i=\frac{df}{f}; \tag{CL1}
\]

2. the additive linear form

\[
 s_m=\sum_i m_i x_i
\]

is algebraic over `C`.  Equivalently, the logarithmic character lattice of the diagonal connection
is

\[
 \Lambda=\{m\in\mathbb Z^n:s_m\in\operatorname{acl}_L(C)\}. \tag{CL2}
\]

## Proof

Put

\[
 u_m=\prod_i y_i^{m_i}.
\]

The Laurent-product rule gives the unconditional identity

\[
 \sum_i m_i\epsilon_i=\frac{du_m}{u_m}-ds_m. \tag{CL3}
\]

If `(CL1)` holds, set `w=u_m/f`.  Equations `(CL1)` and `(CL3)` give

\[
 \frac{dw}{w}=ds_m.
\]

The logarithmic-differential algebraicity theorem forces `s_m` and `w` algebraic over `C`, so in
particular `s_m` is algebraic.  Conversely, if `s_m` is algebraic, then `ds_m=0`; `(CL3)` becomes
`sum m_i epsilon_i=du_m/u_m`, proving `(CL1)` with `f=u_m`. **[PROVED HERE]**

## Picard--Vessiot consequence

Kolchin's character criterion for diagonal hyperexponential equations identifies algebraic
characters of the Picard--Vessiot Galois group with the lattice `(CL1)`.  Hence `(CL2)` computes
that group without ambiguity.

For a stage-two normal form:

- if no nonzero integral combination of `X_1,X_2` is constant, `Lambda=0` and the discrepancy
  torsor has full Galois group `G_m^2`;
- if one primitive combination is a nonzero algebraic constant, `Lambda` has rank one and an
  integral change of coordinates reduces the counterexample to a slice with one algebraic
  additive coordinate;
- rank two would make both additive coordinates algebraic and is excluded by
  Lindemann--Weierstrass in a stage-two counterexample.

Thus the numerical point is either a simultaneous unit specialization of a full two-dimensional
differential torus, or belongs to the still-open one-algebraic-coordinate Schanuel slice.

## Failed conjecture and no-go closure

- **Failed conjecture:** rational independence of the numerical values `x_i` forces the functions
  `Z_i` to be algebraically independent over the curve field.
- **Exact killing mechanism:** numerical `Q`-independence permits a functional affine relation
  `sum m_i X_i=c` with nonzero `c in Qbar`; after extending analytic constants to `C`, this creates
  a Picard--Vessiot character relation even though `sum m_i x_i != 0` numerically.
- **Strongest positive survivor:** exact lattice formula `(CL2)` and its full-torus/rank-one
  dichotomy.
- **New insight:** integral defect independence controls zero logarithmic derivatives, while PV
  rank also quotients nonzero algebraic additive constants.  The remaining obstruction is
  arithmetic specialization of the resulting torus, not functional differential dependence.
- **Status:** exact Lean theorem
  `GaloisForLFunctions.RHTower.defect_integer_combination_is_logarithmic_iff` in
  `RHTower/Schanuel/SchanuelDefectCharacterLattice.lean`; supporting identity
  `sum_valueDefect_eq_log_monomial_sub`.  Scratch `lake env lean` passed.  `#print axioms` reports
  only `propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, project axiom,
  `opaque`, or `unsafe` declaration.

## Novelty audit

The general hyperexponential/Picard--Vessiot character criterion is classical differential
Galois theory.  Targeted search found no statement computing this character lattice for numerical
Schanuel defects by the logarithmic-differential algebraicity obstruction.  Treat as a new internal
bridge theorem; external novelty unconfirmed and no priority claimed.

## New open core

Prove an arithmetic specialization theorem for the full-torus branch, or rule out the rank-one
affine branch.  A theorem based only on differential Galois rank cannot work: full-torus systems
can take algebraic values at isolated transcendental points in one variable.  The missing input
must use the simultaneous `Qbar` origin of `X_i,Y_i` and the selected exponential branch.

## Log

- 2026-08-14 -- full-PV-torus conjecture killed by affine constants; exact character lattice proved
  and formalized; stage-two problem split into full-torus and one-algebraic-coordinate branches.
