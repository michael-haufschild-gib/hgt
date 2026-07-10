# Completed-flux graded reality and the fixed-source RH interface

- **ID:** completed-flux-graded-reality
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean) — formalized, not new scientific knowledge
- **Source:** `CompletedFluxGermRigidity.lean`, `CompletedFluxPrimeArchDecomposition.lean`,
  `CompletedFluxLaguerreReader.lean`
- **Statement:** `[PROVED, BRIDGE]` For every `ρ : ℂ`,
  \[
  \operatorname{Re}ρ=\tfrac12
  \quad\Longleftrightarrow\quad
  \forall n,\;(-1)^n c_n(ρ)=\overline{c_n(ρ)}.
  \]
  Thus every off-critical point has a finite parity-phase defect.  Inside the strip, replacing
  `c_n` by its fixed continued-prime plus archimedean/boundary decomposition gives an exact
  RH-equivalent source-coordinate interface at the zeros of `xi`.

## Goal

Replace the two-base comparison `c_n(1-ρ)=c_n(conj ρ)` by a constraint on the single completed-flux
Taylor sequence at `ρ`.  Functional-equation reflection supplies the factor `(-1)^n`; Schwarz
reflection conjugates the coefficient.  The resulting graded-reality law is meaningful at zeros
because the completed germ is residue-filled there.

This is a coordinate theorem, not the missing source theorem.  Its RH equivalence quantifies over
`xi` zeros and is therefore zero-fed.  A proof of RH must derive the graded-reality law from the
fixed Euler--Gamma source constraint before using the zero location.

## Exact laws

Schwarz reflection acts coefficientwise:

\[
c_n(\bar ρ)=\overline{c_n(ρ)}.
\]

Functional-equation reflection has solved parity form:

\[
c_n(1-ρ)=(-1)^n c_n(ρ).
\]

Combining these with completed-flux germ rigidity gives

\[
\forall n,\;(-1)^n c_n(ρ)=\overline{c_n(ρ)}
\quad\Longleftrightarrow\quad
1-ρ=\bar ρ
\quad\Longleftrightarrow\quad
\operatorname{Re}ρ=\tfrac12.
\]

Equivalently, if `Re ρ ≠ 1/2`, then for some finite `n` either

- `n` is even and `Im c_n(ρ) ≠ 0`, or
- `n` is odd and `Re c_n(ρ) ≠ 0`.

For `0 < Re ρ < 1`, write

\[
c_n(ρ)=p_n(ρ)+a_n(ρ)
\]

for the fixed continued von Mangoldt and archimedean/boundary coefficients.  Then

\[
\mathrm{RH}\quad\Longleftrightarrow\quad
\forall ρ\;(\xi(ρ)=0\Rightarrow
  \forall n,\;(-1)^n(p_n(ρ)+a_n(ρ))
    =\overline{p_n(ρ)+a_n(ρ)}).
\]

## Relation to the quadratic falsifier

Order `n=2` is an even graded-real coefficient on the critical line.  At nonzero line values the
separate exact identity is

\[
(\Xi')^2-\Xi\Xi''=-\Xi^2c_2.
\]

Hence `Re c₂ > 0` at one such point proves `¬RH`.  The finite parity-phase theorem does not claim
that an off-line zero must be detected at order two or by a sign change: its first witness may occur
at any finite order.  This preserves the supplied implication without silently using its converse.

## Main declarations

- `xi_deriv_conj`
- `seamFluxCochain_conj`
- `completedFluxGermAt_conj`
- `iteratedDeriv_conj_conj`
- `completedFluxTaylorCoeff_conj`
- `completedFluxTaylorCoeff_one_sub`
- `CompletedFluxGradedRealAt`
- `completedFluxGradedRealAt_iff`
- `exists_completedFlux_parityPhase_defect`
- `CompletedFluxSourceGradedRealAt`
- `completedFluxSourceGradedRealAt_iff`
- `rh_iff_forall_zero_completedFluxGradedRealAt`
- `rh_iff_forall_strip_zero_completedFluxSourceGradedRealAt`

## Scientific status

`[BRIDGE]` Schwarz-equivariance, functional-equation parity, analytic germ uniqueness, and the
resulting RH equivalence are routine consequences of the parent analytic theory once the
completed-flux germ has been defined.  Lean verification does not promote them to new scientific
knowledge.

`[OPEN CORE]` Prove, without quantifying over a target zero or assuming its location, that the fixed
continued-prime and archimedean/boundary coefficient sequences obey a global compatibility whose
restriction at every pole is the graded-reality law above.  The compatibility must be
order-independent and cannot be reconstructed separately at each Taylor depth.

## Verification

- exact file check: passed
- exact target build: `GaloisForLFunctions.RHTower.CompletedFluxGradedReality` passed
- axiom audit: every listed declaration uses only `propext`, `Classical.choice`, and `Quot.sound`
- no project-wide build or lint was run

## Gates

- [x] 0 → 1: the one-base graded-reality law and its source decomposition were isolated
- [x] 1 → 2: Schwarz, parity, finite phase witness, and both RH equivalences were proved
- [x] 2 → 3: Lean module built and the declarations passed the axiom audit
- [ ] 3 → 4: requires the independent all-order Euler--Gamma compatibility theorem
