# Period-completion dichotomy for stage-two Schanuel defects

- **ID:** schanuel-period-branch-defect-dichotomy
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (paper) + NO-GO
- **Source:** stage-two defect slope, separable Kähler base change, logarithm-period branches
- **Statement:** adjoining `2πi` either resolves every nontrivial logarithm-branch defect or leaves
  infinitely many stage-two counterexamples; Kummer Galois symmetry cannot identify those branches.

## Lean certificate

Every numbered statement of this card is proved unconditionally in Lean; the axiom audit of each
declaration is exactly `propext`, `Classical.choice`, `Quot.sound`.

| Card item | Declaration | Module |
|---|---|---|
| `(1)` exact shifted-defect identity, undivided | `smul_kaehlerPairDefect_eq_of_zpow_of_affine` | `RHTower/SchanuelPeriodBranchDefect` |
| `(1)` divided form `eps^{(m,k)}_i = (eps_i - k_i dtau)/m` | `kaehlerPairDefect_eq_inv_smul_of_zpow_of_affine` | same |
| rank-two criterion for a shifted rank-one pair | `linearIndependent_rankOne_period_shift`, `linearIndependent_rankOne_period_shift_inv_smul` | same |
| `(2)` the new differential is independent of the old direction | `linearIndependent_mapBaseChange_and_D_adjoin_transcendental` | `RHTower/SchanuelPureTranscendentalPeriod` |
| `(3)` **Case I**: every nonzero integral shift has defect rank two | `linearIndependent_nontrivial_integral_period_shift_of_transcendental` | `RHTower/SchanuelPeriodBranchRank` |
| `k_1 rho - k_2 != 0` for integral `k != 0` and transcendental `rho` | `intCast_mul_sub_ne_zero_of_transcendental` | same |
| Case I: every shifted additive pair stays rationally independent | `linearIndependent_period_shift_of_linearIndependent_triple` | `RHTower/SchanuelAlgebraicPeriodBranch` |
| Case I: the branch value field has transcendence degree two | `trdeg_periodField_eq_two` | `RHTower/SchanuelValueFieldInstance` |
| **Case II**: a period inside the old span makes every shifted pair collinear | `not_linearIndependent_smul_pair`, `not_linearIndependent_period_shift_of_mem_span` | `RHTower/SchanuelAlgebraicPeriodBranch` |
| Case II: the shifted pair is independent iff `1 + q_1k_1 + q_2k_2 != 0` | `linearIndependent_period_shift_of_det_ne_zero` | same |
| Case II: only one rational line of integral shifts is excluded | `infinite_setOf_det_ne_zero` | same |
| Case II: every branch value field has transcendence degree one | `trdeg_periodField_eq_one` | `RHTower/SchanuelValueFieldInstance` |
| general input: adjoining a transcendental raises the degree by one | `trdeg_adjoin_simple_eq_one`, `trdeg_eq_add_one_of_transcendental` | `HTGeometry/TranscendenceDegreeOneVariable` |
| general input: an algebraic extension preserves the degree | `trdeg_eq_of_isAlgebraic` | same |
| general input: a simple extension is algebraic over its ring model | `isAlgebraic_adjoin_gen` | same |
| the retired multiplicity amplification | `SchanuelPowerMultiplicityNoGo` (module) | `RHTower/SchanuelPowerMultiplicityNoGo` |

### Deviations from the paper proof

- Case II is proved from collinearity rather than from the dimension count of `(2)` in the
  separable case: a period differential lying in the span of the old defect makes both shifted
  defects multiples of one vector, which is exactly rank at most one and needs no Kähler dimension
  argument.
- The transcendence-degree statements are proved through mathlib's tower additivity `trdeg_add_eq`
  together with `trdeg_adjoin_simple_eq_one`, which is proved here (mathlib has no transcendence
  degree for a simple extension).
- The Kummer no-go is not a separate Lean obligation: it asserts that a *tempting conjecture* is
  false, and the two cases above -- rank two in Case I, rank at most one in Case II -- are the
  proof that branch rank is not constant across the Kummer torsor.

## Setup

Let `A=Qbar`, let

\[
 K=A(x_1,x_2,y_1,y_2),\qquad y_i=e^{x_i},\qquad \operatorname{trdeg}_A K=1,
\]

where `x_1,x_2` are rationally linearly independent.  Put

\[
 \epsilon_i=d\log y_i-dx_i,
 \qquad \epsilon_2=\rho\epsilon_1,
\]

with `epsilon_1 != 0` and `rho` transcendental over `A`.  Let `tau=2 pi i`.  For a positive
integer `m` and `k=(k_1,k_2) in Z^2`, define the selected branch tuple

\[
 z_i^{(m,k)}=\frac{x_i+k_i\tau}{m},\qquad
 w_i^{(m,k)}=\exp z_i^{(m,k)}.
\]

Then `(w_i^{(m,k)})^m=y_i`; hence the `w_i` are algebraic over `K(tau)`.

## Theorem: exact shifted-defect formula

After separable base change to any common field containing the branch tuple,

\[
 \epsilon_i^{(m,k)}
 =d\log w_i^{(m,k)}-dz_i^{(m,k)}
 =\frac1m\bigl(\epsilon_i-k_i\,d\tau\bigr). \tag{1}
\]

Indeed, logarithmic differentiation of `w_i^m=y_i` gives
`m dlog(w_i)=dlog(y_i)`, while direct differentiation gives
`m dz_i=dx_i+k_i d tau`.  Subtraction proves `(1)`.

## Case I: `tau` is transcendental over `K`

Pure-transcendental Kähler base change gives a direct sum

\[
 \Omega_{K(\tau)/A}
 \simeq K(\tau)\otimes_K\Omega_{K/A}\oplus K(\tau)d\tau. \tag{2}
\]

Thus `epsilon_1` and `d tau` are linearly independent.  From `(1)`,

\[
 m^2\epsilon_1^{(m,k)}\wedge\epsilon_2^{(m,k)}
   =(k_1\rho-k_2)\,\epsilon_1\wedge d\tau. \tag{3}
\]

Because `rho` is transcendental over `A`, `k_1 rho-k_2` vanishes for integral `k` only when
`k=(0,0)`.  Consequently every nonzero branch shift has defect rank two.  Also every shifted
additive pair remains rationally linearly independent: a relation would either put `tau` in `K`
or reduce to a relation between `x_1,x_2`.  Its value field has transcendence degree two, since it
is algebraic over `K(tau)`.  Therefore every nonzero branch shift satisfies the expected
stage-two Schanuel bound exactly, while the unshifted branch retains the original defect.

## Case II: `tau` is algebraic over `K`

Characteristic zero makes `K(tau)/K` separable algebraic, so

\[
 \Omega_{K(\tau)/A}\simeq K(\tau)\otimes_K\Omega_{K/A}
\]

has dimension one.  Equation `(1)` then leaves every shifted defect pair of rank at most one, and
every branch value field has transcendence degree one.

Infinitely many `k` retain rational linear independence.  If `tau` is independent of
`x_1,x_2`, all do.  Otherwise write `tau=q_1x_1+q_2x_2`; the shifted pair is obtained from `x` by
the rank-one matrix `I+kq^T` and is independent exactly when
`1+q_1k_1+q_2k_2 != 0`.  Only one rational affine line of integer shifts is excluded.  Hence this
case produces infinitely many stage-two counterexamples.

## No-go closure

The tempting conjecture was that the finite Kummer branch torsor forces equal defect rank across
all branches.  It is false.  A Kummer automorphism sends a chosen root `w_i` to
`zeta_m^{k_i}w_i` while fixing `x_i/m`; it does **not** send the additive logarithm to
`(x_i+k_i tau)/m`.  The simultaneous translation is an analytic branch operation, not a field
automorphism.  Thus neither branch-rank pattern contradicts algebraic Galois symmetry.

- **Positive survivor:** equations `(1)`--`(3)` and the complete period-completion dichotomy.
- **Universal principle exposed:** finite étale/Kummer descent is blind to the affine period
  translation coupling additive and multiplicative coordinates.  Adjoining `tau` resolves the
  defect precisely when it adds a new transcendence direction.
- **Lean status:** `RHTower/SchanuelPeriodBranchDefect.lean` formalizes the exact branch-defect
  identity and determinant criterion. `RHTower/SchanuelPureTranscendentalPeriod.lean` proves that
  a nonzero old Kähler direction and `d tau` are independent after adjoining a transcendental
  period. `RHTower/SchanuelPeriodBranchRank.lean` combines this with transcendence of `rho` to
  prove rank two for every nonzero integral branch shift.  `RHTower/SchanuelAlgebraicPeriodBranch.lean` (new) closes the algebraic-period case: a period
  differential inside the span of the old defect makes every shifted pair collinear, hence of rank
  at most one (`not_linearIndependent_smul_pair`,
  `not_linearIndependent_period_shift_of_mem_span`); the shifted additive pair stays rationally
  independent exactly when the rank-one determinant `1 + q_1k_1 + q_2k_2` is nonzero
  (`linearIndependent_period_shift_of_det_ne_zero`), only one rational line of integral shifts is
  excluded (`infinite_setOf_det_ne_zero`), and in the transcendental-period case every shift keeps
  independence (`linearIndependent_period_shift_of_linearIndependent_triple`).
  All declarations were checked first in
  `/tmp` and use only `propext`, `Classical.choice`, and `Quot.sound`.

  The two transcendence-degree bookkeeping claims are now formal as well, in
  `HTGeometry/TranscendenceDegreeOneVariable.lean` (new, umbrella-wired, axiom-clean):
  `trdeg_eq_one_of_transcendental` (a one-variable extension has degree one),
  `trdeg_eq_add_one_of_transcendental` (adjoining a transcendental period raises the degree by
  one), `trdeg_eq_of_isAlgebraic` (an algebraic period does not),
  `trdeg_eq_two_of_transcendental` (**Case I**: degree two over a degree-one base), and
  `trdeg_eq_one_of_isAlgebraic` (**Case II**: degree one).  The mathlib input is the tower
  additivity `trdeg_add_eq` together with `Algebra.IsAlgebraic.trdeg_le_cardinalMk`.

  **What is still not formal:** only the instantiation bookkeeping -- identifying the abstract
  tower `A -> K -> K(tau)` with the concrete fields of the card inside `C`.
- **Novelty:** no external priority claim; this is a new internal synthesis of standard Kähler
  and branch identities.

## Next conjecture

Find an arithmetic invariant of an isolated exponential intersection that is sensitive to the
simultaneous affine period translation. Multiplicity is now rigorously retired: the local-unit
factorization formalized in `RHTower/SchanuelPowerMultiplicityNoGo.lean` proves scalar powering
preserves the local exponential-intersection ideal and zero order. A branch-counting replacement
would need a genuine degree/height surplus, not merely the full Kummer orbit.

## Log

- 2026-08-14 -- shifted-defect formula proved; exact `tau`-algebraic/transcendental dichotomy and
  Kummer-symmetry failure isolated.
- 2026-08-14 -- exact shifted-defect identity and determinant rank criterion verified
  unconditionally in Lean and wired as `RHTower/SchanuelPeriodBranchDefect.lean`.
- 2026-08-14 -- pure-transcendental base/new differential independence and the full nonzero
  integral-shift rank-two theorem verified unconditionally in Lean and wired as
  `RHTower/SchanuelPureTranscendentalPeriod.lean` and `RHTower/SchanuelPeriodBranchRank.lean`.
- 2026-08-14 -- scalar-power multiplicity amplification retired by an exact local-unit law;
  positive survivor formalized in `RHTower/SchanuelPowerMultiplicityNoGo.lean`.
