# Mass-shifted projective nodal contact cascade

- **ID:** mass-shifted-projective-nodal-contact-cascade
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core

## Claim

Let `L_y` be the real shifted-Xi moment functional and

\[
 M_k(y,p)=L_y(X^k p^2).
\]

For degree label `n`, scalar gauge `a`, and projective Möbius tangent

\[
 V_{n,a}(p)=X^2p'-nXp+ap,
\]

the complete instantaneous moving-amplitude rate is

\[
 \dot M_k^{\rm cov}
 :=-L_y\!\left(X\mathcal E_1(X^kp^2)\right)
   +2L_y(X^kpV_{n,a}(p))
 =2aM_k-(2n+k+1)M_{k+1}.                         \tag{1}
\]

Put `D=M_0M_2-M_1^2` and define its product-rule covariant rate from (1). Then

\[
 \boxed{
 \dot D^{\rm cov}
 =4aD-(2n+3)(M_0M_3-M_1M_2).}                    \tag{2}
\]

For division-free adaptive successor `Q=M_0Xp-M_1p`, the new term is itself a higher mixed
landing:

\[
 M_0M_3-M_1M_2=L_y(pX^2Q).                       \tag{3}
\]

At `y=w^2`, `w>1/2`, (3) is the literal rational--Gamma-minus-von-Mangoldt completed aggregate
formed before reflection aggregation from bilinear packet `(p,XQ)`. Consequently every projective
first contact `D=0` obeys exact source transmutation

\[
 \boxed{
 \dot D^{\rm cov}=-(2n+3)\mathcal L^{\sharp,+}_w(p).} \tag{4}
\]

This is the first member of a closed all-grade law.  Put

\[
 D_k=M_kM_{k+2}-M_{k+1}^2,\qquad
 J_k=M_kM_{k+3}-M_{k+1}M_{k+2},
\]

and `Q_k=M_kXp-M_(k+1)p`.  Then

\[
 \boxed{
 \dot D_k^{\rm cov}=4aD_k-(2n+k+3)J_k,\qquad
 J_k=L_y(pX^{k+2}Q_k).}                              \tag{5}
\]

At every contact `D_k=0`, `J_k` is exactly the literal completed packet formed from
`(p,X^(k+1)Q_k)`.  Hence the producer is an infinite admission-selected arithmetic cascade, not
only one extra landing.

## Paper proof `[PROVED HERE]`

Shifted moment transport is `d L_y(f)/dy=-L_y(X E_1 f)` for fixed `f`. Moving `p` with tangent
`V` contributes `2L_y(X^k pV)`. Substitute `V=V_(n,a)(p)`, expand the derivative of `X^k p^2`,
and cancel the two `X^(k+2)pp'` terms. Remaining coefficients are `2a` at level `k` and
`-(2n+k+1)` at level `k+1`, proving (1).

Apply scalar product rule to `M_kM_(k+2)-M_(k+1)^2` and insert (1) at the three adjacent levels.
Gauge terms combine to
`4aD`; all successor terms combine to

\[
 -(2n+k+3)(M_kM_{k+3}-M_{k+1}M_{k+2}),
\]

proving (5), whose grade-zero specialization is (2). Finally

\[
 L_y(pX^2Q)=L_y\bigl(pX^2(M_0Xp-M_1p)\bigr)=M_0M_3-M_1M_2,
\]

which proves (3). Corpus packet preservation identifies `L_(w^2)(p X (XQ))` with completed
rational--Gamma minus von Mangoldt aggregation of packet `(p,XQ)` at base index one. Setting
`D=0` in (2) proves (4).

## Hostile conjecture loop

- **Nodal refinement monotonicity:** fails. Corpus has explicit right-half-disk datum whose plain
  landing is nonnegative but becomes negative after one rational nodal factor.
- **Sector/far-ray positivity transports through nodal weights:** fails. Polynomial weights are
  complex and signed on divisor atoms; one-signed unweighted cones do not survive multiplication.
- **Christoffel/Toda positivity supplies sign:** circular. Those sign laws begin with positive
  measure/Hankel data, exactly the RH-bearing premise here.
- **Projective coflow preserves landing sign:** fails as a formal consequence of (2); a contact is
  controlled by the independent higher mixed landing, not by `D`.
- **Linear growth of cascade coefficient forces nonsummable work:** fails even in a strictly
  positive two-atom model.  For positive separated atoms `0<r<s`,
  `D_k=AB(rs)^k(r-s)^2>0` and `J_k=AB(rs)^k(r+s)(r-s)^2>0`, but whenever `|rs|<1` every
  linearly weighted `sum_k (c+k)J_k` is summable.
- **Positive survivor:** projective coflow removes the full moving-coefficient connection and
  replaces it by a scalar gauge plus an all-grade literal completed source cascade.  Any
  nonsummability must be Xi-specific and normalized against geometric moment contraction.

## New principle

Finite admission failure is the shadow of a graded compound transport. Projectivizing Möbius root
motion does not close a finite positive cone; it raises first-contact orientation by one mixed
moment level. The correct obstruction is therefore an infinite contact cascade of endogenous
completed packets, not missing finite-dimensional orientation.

## Honest residual

Equation (4) is an exact producer law, not a sign theorem. Closing RH requires either a terminal
rule for the all-grade mixed landings, or a coercive cumulative estimate preventing an infinite
wrong-sign contact cascade along rational nodal amplitudes. No positive-measure assumption is
available.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/XiShiftedProjectiveNodalContactCascade.lean`

Unconditional capstones:

- `xiShiftedProjectiveMobiusVelocity_source_polynomial`;
- `xiShiftedProjectiveNodalWeightedMomentCovariantRate_eq`;
- `xiShiftedProjectiveNodalTuranCovariantRate_eq`;
- `xiShiftedProjectiveNodalHigherMixedLanding_eq_successorLanding`;
- `xiShiftedProjectiveNodalNextCompletedArithmeticLanding_eq_commonKernel_sourceFormation`;
- `xiShiftedProjectiveNodalNextCompletedArithmeticLanding_eq_higherMixed`;
- `xiShiftedProjectiveNodalTuranCovariantRate_eq_neg_nextArithmetic_of_contact`;
- `xiShiftedProjectiveNodalGradedTuranCovariantRate_eq`;
- `xiShiftedProjectiveNodalGradedHigherMixedLanding_eq_successorLanding`;
- `xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding_eq_commonKernel_sourceFormation`;
- `xiShiftedProjectiveNodalGradedNextCompletedArithmeticLanding_eq_higherMixed`;
- `xiShiftedProjectiveNodalGradedTuranCovariantRate_eq_neg_nextArithmetic_of_contact`;
- `projectiveTuranCascadeTwoAtom_turan_factorization`;
- `projectiveTuranCascadeTwoAtom_higherMixed_factorization`;
- `projectiveTuranCascadeTwoAtom_all_grades_pos`;
- `summable_projectiveTuranCascadeTwoAtom_weighted_higherMixed`.

Module is wired into `formal/GaloisForLFunctions/RHTower.lean`.
