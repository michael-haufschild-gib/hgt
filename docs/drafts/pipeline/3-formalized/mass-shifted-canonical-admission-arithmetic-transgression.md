# Mass-shifted canonical-admission arithmetic transgression

- **ID:** `mass-shifted-canonical-admission-arithmetic-transgression`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Frozen completed adaptive `P^sharp` source equals current positive Jacobi source plus an exact source-first bilinear admission transgression; fixed-mass admission transport is a path-independent cocycle.

## Goal

Replace vague frozen/current “shape holonomy” by the exact arithmetic object that can reverse the
sign of a completed adaptive packet.  Formation must use the admitted mixed amplitude inside the
rational--Gamma and von Mangoldt channels, before reflection aggregation.  No orientation map,
fixed linear reporter, or posterior null-vector choice is allowed.

## Gates

- [x] 0 → 1  in-progress: source-pure statement and hostile alternatives isolated
- [x] 1 → 2  fully-proven: complete algebraic proof from literal source identities
- [x] 2 → 3  formalized: module built, umbrella wired, axiom audit clean
- [ ] 3 → 4  publication-ready: not promoted; RH-facing mixed mass--admission curvature remains open

## Exact theorem

Let

\[
 Q_w(A)=\mathcal A_{\rm mix}^{\sharp}(w,A)
\]

be the literal completed adaptive rational--Gamma-minus-von-Mangoldt source and let
\(B_w(A,C)\) be its literal bilinear source formation.  Define

\[
 \mathfrak T_w(P,A)
 =2B_w(P,A-P)+Q_w(A-P).                                      \tag{1}
\]

Both terms are formed after amplitude selection and before reflection aggregation.  Direct
polarization gives

\[
 \boxed{Q_w(A)=Q_w(P)+\mathfrak T_w(P,A)},                  \tag{2}
\]

so

\[
 \boxed{\mathfrak T_w(P,A)=Q_w(A)-Q_w(P)}.                 \tag{3}
\]

Consequently

\[
 \mathfrak T_w(A,B)+\mathfrak T_w(B,C)=\mathfrak T_w(A,C),\qquad
 \mathfrak T_w(A,B)=-\mathfrak T_w(B,A).                   \tag{4}
\]

This is stronger than an admission-mismatch disjunction: fixed-source admission transport is
exact and has zero curvature.

For two source masses \(w,v\), the surviving rectangle is exactly

\[
 \mathfrak T_w(P,A)-\mathfrak T_v(P,A)
 =[Q_w(A)-Q_v(A)]-[Q_w(P)-Q_v(P)].                         \tag{4a}
\]

Thus mixed curvature is not a metaphor: it is failure of source-mass change to be independent of
admitted amplitude.

Let \(P_{n,w}\) be current canonical inverse-Hankel admission and \(P_{n,a}\) admission frozen at
another square-root mass.  In a current positive \((n+2)\)-block,

\[
 \boxed{
 Q_w(P_{n,a})
 =2h_n(w)E_n(w)+\mathfrak T_w(P_{n,w},P_{n,a}).}             \tag{5}
\]

Here \(2h_nE_n>0\) is current Jacobi source formed by actual admission.  Therefore

\[
 \boxed{
 Q_w(P_{n,a})<0
 \iff
 \mathfrak T_w(P_{n,w},P_{n,a})<-2h_n(w)E_n(w).}            \tag{6}
\]

Equation (6) is exact missing frozen/current source law: adverse outgoing sign occurs precisely
when source-native mixed transgression pays more than entire current positive arithmetic source.

## Proof

1. Existing completed packet theorem identifies diagonal source with twice adaptive shear.
2. Existing bilinear producer identifies \(B_w(A,C)\) with moment functional of symmetric Euler
   shear.
3. Euler shear is additive in each amplitude, and its diagonal equals completed mixed source.
4. Substitute \(A=P+(A-P)\) and expand both amplitude slots.  Symmetry combines cross terms into
   \(2B_w(P,A-P)\), proving (2).
5. Equations (3)--(4) follow by cancellation.
6. Current canonical-admission theorem substitutes
   \(Q_w(P_{n,w})=2h_n(w)E_n(w)\), proving (5); ordered-field algebra gives (6).

No analytic limit, numerical experiment, RH premise, new axiom, or fixed observer occurs.

## Conjecture → proof/fail loop

1. **Conjecture:** current source positivity transports to every frozen flag.  **Failed:** existing
   outgoing-ray theorem already permits negative fixed-amplitude source after admission mismatch.
2. **Conjecture:** mixed bilinear source alone has a universal sign.  **Failed:** existing
   null-diagonal/live-polarization theorem makes higher-contact source matrix indefinite.
3. **Conjecture:** frozen/current mismatch is nontrivial fixed-mass holonomy.  **Failed sharply:**
   (3)--(4) prove it is an exact endpoint cocycle.
4. **Positive survivor:** only mixed mass--admission curvature can be nontrivial.  A successful
   global theorem must control how \(\mathfrak T_w(P_{n,a},P_{n,b})\) changes with source mass
   \(w\), not integrate a fixed-mass orientation or reporter.

## Novelty audit

Corpus search found no prior admission-transgression, cocycle, or frozen/current exact source law.
External orthogonal-polynomial work studies Christoffel transformations, recurrence compatibility,
and Toda deformations, for example [Kozhan--Vaktnäs](https://arxiv.org/abs/2407.13946) and
[Álvarez-Fernández et al.](https://arxiv.org/abs/1511.04771).  Xi orthogonal expansions are studied
by [Romik](https://arxiv.org/abs/1902.06330).  None of these located sources contains the present
Xi-specific rational--Gamma/von-Mangoldt adaptive source, its bilinear arithmetic polarization, or
the frozen/current sign equivalence (6).  Novelty claim is internal and formulation-level pending
publication review.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionArithmeticTransgression.lean`

Principal declarations:

- `xiShiftedAdaptiveBilinearCompletedArithmeticSource_self_eq_mixed`
- `xiShiftedAdaptiveMixedCompletedArithmeticSource_admission_decomposition`
- `xiShiftedAdaptiveArithmeticAdmissionTransgression_eq_source_sub`
- `xiShiftedAdaptiveArithmeticAdmissionTransgression_trans`
- `xiShiftedAdaptiveArithmeticAdmissionTransgression_mass_rectangle`
- `xiShiftedCanonicalFrozenCurrentArithmeticTransgression`
- `xiShiftedCompletedMomentAggregate_frozenAdmission_eq_currentJacobiEnergy_add_transgression`
- `xiShiftedCompletedMomentAggregate_frozenAdmission_neg_iff_transgression_lt_neg_currentEnergy`

Verification:

- direct `lake env lean` check passes;
- targeted module build produces the `.olean`;
- capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.

## RH impact

Producer construction is closed at exact type.  Fixed-mass admission comparison is also closed and
cannot carry genuine holonomy.  Remaining Route-U theorem is now narrower:

> control mixed mass--admission curvature of the literal arithmetic transgression along the
> selected bounded-scale frozen/current path strongly enough to exclude (6).

This does not prove RH.

## Log

- 2026-08-11 — exact source polarization conjectured, proved, formalized, built, and axiom-audited
