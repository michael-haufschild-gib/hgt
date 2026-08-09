# Isotropic law, passive gauge, intervention port, and open projective history law

- **ID:** ULF-IPE-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort`
- **Source:** synthesis of law-phase and counterfactual forks
- **Statement:** A source symmetry can be completely invisible passively, observable under a marked intervention, recurrent after projectivization, and open on its lifted history.

## Goal

Give a non-product finite theorem joining observer equivalence, positivity, marked intervention,
orientation, recurrence, and open history. The same source symmetry controls every clause.

## Gates

- [x] 0 → 1: explicit Gaussian law with marked source port
- [x] 1 → 2: exact distribution, support, quotient, and lift computations
- [x] 2 → 3: Lean-certified in
  `GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort`
- [ ] 3 → 4: no publication/priority claim

## 1. Passive family

Let (U=(U_1,U_2)\sim N(0,I_2)). For (t\in\mathbb R), let

\[
R_t=\begin{pmatrix}\cos t&-\sin t\\\sin t&\cos t\end{pmatrix},
\qquad
Y_t=R_tU.
\tag{1}
\]

Mark the first source coordinate as an intervention port. The intervention
(\operatorname{do}(U_1=0)) leaves (U_2\sim N(0,1)) unchanged.

## Theorem 1 — passive gauge becomes an intervention observable

1. For every (t), (Y_t\sim N(0,I_2)). Hence the complete passive probability law, every
   moment, every positive quadratic statistic, and the covariance (R_tR_t^*=I_2) are independent
   of (t).
2. After (\operatorname{do}(U_1=0)),
   \[
   Y_t^{\mathrm{do}}=U_2R_te_2,
   \tag{2}
   \]
   so its support is the line
   \[
   L_t=\operatorname{span}(R_te_2)\in\mathbb{RP}^1.
   \tag{3}
   \]
   Thus marked intervention responses distinguish (t\) modulo (\pi), even though no passive
   statistic distinguishes any (t).
3. If the source-coordinate marking is forgotten, (R_t) is absorbed by the isotropic source
   symmetry and all (t) are gauge-equivalent. If the intervention port is retained, only
   (t\equiv s\pmod\pi) have the same support response.

### Proof

Orthogonal invariance of the standard Gaussian gives (1). Under intervention,
(U=(0,U_2)), yielding (2). Two nonzero vectors (R_te_2,R_se_2) span the same unoriented line
exactly when (t-s\in\pi\mathbb Z). The final claim is precisely the distinction between allowing
all source rotations and requiring preservation of the marked port. ∎

## Theorem 2 — recurrent interventional shadow, open lifted history

The projective intervention history satisfies

\[
L_{t+\pi}=L_t.
\tag{4}
\]

Its basepoint lift to the universal cover (\mathbb R\to\mathbb{RP}^1\cong S^1) is the angle
(t). Consequently, at recurrent times (t_n=n\pi), every passive observer and the projective
intervention support have returned, while the lifted history equals (n\pi) and is unbounded.

### Proof

Equation (4) follows from (R_{t+\pi}e_2=-R_te_2). The standard covering of the line circle by
its angle coordinate gives the lift and its unbounded values. ∎

## Theorem 3 — positive passive law erases source orientation

Let

\[
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

The laws (Y=U) and (Y'=SU) have the same complete passive distribution and the same positive
Gram operator (I_2), while

\[
\det I_2=1,\qquad \det S=-1.
\tag{5}
\]

Under (\operatorname{do}(U_1=0)), the first output is supported on the (e_2)-axis and the
second on the (e_1)-axis. Thus positive passive data erase orientation, whereas a marked
intervention recovers a distinction.

### Proof

Both matrices are orthogonal, so isotropic Gaussian invariance gives identical passive laws and Gram
operators. Equation (5) and the two column images give the remaining claims. ∎

## 2. Route-independent classification principle

This theorem gives an exact answer to "are routes gauges?":

- relative to the passive isotropic doctrine, the rotations are gauges;
- relative to the marked-intervention doctrine, they are distinct laws modulo a smaller stabilizer;
- relative to positive passive data, orientation is erased;
- relative to projective intervention data, history is recurrent;
- relative to the lifted marked history, it is open.

Gauge status is therefore not intrinsic to a transformation alone. It is relative to retained marks,
legal interventions, and observer doctrine.

## 3. Hostile scope

Gaussian symmetry, interventions, and projective winding are classical. This is a finite calibration,
not a universal source model. It proves no hypertranscendence or arithmetic theorem. Its field-level
content is the non-product coupling: marking one intervention port simultaneously breaks passive gauge
symmetry, exposes orientation, and changes recurrence from a closed quotient to an open lift.

## Log

- 2026-08-09 — exact passive/interventional/projective synthesis recorded; no Lean.

## Lean certification status (2026-08-09) — COMPLETE

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort`
(wired into `HTGeometry.UniversalLawField`).

The plane is modelled as `ℂ` with source coordinates `1` and `i`, the first marked as the
intervention port; `sourceLaw = stdGaussian ℂ` and `passiveRotation t = rotation (Circle.exp t)`.

Theorem 1: `map_passiveRotation_sourceLaw` — `Measure.map (R_t) sourceLaw = sourceLaw` for every
`t`, so the complete passive law and therefore every moment and every positive statistic is
independent of `t`; `passiveRotation_inner` and `passiveRotation_norm` are the Gram identity
`R_t R_t^* = 1`. `interventionResponse_eq` gives the `do(U₁ = 0)` response `u • R_t i`, whose
support is `supportLine t = span ℝ {R_t i}`, and `supportLine_eq_iff` proves
`supportLine t = supportLine s ↔ ∃ k : ℤ, t − s = kπ`.

Theorem 2: `supportLine_periodic`, `supportLine_int_mul_pi`, `lift_unbounded`, bundled as
`recurrent_shadow_open_lift`.

Theorem 3: `swapSymmetry` is the orientation-reversing symmetry `z ↦ i·conj z`, i.e. the swap of
the two source axes in the basis `(1, i)`. `map_swapSymmetry_sourceLaw` and `swapSymmetry_inner`
give the identical passive law and Gram operator; `toMatrix_swapSymmetry` computes its matrix in
`Complex.basisOneI` as the swap matrix and `det_swapSymmetry` gives `−1` against `det_id = 1`;
`swap_support_ne` shows the interventional supports are the two different axes. The capstone is
`positive_erases_orientation`.

`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
