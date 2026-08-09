# Isotropic law, passive gauge, intervention port, open projective history — Lean certification

- **ID:** ULF-IPE-1
- **Paper card:**
  `isotropic-law-passive-gauge-intervention-port-and-open-projective-history-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Model

The plane is `ℂ`, a two-dimensional real inner product space, with source coordinates `1` and `i`
and the first one marked as the intervention port.  `sourceLaw = ProbabilityTheory.stdGaussian ℂ`
is the standard Gaussian and `passiveRotation t = rotation (Circle.exp t)` is the rotation family,
acting by `z ↦ exp(it) · z`.  Mathlib's multivariate Gaussian and its isometry invariance
(`stdGaussian_map`) are used directly; no Gaussian theory is rebuilt.

## Certified declarations

### Theorem 1 — passive gauge becomes an intervention observable

- `map_passiveRotation_sourceLaw` — `Measure.map (R_t) sourceLaw = sourceLaw` for **every** `t`.
  This is the complete passive statement: the whole law agrees, hence so does every moment and
  every positive statistic;
- `passiveRotation_inner`, `passiveRotation_norm` — the Gram identity `R_t R_t^* = 1`;
- `interventionResponse_eq` — after `do(U₁ = 0)` the source is `u · i` and the response is
  `u • portDirection t` with `portDirection t = R_t i` a unit vector (`norm_portDirection`);
- `supportLine t = span ℝ {R_t i}` and `supportLine_eq_iff` —

  `supportLine t = supportLine s ↔ ∃ k : ℤ, t − s = k π`.

  So the marked intervention distinguishes `t` modulo `π`, while nothing passive distinguishes any
  `t` at all.  This is also the card's clause 3: forgetting the marking makes all rotations gauge
  equivalent; retaining the port leaves only the stabiliser `πℤ`.

### Theorem 2 — recurrent interventional shadow, open lifted history

`supportLine_periodic` and `supportLine_int_mul_pi` give `L_{t+kπ} = L_t`;
`portDirection_add_int_mul_pi` supplies the underlying sign `R_{t+kπ} i = (−1)^k R_t i`, via
`exp_int_mul_pi_mul_I`.  `lift_unbounded` shows the angle lift takes values `nπ` beyond every
bound.  `recurrent_shadow_open_lift` bundles: at the recurrent times every passive observer and the
projective interventional support have returned, while the lift has not.

### Theorem 3 — positive passive law erases source orientation

`swapSymmetry z = i · conj z` is the swap of the two source axes: `swapSymmetry_one` and
`swapSymmetry_I` give `1 ↦ i` and `i ↦ 1`, and `toMatrix_swapSymmetry` computes its matrix in
`Complex.basisOneI` as the card's `S = !![0,1;1,0]`.

- `map_swapSymmetry_sourceLaw` — identical passive law;
- `swapSymmetry_inner` — identical Gram operator;
- `det_swapSymmetry` and `det_id` — determinants `−1` and `1`;
- `swap_support_ne` — under the intervention the two supports are the two *different* axes;
- `positive_erases_orientation` — the capstone.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveIsotropicInterventionPort.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed with no warnings.  `#print axioms` on the passive invariance, the Gram identity,
the interventional response, the modulo-`π` criterion, the recurrence capstone, the determinant and
the orientation capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.  No project
axiom, placeholder, hypothesis interface, or unresolved theorem premise is used.

## Exact field consequence

Gauge status is not a property of a transformation.  The same rotation family is a complete gauge
for the passive isotropic doctrine, a family of genuinely distinct laws modulo `πℤ` for the
marked-intervention doctrine, orientation-blind for positive passive data, recurrent for projective
interventional data, and open for the lifted marked history.  Marking a single intervention port
simultaneously breaks the passive symmetry, exposes orientation, and turns a closed quotient
history into an open lift.
