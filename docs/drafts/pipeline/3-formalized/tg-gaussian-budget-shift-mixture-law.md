# TG — Positive mixtures of Gaussian budgets: the smallest shift decides; temperedness gate

- **ID:** TG-MIX-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional) + NO-GO certificate (wall 9 in TG form)
- **Statement:** For a finite family of shifts σ_j > 0 (repetition = integer weights) with
  M(y) = Σ_j (P_{σ_j} − C_{σ_j})(y):
  (a) M ≤ B on (0,1] ⇒ ξ ≠ 0 on Re z > σ_j for every j (the smallest shift decides);
  (b) zeros ≤ θ, θ < σ_j < 2 ∀j ⇒ ∃B: M ≤ B;
  (c) shifts in [½,2) with minimum ½: RH ⟺ ∃B: M ≤ B;
  (d) temperedness gate: for 0 < a < ½, the central Gaussian gap of ζ(s−a)ζ(s+a)
      (coefficients Λ(n)(n^a + n^{−a}) ≥ 0, functional equation, Euler product) is unbounded above on (0,1].

## Proof
Deficit B − M(e^{-u}) ≥ 0 is a Laplace carrier; transform = B/w − Σ_j(Γ(w)(A − ξ'/ξ)(σ_j+2w) − T_j(w)) + 1/(w+1)
for Re w > 3, analytic at every positive real (ξ has no real zeros) ⇒ Landau: abscissa ≤ 0. So
Σ_j ξ'/ξ(σ_j+2w) = ½ logDeriv H, H(w) = Π_j ξ(σ_j+2w), continues holomorphically to Re w > 0;
H' = K H with K holomorphic ⇒ H zero-free there (order count) ⇒ each factor zero-free. Zero multiplicities
are positive, so no cancellation between shifts. (d): Hardy critical zero at Re ½ > ½ − a.

## Lean
`RHTower/GaussianBudgetShiftMixtureLaw.lean` (399 lines), wired after GaussianCentralGapMeanSquareBudget.
`integral_gaussianMixtureDeficit_mul_cexp`, `xi_ne_zero_of_gaussianMixtureBudget`,
`xi_zero_re_le_of_gaussianMixtureBudget`, `exists_gaussianMixtureBudget_of_zero_bound`,
`riemannHypothesis_iff_gaussianMixtureBudget`, `gaussianMixtureGap_eisensteinShift`,
`not_exists_gaussianEisensteinBudget`. Axioms [propext, Classical.choice, Quot.sound]. Uses
HTGeometry/LogDerivNoZero (`ne_zero_of_deriv_eq_mul`).

## Reading (producer consequences)
- Mixing budgets across shifts cannot help a producer: a provable budget at σ>1 added to the target at ½
  gives exactly the target's content (smallest shift decides, no cancellation by positivity of multiplicities).
- Wall 9 in TG form, unconditional and formal: FE + Euler product + Λ ≥ 0 do not imply the central
  Gaussian budget; a producer must use coefficient size |Λ_L(n)| ≤ Λ(n)·O(1).
