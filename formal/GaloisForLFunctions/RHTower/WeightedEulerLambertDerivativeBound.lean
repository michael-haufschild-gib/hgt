import GaloisForLFunctions.RHTower.CompactCarrierLambert

/-!
# Derivative bounds for the compact-carrier Lambert transform

The Lambert transform `H` of a functional carried by a
compact set with real part `≥ δ > 0` and norm `≤ M` satisfies, at every point
`x` of the positive ray and every derivative order `N ≤ δx/(4M)`,

`‖H^{(N)}(x)‖ ≤ 4 ‖L‖ e^{-δx/2}`.

The proof replaces term-by-term differentiation and `M^N`
absorption by a Cauchy estimate on the disc `|z - x| ≤ δx/(2M)`: on
that disc `Re(z·s) ≥ δx/2`, so the exponential test contracts at rate
`e^{-δx/2}`, the kernel majorant is geometric, and Cauchy's inequality
converts the sup bound into all scale-linear derivative bounds at once — the
factorial is absorbed by `N! ≤ N^N ≤ (r/2)^N`.  This is the derivative bound with `δ₁ = δ/2`, the analytic input to the
prime-log oversampling lemma.

Everything is unconditional.
-/

noncomputable section

namespace RHTower

open Complex Metric Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

omit [CompactSpace K] in
/-- On the disc `|z - x| ≤ r` around a positive real center, a carrier with
real part `≥ δ` and norm `≤ M` keeps `Re (z·s)` above `xδ - rM`. -/
theorem re_mul_carrier_ge_on_closedBall
    (s : C(K, ℂ)) {δ M x r : ℝ}
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M)
    (hx : 0 ≤ x) (hr : 0 ≤ r)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) r) (k : K) :
    x * δ - r * M ≤ (z * s k).re := by
  have hsplit : z * s k = (x : ℂ) * s k + (z - (x : ℂ)) * s k := by ring
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (s k)) (hnorm k)
  have h1 : x * δ ≤ ((x : ℂ) * s k).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (hre k) hx
  have h2 : -(r * M) ≤ ((z - (x : ℂ)) * s k).re := by
    have habs : |((z - (x : ℂ)) * s k).re| ≤ r * M := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_mul]
      have hz' : ‖z - (x : ℂ)‖ ≤ r := by
        rwa [mem_closedBall, dist_eq_norm] at hz
      exact mul_le_mul hz' (hnorm k) (norm_nonneg _) hr
    linarith [neg_abs_le (((z - (x : ℂ)) * s k).re), habs]
  calc x * δ - r * M ≤ ((x : ℂ) * s k).re + ((z - (x : ℂ)) * s k).re := by
        linarith
    _ = (z * s k).re := by rw [hsplit, Complex.add_re]

/-- **Sup bound for the Lambert transform on sector discs**: on the disc
`|z - x| ≤ δx/(2M)` the transform is bounded by `4‖L‖e^{-δx/2}` once the
contraction ratio has fallen below `1/2`. -/
theorem norm_compactCarrierLambertTransform_le_on_closedBall
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {δ M x : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M)
    (hx0 : 0 < x)
    (hcontr : Real.exp (-(x * δ / 2)) ≤ 1 / 2)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) (δ * x / (2 * M))) :
    ‖compactCarrierLambertTransform L s z‖
      ≤ 4 * ‖L‖ * Real.exp (-(x * δ / 2)) := by
  have hM : 0 < M := lt_of_lt_of_le hδ hδM
  have hr : 0 ≤ δ * x / (2 * M) := by positivity
  have hre2 : ∀ k, x * δ / 2 ≤ (z * s k).re := by
    intro k
    have h := re_mul_carrier_ge_on_closedBall s hre hnorm hx0.le hr hz k
    have : δ * x / (2 * M) * M = x * δ / 2 := by
      field_simp
    calc x * δ / 2 = x * δ - δ * x / (2 * M) * M := by rw [this]; ring
      _ ≤ (z * s k).re := h
  have hq : ‖compactExponentialTest s z‖ ≤ Real.exp (-(x * δ / 2)) :=
    norm_compactExponentialTest_le_exp_neg_of_re s z _ hre2
  set ρ : ℝ := Real.exp (-(x * δ / 2)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := lt_of_le_of_lt hcontr (by norm_num)
  have hker : ‖compactLambertKernel s z‖ ≤ ∑' n : ℕ, (n : ℝ) * ρ ^ n :=
    norm_compactLambertKernel_le_geometricMajorant s z ρ hρ0.le hρ1 hq
  have hgeom : (∑' n : ℕ, (n : ℝ) * ρ ^ n) = ρ / (1 - ρ) ^ (2 : ℕ) :=
    tsum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
  have hquarter : (1/4 : ℝ) ≤ (1 - ρ) ^ (2 : ℕ) := by nlinarith
  have hmajor : ρ / (1 - ρ) ^ (2 : ℕ) ≤ 4 * ρ := by
    calc ρ / (1 - ρ) ^ (2 : ℕ) ≤ ρ / (1/4) :=
          div_le_div_of_nonneg_left hρ0.le (by norm_num) hquarter
      _ = 4 * ρ := by ring
  calc ‖compactCarrierLambertTransform L s z‖
      = ‖L (compactLambertKernel s z)‖ := rfl
    _ ≤ ‖L‖ * ‖compactLambertKernel s z‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (4 * ρ) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg L)
        exact le_trans hker (le_of_eq hgeom |>.trans hmajor)
    _ = 4 * ‖L‖ * ρ := by ring

/-- **Cauchy derivative bound**: every derivative of the
compact-carrier Lambert transform up to the scale-linear order `δx/(4M)`
decays at the fixed exponential rate `δ/2` along the positive ray. -/
theorem norm_iteratedDeriv_compactCarrierLambertTransform_le
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {δ M x : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hre : ∀ k, δ ≤ (s k).re) (hnorm : ∀ k, ‖s k‖ ≤ M)
    (hx0 : 0 < x)
    (hcontr : Real.exp (-(x * δ / 2)) ≤ 1 / 2)
    {N : ℕ} (hN : (N : ℝ) ≤ δ * x / (4 * M)) :
    ‖iteratedDeriv N (compactCarrierLambertTransform L s) (x : ℂ)‖
      ≤ 4 * ‖L‖ * Real.exp (-(x * δ / 2)) := by
  have hM : 0 < M := lt_of_lt_of_le hδ hδM
  set r : ℝ := δ * x / (2 * M) with hrdef
  have hr0 : 0 < r := by positivity
  set C : ℝ := 4 * ‖L‖ * Real.exp (-(x * δ / 2)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hcontr_ball : ∀ z ∈ closedBall (x : ℂ) r,
      ‖compactExponentialTest s z‖ < 1 := by
    intro z hz
    have hre2 : ∀ k, x * δ / 2 ≤ (z * s k).re := by
      intro k
      have h := re_mul_carrier_ge_on_closedBall s hre hnorm hx0.le hr0.le hz k
      have heq : r * M = x * δ / 2 := by
        rw [hrdef]; field_simp
      calc x * δ / 2 = x * δ - r * M := by rw [heq]; ring
        _ ≤ (z * s k).re := h
    exact norm_compactExponentialTest_lt_one_of_re_pos s z _
      (by positivity) hre2
  have hdiff : DiffContOnCl ℂ (compactCarrierLambertTransform L s)
      (ball (x : ℂ) r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (x : ℂ) hr0.ne']
    intro z hz
    exact ((compactCarrierLambertTransform_analyticAt L s z
      (hcontr_ball z hz)).differentiableAt).differentiableWithinAt
  have hsphere : ∀ z ∈ sphere (x : ℂ) r,
      ‖compactCarrierLambertTransform L s z‖ ≤ C := by
    intro z hz
    exact norm_compactCarrierLambertTransform_le_on_closedBall L s hδ hδM
      hre hnorm hx0 hcontr (sphere_subset_closedBall hz)
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    N hr0 hdiff hsphere
  refine le_trans hcauchy ?_
  have hNr : (N : ℝ) ≤ r / 2 := by
    rw [hrdef]
    calc (N : ℝ) ≤ δ * x / (4 * M) := hN
      _ = δ * x / (2 * M) / 2 := by ring
  have hfact : (N.factorial : ℝ) ≤ (r / 2) ^ N := by
    calc (N.factorial : ℝ) ≤ ((N : ℕ) ^ N : ℕ) := by
          exact_mod_cast Nat.factorial_le_pow N
      _ = ((N : ℝ)) ^ N := by push_cast; rfl
      _ ≤ (r / 2) ^ N := pow_le_pow_left₀ (Nat.cast_nonneg N) hNr N
  have hpow : (0:ℝ) < r ^ N := pow_pos hr0 N
  rw [div_le_iff₀ hpow]
  have hhalf : (r / 2) ^ N ≤ r ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  calc (N.factorial : ℝ) * C ≤ r ^ N * C :=
        mul_le_mul_of_nonneg_right (hfact.trans hhalf) hC0
    _ = C * r ^ N := by ring

end RHTower
