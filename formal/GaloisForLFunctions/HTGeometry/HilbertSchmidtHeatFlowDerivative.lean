import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import Mathlib.Analysis.Normed.Group.Tannery
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Schatten-two derivatives of a kernel heat flow

Let `K` be a kernel on `ι × ι` and `s ≥ 0` a rate on the index pairs.  The heat flow
`u ↦ e^{-u s} K`, `u ≥ 0`, and its formal derivatives `(-s)^k e^{-us} K` are Hilbert–Schmidt as soon as
`s^k K` is square summable.  If moreover `s^{k+1} K` is square summable, then the `k`-th kernel is
differentiable on `[0, ∞)` with derivative the `(k+1)`-st kernel, and the difference quotients
converge in Hilbert–Schmidt norm; in particular the represented operators are differentiable in
operator norm.

The mechanism is dominated convergence: the difference quotient of `t ↦ e^{-ts}` minus its
derivative is bounded by `2s` (the exponential is `1`-Lipschitz on `(-∞, 0]`) and tends to zero
pointwise.
-/

open Filter Topology Set

noncomputable section

namespace HilbertSchmidt

variable {ι : Type*}

/-- The heat-flow kernel `(-s)^k e^{-u⁺ s} K`, with `u⁺ = max u 0`. -/
def heatFlowKernel (s : ι × ι → ℝ) (K : ι × ι → ℂ) (k : ℕ) (u : ℝ) (ab : ι × ι) : ℂ :=
  (((-s ab) ^ k * Real.exp (-(max u 0 * s ab)) : ℝ) : ℂ) * K ab

variable {s : ι × ι → ℝ} {K : ι × ι → ℂ}

theorem heatFlowKernel_of_nonneg (k : ℕ) {u : ℝ} (hu : 0 ≤ u) (ab : ι × ι) :
    heatFlowKernel s K k u ab = (((-s ab) ^ k * Real.exp (-(u * s ab)) : ℝ) : ℂ) * K ab := by
  rw [heatFlowKernel, max_eq_left hu]

theorem norm_heatFlowKernel_le (hs : ∀ ab, 0 ≤ s ab) (k : ℕ) (u : ℝ) (ab : ι × ι) :
    ‖heatFlowKernel s K k u ab‖ ≤ s ab ^ k * ‖K ab‖ := by
  have he : Real.exp (-(max u 0 * s ab)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (le_max_right u 0) (hs ab)))
  rw [heatFlowKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (hs ab), abs_of_pos (Real.exp_pos _)]
  have h0 := pow_nonneg (hs ab) k
  calc s ab ^ k * Real.exp (-(max u 0 * s ab)) * ‖K ab‖ ≤ s ab ^ k * 1 * ‖K ab‖ := by
        gcongr
    _ = s ab ^ k * ‖K ab‖ := by ring

theorem isHS_heatFlowKernel (hs : ∀ ab, 0 ≤ s ab) {k : ℕ}
    (hk : Summable fun ab => (s ab ^ k * ‖K ab‖) ^ 2) (u : ℝ) : IsHS (heatFlowKernel s K k u) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun ab => pow_le_pow_left₀ (norm_nonneg _) (norm_heatFlowKernel_le hs k u ab) 2) hk

/-- The represented heat-flow operator (zero if the kernel is not Hilbert–Schmidt). -/
def heatFlowOperator (s : ι × ι → ℝ) (K : ι × ι → ℂ) (k : ℕ) (u : ℝ) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  open scoped Classical in if h : IsHS (heatFlowKernel s K k u) then toOperator h else 0

theorem heatFlowOperator_eq {k : ℕ} {u : ℝ} (h : IsHS (heatFlowKernel s K k u)) :
    heatFlowOperator s K k u = toOperator h := by
  classical
  rw [heatFlowOperator, dif_pos h]

/-- The slope kernel `(v-u)^{-1}(H_k(v) - H_k(u)) - H_{k+1}(u)`. -/
def heatFlowSlopeDefect (s : ι × ι → ℝ) (K : ι × ι → ℂ) (k : ℕ) (u v : ℝ) : ι × ι → ℂ :=
  ((v - u)⁻¹ : ℂ) • (heatFlowKernel s K k v - heatFlowKernel s K k u) - heatFlowKernel s K (k + 1) u

theorem toOperator_slope_sub {A B C : ι × ι → ℂ} (hA : IsHS A) (hB : IsHS B) (hC : IsHS C) (c : ℂ) :
    c • (toOperator hA - toOperator hB) - toOperator hC =
      toOperator ((isHS_sub hA hB).smul c |> fun h => isHS_sub h hC) := by
  rw [toOperator_sub hA hB]
  ext f i
  change c * toOperator (isHS_sub hA hB) f i - toOperator hC f i =
    ∑' j, (c • (A - B) - C) (i, j) * f j
  rw [toOperator_apply, toOperator_apply, ← tsum_mul_left,
    ← (((summable_row_mul (isHS_sub hA hB) f i).mul_left c)).tsum_sub (summable_row_mul hC f i)]
  exact tsum_congr fun j => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The slope defect is pointwise `(-s)^k K · ψ`, `ψ(v) = (e^{-vs} - e^{-us})/(v-u) + s e^{-us}`. -/
theorem heatFlowSlopeDefect_apply (k : ℕ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ab : ι × ι) :
    heatFlowSlopeDefect s K k u v ab =
      ((((-s ab) ^ k * ((v - u)⁻¹ * (Real.exp (-(v * s ab)) - Real.exp (-(u * s ab))) +
        s ab * Real.exp (-(u * s ab)))) : ℝ) : ℂ) * K ab := by
  simp only [heatFlowSlopeDefect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    heatFlowKernel_of_nonneg _ hu, heatFlowKernel_of_nonneg _ hv]
  push_cast
  ring

/-- `|ψ| ≤ 2s` for `u, v ≥ 0`. -/
theorem abs_heatSlope_le {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hvu : v ≠ u) (ht : 0 ≤ t) :
    |(v - u)⁻¹ * (Real.exp (-(v * t)) - Real.exp (-(u * t))) + t * Real.exp (-(u * t))| ≤ 2 * t := by
  have h1 : |Real.exp (-(v * t)) - Real.exp (-(u * t))| ≤ t * |v - u| := by
    refine (GaloisForLFunctions.HTGeometry.abs_exp_sub_exp_le (M := 0) (by nlinarith)
      (by nlinarith)).trans (le_of_eq ?_)
    rw [Real.exp_zero, one_mul, show -(v * t) - -(u * t) = -(t * (v - u)) by ring, abs_neg, abs_mul,
      abs_of_nonneg ht]
  have hvu' : 0 < |v - u| := abs_pos.2 (sub_ne_zero.2 hvu)
  have h2 : |(v - u)⁻¹ * (Real.exp (-(v * t)) - Real.exp (-(u * t)))| ≤ t := by
    rw [abs_mul, abs_inv, inv_mul_le_iff₀ hvu']
    linarith
  have h3 : |t * Real.exp (-(u * t))| ≤ t := by
    rw [abs_mul, abs_of_nonneg ht, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right ht (Real.exp_le_one_iff.2 (by nlinarith))
  calc _ ≤ |(v - u)⁻¹ * (Real.exp (-(v * t)) - Real.exp (-(u * t)))| + |t * Real.exp (-(u * t))| :=
        abs_add_le _ _
    _ ≤ 2 * t := by linarith

/-- `ψ → 0` as `v → u`. -/
theorem tendsto_heatSlope (u t : ℝ) :
    Tendsto (fun v => (v - u)⁻¹ * (Real.exp (-(v * t)) - Real.exp (-(u * t))) +
      t * Real.exp (-(u * t))) (𝓝[≠] u) (𝓝 0) := by
  have h1 : HasDerivAt (fun v : ℝ => -(v * t)) (-t) u := (hasDerivAt_mul_const t).neg
  have hd : HasDerivAt (fun v : ℝ => Real.exp (-(v * t))) (-t * Real.exp (-(u * t))) u :=
    h1.exp.congr_deriv (by ring)
  have h := (hasDerivAt_iff_tendsto_slope.1 hd).add_const (t * Real.exp (-(u * t)))
  rw [show -t * Real.exp (-(u * t)) + t * Real.exp (-(u * t)) = 0 by ring] at h
  refine h.congr fun v => ?_
  simp only [slope_def_field]
  ring

/-- **Schatten-two derivative.**  The slope defect tends to zero in Hilbert–Schmidt norm. -/
theorem tendsto_hsNorm_heatFlowSlopeDefect (hs : ∀ ab, 0 ≤ s ab) {k : ℕ}
    (hk1 : Summable fun ab => (s ab ^ (k + 1) * ‖K ab‖) ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun v => hsNorm (heatFlowSlopeDefect s K k u v)) (𝓝[Ici 0 \ {u}] u) (𝓝 0) := by
  have hfilt : 𝓝[Ici 0 \ {u}] u ≤ 𝓝[≠] u := nhdsWithin_mono _ fun x hx => hx.2
  have hmem : ∀ᶠ v in 𝓝[Ici 0 \ {u}] u, v ∈ Ici (0 : ℝ) \ {u} := self_mem_nhdsWithin
  have hsq : Tendsto (fun v => hsNormSq (heatFlowSlopeDefect s K k u v)) (𝓝[Ici 0 \ {u}] u)
      (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Ici 0 \ {u}] u)
      (f := fun v ab => ‖heatFlowSlopeDefect s K k u v ab‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun ab => 4 * (s ab ^ (k + 1) * ‖K ab‖) ^ 2) (hk1.mul_left 4) ?_ ?_
    · simpa [hsNormSq] using h
    · intro ab
      have hψ := ((tendsto_heatSlope u (s ab)).mono_left hfilt).const_mul ((-s ab) ^ k)
      rw [mul_zero] at hψ
      have hn := hψ.abs.mul_const ‖K ab‖
      rw [abs_zero, zero_mul] at hn
      have hlim := ((continuous_pow 2).tendsto 0).comp hn
      rw [zero_pow two_ne_zero] at hlim
      refine hlim.congr' ?_
      filter_upwards [hmem] with v hv
      rw [heatFlowSlopeDefect_apply k hu hv.1, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rfl
    · filter_upwards [hmem] with v hv ab
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heatFlowSlopeDefect_apply k hu hv.1,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
        abs_of_nonneg (hs ab)]
      have hb := abs_heatSlope_le hu hv.1 hv.2 (hs ab)
      have h0 := pow_nonneg (hs ab) k
      have hK0 := norm_nonneg (K ab)
      calc (s ab ^ k * |(v - u)⁻¹ * (Real.exp (-(v * s ab)) - Real.exp (-(u * s ab))) +
            s ab * Real.exp (-(u * s ab))| * ‖K ab‖) ^ 2
          ≤ (s ab ^ k * (2 * s ab) * ‖K ab‖) ^ 2 := by gcongr
        _ = 4 * (s ab ^ (k + 1) * ‖K ab‖) ^ 2 := by ring
  have h := ((Real.continuous_sqrt.tendsto 0).comp hsq)
  rw [Real.sqrt_zero] at h
  exact h

/-- **Operator-norm derivative.**  On `[0, ∞)` the heat-flow operator of order `k` has derivative
the heat-flow operator of order `k + 1`. -/
theorem hasDerivWithinAt_heatFlowOperator (hs : ∀ ab, 0 ≤ s ab) {k : ℕ}
    (hk : Summable fun ab => (s ab ^ k * ‖K ab‖) ^ 2)
    (hk1 : Summable fun ab => (s ab ^ (k + 1) * ‖K ab‖) ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivWithinAt (heatFlowOperator s K k) (heatFlowOperator s K (k + 1) u) (Ici 0) u := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_)
    (tendsto_hsNorm_heatFlowSlopeDefect hs hk1 hu)
  rw [slope_def_module, heatFlowOperator_eq (isHS_heatFlowKernel hs hk v),
    heatFlowOperator_eq (isHS_heatFlowKernel hs hk u), heatFlowOperator_eq (isHS_heatFlowKernel hs hk1 u),
    show ((v - u)⁻¹ : ℝ) • (toOperator (isHS_heatFlowKernel hs hk v) -
        toOperator (isHS_heatFlowKernel hs hk u)) =
      ((v - u)⁻¹ : ℂ) • (toOperator (isHS_heatFlowKernel hs hk v) -
        toOperator (isHS_heatFlowKernel hs hk u)) by
      rw [show ((v : ℂ) - u)⁻¹ = (((v - u)⁻¹ : ℝ) : ℂ) by push_cast; rfl]
      exact (algebraMap_smul ℂ ((v - u)⁻¹ : ℝ) _).symm,
    toOperator_slope_sub]
  exact norm_toOperator_le _

/-- **Iterated derivatives.**  If `s^j K` is square summable for `j ≤ n`, the `n`-th derivative
of the heat flow on `[0, ∞)` is the heat-flow operator of order `n`. -/
theorem iteratedDerivWithin_heatFlowOperator (hs : ∀ ab, 0 ≤ s ab) :
    ∀ n : ℕ, (∀ j ≤ n, Summable fun ab => (s ab ^ j * ‖K ab‖) ^ 2) →
      ∀ u ∈ Ici (0 : ℝ),
        iteratedDerivWithin n (heatFlowOperator s K 0) (Ici 0) u = heatFlowOperator s K n u
  | 0, _, u, _ => by rw [iteratedDerivWithin_zero]
  | n + 1, hK, u, hu => by
    have ih := iteratedDerivWithin_heatFlowOperator hs n (fun j hj => hK j (by omega))
    rw [iteratedDerivWithin_succ, derivWithin_congr (fun v hv => ih v hv) (ih u hu)]
    exact (hasDerivWithinAt_heatFlowOperator hs (hK n (by omega)) (hK (n + 1) le_rfl)
      (mem_Ici.1 hu)).derivWithin (uniqueDiffOn_Ici 0 u hu)

end HilbertSchmidt
