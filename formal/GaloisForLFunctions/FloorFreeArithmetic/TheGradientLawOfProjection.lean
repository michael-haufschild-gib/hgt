import GaloisForLFunctions.FloorFreeArithmetic.LinearStatisticsAreNotMonotoneUnderProjection

/-!
# The gradient law of projection

A functional of a zero configuration that is a differentiable function `φ` of finitely many
linear statistics `Σ_ρ F_i(ξ_ρ)` changes, when a double point `ξ` of the line splits into the
reflection pair `ξ ± iδ`, from `φ(S)` to `φ(S + Δ(ξ, δ))`, where `Δ_i` is the split increment of
`F_i`. To first order in `φ` this is the linear statistic with the symbol `Σ_i ∂_iφ(S) F_i`.

* `abs_splitIncrement_add_le`: the second-order expansion of a split increment,
  `Δ = −δ² Re F''(ξ) + o(δ²)`.
* `sum_gradient_mul_re_deriv2_nonpos`: if splitting at `ξ` does not decrease `φ` for all small
  depths, then `Σ_i ∂_iφ(S) Re F_i''(ξ) ≤ 0`.
* `concaveOn_re_gradientSymbol`: if this holds at every ordinate, the real part of the gradient
  symbol `Σ_i ∂_iφ(S) F_i` is concave on the line.
* `re_gradientSymbol_eq_zero`: if moreover that real part is bounded below and tends to zero,
  it vanishes on the line.

So a differentiable function of finitely many convergent linear statistics is monotone under
projection only where its gradient annihilates the symbols on the line: the functional has no
first-order dependence on the statistics there. Monotonicity is never produced by combining
linear statistics.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

/-! ### The second-order expansion of a split increment -/

/-- The split increment of `w²` is `−2δ²`: subtracting `(c/2) w²` adds `c δ²`. -/
theorem splitIncrement_sub_quadratic (F : ℂ → ℂ) (c ξ δ : ℝ) :
    splitIncrement (fun w => F w - ((c / 2 : ℝ) : ℂ) * w ^ 2) ξ δ =
      splitIncrement F ξ δ + c * δ ^ 2 := by
  have h1 : ((((c / 2 : ℝ) : ℂ)) * ((ξ : ℂ) + δ * I) ^ 2).re = c / 2 * (ξ ^ 2 - δ ^ 2) := by
    rw [Complex.re_ofReal_mul]
    congr 1
    simp [pow_two, Complex.add_re, Complex.mul_re]
  have h2 : ((((c / 2 : ℝ) : ℂ)) * ((ξ : ℂ) + δ * -I) ^ 2).re = c / 2 * (ξ ^ 2 - δ ^ 2) := by
    rw [Complex.re_ofReal_mul]
    congr 1
    simp [pow_two, Complex.add_re, Complex.mul_re]
  have h3 : ((((c / 2 : ℝ) : ℂ)) * (ξ : ℂ) ^ 2).re = c / 2 * ξ ^ 2 := by
    rw [Complex.re_ofReal_mul]
    congr 1
    simp [pow_two]
  simp only [splitIncrement, Complex.sub_re, h1, h2, h3]
  ring

/-- The second derivative of `F − (c/2) w²` is `F'' − c`. -/
theorem deriv_deriv_sub_quadratic {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℝ) (w : ℂ) :
    deriv (deriv fun w => F w - ((c / 2 : ℝ) : ℂ) * w ^ 2) w = deriv (deriv F) w - c := by
  have h1 : deriv (fun w => F w - ((c / 2 : ℝ) : ℂ) * w ^ 2) = fun w => deriv F w - c * w :=
    funext fun w => by
      have hq : HasDerivAt (fun w : ℂ => ((c / 2 : ℝ) : ℂ) * w ^ 2)
          (((c / 2 : ℝ) : ℂ) * (2 * w)) w := by
        simpa using (hasDerivAt_pow 2 w).const_mul ((c / 2 : ℝ) : ℂ)
      have hsub : HasDerivAt (fun w => F w - ((c / 2 : ℝ) : ℂ) * w ^ 2)
          (deriv F w - ((c / 2 : ℝ) : ℂ) * (2 * w)) w := (hF w).hasDerivAt.sub hq
      rw [hsub.deriv]
      push_cast
      ring
  rw [h1]
  have h2 : HasDerivAt (fun w => deriv F w - (c : ℂ) * w) (deriv (deriv F) w - (c : ℂ) * 1) w :=
    (differentiable_deriv_of_entire hF w).hasDerivAt.sub ((hasDerivAt_id w).const_mul (c : ℂ))
  rw [h2.deriv, mul_one]

/-- **The second-order expansion.** For every `ε > 0` and all small `δ ≠ 0`,
`|Δ(ξ, δ) + δ² Re F''(ξ)| ≤ ε δ²`. -/
theorem abs_splitIncrement_add_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (ξ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,
      |splitIncrement F ξ δ + (deriv (deriv F) ξ).re * δ ^ 2| ≤ ε * δ ^ 2 := by
  have hGd : ∀ c : ℝ, Differentiable ℂ (fun w => F w - ((c / 2 : ℝ) : ℂ) * w ^ 2) := fun c =>
    hF.sub ((differentiable_const _).mul (differentiable_id.pow 2))
  -- tilting the curvature to `−ε` and to `ε` gives the two one-sided bounds
  have hplus := eventually_splitIncrement_pos_of_re_deriv2_neg
    (hGd ((deriv (deriv F) ξ).re + ε)) (ξ := ξ) (by
      rw [deriv_deriv_sub_quadratic hF, Complex.sub_re, Complex.ofReal_re]
      linarith only [hε])
  have hminus := eventually_splitIncrement_neg_of_re_deriv2_pos
    (hGd ((deriv (deriv F) ξ).re - ε)) (ξ := ξ) (by
      rw [deriv_deriv_sub_quadratic hF, Complex.sub_re, Complex.ofReal_re]
      linarith only [hε])
  filter_upwards [hplus, hminus] with δ h1 h2
  rw [splitIncrement_sub_quadratic] at h1 h2
  rw [abs_le]
  constructor
  · linarith only [h1, add_mul (deriv (deriv F) ξ).re ε (δ ^ 2)]
  · linarith only [h2, sub_mul (deriv (deriv F) ξ).re ε (δ ^ 2)]

/-! ### The gradient law -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A continuous linear functional on `ι → ℝ` in coordinates. -/
theorem clm_apply_eq_sum (φ' : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    φ' v = ∑ i, v i * φ' (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : (Pi.single i (v i) : ι → ℝ) = v i • Pi.single i (1 : ℝ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [hs, map_smul, smul_eq_mul]

/-- **The gradient law at one ordinate.** Let `φ` be differentiable at `S` with derivative
`φ'`. If splitting the double point `ξ` does not decrease `φ` of the statistics for all small
depths, then `Σ_i ∂_iφ(S) Re F_i''(ξ) ≤ 0`. -/
theorem sum_gradient_mul_re_deriv2_nonpos {F : ι → ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    {φ : (ι → ℝ) → ℝ} {S : ι → ℝ} {φ' : (ι → ℝ) →L[ℝ] ℝ} (hφ : HasFDerivAt φ φ' S) {ξ : ℝ}
    (h : ∀ᶠ δ : ℝ in 𝓝[>] 0, φ S ≤ φ (fun i => S i + splitIncrement (F i) ξ δ)) :
    ∑ i, φ' (Pi.single i 1) * (deriv (deriv (F i)) ξ).re ≤ 0 := by
  by_contra hcon
  obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, c = fun i => φ' (Pi.single i 1) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ι → ℝ, a = fun i => (deriv (deriv (F i)) ξ).re := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ∑ i, c i * a i := ⟨_, rfl⟩
  have hL : 0 < L := by
    rw [hLdef, hc, ha]
    exact lt_of_not_ge hcon
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i, |c i| := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ∑ i, |a i| + 1 := ⟨_, rfl⟩
  have haK : ∀ i, |a i| + 1 ≤ K := fun i => by
    have := Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    rw [hK]
    linarith only [this]
  have hK0 : 0 < K := lt_of_lt_of_le (by linarith only [abs_nonneg (0 : ℝ)]) (by
    rw [hK]
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (a i)
    linarith only [this] : (1 : ℝ) ≤ K)
  -- differentiability of `φ` at `S`, with the constant `L/(4K)`
  obtain ⟨η, hη, hηφ⟩ := Metric.eventually_nhds_iff.mp
    (hφ.isLittleO.def (show 0 < L / (4 * K) by positivity))
  -- the expansion of the increments, with the constants `ε` and `1`
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = L / (4 * (A + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    positivity
  have hAε : A * ε ≤ L / 4 := by
    have h1 : (A + 1) * ε = L / 4 := by
      rw [hε]
      field_simp
    nlinarith only [h1, hε0]
  have hexp : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i,
      |splitIncrement (F i) ξ δ + a i * δ ^ 2| ≤ min ε 1 * δ ^ 2 :=
    Filter.eventually_all.mpr fun i => by
      rw [ha]
      exact (abs_splitIncrement_add_le (hF i) ξ (lt_min hε0 one_pos)).filter_mono
        (nhdsGT_le_nhdsNE 0)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, K * δ ^ 2 < η := by
    have hcont : Tendsto (fun δ : ℝ => K * δ ^ 2) (𝓝 0) (𝓝 (K * 0 ^ 2)) :=
      (continuous_const.mul (continuous_id.pow 2)).tendsto 0
    rw [zero_pow two_ne_zero, mul_zero] at hcont
    exact (hcont.eventually (gt_mem_nhds hη)).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδφ, hδexp, hδsmall, hδpos⟩ :=
    (h.and (hexp.and (hsmall.and self_mem_nhdsWithin))).exists
  have hδ2 : 0 < δ ^ 2 := pow_pos hδpos 2
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ι → ℝ, Δ = fun i => splitIncrement (F i) ξ δ := ⟨_, rfl⟩
  have hexp' : ∀ i, |Δ i + a i * δ ^ 2| ≤ min ε 1 * δ ^ 2 := fun i => by
    rw [hΔ]
    exact hδexp i
  -- the increments are of size `K δ²`
  have hΔi : ∀ i, |Δ i| ≤ K * δ ^ 2 := fun i => by
    have h1 := (hexp' i).trans (mul_le_mul_of_nonneg_right (min_le_right ε 1) hδ2.le)
    have h2 := abs_sub (Δ i + a i * δ ^ 2) (a i * δ ^ 2)
    rw [add_sub_cancel_right, abs_mul, abs_of_pos hδ2] at h2
    have h3 := mul_le_mul_of_nonneg_right (haK i) hδ2.le
    linarith only [h1, h2, h3]
  have hnorm : ‖Δ‖ ≤ K * δ ^ 2 :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hK0.le hδ2.le)).mpr fun i => by
      rw [Real.norm_eq_abs]
      exact hΔi i
  have hsub : (fun i => S i + Δ i) - S = Δ := by
    funext i
    simp
  have hdist : dist (fun i => S i + Δ i) S < η := by
    rw [dist_eq_norm, hsub]
    exact lt_of_le_of_lt hnorm hδsmall
  -- the first-order remainder of `φ`
  have hrem := hηφ hdist
  rw [hsub, Real.norm_eq_abs] at hrem
  have hrem' : φ (fun i => S i + Δ i) - φ S - φ' Δ ≤ L / 4 * δ ^ 2 := by
    have h1 := (le_abs_self _).trans hrem
    have h2 : L / (4 * K) * ‖Δ‖ ≤ L / (4 * K) * (K * δ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    have h3 : L / (4 * K) * (K * δ ^ 2) = L / 4 * δ ^ 2 := by
      field_simp
    linarith only [h1, h2, h3]
  -- the linear term is `−L δ²` up to `A ε δ²`
  have hlin : φ' Δ = -(L * δ ^ 2) + ∑ i, c i * (Δ i + a i * δ ^ 2) := by
    rw [clm_apply_eq_sum, hLdef, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib, hc]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ i, c i * (Δ i + a i * δ ^ 2) ≤ A * ε * δ ^ 2 := by
    have h1 : ∑ i, c i * (Δ i + a i * δ ^ 2) ≤ ∑ i, |c i| * (ε * δ ^ 2) :=
      Finset.sum_le_sum fun i _ => by
        have h2 := (hexp' i).trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) hδ2.le)
        calc c i * (Δ i + a i * δ ^ 2) ≤ |c i * (Δ i + a i * δ ^ 2)| := le_abs_self _
          _ = |c i| * |Δ i + a i * δ ^ 2| := abs_mul _ _
          _ ≤ |c i| * (ε * δ ^ 2) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    rw [← Finset.sum_mul, ← hA] at h1
    linarith only [h1]
  have hAεδ : A * ε * δ ^ 2 ≤ L / 4 * δ ^ 2 := mul_le_mul_of_nonneg_right hAε hδ2.le
  have hΔeq : (fun i => S i + splitIncrement (F i) ξ δ) = fun i => S i + Δ i := by
    rw [hΔ]
  rw [hΔeq] at hδφ
  have hLδ : 0 < L * δ ^ 2 := mul_pos hL hδ2
  linarith only [hδφ, hrem', hlin, hR, hAεδ, hLδ]

omit [DecidableEq ι] in
/-- The second derivative of the gradient symbol. -/
theorem re_deriv2_gradientSymbol {F : ι → ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    (c : ι → ℝ) (x : ℂ) :
    (deriv (deriv fun w => ∑ i, (c i : ℂ) * F i w) x).re =
      ∑ i, c i * (deriv (deriv (F i)) x).re := by
  have h1 : deriv (fun w => ∑ i, (c i : ℂ) * F i w) = fun w => ∑ i, (c i : ℂ) * deriv (F i) w :=
    funext fun w => (HasDerivAt.fun_sum fun i _ =>
      ((hF i w).hasDerivAt.const_mul (c i : ℂ))).deriv
  have h2 : deriv (fun w => ∑ i, (c i : ℂ) * deriv (F i) w) x =
      ∑ i, (c i : ℂ) * deriv (deriv (F i)) x :=
    (HasDerivAt.fun_sum fun i _ =>
      ((differentiable_deriv_of_entire (hF i) x).hasDerivAt.const_mul (c i : ℂ))).deriv
  rw [h1, h2, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.re_ofReal_mul _ _

omit [DecidableEq ι] in
theorem differentiable_gradientSymbol {F : ι → ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    (c : ι → ℝ) : Differentiable ℂ fun w => ∑ i, (c i : ℂ) * F i w :=
  Differentiable.fun_sum fun i _ => (hF i).const_mul _

/-- **Monotone functions of linear statistics have a concave gradient symbol.** If at every
ordinate splitting does not decrease `φ` of the statistics for all small depths, the real part
of `Σ_i ∂_iφ(S) F_i` is concave on the line. -/
theorem concaveOn_re_gradientSymbol {F : ι → ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    {φ : (ι → ℝ) → ℝ} {S : ι → ℝ} {φ' : (ι → ℝ) →L[ℝ] ℝ} (hφ : HasFDerivAt φ φ' S)
    (h : ∀ ξ : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0,
      φ S ≤ φ (fun i => S i + splitIncrement (F i) ξ δ)) :
    ConcaveOn ℝ univ
      (fun ξ : ℝ => (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i ξ).re) := by
  have hG := differentiable_gradientSymbol hF fun i => φ' (Pi.single i 1)
  have h1 : ∀ x : ℝ, HasDerivAt
      (fun ξ : ℝ => (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i ξ).re)
      (deriv (fun w => ∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i w) x).re x := fun x =>
    (hG x).hasDerivAt.real_of_complex
  have h2 : ∀ x : ℝ, HasDerivAt
      (fun ξ : ℝ => (deriv (fun w => ∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i w) ξ).re)
      (deriv (deriv fun w => ∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i w) x).re x := fun x =>
    ((differentiable_deriv_of_entire hG) x).hasDerivAt.real_of_complex
  have hd1 : deriv (fun ξ : ℝ => (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i ξ).re) =
      fun ξ : ℝ => (deriv (fun w => ∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i w) ξ).re :=
    funext fun x => (h1 x).deriv
  refine concaveOn_univ_of_deriv2_nonpos (fun x => (h1 x).differentiableAt) ?_ ?_
  · rw [hd1]
    exact fun x => (h2 x).differentiableAt
  · intro x
    rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hd1, (h2 x).deriv,
      re_deriv2_gradientSymbol hF]
    exact sum_gradient_mul_re_deriv2_nonpos hF hφ (h x)

/-- **The gradient annihilates the symbols on the line.** If moreover the real part of the
gradient symbol is bounded below on the line and tends to zero at `+∞`, it vanishes there. -/
theorem re_gradientSymbol_eq_zero {F : ι → ℂ → ℂ} (hF : ∀ i, Differentiable ℂ (F i))
    {φ : (ι → ℝ) → ℝ} {S : ι → ℝ} {φ' : (ι → ℝ) →L[ℝ] ℝ} (hφ : HasFDerivAt φ φ' S)
    (h : ∀ ξ : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0,
      φ S ≤ φ (fun i => S i + splitIncrement (F i) ξ δ))
    {m : ℝ} (hm : ∀ x : ℝ, m ≤ (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i x).re)
    (hlim : Tendsto (fun x : ℝ => (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i x).re) atTop
      (𝓝 0)) (x : ℝ) :
    (∑ i, ((φ' (Pi.single i 1) : ℝ) : ℂ) * F i x).re = 0 :=
  eq_zero_of_concaveOn_of_tendsto (concaveOn_re_gradientSymbol hF hφ h) hm hlim x

end GaloisForLFunctions.FloorFreeArithmetic
