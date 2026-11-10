import GaloisForLFunctions.InfiniteRankPurityTheory.EliminationNeedsOnlyAnAttainedTop

/-!
# A family sees its mean and its members of positive mass

In finite rank a family with big monodromy proves the purity of each member from bounds for the
moments of the traces over the family: each member enters every even moment with positive mass, and
the growth of the base is amortized over the tensor powers. This module gives the infinite-rank
form and decides what the same moments say about the fixed part.

A family over a probability space `(Ω, μ)` has level sums `S_ω(ν) = F(ν) + V_ω(ν)`, where `F` is
the level sum of the fixed part, a summable tower, and the variable part has mean zero.

* `norm_le_of_thick_levelSums_le`, `norm_le_of_amortized_levelSums`: elimination at any radius,
  and amortization: if `‖S(ν)‖^k ≤ C_k (B R^k)^ν` on a thick set of levels for every `k ≥ 1`, a
  tower with an attained top lies in the closed disc of radius `R`; the factor `B^{1/k}` tends to
  one. For finitely many modes of weight one on all levels this is
  `ArithmeticKunnethTheory.WeightFamilies.tensor_moment_bound_iff`.
* `member_norm_le_of_family_moments`: a member of positive mass whose family satisfies
  `∫ ‖S_ω(ν)‖^k dμ ≤ C_k (B R^k)^ν` on a thick set of levels lies in the closed disc of radius `R`.
* `integral_fixedPart_add`, `norm_fixedPart_le_integral`: the fixed part is the mean of the family,
  so it enters the first moment with mass one.
* `integral_norm_sq_fixedPart_add`: `∫ ‖S_ω‖² dμ = ‖F‖² + ∫ ‖V_ω‖² dμ`: the fixed part is the excess
  of the second moment over the variance.
* `fixedPart_norm_le_one_of_mean_bounded`, `fixedPart_norm_le_one_of_excess_bounded`: a bound for
  the first moment of the full traces, or for the excess of the second moment over the variance, on
  a thick set of levels puts a fixed part with an attained top in the closed unit disc.

The price is visible in the statements: the moments must be those of the full traces. Moments of
the variable part alone do not contain `F`.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open GaloisForLFunctions.InfiniteRankWeilTheory (Thick)

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-! ### Elimination at any radius and amortization -/

/-- **Elimination at any radius.** Level sums `O(R^ν)` on a thick set and an attained top put the
tower in the closed disc of radius `R`. -/
theorem norm_le_of_thick_levelSums_le {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re)
    {G : Set ℕ} (hG : Thick G) {C R : ℝ} (hR : 0 < R)
    (hb : ∀ ν ∈ G, ‖towerSum c z ν‖ ≤ C * R ^ ν) : ‖z i₀‖ ≤ R := by
  have hnorm : ∀ i, ‖z i / (R : ℂ)‖ = ‖z i‖ / R := fun i => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hmax' : ∀ i, ‖z i / (R : ℂ)‖ ≤ ‖z i₀ / (R : ℂ)‖ := fun i => by
    rw [hnorm, hnorm]
    exact div_le_div_of_nonneg_right (hmax i) hR.le
  have hb' : ∀ ν ∈ G, ‖∑' i, c i * (z i / (R : ℂ)) ^ ν‖ ≤ C := by
    intro ν hν
    have hrel : (∑' i, c i * (z i / (R : ℂ)) ^ ν) = towerSum c z ν / (R : ℂ) ^ ν := by
      rw [towerSum, ← tsum_div_const]
      refine tsum_congr fun i => ?_
      rw [div_pow, mul_div_assoc]
    rw [hrel, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le,
      div_le_iff₀ (pow_pos hR ν)]
    exact hb ν hν
  have h1 := norm_le_one_of_thick_bounded_levelSums hc hre hmax' hpos hG hb'
  rw [hnorm, div_le_one hR] at h1
  exact h1

/-- **Amortization.** If for every `k ≥ 1` the `k`-th powers of the level sums are
`O((B R^k)^ν)` on a thick set of levels, a tower with an attained top lies in the closed disc of
radius `R`: the modes are at most `B^{1/k} R` for every `k`. -/
theorem norm_le_of_amortized_levelSums {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re)
    {G : Set ℕ} (hG : Thick G) {R B : ℝ} (hR : 0 < R) (hB : 1 ≤ B)
    (h : ∀ k : ℕ, 0 < k → ∃ C : ℝ, ∀ ν ∈ G, ‖towerSum c z ν‖ ^ k ≤ C * (B * R ^ k) ^ ν) :
    ‖z i₀‖ ≤ R := by
  have hB0 : 0 < B := by linarith
  have hk : ∀ k : ℕ, 0 < k → ‖z i₀‖ ≤ B ^ ((k : ℝ)⁻¹) * R := by
    intro k hk0
    obtain ⟨C, hC⟩ := h k hk0
    have hkne : k ≠ 0 := hk0.ne'
    have hρ0 : 0 < B ^ ((k : ℝ)⁻¹) * R := mul_pos (Real.rpow_pos_of_pos hB0 _) hR
    have hρk : (B ^ ((k : ℝ)⁻¹) * R) ^ k = B * R ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (B ^ ((k : ℝ)⁻¹)) k, ← Real.rpow_mul hB0.le,
        inv_mul_cancel₀ (by exact_mod_cast hkne), Real.rpow_one]
    have hBR : ∀ ν : ℕ, 0 ≤ (B * R ^ k) ^ ν := fun ν =>
      pow_nonneg (mul_nonneg hB0.le (pow_nonneg hR.le k)) ν
    refine norm_le_of_thick_levelSums_le hc hre hmax hpos hG (C := max C 1) hρ0 fun ν hν => ?_
    have hM1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    have hM0 : (0 : ℝ) ≤ max C 1 := by linarith
    have e : (max C 1 * (B ^ ((k : ℝ)⁻¹) * R) ^ ν) ^ k = max C 1 ^ k * (B * R ^ k) ^ ν := by
      rw [mul_pow, ← pow_mul, mul_comm ν k, pow_mul, hρk]
    refine le_of_pow_le_pow_left₀ hkne (mul_nonneg hM0 (pow_nonneg hρ0.le ν)) ?_
    calc ‖towerSum c z ν‖ ^ k ≤ C * (B * R ^ k) ^ ν := hC ν hν
      _ ≤ max C 1 * (B * R ^ k) ^ ν := mul_le_mul_of_nonneg_right (le_max_left _ _) (hBR ν)
      _ ≤ max C 1 ^ k * (B * R ^ k) ^ ν :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 hkne) (hBR ν)
      _ = (max C 1 * (B ^ ((k : ℝ)⁻¹) * R) ^ ν) ^ k := e.symm
  have htend : Tendsto (fun k : ℕ => B ^ ((k : ℝ)⁻¹) * R) atTop (𝓝 R) := by
    have h1 : Tendsto (fun k : ℕ => B ^ ((k : ℝ)⁻¹)) atTop (𝓝 (B ^ (0 : ℝ))) :=
      ((Real.continuousAt_const_rpow hB0.ne').tendsto).comp tendsto_inv_atTop_nhds_zero_nat
    rw [Real.rpow_zero] at h1
    simpa using h1.mul_const R
  exact ge_of_tendsto htend (eventually_atTop.mpr ⟨1, fun k hk1 => hk k hk1⟩)

/-! ### Members of positive mass -/

theorem measureReal_singleton_mul_le_integral [MeasurableSingletonClass Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Integrable f μ) (h0 : ∀ ω, 0 ≤ f ω) (ω₀ : Ω) :
    μ.real {ω₀} * f ω₀ ≤ ∫ ω, f ω ∂μ := by
  have h1 : ∫ ω in {ω₀}, f ω ∂μ = μ.real {ω₀} * f ω₀ := by
    rw [integral_singleton, smul_eq_mul]
  rw [← h1]
  exact setIntegral_le_integral hf (Eventually.of_forall h0)

/-- **A member of positive mass is seen.** If the `k`-th absolute moments of the level sums over
the family are `O((B R^k)^ν)` on a thick set of levels for every `k ≥ 1`, a member of positive mass
whose tower has an attained top lies in the closed disc of radius `R`. -/
theorem member_norm_le_of_family_moments [MeasurableSingletonClass Ω] {μ : Measure Ω} {ω₀ : Ω}
    (hω₀ : 0 < μ.real {ω₀}) {S : Ω → ℕ → ℂ} {c z : ι → ℂ}
    (hS : ∀ ν, S ω₀ ν = towerSum c z ν) (hc : Summable fun i => ‖c i‖)
    (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι} (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re)
    {G : Set ℕ} (hG : Thick G) {R B : ℝ} (hR : 0 < R) (hB : 1 ≤ B)
    (hint : ∀ (k ν : ℕ), Integrable (fun ω => ‖S ω ν‖ ^ k) μ)
    (h : ∀ k : ℕ, 0 < k → ∃ C : ℝ, ∀ ν ∈ G, ∫ ω, ‖S ω ν‖ ^ k ∂μ ≤ C * (B * R ^ k) ^ ν) :
    ‖z i₀‖ ≤ R := by
  refine norm_le_of_amortized_levelSums hc hre hmax hpos hG hR hB fun k hk => ?_
  obtain ⟨C, hC⟩ := h k hk
  refine ⟨C / μ.real {ω₀}, fun ν hν => ?_⟩
  have h1 := measureReal_singleton_mul_le_integral (hint k ν)
    (fun ω => pow_nonneg (norm_nonneg _) k) ω₀
  rw [hS ν] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hω₀, mul_comm (‖towerSum c z ν‖ ^ k)]
  exact h1.trans (hC ν hν)

/-! ### The fixed part -/

/-- **The fixed part is the mean of the family.** -/
theorem integral_fixedPart_add {μ : Measure Ω} [IsProbabilityMeasure μ] (F : ℂ) {V : Ω → ℂ}
    (hV : Integrable V μ) (h0 : ∫ ω, V ω ∂μ = 0) : ∫ ω, (F + V ω) ∂μ = F := by
  rw [integral_add (integrable_const F) hV, h0, add_zero, integral_const]
  simp

/-- The fixed part enters the first moment with mass one. -/
theorem norm_fixedPart_le_integral {μ : Measure Ω} [IsProbabilityMeasure μ] (F : ℂ)
    {V : Ω → ℂ} (hV : Integrable V μ) (h0 : ∫ ω, V ω ∂μ = 0) :
    ‖F‖ ≤ ∫ ω, ‖F + V ω‖ ∂μ := by
  have h := norm_integral_le_integral_norm (μ := μ) fun ω => F + V ω
  rwa [integral_fixedPart_add F hV h0] at h

/-- **The fixed part is the excess of the second moment over the variance.** -/
theorem integral_norm_sq_fixedPart_add {μ : Measure Ω} [IsProbabilityMeasure μ] (F : ℂ)
    {V : Ω → ℂ} (hV : Integrable V μ) (hV2 : Integrable (fun ω => ‖V ω‖ ^ 2) μ)
    (h0 : ∫ ω, V ω ∂μ = 0) :
    ∫ ω, ‖F + V ω‖ ^ 2 ∂μ = ‖F‖ ^ 2 + ∫ ω, ‖V ω‖ ^ 2 ∂μ := by
  have hVre : Integrable (fun ω => (V ω).re) μ := by
    simpa using Complex.reCLM.integrable_comp hV
  have hVim : Integrable (fun ω => (V ω).im) μ := by
    simpa using Complex.imCLM.integrable_comp hV
  have hre : ∫ ω, (V ω).re ∂μ = 0 := by
    have h := Complex.reCLM.integral_comp_comm hV
    simpa [h0] using h
  have him : ∫ ω, (V ω).im ∂μ = 0 := by
    have h := Complex.imCLM.integral_comp_comm hV
    simpa [h0] using h
  have hpt : ∀ ω, ‖F + V ω‖ ^ 2 =
      ‖F‖ ^ 2 + (2 * F.re * (V ω).re + 2 * F.im * (V ω).im) + ‖V ω‖ ^ 2 := by
    intro ω
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im]
    ring
  have hlin : Integrable (fun ω => 2 * F.re * (V ω).re + 2 * F.im * (V ω).im) μ :=
    (hVre.const_mul _).add (hVim.const_mul _)
  have e1 : ∫ ω, (‖F‖ ^ 2 + (2 * F.re * (V ω).re + 2 * F.im * (V ω).im) + ‖V ω‖ ^ 2) ∂μ =
      (∫ ω, (‖F‖ ^ 2 + (2 * F.re * (V ω).re + 2 * F.im * (V ω).im)) ∂μ) +
        ∫ ω, ‖V ω‖ ^ 2 ∂μ := integral_add ((integrable_const _).add hlin) hV2
  have e2 : ∫ ω, (‖F‖ ^ 2 + (2 * F.re * (V ω).re + 2 * F.im * (V ω).im)) ∂μ =
      (∫ _ω, ‖F‖ ^ 2 ∂μ) + ∫ ω, (2 * F.re * (V ω).re + 2 * F.im * (V ω).im) ∂μ :=
    integral_add (integrable_const _) hlin
  have e3 : ∫ ω, (2 * F.re * (V ω).re + 2 * F.im * (V ω).im) ∂μ =
      (∫ ω, 2 * F.re * (V ω).re ∂μ) + ∫ ω, 2 * F.im * (V ω).im ∂μ :=
    integral_add (hVre.const_mul _) (hVim.const_mul _)
  simp_rw [hpt]
  rw [e1, e2, e3, integral_const_mul, integral_const_mul, hre, him, integral_const]
  simp

/-- **Law to point for the fixed part.** A bound for the first moment of the full level sums on a
thick set of levels puts a fixed part with an attained top in the closed unit disc. -/
theorem fixedPart_norm_le_one_of_mean_bounded {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι}
    (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re) {G : Set ℕ} (hG : Thick G)
    {V : ℕ → Ω → ℂ} (hV : ∀ ν ∈ G, Integrable (V ν) μ) (hV0 : ∀ ν ∈ G, ∫ ω, V ν ω ∂μ = 0)
    {C : ℝ} (hb : ∀ ν ∈ G, ∫ ω, ‖towerSum c z ν + V ν ω‖ ∂μ ≤ C) : ‖z i₀‖ ≤ 1 :=
  norm_le_one_of_thick_bounded_levelSums hc hre hmax hpos hG fun ν hν =>
    (norm_fixedPart_le_integral (towerSum c z ν) (hV ν hν) (hV0 ν hν)).trans (hb ν hν)

/-- The same from the second moment: a bounded excess over the variance on a thick set of
levels. -/
theorem fixedPart_norm_le_one_of_excess_bounded {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) (hre : ∀ i, 0 ≤ (c i).re) {i₀ : ι}
    (hmax : ∀ i, ‖z i‖ ≤ ‖z i₀‖) (hpos : 0 < (c i₀).re) {G : Set ℕ} (hG : Thick G)
    {V : ℕ → Ω → ℂ} (hV : ∀ ν ∈ G, Integrable (V ν) μ)
    (hV2 : ∀ ν ∈ G, Integrable (fun ω => ‖V ν ω‖ ^ 2) μ)
    (hV0 : ∀ ν ∈ G, ∫ ω, V ν ω ∂μ = 0) {C : ℝ}
    (hb : ∀ ν ∈ G, ∫ ω, ‖towerSum c z ν + V ν ω‖ ^ 2 ∂μ - ∫ ω, ‖V ν ω‖ ^ 2 ∂μ ≤ C) :
    ‖z i₀‖ ≤ 1 := by
  refine norm_le_one_of_thick_bounded_levelSums hc hre hmax hpos hG (C := Real.sqrt C)
    fun ν hν => ?_
  have h := hb ν hν
  rw [integral_norm_sq_fixedPart_add (towerSum c z ν) (hV ν hν) (hV2 ν hν) (hV0 ν hν),
    add_sub_cancel_right] at h
  have h2 := Real.abs_le_sqrt h
  rwa [abs_of_nonneg (norm_nonneg _)] at h2

end GaloisForLFunctions.InfiniteRankPurityTheory
