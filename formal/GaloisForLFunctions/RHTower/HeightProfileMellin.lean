import GaloisForLFunctions.RHTower.DeckScatteringUnitarity
import Mathlib.Analysis.MellinInversion

/-!
# Mellin transforms of height profiles

For a continuous profile `ψ` supported in `[a, b] ⊂ (0, ∞)` put
`ψ̂(s) = ∫_0^∞ ψ(y) y^{-s-1} dy` (`hMellin`, the Mellin transform at `-s`).

* `ψ̂` is entire (`HeightProfile.differentiable_hMellin`).
* For a `C²` profile two integrations by parts give `s(s-1) ψ̂(s) = ∫ ψ''(y) y^{1-s} dy`
  (`HeightProfile.hMellin_byParts`), hence `|ψ̂(σ+it)| ≤ C (1+t²)⁻¹` uniformly on every vertical
  strip (`HeightProfile.exists_bound_hMellin`).
* Mellin inversion on every vertical line: `ψ(y) = (2π)⁻¹ ∫ ψ̂(σ+it) y^{σ+it} dt`
  (`HeightProfile.hMellin_inversion`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-- The Mellin transform `f̂(s) = ∫_0^∞ f(y) y^{-s-1} dy`, i.e. `mellin f (-s)`. -/
def hMellin (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f (-s)

theorem hMellin_eq (f : ℝ → ℂ) (s : ℂ) :
    hMellin f s = ∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (-s - 1) * f y := by
  simp only [hMellin, mellin, smul_eq_mul]

/-- `conj f̂(s) = (conj f)^(conj s)`. -/
theorem conj_hMellin (f : ℝ → ℂ) (s : ℂ) :
    conj (hMellin f s) = hMellin (fun y => conj (f y)) (conj s) := by
  rw [hMellin_eq, hMellin_eq, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [map_mul, conj_ofReal_nonneg_cpow (le_of_lt hy)]
  congr 2
  simp

/-- `y^c ≤ y^a + y^b` for `a ≤ c ≤ b`. -/
theorem rpow_le_rpow_add_rpow {y a b c : ℝ} (hy : 0 < y) (hac : a ≤ c) (hcb : c ≤ b) :
    y ^ c ≤ y ^ a + y ^ b := by
  rcases le_or_gt 1 y with h1 | h1
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hcb).trans (le_add_of_nonneg_left (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy h1.le hac).trans
      (le_add_of_nonneg_right (by positivity))

namespace HeightProfile

variable (ψ : HeightProfile)

theorem eq_zero_of_not_mem_Icc {y : ℝ} (hy : y ∉ Icc ψ.lower ψ.upper) : ψ.toFun y = 0 := by
  rcases not_and_or.1 hy with h | h
  · exact ψ.eq_zero_of_lt y (not_le.1 h)
  · exact ψ.eq_zero_of_gt y (not_le.1 h)

theorem continuousOn_cpow_mul (u : ℂ) :
    ContinuousOn (fun y : ℝ => (y : ℂ) ^ u * ψ.toFun y) (Ioi 0) := fun y hy =>
  ((continuousAt_ofReal_cpow_const y u (Or.inr (ne_of_gt hy))).mul
    ψ.continuous.continuousAt).continuousWithinAt

theorem integrableOn_cpow_mul (u : ℂ) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ u * ψ.toFun y) (Ioi 0) := by
  have h1 : IntegrableOn (fun y : ℝ => (y : ℂ) ^ u * ψ.toFun y) (Icc ψ.lower ψ.upper) :=
    ((ψ.continuousOn_cpow_mul u).mono fun y hy => lt_of_lt_of_le ψ.lower_pos hy.1).integrableOn_compact
      isCompact_Icc
  exact h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun y hy => by
    rw [ψ.eq_zero_of_not_mem_Icc hy.2, mul_zero]

theorem mellinConvergent (s : ℂ) : MellinConvergent ψ.toFun s := by
  simpa only [MellinConvergent, smul_eq_mul] using ψ.integrableOn_cpow_mul (s - 1)

theorem hMellin_eq_Icc (s : ℂ) :
    hMellin ψ.toFun s = ∫ y in Icc ψ.lower ψ.upper, (y : ℂ) ^ (-s - 1) * ψ.toFun y := by
  rw [hMellin_eq]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun y hy => lt_of_lt_of_le ψ.lower_pos hy.1) fun y hy => by
      rw [ψ.eq_zero_of_not_mem_Icc hy.2, mul_zero]

/-- The transform over any interval `[α, β]` with `0 < α < a ≤ b ≤ β`. -/
theorem hMellin_eq_intervalIntegral {α β : ℝ} (hα : 0 < α) (hαl : α < ψ.lower)
    (hβ : ψ.upper ≤ β) (s : ℂ) :
    hMellin ψ.toFun s = ∫ y in α..β, (y : ℂ) ^ (-s - 1) * ψ.toFun y := by
  rw [hMellin_eq, intervalIntegral.integral_of_le (hαl.le.trans (ψ.lower_le_upper.trans hβ))]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun y hy => lt_trans hα hy.1) fun y hy => ?_
  rw [ψ.eq_zero_of_not_mem_Icc (fun h => hy.2 ⟨lt_of_lt_of_le hαl h.1, h.2.trans hβ⟩), mul_zero]

/-- **The transform is entire.** -/
theorem differentiable_hMellin : Differentiable ℂ (hMellin ψ.toFun) := by
  intro s
  have hloc : LocallyIntegrableOn ψ.toFun (Ioi 0) :=
    ψ.continuous.locallyIntegrable.locallyIntegrableOn _
  have htop : ψ.toFun =O[atTop] fun x : ℝ => x ^ (-((-s).re + 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop ψ.upper] with x hx
    rw [ψ.eq_zero_of_gt x hx, norm_zero, zero_mul]
  have hzero : ψ.toFun =O[𝓝[>] 0] fun x : ℝ => x ^ (-((-s).re - 1)) := by
    refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT ψ.lower_pos] with x hx
    rw [ψ.eq_zero_of_lt x hx.2, norm_zero, zero_mul]
  have h := mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hzero (by linarith)
  exact h.comp s differentiableAt_id.neg

/-- Order-zero bound on a vertical strip. -/
theorem exists_bound_hMellin_zero (σ₀ σ₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → ‖hMellin ψ.toFun s‖ ≤ C := by
  set g : ℝ → ℝ := fun y => ‖ψ.toFun y‖ * (y ^ (-σ₁ - 1) + y ^ (-σ₀ - 1))
  have hsub : Icc ψ.lower ψ.upper ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le ψ.lower_pos hy.1
  have hg : IntegrableOn g (Icc ψ.lower ψ.upper) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine (ψ.continuous.norm.continuousOn).mul ((ContinuousOn.add ?_ ?_))
    · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (hsub hy).ne')).continuousWithinAt
    · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (hsub hy).ne')).continuousWithinAt
  refine ⟨∫ y in Icc ψ.lower ψ.upper, g y, setIntegral_nonneg measurableSet_Icc fun y hy => ?_,
    fun s h0 h1 => ?_⟩
  · have h : 0 < y := hsub hy
    exact mul_nonneg (norm_nonneg _) (add_nonneg (Real.rpow_nonneg h.le _) (Real.rpow_nonneg h.le _))
  rw [ψ.hMellin_eq_Icc]
  refine norm_integral_le_of_norm_le hg (ae_restrict_of_forall_mem measurableSet_Icc fun y hy => ?_)
  have hy0 : 0 < y := hsub hy
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine rpow_le_rpow_add_rpow hy0 ?_ ?_ <;> simp <;> linarith

/-- **Two integrations by parts**: `s(s-1) ψ̂(s) = ∫ ψ''(y) y^{1-s} dy`. -/
theorem hMellin_byParts (hψ : ContDiff ℝ 2 ψ.toFun) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * (s - 1) * hMellin ψ.toFun s =
      ∫ y in (ψ.lower / 2)..(ψ.upper + 1), iteratedDeriv 2 ψ.toFun y * (y : ℂ) ^ (1 - s) := by
  set α := ψ.lower / 2
  set β := ψ.upper + 1
  have hα : 0 < α := half_pos ψ.lower_pos
  have hαl : α < ψ.lower := half_lt_self ψ.lower_pos
  have hβ : ψ.upper < β := lt_add_one _
  have hαβ : α ≤ β := by linarith [ψ.lower_le_upper]
  have hpos : ∀ y ∈ uIcc α β, 0 < y := fun y hy => by
    rw [uIcc_of_le hαβ] at hy; exact lt_of_lt_of_le hα hy.1
  have hd : Differentiable ℝ ψ.toFun := hψ.differentiable (by norm_num)
  have hd' : ContDiff ℝ 1 (deriv ψ.toFun) := hψ.deriv' (n := 1)
  have hdd : Differentiable ℝ (deriv ψ.toFun) := hd'.differentiable (by norm_num)
  have hzα : ψ.toFun =ᶠ[𝓝 α] fun _ => 0 :=
    eventually_of_mem (Iio_mem_nhds hαl) fun y hy => ψ.eq_zero_of_lt y hy
  have hzβ : ψ.toFun =ᶠ[𝓝 β] fun _ => 0 :=
    eventually_of_mem (Ioi_mem_nhds hβ) fun y hy => ψ.eq_zero_of_gt y hy
  have hψα : ψ.toFun α = 0 := hzα.eq_of_nhds
  have hψβ : ψ.toFun β = 0 := hzβ.eq_of_nhds
  have hψ'α : deriv ψ.toFun α = 0 := by rw [hzα.deriv_eq]; simp
  have hψ'β : deriv ψ.toFun β = 0 := by rw [hzβ.deriv_eq]; simp
  have hcpow : ∀ r : ℂ, ContinuousOn (fun y : ℝ => (y : ℂ) ^ r) (uIcc α β) := fun r y hy =>
    (continuousAt_ofReal_cpow_const y r (Or.inr (hpos y hy).ne')).continuousWithinAt
  -- first integration by parts
  have hv1 : ∀ y ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s) / (-s)) ((y : ℂ) ^ (-s - 1)) y := by
    intro y hy
    have h := hasDerivAt_ofReal_cpow_const' (hpos y hy).ne' (r := -s - 1)
      (fun h => hs0 (by linear_combination -h))
    rwa [sub_add_cancel] at h
  have hstep1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (u := ψ.toFun) (v := fun y : ℝ => (y : ℂ) ^ (-s) / (-s)) (u' := deriv ψ.toFun)
    (v' := fun y : ℝ => (y : ℂ) ^ (-s - 1)) (fun y _ => (hd y).hasDerivAt) hv1
    (hd'.continuous.intervalIntegrable _ _) ((hcpow _).intervalIntegrable)
  rw [hψα, hψβ, zero_mul, zero_mul, sub_zero, zero_sub] at hstep1
  -- second integration by parts
  have hv2 : ∀ y ∈ uIcc α β, HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s)) ((y : ℂ) ^ (-s)) y := by
    intro y hy
    have h := hasDerivAt_ofReal_cpow_const' (hpos y hy).ne' (r := -s)
      (fun h => hs1 (by linear_combination -h))
    rwa [neg_add_eq_sub] at h
  have hψ2 : Continuous (iteratedDeriv 2 ψ.toFun) := hψ.continuous_iteratedDeriv 2 le_rfl
  have hstep2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
    (u := deriv ψ.toFun) (v := fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s))
    (u' := iteratedDeriv 2 ψ.toFun) (v' := fun y : ℝ => (y : ℂ) ^ (-s))
    (fun y _ => by
      rw [show iteratedDeriv 2 ψ.toFun = deriv (deriv ψ.toFun) by
        rw [iteratedDeriv_succ, iteratedDeriv_one]]
      exact (hdd y).hasDerivAt) hv2
    (hψ2.intervalIntegrable _ _) ((hcpow _).intervalIntegrable)
  rw [hψ'α, hψ'β, zero_mul, zero_mul, sub_zero, zero_sub] at hstep2
  have hsm : (-s : ℂ) ≠ 0 := neg_ne_zero.2 hs0
  have hs1' : (1 - s : ℂ) ≠ 0 := sub_ne_zero.2 (Ne.symm hs1)
  have hA : (∫ y in α..β, deriv ψ.toFun y * ((y : ℂ) ^ (-s) / -s)) =
      (∫ y in α..β, deriv ψ.toFun y * (y : ℂ) ^ (-s)) / (-s) := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have hB : (∫ y in α..β, iteratedDeriv 2 ψ.toFun y * ((y : ℂ) ^ (1 - s) / (1 - s))) =
      (∫ y in α..β, iteratedDeriv 2 ψ.toFun y * (y : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun y _ => by ring
  have hM : hMellin ψ.toFun s = ∫ y in α..β, ψ.toFun y * (y : ℂ) ^ (-s - 1) := by
    rw [ψ.hMellin_eq_intervalIntegral hα hαl hβ.le]
    exact intervalIntegral.integral_congr fun y _ => by ring
  rw [hM, hstep1, hA, hstep2, hB]
  field_simp
  ring

/-- Quadratic bound on a vertical strip. -/
theorem exists_bound_sq_im_hMellin (hψ : ContDiff ℝ 2 ψ.toFun) (σ₀ σ₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ → s.im ^ 2 * ‖hMellin ψ.toFun s‖ ≤ C := by
  set α := ψ.lower / 2
  set β := ψ.upper + 1
  have hα : 0 < α := half_pos ψ.lower_pos
  have hαl : α < ψ.lower := half_lt_self ψ.lower_pos
  have hβ : ψ.upper < β := lt_add_one _
  have hαβ : α ≤ β := by linarith [ψ.lower_le_upper]
  have hsub : Icc α β ⊆ Ioi 0 := fun y hy => lt_of_lt_of_le hα hy.1
  set g : ℝ → ℝ := fun y => ‖iteratedDeriv 2 ψ.toFun y‖ * (y ^ (1 - σ₁) + y ^ (1 - σ₀))
  have hgc : ContinuousOn g (Icc α β) := by
    refine ((hψ.continuous_iteratedDeriv 2 le_rfl).norm.continuousOn).mul ((ContinuousOn.add ?_ ?_))
    · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (hsub hy).ne')).continuousWithinAt
    · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (hsub hy).ne')).continuousWithinAt
  have hg : IntervalIntegrable g volume α β := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hαβ]
    exact hgc.integrableOn_compact isCompact_Icc
  have hg0 : ∀ y ∈ Icc α β, 0 ≤ g y := fun y hy => by
    have h : 0 < y := hsub hy
    exact mul_nonneg (norm_nonneg _) (add_nonneg (Real.rpow_nonneg h.le _) (Real.rpow_nonneg h.le _))
  refine ⟨∫ y in α..β, g y, intervalIntegral.integral_nonneg hαβ hg0, fun s h0 h1 => ?_⟩
  rcases eq_or_ne s.im 0 with ht | ht
  · rw [ht]; simpa using intervalIntegral.integral_nonneg hαβ hg0
  have hs0 : s ≠ 0 := fun h => ht (by rw [h]; simp)
  have hs1 : s ≠ 1 := fun h => ht (by rw [h]; simp)
  have hbp := ψ.hMellin_byParts hψ hs0 hs1
  have hn1 : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have hn2 : |s.im| ≤ ‖s - 1‖ := by simpa using abs_im_le_norm (s - 1)
  have hsq : s.im ^ 2 ≤ ‖s * (s - 1)‖ := by
    rw [norm_mul, ← sq_abs]
    exact pow_two (|s.im|) ▸ mul_le_mul hn1 hn2 (abs_nonneg _) (norm_nonneg _)
  calc s.im ^ 2 * ‖hMellin ψ.toFun s‖ ≤ ‖s * (s - 1)‖ * ‖hMellin ψ.toFun s‖ :=
        mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
    _ = ‖∫ y in α..β, iteratedDeriv 2 ψ.toFun y * (y : ℂ) ^ (1 - s)‖ := by rw [← norm_mul, hbp]
    _ ≤ ∫ y in α..β, g y := by
        refine intervalIntegral.norm_integral_le_of_norm_le hαβ
          (Eventually.of_forall fun y hy => ?_) hg
        have hy0 : 0 < y := lt_of_lt_of_le hα (le_of_lt hy.1)
        rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hy0]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine rpow_le_rpow_add_rpow hy0 ?_ ?_ <;> simp <;> linarith

/-- **Uniform decay on vertical strips**: `‖ψ̂(s)‖ ≤ C (1 + (Im s)²)⁻¹` for `σ₀ ≤ Re s ≤ σ₁`. -/
theorem exists_bound_hMellin (hψ : ContDiff ℝ 2 ψ.toFun) (σ₀ σ₁ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ σ₁ →
      ‖hMellin ψ.toFun s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, h₀⟩ := ψ.exists_bound_hMellin_zero σ₀ σ₁
  obtain ⟨C₂, hC₂, h₂⟩ := ψ.exists_bound_sq_im_hMellin hψ σ₀ σ₁
  refine ⟨C₀ + C₂, add_nonneg hC₀ hC₂, fun s hs0 hs1 => ?_⟩
  have hpos : 0 < 1 + s.im ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith [h₀ s hs0 hs1, h₂ s hs0 hs1]

theorem continuous_hMellin_line (σ : ℝ) :
    Continuous fun t : ℝ => hMellin ψ.toFun ((σ : ℂ) + t * I) :=
  ψ.differentiable_hMellin.continuous.comp (by fun_prop)

theorem integrable_hMellin_line (hψ : ContDiff ℝ 2 ψ.toFun) (σ : ℝ) :
    Integrable fun t : ℝ => hMellin ψ.toFun ((σ : ℂ) + t * I) := by
  obtain ⟨C, _, hb⟩ := ψ.exists_bound_hMellin hψ σ σ
  refine (integrable_inv_one_add_sq.const_mul C).mono' (ψ.continuous_hMellin_line σ).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simpa using hb ((σ : ℂ) + t * I) (by simp) (by simp)

/-- **Mellin inversion** on the line `Re s = σ`. -/
theorem hMellin_inversion (hψ : ContDiff ℝ 2 ψ.toFun) (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ψ.toFun y = ((2 * Real.pi)⁻¹ : ℝ) •
      ∫ t : ℝ, hMellin ψ.toFun ((σ : ℂ) + t * I) * (y : ℂ) ^ ((σ : ℂ) + t * I) := by
  have hvert : VerticalIntegrable (mellin ψ.toFun) (-σ) := by
    have h := (ψ.integrable_hMellin_line hψ σ).comp_neg
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [hMellin]
    congr 1
    push_cast
    ring
  have h := mellinInv_mellin_eq (-σ) ψ.toFun hy (ψ.mellinConvergent _) hvert ψ.continuous.continuousAt
  rw [← h, mellinInv, one_div]
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [hMellin, smul_eq_mul]
  push_cast
  rw [mul_comm]
  congr 2 <;> ring

/-- Pairing with a power against `y⁻² dy`: `∫_0^∞ y⁻² ψ(y) y^u dy = ψ̂(1 - u)`. -/
theorem integral_inv_sq_smul_mul_cpow (u : ℂ) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • (ψ.toFun y * (y : ℂ) ^ u) = hMellin ψ.toFun (1 - u) := by
  rw [hMellin_eq]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hy)
  have hpow : (y : ℂ) ^ (-(1 - u) - 1) = (y : ℂ) ^ u / (y : ℂ) ^ 2 := by
    rw [show -(1 - u) - 1 = u - (2 : ℕ) by push_cast; ring, cpow_sub _ _ hy0, cpow_natCast]
  rw [hpow, real_smul]
  push_cast
  field_simp

theorem integrableOn_inv_sq_smul_mul_cpow (u : ℂ) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ • (ψ.toFun y * (y : ℂ) ^ u)) (Ioi 0) := by
  refine (ψ.integrableOn_cpow_mul (u - 2)).congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hy)
  simp only
  rw [show u - 2 = u - (2 : ℕ) by push_cast; ring, cpow_sub _ _ hy0, cpow_natCast, real_smul]
  push_cast
  field_simp

/-- The complex conjugate profile. -/
def conjProfile : HeightProfile where
  toFun y := conj (ψ.toFun y)
  lower := ψ.lower
  upper := ψ.upper
  lower_pos := ψ.lower_pos
  lower_le_upper := ψ.lower_le_upper
  continuous := continuous_conj.comp ψ.continuous
  eq_zero_of_lt y hy := by rw [ψ.eq_zero_of_lt y hy, map_zero]
  eq_zero_of_gt y hy := by rw [ψ.eq_zero_of_gt y hy, map_zero]

theorem conjProfile_apply (y : ℝ) : ψ.conjProfile.toFun y = conj (ψ.toFun y) := rfl

theorem contDiff_conjProfile (hψ : ContDiff ℝ 2 ψ.toFun) : ContDiff ℝ 2 ψ.conjProfile.toFun :=
  Complex.conjCLE.contDiff.comp hψ

theorem hMellin_conjProfile (s : ℂ) :
    hMellin ψ.conjProfile.toFun s = conj (hMellin ψ.toFun (conj s)) := by
  rw [conj_hMellin, Complex.conj_conj]
  rfl

end HeightProfile

end

end GaloisForLFunctions.RHTower.DeckPointPair
