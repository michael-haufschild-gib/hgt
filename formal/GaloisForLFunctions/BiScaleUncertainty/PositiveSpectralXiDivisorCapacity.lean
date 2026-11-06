import GaloisForLFunctions.RHTower.ThetaTailSimpleCriticalThreshold
import GaloisForLFunctions.HTGeometry.RealNonnegativeZeroEvenOrder
import GaloisForLFunctions.RHTower.StripFactorXiDivisibleBlindTest

/-!
# Positive spectral densities double the real Xi divisor capacity

A nonzero entire function, even and nonnegative on the real axis, pays at least two
zeros at each simple critical Xi ordinate. Its disc divisor mass is at least
`4 N₀,s(T)`. An even source with such a transform cannot decay as
`exp(−a exp(b|x|))` for `b > 3/2`: its angular growth capacity is too small.
For strip-holomorphic Xi factors, this excludes such tails for the literal autocorrelation;
only pointwise Xi division and nonvanishing at the origin are needed.
-/

open MeasureTheory Set Filter Topology Complex Metric

namespace GaloisForLFunctions.BiScaleUncertainty

open _root_.RHTower

noncomputable section

/-- Nonnegativity doubles the divisor mass forced by the simple critical Xi zeros. -/
theorem four_mul_simpleCriticalCount_le_divisor_of_nonnegative {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hH0 : ∃ z, H z ≠ 0)
    (hreal : ∀ t : ℝ, (H t).im = 0) (hpos : ∀ t : ℝ, 0 ≤ (H t).re)
    (heven : ∀ z, H (-z) = H z)
    (hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → H γ = 0)
    (c : ℂ) {T r : ℝ} (hTr : T + ‖c‖ ≤ r) :
    4 * (xiSimpleCriticalZeroCount T : ℝ) ≤
      ∑ᶠ z, (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := by
  set P := (stripFinsetPos T).filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)
  have hP : ∀ ρ ∈ P, 0 < ρ.im ∧ ρ.im ≤ T ∧ ρ = 1 / 2 + (ρ.im : ℂ) * I ∧ xi ρ = 0 ∧
      (analyticOrderAt xi ρ).toNat = 1 := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_stripFinsetPos] at hρ
    obtain ⟨⟨_, _, him, hT, hxi⟩, hre, hsimple⟩ := hρ
    refine ⟨him, hT, ?_, hxi, hsimple⟩
    apply Complex.ext <;> simp [hre]
  set S₁ := P.image fun ρ => ((ρ.im : ℝ) : ℂ)
  set S₂ := P.image fun ρ => ((-ρ.im : ℝ) : ℂ)
  have hinj : Set.InjOn (fun ρ : ℂ => ρ.im) P := by
    intro ρ hρ σ hσ h
    rw [(hP ρ hρ).2.2.1, (hP σ hσ).2.2.1]
    simp only at h
    rw [h]
  have hc1 : S₁.card = P.card := Finset.card_image_of_injOn fun ρ hρ σ hσ h => by
    have := Complex.ofReal_injective h
    exact hinj hρ hσ this
  have hc2 : S₂.card = P.card := Finset.card_image_of_injOn fun ρ hρ σ hσ h => by
    have := Complex.ofReal_injective h
    exact hinj hρ hσ (by simpa using this)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨σ, hσ, h⟩ := Finset.mem_image.mp hz2
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    linarith [(hP ρ hρ).1, (hP σ hσ).1]
  set S := S₁ ∪ S₂
  have hcard : (S.card : ℝ) = 2 * (xiSimpleCriticalZeroCount T : ℝ) := by
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2, xiSimpleCriticalZeroCount]
    push_cast; ring
  have hHA : AnalyticOnNhd ℂ H (closedBall c r) := fun z _ => hH.analyticAt z
  have hzero : ∀ z ∈ S, H z = 0 ∧ z ∈ closedBall c r := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP ρ hρ
      refine ⟨hvan ρ.im h1 (by rw [← h3]; exact h4) (by rw [← h3]; exact h5), ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      calc ‖((ρ.im : ℝ) : ℂ) - c‖ ≤ ‖((ρ.im : ℝ) : ℂ)‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ r := by rw [Complex.norm_real, Real.norm_of_nonneg h1.le]; linarith
    · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP ρ hρ
      refine ⟨?_, ?_⟩
      · rw [Complex.ofReal_neg, heven]
        exact hvan ρ.im h1 (by rw [← h3]; exact h4) (by rw [← h3]; exact h5)
      · rw [mem_closedBall, dist_eq_norm]
        calc ‖((-ρ.im : ℝ) : ℂ) - c‖ ≤ ‖((-ρ.im : ℝ) : ℂ)‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos h1]; linarith
  have hrealS : ∀ z ∈ S, ∃ t : ℝ, z = (t : ℂ) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨ρ.im, rfl⟩
    · obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨-ρ.im, rfl⟩
  have hge2 : ∀ z ∈ S, (2 : ℝ) ≤ (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := by
    intro z hz
    obtain ⟨t, rfl⟩ := hrealS z hz
    obtain ⟨hHz, hzb⟩ := hzero t hz
    obtain ⟨w, hw⟩ := hH0
    obtain ⟨k, hk, horder, -⟩ :=
      GaloisForLFunctions.HTGeometry.exists_even_order_factor_of_real_nonneg hH hreal hHz
        (Eventually.of_forall hpos) hw
    rw [MeromorphicOn.divisor_apply hHA.meromorphicOn hzb,
      (hH.analyticAt _).meromorphicOrderAt_eq, horder, ENat.map_coe, WithTop.untop₀_coe]
    exact_mod_cast (show 2 ≤ 2 * k by omega)
  have hnn : ∀ z, (0 : ℝ) ≤ (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := fun z => by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hHA z
  have hfin : (MeromorphicOn.divisor H (closedBall c r)).support.Finite :=
    (MeromorphicOn.divisor H _).finiteSupport (isCompact_closedBall c r)
  have hsupp : Function.support (fun z => (MeromorphicOn.divisor H (closedBall c r) z : ℝ)) ⊆
      (hfin.toFinset ∪ S : Finset ℂ) := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    left
    rw [Function.mem_support]
    exact_mod_cast hz
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  calc 4 * (xiSimpleCriticalZeroCount T : ℝ) = ∑ z ∈ S, (2 : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; rw [hcard]; ring
    _ ≤ ∑ z ∈ S, (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := Finset.sum_le_sum hge2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        fun z _ _ => hnn z

/-- The simple critical Xi divisor forbids exponent `b > 3/2` for a source with
nonnegative entire transform. No multiplicity condition on Xi division is needed. -/
theorem ae_eq_zero_of_nonnegativeTransform_fastDoubleExp {u : ℝ → ℂ} {a b C : ℝ}
    (hu : AEStronglyMeasurable u)
    (hreal : ∀ t : ℝ, (sourceTransform u t).im = 0)
    (hpos : ∀ t : ℝ, 0 ≤ (sourceTransform u t).re)
    (heven : ∀ x, u (-x) = u x) (ha : 0 < a) (hb : 3 / 2 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hb0 : 0 < b := by linarith
  have hms := measurableMomentSource_of_doubleExp hu ha hb0 hC
  have hHd := hms.differentiable_sourceTransform
  have hint_u : Integrable u := (hms.moment 0).mono' hu (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, sourceTransform u z = 0
  · exact ae_eq_zero_of_sourceTransform_eq_zero hint_u hH
  exfalso
  push Not at hH
  obtain ⟨c, hc⟩ := hH
  have hπ := Real.pi_pos
  set δ := 4 / (3 * Real.pi) - 2 / (Real.pi * b) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  set η := min (1 / 10) (δ / 8) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη6 : η ≤ 1 / 10 := min_le_left _ _
  have hηδ : η ≤ δ / 8 := min_le_right _ _
  obtain ⟨T₁, hT₁⟩ := two_thirds_simpleCritical_epsilon η hη0
  obtain ⟨T₂, hT₂4, hN⟩ := exists_xiZeroCount_close η hη0
  set κ := 4 * ((2 / 3 - η) * (1 / (2 * Real.pi) - η)) with hκdef
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hκ : 2 / (Real.pi * b) < κ := by
    have h1 : κ = 4 / (3 * Real.pi) - 8 * η / 3 - 2 * (η / Real.pi) + 4 * η ^ 2 := by
      rw [hκdef]; field_simp; ring
    have h2 : η / Real.pi ≤ η / 3 := div_le_div_of_nonneg_left hη0.le (by norm_num) hπ3.le
    nlinarith
  refine false_of_capacity hu ha hb0 hC hc (κ := κ) (K := ‖c‖) (T₀ := max (max T₁ T₂) 1)
    (norm_nonneg _) hκ (le_max_right _ _) fun T hT => ?_
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTone : 1 ≤ T := (le_max_right _ _).trans hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hsimple := hT₁ T hT1
  have hNT := (abs_le.mp (hN T hT2)).1
  rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)] at hNT
  push_cast at hNT
  have hcount := four_mul_simpleCriticalCount_le_divisor_of_nonnegative hHd ⟨c, hc⟩ hreal hpos
    (sourceTransform_neg_of_even heven) hvan c (T := T) (r := T + ‖c‖) le_rfl
  have hpos1 : 0 ≤ 2 / 3 - η := by linarith
  have hpos2 : 0 ≤ 1 / (2 * Real.pi) - η := by
    have : 1 / 10 < 1 / (2 * Real.pi) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_lt_d2]
    linarith
  have hlow : (1 / (2 * Real.pi) - η) * (T * Real.log T) ≤ (xiPosZeroCount T : ℝ) := by linarith
  calc κ * (T * Real.log T) = 4 * ((2 / 3 - η) * ((1 / (2 * Real.pi) - η) * (T * Real.log T))) := by
        rw [hκdef]; ring
    _ ≤ 4 * ((2 / 3 - η) * (xiPosZeroCount T : ℝ)) := by
        gcongr
    _ ≤ 4 * (xiSimpleCriticalZeroCount T : ℝ) := by linarith
    _ ≤ _ := hcount

open _root_.RHTower.WeilSpectral
open scoped ComplexConjugate

/-- Reflection products inherit strip decay and have real nonnegative boundary values. -/
theorem stripDecay_reflectionProduct {Φ : ℂ → ℂ} {d ε C : ℝ}
    (hd : 0 ≤ d) (hΦ : StripDecay Φ d ε C) :
    StripDecay (fun z => Φ z * Φ (-z)) d (2 * ε) (C ^ 2) := by
  refine ⟨fun z hz => (hΦ.diff z hz).mul
    ((hΦ.diff (-z) (by simpa using hz)).comp z (differentiableAt_id.neg)), ?_⟩
  intro z hz
  rw [norm_mul]
  have hC := hΦ.const_nonneg hd
  have hn := hΦ.bound (-z) (by simpa using hz)
  simp only [Complex.neg_re, abs_neg] at hn
  calc ‖Φ z‖ * ‖Φ (-z)‖ ≤
      (C * Real.exp (-(ε * |z.re|))) * (C * Real.exp (-(ε * |z.re|))) :=
        mul_le_mul (hΦ.bound z hz) hn (norm_nonneg _) (by positivity)
    _ = C ^ 2 * Real.exp (-((2 * ε) * |z.re|)) := by
      rw [show -(2 * ε * |z.re|) = -(ε * |z.re|) + -(ε * |z.re|) by ring,
        Real.exp_add]; ring

private theorem reflectionProduct_real {Φ : ℂ → ℂ}
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (r : ℝ) :
    Φ r * Φ (-(r : ℂ)) = (‖Φ r‖ ^ 2 : ℝ) := by
  rw [hsym, Complex.ofReal_pow, Complex.mul_conj']

/-- The reflection product's inverse transform is the original test's autocorrelation. -/
theorem stripTest_reflectionProduct {Φ : ℂ → ℂ} {d ε C : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hΦ : StripDecay Φ d ε C)
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r)) (y : ℝ) :
    stripTest (fun z => Φ z * Φ (-z)) y = crossCorr (stripTest Φ) (stripTest Φ) y := by
  let Ψ : ℂ → ℂ := fun z => Φ z * Φ (-z)
  have hΨ : StripDecay Ψ d (2 * ε) (C ^ 2) := stripDecay_reflectionProduct hd.le hΦ
  have hc := continuous_ofReal_comp_of_stripDecay hΨ hd.le
  have hi : Integrable (fun r : ℝ => Ψ r * cexp (-(I * r * y))) := by
    refine ((integrable_exp_neg_mul_abs' (show 0 < 2 * ε by positivity)).const_mul
      (C ^ 2)).mono' (hc.mul (by fun_prop)).aestronglyMeasurable
        (Eventually.of_forall fun r => ?_)
    rw [norm_mul, norm_cexp_neg_I_real, mul_one]
    simpa only [Complex.ofReal_re] using hΨ.bound r (by simpa using hd.le)
  rw [crossCorr_stripTest hd hε hΦ hsym, stripTest, stripInvFT]
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul, ← RCLike.re_eq_complex_re, ← integral_re hi]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with r
  change (Ψ r * cexp (-(I * r * y))).re = _
  rw [show Ψ r = (‖Φ r‖ ^ 2 : ℝ) from reflectionProduct_real hsym r,
    Complex.re_ofReal_mul]
  congr 1
  rw [show -(I * (r : ℂ) * y) = (((-(r * y)) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- Xi division prevents a spectral square from having an autocorrelation tail of
exponent greater than `3/2`. The quotient need not be analytic. -/
theorem not_fastDoubleExp_crossCorr_of_stripXiFactor
    {Φ g : ℂ → ℂ} {d ε C a b M : ℝ}
    (hd : 1 / 2 < d) (hε : 0 < ε) (hΦ : StripDecay Φ d ε C)
    (hsym : ∀ r : ℝ, Φ (-(r : ℂ)) = conj (Φ r))
    (hfac : ∀ z : ℂ, |z.im| ≤ 1 / 2 → Φ z = XiC z * g z)
    (hg : g 0 ≠ 0) (ha : 0 < a) (hb : 3 / 2 < b) :
    ¬ ∀ x : ℝ, |crossCorr (stripTest Φ) (stripTest Φ) x| ≤
      M * Real.exp (-a * Real.exp (b * |x|)) := by
  intro hbound
  have hd0 : 0 < d := by linarith
  let Ψ : ℂ → ℂ := fun z => Φ z * Φ (-z)
  let u : ℝ → ℂ := fun x => (stripTest Ψ x : ℂ)
  have hΨ : StripDecay Ψ d (2 * ε) (C ^ 2) := stripDecay_reflectionProduct hd0.le hΦ
  have hε2 : 0 < 2 * ε := by positivity
  have hΨreal : ∀ r : ℝ, Ψ r = (‖Φ r‖ ^ 2 : ℝ) := reflectionProduct_real hsym
  have hΨeven : ∀ z : ℂ, Ψ (-z) = Ψ z := fun z => by
    dsimp only [Ψ]; rw [neg_neg, mul_comm]
  have hΨsym : ∀ r : ℝ, Ψ (-(r : ℂ)) = conj (Ψ r) := by
    intro r
    rw [hΨeven, hΨreal]
    exact (Complex.conj_ofReal _).symm
  have hu : Continuous u := Complex.continuous_ofReal.comp
    (continuous_stripTest hd0.le hε2 hΨ)
  have hcorr : ∀ x, stripTest Ψ x = crossCorr (stripTest Φ) (stripTest Φ) x :=
    stripTest_reflectionProduct hd0 hε hΦ hsym
  have heven : ∀ x, u (-x) = u x := by
    intro x
    simp only [u, hcorr, crossCorr_self_neg]
  have htransform : ∀ r : ℝ, sourceTransform u r = Ψ r := by
    intro r
    have h := paperFT_stripTest (Φ := Ψ) hd0 hε2 hΨ hΨsym
      (z := -(r : ℂ)) (by simpa using hd0)
    have heq : sourceTransform u r = Zeta23.paperFT u (-(r : ℂ)) := by
      unfold sourceTransform Zeta23.paperFT
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show I * (-(r : ℂ)) * (x : ℂ) = -I * r * x by ring]
      exact mul_comm _ _
    rw [heq, h, hΨeven]
  have hreal : ∀ r : ℝ, (sourceTransform u r).im = 0 := by
    intro r; rw [htransform, hΨreal]; rfl
  have hpos : ∀ r : ℝ, 0 ≤ (sourceTransform u r).re := by
    intro r; rw [htransform, hΨreal, Complex.ofReal_re]; positivity
  have hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → sourceTransform u γ = 0 := by
    intro γ _ hzero _
    rw [htransform]
    dsimp only [Ψ]
    rw [hfac _ (by simp), XiC, hzero, zero_mul, zero_mul]
  have hzero := ae_eq_zero_of_nonnegativeTransform_fastDoubleExp
    hu.aestronglyMeasurable hreal hpos heven ha hb (C := M) (fun x => by
      simpa only [u, Complex.norm_real, Real.norm_eq_abs, hcorr] using hbound x) hvan
  have hH0 : sourceTransform u 0 = 0 := by
    unfold sourceTransform
    calc (∫ x : ℝ, cexp (-I * 0 * x) * u x) = ∫ _ : ℝ, (0 : ℂ) := by
          apply integral_congr_ae
          filter_upwards [hzero] with x hx
          simp only [hx, Pi.zero_apply, mul_zero]
      _ = 0 := integral_zero _ _
  have hΦ0 : Φ 0 ≠ 0 := by
    rw [hfac 0 (by simp)]
    exact mul_ne_zero XiC_zero_ne hg
  have hΨ0 : Ψ 0 ≠ 0 := by
    dsimp only [Ψ]; rw [neg_zero]; exact mul_ne_zero hΦ0 hΦ0
  exact hΨ0 (by simpa using (htransform 0).symm.trans hH0)

end

end GaloisForLFunctions.BiScaleUncertainty

#print axioms GaloisForLFunctions.BiScaleUncertainty.four_mul_simpleCriticalCount_le_divisor_of_nonnegative
#print axioms GaloisForLFunctions.BiScaleUncertainty.ae_eq_zero_of_nonnegativeTransform_fastDoubleExp
#print axioms GaloisForLFunctions.BiScaleUncertainty.not_fastDoubleExp_crossCorr_of_stripXiFactor
