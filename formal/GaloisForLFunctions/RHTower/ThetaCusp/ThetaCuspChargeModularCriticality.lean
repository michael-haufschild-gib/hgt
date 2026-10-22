import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspChargeCriticality
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceUnconditional
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.ThetaGroupDeformationPrimeTwo

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ### Reality of the charge source -/

theorem im_eq_zero_of_hasDerivAt {T T' : ℝ → ℂ} (hT : ∀ x, HasDerivAt T (T' x) x)
    (him : ∀ x, (T x).im = 0) (x : ℝ) : (T' x).im = 0 := by
  have h1 : HasDerivAt (fun y => (T y).im) (T' x).im x := by
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hT x))
  have h2 : (fun y => (T y).im) = fun _ => (0 : ℝ) := funext him
  rw [h2] at h1
  exact (h1.unique (hasDerivAt_const x 0))

theorem modTail_thetaGroupBasis_one_im (x : ℝ) : (modTail (thetaGroupBasis 1) 0 x).im = 0 := by
  have h := conj_modTail_thetaGroupBasis_one x
  exact Complex.conj_eq_iff_im.mp h

theorem modSource_thetaGroupBasis_one_im (x : ℝ) :
    (modSource (thetaGroupBasis 1) x).im = 0 := by
  have hF := differentiableOn_thetaGroupBasis 1
  have h1 : ∀ y, (modTailDeriv (thetaGroupBasis 1) 0 y).im = 0 :=
    im_eq_zero_of_hasDerivAt (fun y => hasDerivAt_modTail (c := 0) hF y)
      modTail_thetaGroupBasis_one_im
  have h2 : ∀ y, (modTailDeriv2 (thetaGroupBasis 1) 0 y).im = 0 :=
    im_eq_zero_of_hasDerivAt (fun y => hasDerivAt_modTailDeriv (c := 0) hF y) h1
  rw [modSource_eq _ 0, Complex.sub_im, h2, Complex.div_im]
  simp [modTail_thetaGroupBasis_one_im]

/-! ### Domination of the charge source by the `ξ` source -/

theorem thetaCuspFullSource_ge_first {x : ℝ} (hx : 0 < x) :
    thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x :=
  (summable_thetaCuspSourceTerm x).le_tsum 1 (fun j _ => thetaCuspSourceTerm_nonneg_of_pos hx j)

theorem thetaCuspSourceTerm_one_ge_quadratic {x : ℝ} (hy : 3 ≤ Real.exp (2 * x)) :
    2 * π * (2 * π - 1) * Real.exp (x / 2) * Real.exp (2 * x) ^ 2 *
      Real.exp (-π * Real.exp (2 * x)) ≤ thetaCuspSourceTerm x 1 := by
  unfold thetaCuspSourceTerm thetaCuspSeed
  have he : Real.exp x ^ 2 = Real.exp (2 * x) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have he4 : Real.exp x ^ 4 = Real.exp (2 * x) ^ 2 := by rw [← he]; ring
  simp only [Nat.cast_one, one_mul]
  rw [he4, he]
  set y := Real.exp (2 * x)
  have hy0 : 0 < y := by positivity
  have hpoly : (2 * π - 1) * y ^ 2 ≤ 2 * π * y ^ 2 - 3 * y := by nlinarith
  have hE := Real.exp_pos (-π * y)
  have hx2 := Real.exp_pos (x / 2)
  calc 2 * π * (2 * π - 1) * Real.exp (x / 2) * y ^ 2 * Real.exp (-π * y)
      = Real.exp (x / 2) * (2 * π * ((2 * π - 1) * y ^ 2) * Real.exp (-π * y)) := by ring
    _ ≤ Real.exp (x / 2) * (2 * π * (2 * π * y ^ 2 - 3 * y) * Real.exp (-π * y)) := by
        gcongr
    _ = _ := by ring

theorem exists_charge_source_domination :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖modSource (thetaGroupBasis 1) x‖ ≤ C * thetaCuspFullSource x := by
  obtain ⟨M, hM⟩ := exists_thetaGroupBasis_one_cusp
  have hM' : ∀ τ : ℂ, 1 ≤ τ.im → ‖thetaGroupBasis 1 τ - 0‖ ≤ M * Real.exp (-π * τ.im) := by
    intro τ hτ; rw [sub_zero]; exact hM τ hτ
  have hM0 : 0 ≤ M := by
    have h := hM Complex.I (by simp)
    have h1 : (0:ℝ) ≤ M * Real.exp (-π * Complex.I.im) := le_trans (norm_nonneg _) h
    exact nonneg_of_mul_nonneg_left h1 (Real.exp_pos _)
  have hF := differentiableOn_thetaGroupBasis 1
  set X₃ : ℝ := Real.log 3 / 2 with hX₃
  have hX₃0 : 0 < X₃ := by have := Real.log_pos (by norm_num : (1:ℝ) < 3); positivity
  -- compact part
  have hk0c : Continuous thetaCuspFullSource := by
    have h := continuous_modSource (thetaGroupBasis_eq_form 0 ▸ differentiableOn_thetaGroupBasis 0)
    have e : (fun x => ((thetaCuspFullSource x : ℝ) : ℂ)) = modSource (thetaGroupBasis 0) := by
      funext x; rw [modSource_thetaGroupBasis_zero]
    have h2 : Continuous (fun x => ((thetaCuspFullSource x : ℝ) : ℂ)) := by
      rw [e]; exact continuous_modSource (differentiableOn_thetaGroupBasis 0)
    exact (Complex.continuous_re.comp h2).congr (fun x => by simp)
  have hk1c : Continuous fun x => ‖modSource (thetaGroupBasis 1) x‖ :=
    (continuous_modSource hF).norm
  obtain ⟨xm, hxm, hmin⟩ := (isCompact_Icc (a := 0) (b := X₃)).exists_isMinOn
    (nonempty_Icc.mpr hX₃0.le) hk0c.continuousOn
  obtain ⟨xM, hxM, hmax⟩ := (isCompact_Icc (a := 0) (b := X₃)).exists_isMaxOn
    (nonempty_Icc.mpr hX₃0.le) hk1c.continuousOn
  set m₀ := thetaCuspFullSource xm
  have hm₀ : 0 < m₀ := thetaCuspFullSource_pos xm
  set C₂ : ℝ := ‖modSource (thetaGroupBasis 1) xM‖ / m₀
  set C₁ : ℝ := 4 * M * Real.exp π * 3 / (2 * π * (2 * π - 1))
  have hπ := Real.pi_gt_three
  have h2π : 0 < 2 * π - 1 := by linarith
  have hC₁ : 0 ≤ C₁ := div_nonneg (by positivity) (mul_nonneg (by positivity) h2π.le)
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, ?_⟩
  -- nonnegative half-line
  have hpos : ∀ x : ℝ, 0 ≤ x →
      ‖modSource (thetaGroupBasis 1) x‖ ≤ max C₁ C₂ * thetaCuspFullSource x := by
    intro x hx
    have hk0 := thetaCuspFullSource_pos x
    rcases le_or_gt x X₃ with hxX | hxX
    · have h1 : ‖modSource (thetaGroupBasis 1) x‖ ≤ ‖modSource (thetaGroupBasis 1) xM‖ :=
        hmax ⟨hx, hxX⟩
      have h2 : m₀ ≤ thetaCuspFullSource x := hmin ⟨hx, hxX⟩
      calc ‖modSource (thetaGroupBasis 1) x‖ ≤ C₂ * m₀ := by
            rw [div_mul_cancel₀ _ hm₀.ne']; exact h1
        _ ≤ C₂ * thetaCuspFullSource x := mul_le_mul_of_nonneg_left h2 hC₂
        _ ≤ max C₁ C₂ * thetaCuspFullSource x :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hk0.le
    · have hy : 3 ≤ Real.exp (2 * x) := by
        have : Real.exp (2 * X₃) = 3 := by
          rw [hX₃, show 2 * (Real.log 3 / 2) = Real.log 3 by ring, Real.exp_log (by norm_num)]
        rw [← this]; exact Real.exp_le_exp.mpr (by linarith)
      have hub := norm_modSource_le_of_cuspDecay hF hM' hy
      have hlb := le_trans (thetaCuspSourceTerm_one_ge_quadratic hy)
        (thetaCuspFullSource_ge_first (lt_of_lt_of_le hX₃0 hxX.le))
      set y := Real.exp (2 * x)
      have hy0 : 0 < y := by positivity
      have hq : 3 * y + 2 * y ^ 2 ≤ 3 * y ^ 2 := by nlinarith
      have hA : 0 ≤ 4 * M * Real.exp π * Real.exp (x / 2) := by positivity
      have hE := Real.exp_pos (-π * y)
      calc ‖modSource (thetaGroupBasis 1) x‖
          ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (3 * y + 2 * y ^ 2) * Real.exp (-π * y) := hub
        _ ≤ 4 * M * Real.exp π * Real.exp (x / 2) * (3 * y ^ 2) * Real.exp (-π * y) := by gcongr
        _ = C₁ * (2 * π * (2 * π - 1) * Real.exp (x / 2) * y ^ 2 * Real.exp (-π * y)) := by
            simp only [C₁]; field_simp [h2π.ne']
        _ ≤ C₁ * thetaCuspFullSource x := mul_le_mul_of_nonneg_left hlb hC₁
        _ ≤ max C₁ C₂ * thetaCuspFullSource x :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hk0.le
  intro x
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have h := hpos (-x) (by linarith)
    rwa [modSource_neg hF (thetaGroupBasis_axis 1), thetaCuspFullSource_neg] at h

/-! ### The frozen statement -/

theorem modSource_thetaGroupDeformation (s : ℝ) (x : ℝ) :
    modSource (thetaGroupDeformation s 0) x =
      ((thetaCuspFullSource x : ℝ) : ℂ) + (s : ℂ) * modSource (thetaGroupBasis 1) x := by
  have e : thetaGroupDeformation s 0 =
      fun τ => (1 : ℂ) * thetaGroupBasis 0 τ + (s : ℂ) * thetaGroupBasis 1 τ := by
    funext τ; unfold thetaGroupDeformation thetaGroupBasis; push_cast; ring
  rw [e, modSource_linear_comb (differentiableOn_thetaGroupBasis 0)
    (differentiableOn_thetaGroupBasis 1), modSource_thetaGroupBasis_zero, one_mul]

/-- **`ξ` is critical inside the positive, exactly `Γ_θ`-modular class.**  For every `ε > 0`
there is `0 < s < ε` such that the exactly modular weight-½ source of `θ₃(1 + s·h)`
(`h = θ₂⁴θ₄⁴/θ₃⁸`) is real and strictly positive on the whole line, while its transform
`Ξ + sΞ₁` vanishes at a point `z` with `0 < Im z < 1/2`. -/
theorem thetaGroup_modular_criticality {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < ε ∧
      (∀ x : ℝ, (modSource (thetaGroupDeformation s 0) x).im = 0 ∧
        0 < (modSource (thetaGroupDeformation s 0) x).re) ∧
      ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ modXi (thetaGroupDeformation s 0) z = 0 := by
  obtain ⟨C, hC0, hdom⟩ := exists_charge_source_domination
  set ε' : ℝ := min ε (1 / (2 * (C + 1))) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by positivity)
  obtain ⟨s, hs0, hsε, z, hz0, hz1, hz⟩ := thetaGroup_charge_critical hε'pos
  refine ⟨s, hs0, lt_of_lt_of_le hsε (min_le_left _ _), fun x => ?_, z, hz0, hz1, ?_⟩
  · rw [modSource_thetaGroupDeformation]
    have him := modSource_thetaGroupBasis_one_im x
    constructor
    · simp [him]
    · have hk := thetaCuspFullSource_pos x
      have hre : (((thetaCuspFullSource x : ℝ) : ℂ) + (s : ℂ) * modSource (thetaGroupBasis 1) x).re
          = thetaCuspFullSource x + s * (modSource (thetaGroupBasis 1) x).re := by simp
      rw [hre]
      have h1 : |(modSource (thetaGroupBasis 1) x).re| ≤ C * thetaCuspFullSource x :=
        le_trans (Complex.abs_re_le_norm _) (hdom x)
      have hsC : s * C ≤ 1 / 2 := by
        have : s ≤ 1 / (2 * (C + 1)) := le_trans hsε.le (min_le_right _ _)
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith
      have h2 := neg_abs_le (modSource (thetaGroupBasis 1) x).re
      nlinarith [mul_le_mul_of_nonneg_left h1 hs0.le]
  · rw [modXi_thetaGroupDeformation]
    simpa using hz

end RHTower
