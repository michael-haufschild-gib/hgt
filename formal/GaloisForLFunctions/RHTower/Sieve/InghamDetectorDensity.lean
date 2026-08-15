import GaloisForLFunctions.RHTower.Sieve.InghamDetectorHorizontalTube
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitWeightedLittlewood

/-!
# Selected horizontal boundary and fixed-gap Route-T zero density

Horizontal detector tubes yield a polylogarithmic argument-variation bound at two compatible
heights.  Combining those same heights with weighted Littlewood, pole-gauge cancellation, the
Gabriel center moment, and the far-right estimate closes the detector rectangle.  The positive
gap from `699/1000` to `7/10` then gives an unconditional analytic-multiplicity zero count.
-/

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

theorem exists_inghamClassicalHorizontalBoundary_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc inghamFixedGabrielSigma 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Icc inghamFixedGabrielSigma 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ ≤
          K * (1 + Real.log X) ^ 2 := by
  obtain ⟨K0, hK0, hselected⟩ :=
    exists_inghamDetector_two_horizontal_edges_polylog
  let B : ℝ := K0 + 2
  let W : ℝ := 4 - inghamFixedGabrielSigma
  let K : ℝ := 2 * W ^ 2 * B
  have hB : 0 ≤ B := by dsimp only [B]; linarith
  have hW : 0 ≤ W := by norm_num [W, inghamFixedGabrielSigma]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hbottom, htop⟩ := hselected hX
  let u : ℝ := 1 + Real.log X
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    have := Real.log_nonneg hX1
    linarith
  have huSq1 : 1 ≤ u ^ 2 := by nlinarith
  have hT₁abs : 1 ≤ |T₁| := by
    rw [abs_of_nonpos (by linarith [hT₁.2, hXR])]
    linarith [hT₁.2]
  have hT₂abs : 1 ≤ |T₂| := by
    rw [abs_of_nonneg (by linarith [hT₂.1, hXR])]
    linarith [hT₂.1]
  have hclassical₁ : ∀ x ∈ Icc inghamFixedGabrielSigma 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)‖ ≤
        B * u ^ 2 := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 := by
      simpa only [inghamFixedGabrielSigma] using hx
    obtain ⟨hH, hdet⟩ := hbottom x hx'
    let s : ℂ := (x : ℂ) + (T₁ : ℂ) * I
    have hsIm : |s.im| = |T₁| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₁ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₁abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₁abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ 2 := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ 2 + 2 := by
        exact add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ 2 := by
        dsimp only [B]
        nlinarith
  have hclassical₂ : ∀ x ∈ Icc inghamFixedGabrielSigma 4,
      ‖logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)‖ ≤
        B * u ^ 2 := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 := by
      simpa only [inghamFixedGabrielSigma] using hx
    obtain ⟨hH, hdet⟩ := htop x hx'
    let s : ℂ := (x : ℂ) + (T₂ : ℂ) * I
    have hsIm : |s.im| = |T₂| := by simp [s]
    have hs1 : s ≠ 1 := by
      intro hs
      have himEq := congrArg Complex.im hs
      have hTzero : T₂ = 0 := by simpa [s] using himEq
      rw [hTzero, abs_zero] at hT₂abs
      linarith
    have htransfer := norm_logDeriv_inghamClassicalDetector_le
      X hs1 (by simpa only [s] using hH) (by rw [hsIm]; exact hT₂abs)
    have hdet' : ‖logDeriv (inghamDetector X) s‖ ≤ K0 * u ^ 2 := by
      simpa only [s, u] using hdet
    calc
      ‖logDeriv (inghamClassicalDetector X) s‖ ≤
          ‖logDeriv (inghamDetector X) s‖ + 2 := htransfer
      _ ≤ K0 * u ^ 2 + 2 := by
        exact add_le_add hdet' (le_refl 2)
      _ ≤ B * u ^ 2 := by
        dsimp only [B]
        nlinarith
  let M : ℝ := W * (B * u ^ 2)
  have hpoint₁ : ∀ x ∈ Set.uIoc inghamFixedGabrielSigma 4,
      ‖(x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le (by norm_num [inghamFixedGabrielSigma])] at hx
    have hxIcc : x ∈ Icc inghamFixedGabrielSigma 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamFixedGabrielSigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₁ : ℂ) * I)).im| ≤
          (x - inghamFixedGabrielSigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₁ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ 2) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₁ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hpoint₂ : ∀ x ∈ Set.uIoc inghamFixedGabrielSigma 4,
      ‖(x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M := by
    intro x hx
    rw [uIoc_of_le (by norm_num [inghamFixedGabrielSigma])] at hx
    have hxIcc : x ∈ Icc inghamFixedGabrielSigma 4 := ⟨hx.1.le, hx.2⟩
    have himle := Complex.abs_im_le_norm
      (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxIcc.1)]
    calc
      (x - inghamFixedGabrielSigma) *
          |(logDeriv (inghamClassicalDetector X)
            ((x : ℂ) + (T₂ : ℂ) * I)).im| ≤
          (x - inghamFixedGabrielSigma) *
            ‖logDeriv (inghamClassicalDetector X)
              ((x : ℂ) + (T₂ : ℂ) * I)‖ :=
        mul_le_mul_of_nonneg_left himle (sub_nonneg.mpr hxIcc.1)
      _ ≤ W * (B * u ^ 2) := by
        apply mul_le_mul (by dsimp only [W]; linarith [hxIcc.2])
          (hclassical₂ x hxIcc) (norm_nonneg _) hW
      _ = M := rfl
  have hint₁ : ‖∫ x in inghamFixedGabrielSigma..4,
      (x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₁ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₁
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hint₂ : ‖∫ x in inghamFixedGabrielSigma..4,
      (x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X)
          ((x : ℂ) + (T₂ : ℂ) * I)).im‖ ≤ M * W := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint₂
    rw [abs_of_nonneg hW] at h
    simpa only [W] using h
  have hzero₁ : ∀ x ∈ Icc inghamFixedGabrielSigma 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 := by
      simpa only [inghamFixedGabrielSigma] using hx
    exact (hbottom x hx').1
  have hzero₂ : ∀ x ∈ Icc inghamFixedGabrielSigma 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (699 / 1000 : ℝ) 4 := by
      simpa only [inghamFixedGabrielSigma] using hx
    exact (htop x hx').1
  refine ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, ?_⟩
  dsimp only [inghamClassicalHorizontalBoundary]
  let I₁ : ℝ := ∫ x in inghamFixedGabrielSigma..4,
      (x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₁ : ℂ) * I)).im
  let I₂ : ℝ := ∫ x in inghamFixedGabrielSigma..4,
      (x - inghamFixedGabrielSigma) *
        (logDeriv (inghamClassicalDetector X) ((x : ℂ) + (T₂ : ℂ) * I)).im
  change I₁ - I₂ ≤ K * u ^ 2
  have hdiff : I₁ - I₂ ≤ ‖I₁ - I₂‖ := by
    rw [Real.norm_eq_abs]
    exact le_abs_self _
  have htri : ‖I₁ - I₂‖ ≤ ‖I₁‖ + ‖I₂‖ := norm_sub_le _ _
  have hI₁ : ‖I₁‖ ≤ M * W := by simpa only [I₁] using hint₁
  have hI₂ : ‖I₂‖ ≤ M * W := by simpa only [I₂] using hint₂
  calc
    I₁ - I₂ ≤ ‖I₁ - I₂‖ := hdiff
    _ ≤ ‖I₁‖ + ‖I₂‖ := htri
    _ ≤ M * W + M * W := add_le_add hI₁ hI₂
    _ = K * u ^ 2 := by dsimp only [M, K]; ring

theorem exists_inghamClassicalHorizontalBoundary_fixedPower :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ}, 10 ≤ X →
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
      ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
        (∀ x ∈ Icc inghamFixedGabrielSigma 4,
          inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x ∈ Icc inghamFixedGabrielSigma 4,
          inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ ≤
          K * (X : ℝ) ^ (1 / 100 : ℝ) := by
  obtain ⟨K0, hK0, hpoly⟩ :=
    exists_inghamClassicalHorizontalBoundary_polylog
  let K : ℝ := K0 * (401 : ℝ) ^ 4
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hbound⟩ := hpoly hX
  refine ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hbound.trans ?_⟩
  have hX1 : 1 ≤ X := by omega
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hu1 : 1 ≤ 1 + Real.log X := by
    have := Real.log_nonneg hXR
    linarith
  have h24 : (1 + Real.log X) ^ 2 ≤ (1 + Real.log X) ^ 4 :=
    pow_le_pow_right₀ hu1 (by norm_num)
  have h4 := one_add_log_nat_pow_four_le_rpow_one_hundredth X hX1
  calc
    K0 * (1 + Real.log X) ^ 2 ≤ K0 * (1 + Real.log X) ^ 4 := by gcongr
    _ ≤ K0 * ((401 : ℝ) ^ 4 * (X : ℝ) ^ (1 / 100 : ℝ)) := by gcongr
    _ = K * (X : ℝ) ^ (1 / 100 : ℝ) := by dsimp only [K]; ring

/-- The horizontal-tube height selector is compatible with the complete weighted Littlewood
rectangle.  Thus the horizontal loss is absorbed below the already established fixed Gabriel
center exponent, rather than merely estimated on unrelated admissible heights. -/
theorem exists_eventually_zetaZeroMass_le_routeTExponent :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            K * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
  obtain ⟨Kₕ, hKₕ, hhorizontal⟩ :=
    exists_inghamClassicalHorizontalBoundary_fixedPower
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_fixedGabrielCenter_le
  let P : ℝ := 4 * Real.pi * (1 - inghamFixedGabrielSigma)
  let K : ℝ := C + Kₕ + 1 + P
  have hP : 0 ≤ P := by
    dsimp only [P]
    have hpi := Real.pi_pos.le
    have hc : 0 ≤ 1 - inghamFixedGabrielSigma := by
      norm_num [inghamFixedGabrielSigma]
    positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_inghamDetector_ne_zero_on_rightEdge
      (beta := 4) (by norm_num), eventually_ge_atTop (10 : ℕ)] with X hright hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hzero₁, hzero₂, hhorizontalX⟩ :=
    hhorizontal hX
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hT₁neg : T₁ < 0 := by linarith [hT₁.2]
  have hT₂pos : 0 < T₂ := by linarith [hT₂.1]
  have hT : T₁ < T₂ := hT₁neg.trans hT₂pos
  have hbot : ∀ x ∈ Set.uIcc inghamFixedGabrielSigma 4,
      inghamDetector X ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num [inghamFixedGabrielSigma])] at hx
    exact hzero₁ x hx
  have htop : ∀ x ∈ Set.uIcc inghamFixedGabrielSigma 4,
      inghamDetector X ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num [inghamFixedGabrielSigma])] at hx
    exact hzero₂ x hx
  have hright' : ∀ t ∈ Set.uIcc T₁ T₂,
      inghamDetector X ((4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    exact hright t
  have hmass0 := two_pi_mul_zetaZeroMass_le_inghamLittlewoodBoundary X
    (c := inghamFixedGabrielSigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) hT hbot htop hright'
  have hgauge := inghamLittlewoodBoundary_eq_classical_add_poleCharge X
    (c := inghamFixedGabrielSigma) (d := 4) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) (by norm_num)
    hT₁neg hT₂pos hbot htop hright'
  rw [hgauge] at hmass0
  have hboundary := inghamClassicalLittlewoodBoundary_four_le
    (show 1 ≤ X by omega) (c := inghamFixedGabrielSigma) (T₁ := T₁) (T₂ := T₂)
    (by norm_num [inghamFixedGabrielSigma]) hT.le
  have hleft := hcenter (show 4 ≤ X by omega)
    (le_of_lt hT₁.1) hT.le (by linarith [hT₂.2])
  have hleft' :
      (∫ t in T₁..T₂,
        Real.log ‖inghamClassicalDetector X
          ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖) ≤
        C * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
    simpa only [inghamClassicalDetector] using hleft
  have hlen : T₂ - T₁ ≤ 2 * (X : ℝ) := by
    linarith [hT₁.1, hT₂.2]
  have hvertical := farRightFour_verticalLoss_le_one
    (show 4 ≤ X by omega) hT.le hlen
  have hdecomp :
      2 * Real.pi *
            (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                ((4 : ℂ) + (T₂ : ℂ) * I),
              ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                (w.re - inghamFixedGabrielSigma)) ≤
          (∫ t in T₁..T₂,
            Real.log ‖inghamClassicalDetector X
              ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖) +
          ((T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ)))) +
          inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ + P := by
    calc
      _ ≤ inghamClassicalLittlewoodBoundary X inghamFixedGabrielSigma 4 T₁ T₂ +
          4 * Real.pi * (1 - inghamFixedGabrielSigma) := hmass0
      _ ≤ ((∫ t in T₁..T₂,
              Real.log ‖inghamClassicalDetector X
                ((inghamFixedGabrielSigma : ℂ) + (t : ℂ) * I)‖) +
            (T₂ - T₁) * (2 * ((X : ℝ) ^ (-2 : ℝ) / 2) ^ 2) +
            (4 - inghamFixedGabrielSigma) * ((T₂ - T₁) *
              (4 * ((X : ℝ) ^ (-2 : ℝ) / 2) * (X : ℝ) ^ (-1 : ℝ))) +
            inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂) +
          4 * Real.pi * (1 - inghamFixedGabrielSigma) :=
        add_le_add hboundary (le_refl _)
      _ = _ := by dsimp only [P]; ring
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hq : 0 ≤ inghamFixedGabrielRouteTExponent := by
    rw [inghamFixedGabrielRouteTExponent_eq]
    norm_num
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ inghamFixedGabrielRouteTExponent :=
    Real.one_le_rpow hX1 hq
  have hsmallExp : (1 / 100 : ℝ) ≤ inghamFixedGabrielRouteTExponent := by
    rw [inghamFixedGabrielRouteTExponent_eq]
    norm_num
  have hsmallPow : (X : ℝ) ^ (1 / 100 : ℝ) ≤
      (X : ℝ) ^ inghamFixedGabrielRouteTExponent :=
    Real.rpow_le_rpow_of_exponent_le hX1 hsmallExp
  have hhorizontal' :
      inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ ≤
        Kₕ * (X : ℝ) ^ inghamFixedGabrielRouteTExponent :=
    hhorizontalX.trans (by gcongr)
  have hconst : 1 + P ≤ (1 + P) *
      (X : ℝ) ^ inghamFixedGabrielRouteTExponent :=
    le_mul_of_one_le_right (by positivity) hpow1
  refine ⟨T₁, hT₁, T₂, hT₂, hdecomp.trans ?_⟩
  dsimp only [K]
  linarith

private theorem zetaLittlewoodZeroCountAbove_mul_le_selectedMass
    {c d T T₁ T₂ σ : ℝ} (hcd : c ≤ d) (hT : 0 ≤ T)
    (hbot : T₁ ≤ -T) (htop : T ≤ T₂) :
    (σ - c) * zetaLittlewoodZeroCountAbove c d T σ ≤
      ∑ w ∈ zetaResidueUnitClosedRectangleZeros
          ((c : ℂ) + (T₁ : ℂ) * I) ((d : ℂ) + (T₂ : ℂ) * I),
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := by
  let Zsmall : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (-T : ℝ) * I) ((d : ℂ) + T * I)
  let Zlarge : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + (T₁ : ℂ) * I) ((d : ℂ) + (T₂ : ℂ) * I)
  have hsub : Zsmall ⊆ Zlarge := by
    intro w hw
    have hw' := (mem_zetaResidueUnitClosedRectangleZeros.mp hw)
    apply mem_zetaResidueUnitClosedRectangleZeros.mpr
    refine ⟨?_, hw'.2⟩
    rw [Complex.mem_reProdIm] at hw' ⊢
    constructor
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.neg_im, Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul,
        mul_one, sub_zero, add_zero] using hw'.1.1
    · have him := hw'.1.2
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add] at him ⊢
      rw [Set.uIcc_of_le (by linarith)] at him ⊢
      constructor <;> linarith [him.1, him.2]
  have hmono : zetaLittlewoodZeroMass c d T ≤
      ∑ w ∈ Zlarge,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := by
    dsimp only [zetaLittlewoodZeroMass, Zsmall]
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro w hwlarge _
    have hwK := (mem_zetaResidueUnitClosedRectangleZeros.mp hwlarge).1
    have hwre := (Complex.mem_reProdIm.mp hwK).1
    have hwre' : w.re ∈ Set.Icc c d := by
      simpa [Zlarge, Set.uIcc_of_le hcd] using hwre
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hwre'.1)
  calc
    _ ≤ zetaLittlewoodZeroMass c d T :=
      zetaLittlewoodZeroCountAbove_mul_le_zeroMass hcd
    _ ≤ ∑ w ∈ Zlarge,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) * (w.re - c) := hmono
    _ = _ := rfl

/-- Fixed-gap density consequence of the completed detector rectangle.  This is a literal count of
zeta zeros with analytic multiplicity in `[7/10,4] × [-(X-2),X-2]`. -/
theorem exists_eventually_zetaLittlewoodZeroCountAbove_sevenTenths_le_routeTExponent :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4 ((X : ℝ) - 2) (7 / 10) ≤
        K * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
  obtain ⟨K₀, hK₀, hmass⟩ := exists_eventually_zetaZeroMass_le_routeTExponent
  let K : ℝ := K₀ * (1000 / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (10 : ℕ)] with X hselected hX
  obtain ⟨T₁, hT₁, T₂, hT₂, hmassX⟩ := hselected
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX
  have hTnonneg : 0 ≤ (X : ℝ) - 2 := by linarith
  have hbot : T₁ ≤ -((X : ℝ) - 2) := by linarith [hT₁.2]
  have htop : (X : ℝ) - 2 ≤ T₂ := le_of_lt hT₂.1
  have hcountMass := zetaLittlewoodZeroCountAbove_mul_le_selectedMass
    (c := inghamFixedGabrielSigma) (d := 4) (T := (X : ℝ) - 2)
    (T₁ := T₁) (T₂ := T₂) (σ := 7 / 10)
    (by norm_num [inghamFixedGabrielSigma]) hTnonneg hbot htop
  have hgap : (7 / 10 : ℝ) - inghamFixedGabrielSigma = 1 / 1000 := by
    norm_num [inghamFixedGabrielSigma]
  rw [hgap] at hcountMass
  have hscaled :
      (2 * Real.pi / 1000) *
          zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4
            ((X : ℝ) - 2) (7 / 10) ≤
        K₀ * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := by
    calc
      _ = 2 * Real.pi * ((1 / 1000) *
          zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4
            ((X : ℝ) - 2) (7 / 10)) := by ring
      _ ≤ 2 * Real.pi *
          (∑ w ∈ zetaResidueUnitClosedRectangleZeros
              ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
              ((4 : ℂ) + (T₂ : ℂ) * I),
            ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
              (w.re - inghamFixedGabrielSigma)) :=
        mul_le_mul_of_nonneg_left hcountMass hpi.le
      _ ≤ K₀ * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := hmassX
  have hfactor : 0 < 2 * Real.pi / 1000 := by positivity
  apply le_of_mul_le_mul_left (a := 2 * Real.pi / 1000) (a0 := hfactor)
  calc
    (2 * Real.pi / 1000) *
          zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4
            ((X : ℝ) - 2) (7 / 10) ≤
        K₀ * (X : ℝ) ^ inghamFixedGabrielRouteTExponent := hscaled
    _ = (2 * Real.pi / 1000) *
          (K * (X : ℝ) ^ inghamFixedGabrielRouteTExponent) := by
      dsimp only [K]
      field_simp [ne_of_gt Real.pi_pos]

end

end RHTower.Sieve
