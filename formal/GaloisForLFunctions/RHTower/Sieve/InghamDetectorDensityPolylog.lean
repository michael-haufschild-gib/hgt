import GaloisForLFunctions.RHTower.Sieve.InghamDetectorDensity
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorCenterLogMomentPolylog

open Complex Filter Metric Set ArithmeticFunction Finset

namespace RHTower.Sieve

noncomputable section

theorem exists_eventually_zetaZeroMass_le_routeTPolylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      ∃ T₁ ∈ Ioo (-(X : ℝ)) (-(X : ℝ) + 1),
        ∃ T₂ ∈ Ioo ((X : ℝ) - 2) ((X : ℝ) - 1),
          2 * Real.pi *
              (∑ w ∈ zetaResidueUnitClosedRectangleZeros
                  ((inghamFixedGabrielSigma : ℂ) + (T₁ : ℂ) * I)
                  ((4 : ℂ) + (T₂ : ℂ) * I),
                ((analyticOrderAt zetaResidueUnit w).toNat : ℝ) *
                  (w.re - inghamFixedGabrielSigma)) ≤
            K * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨Kₕ, hKₕ, hhorizontal⟩ :=
    exists_inghamClassicalHorizontalBoundary_polylog
  obtain ⟨C, hC, hcenter⟩ :=
    exists_intervalIntegral_log_norm_inghamClassicalDetector_fixedGabrielCenter_le_polylog
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
        C * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
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
  have hq : 0 ≤ (82571 / 118590 : ℝ) := by norm_num
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ (82571 / 118590 : ℝ) :=
    Real.one_le_rpow hX1 hq
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    linarith [Real.log_nonneg hX1]
  have hlogSq1 : (1 : ℝ) ≤ (1 + Real.log (X : ℝ)) ^ 2 :=
    one_le_pow₀ hlog1
  have hscale1 : (1 : ℝ) ≤
      (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 :=
        mul_le_mul hpow1 hlogSq1 (by norm_num) (by positivity)
  have hhorizontal' :
      inghamClassicalHorizontalBoundary X inghamFixedGabrielSigma 4 T₁ T₂ ≤
        Kₕ * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 :=
    calc
      _ ≤ Kₕ * (1 + Real.log (X : ℝ)) ^ 2 := hhorizontalX
      _ ≤ Kₕ * ((X : ℝ) ^ (82571 / 118590 : ℝ) *
          (1 + Real.log (X : ℝ)) ^ 2) := by
        gcongr
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hpow1 (sq_nonneg (1 + Real.log (X : ℝ))))
      _ = _ := by ring
  have hconst : 1 + P ≤ (1 + P) *
      (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 :=
    calc
      1 + P = (1 + P) * 1 := by ring
      _ ≤ (1 + P) * ((X : ℝ) ^ (82571 / 118590 : ℝ) *
          (1 + Real.log (X : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hscale1 (by positivity)
      _ = _ := by ring
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
theorem exists_eventually_zetaLittlewoodZeroCountAbove_sevenTenths_le_routeTPolylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in Filter.atTop,
      zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4 ((X : ℝ) - 2) (7 / 10) ≤
        K * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨K₀, hK₀, hmass⟩ := exists_eventually_zetaZeroMass_le_routeTPolylog
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
        K₀ * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := by
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
      _ ≤ K₀ * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := hmassX
  have hfactor : 0 < 2 * Real.pi / 1000 := by positivity
  apply le_of_mul_le_mul_left (a := 2 * Real.pi / 1000) (a0 := hfactor)
  calc
    (2 * Real.pi / 1000) *
          zetaLittlewoodZeroCountAbove inghamFixedGabrielSigma 4
            ((X : ℝ) - 2) (7 / 10) ≤
        K₀ * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2 := hscaled
    _ = (2 * Real.pi / 1000) *
          (K * (X : ℝ) ^ (82571 / 118590 : ℝ) * (1 + Real.log (X : ℝ)) ^ 2) := by
      dsimp only [K]
      field_simp [ne_of_gt Real.pi_pos]
