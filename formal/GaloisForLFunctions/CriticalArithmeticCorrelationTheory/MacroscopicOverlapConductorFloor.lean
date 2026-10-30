import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheShellsRepayEveryConductor
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# A common floor for the completed conductor energies

The first coprime term of the repayment series bounds every completed conductor energy below by
the conductor-free spectral tail `(2/M) ∫_{t>c} |φ̂(2πt)|² dt`: it carries the weight
`m/φ(m) ≥ 1` and starts at `c/m ≤ c`. For the boosted unit spline the Fourier transform has no
real zeros, so this tail is strictly positive at every overlap.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- The spectrum of a compactly supported `C²` profile is integrable on every half-line. -/
theorem integrableOn_shellSpectrum_Ioi {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (a : ℝ) :
    IntegrableOn (shellSpectrum φ) (Ioi a) := by
  obtain ⟨N, -, hN⟩ := exists_shellSpectrum_le hφ hφc
  have hdom : Integrable (fun t : ℝ => N ^ 2 * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul _
  refine (hdom.integrableOn).mono' (continuous_shellSpectrum hφ.continuous hφc).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (shellSpectrum_nonneg t), Real.norm_eq_abs]
  have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h2 : 1 + |t| ≤ 1 + |2 * Real.pi * t| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [abs_nonneg t, Real.pi_gt_three]
  have h3 : (1 + |t|) ^ 2 ≤ ((1 + |2 * Real.pi * t|) ^ 2) ^ 2 := by
    calc (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 2 * (1 + |t|) ^ 2 :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ h1)
      _ = ((1 + |t|) ^ 2) ^ 2 := by ring
      _ ≤ ((1 + |2 * Real.pi * t|) ^ 2) ^ 2 := by gcongr
  have hrpow : (1 + |t|) ^ (-(2 : ℝ)) = 1 / (1 + |t|) ^ 2 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two, one_div]
  rw [hrpow]
  calc shellSpectrum φ t ≤ N ^ 2 / ((1 + |2 * Real.pi * t|) ^ 2) ^ 2 := hN t
    _ ≤ N ^ 2 / (1 + |t|) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg N) (by positivity) h3
    _ = N ^ 2 * (1 / (1 + |t|) ^ 2) := by ring

/-- **Conductor floor.** Every completed conductor energy dominates the conductor-free tail. -/
theorem completedConductorEnergy_ge_shellTail {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    2 / (∫ u, φ u ^ 2) * ∫ t in Ioi c, shellSpectrum φ t ≤ completedConductorEnergy φ c m := by
  set M := ∫ u, φ u ^ 2
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro isCompact_Icc fun u hu => hsupp u hu
  have hsum := hasSum_completedConductorEnergy hφ hsupp hM hc hm
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ (if Nat.Coprime m (n + 1) then
      2 / (M * m.totient) * ((m : ℝ) / ((n : ℝ) + 1)) *
        ∫ t in Ioi (((n : ℝ) + 1) * c / m), shellSpectrum φ t else 0) := by
    intro n
    split_ifs
    · refine mul_nonneg (mul_nonneg (div_nonneg zero_le_two
        (mul_nonneg hM.le (Nat.cast_nonneg _))) (div_nonneg (Nat.cast_nonneg _) (by positivity))) ?_
      exact setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
    · exact le_rfl
  have hfirst := le_hasSum hsum 0 fun n _ => hterm_nonneg n
  simp only [Nat.coprime_one_right_eq_true, if_true, Nat.cast_zero, zero_add, one_mul,
    div_one] at hfirst
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have htot : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have htot_le : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hcm : c / m ≤ c := div_le_self hc.le (by exact_mod_cast hm)
  have hT0 : 0 ≤ ∫ t in Ioi c, shellSpectrum φ t :=
    setIntegral_nonneg measurableSet_Ioi fun t _ => shellSpectrum_nonneg t
  have hmono : (∫ t in Ioi c, shellSpectrum φ t) ≤ ∫ t in Ioi (c / m), shellSpectrum φ t :=
    setIntegral_mono_set (integrableOn_shellSpectrum_Ioi hφ hφc _)
      (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall (Ioi_subset_Ioi hcm))
  have hratio : 1 ≤ (m : ℝ) / m.totient := (one_le_div htot).mpr htot_le
  calc 2 / M * ∫ t in Ioi c, shellSpectrum φ t
      ≤ 2 / M * ∫ t in Ioi (c / m), shellSpectrum φ t :=
        mul_le_mul_of_nonneg_left hmono (div_nonneg zero_le_two hM.le)
    _ ≤ 2 / M * (((m : ℝ) / m.totient) * ∫ t in Ioi (c / m), shellSpectrum φ t) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg zero_le_two hM.le)
        exact le_mul_of_one_le_left (hT0.trans hmono) hratio
    _ = 2 / (M * m.totient) * (m : ℝ) * ∫ t in Ioi (c / m), shellSpectrum φ t := by
        field_simp
    _ ≤ completedConductorEnergy φ c m := hfirst

/-- The boosted unit spline has a strictly positive spectral tail beyond every overlap. -/
theorem integral_shellSpectrum_tiltedUnitSpline_pos (c : ℝ) :
    0 < ∫ t in Ioi c, shellSpectrum tiltedUnitSpline t := by
  have hφc := hasCompactSupport_tiltedUnitSpline
  have hcont := continuous_shellSpectrum contDiff_tiltedUnitSpline.continuous hφc
  have hpos : ∀ t : ℝ, 0 < shellSpectrum tiltedUnitSpline t := fun t =>
    sq_pos_of_pos (norm_pos_iff.mpr (paperFT_tiltedUnitSpline_real_ne_zero (2 * Real.pi * t)))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (c + 1) (c + 2)).Nonempty from ⟨c + 1, le_rfl, by linarith⟩) hcont.continuousOn
  have hsub : Icc (c + 1) (c + 2) ⊆ Ioi c := fun t ht => by
    simp only [mem_Ioi]; linarith [ht.1]
  have hint := integrableOn_shellSpectrum_Ioi contDiff_tiltedUnitSpline hφc c
  calc (0 : ℝ) < shellSpectrum tiltedUnitSpline t₀ := hpos t₀
    _ = ∫ t in Icc (c + 1) (c + 2), shellSpectrum tiltedUnitSpline t₀ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc]
        norm_num
    _ ≤ ∫ t in Icc (c + 1) (c + 2), shellSpectrum tiltedUnitSpline t :=
        setIntegral_mono_on (integrableOn_const (by simp))
          (hint.mono_set hsub) measurableSet_Icc fun t ht => hmin ht
    _ ≤ ∫ t in Ioi c, shellSpectrum tiltedUnitSpline t :=
        setIntegral_mono_set hint (ae_of_all _ fun t => shellSpectrum_nonneg t)
          (Eventually.of_forall hsub)

/-- **Uniform conductor floor for the boosted spline** at every positive overlap. -/
theorem exists_tiltedUnitSpline_conductor_floor {c : ℝ} (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ m : ℕ, 0 < m → e ≤ completedConductorEnergy tiltedUnitSpline c m :=
  ⟨2 / (∫ u, tiltedUnitSpline u ^ 2) * ∫ t in Ioi c, shellSpectrum tiltedUnitSpline t,
    mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
      (integral_shellSpectrum_tiltedUnitSpline_pos c),
    fun _ hm => completedConductorEnergy_ge_shellTail contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
