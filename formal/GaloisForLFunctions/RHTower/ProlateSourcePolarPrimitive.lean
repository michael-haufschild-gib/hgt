import GaloisForLFunctions.RHTower.ProlateChannelPrimitiveBound
import GaloisForLFunctions.RHTower.PoissonAbelChannelSplit

/-!
# The polar primitive bound for the prolate mean-zero source

Assembling the variational mode, its cut-off mean-zero source and the all-channel radial estimate
gives the growing half-line primitive bound `(11)` for an explicitly constructed source, with no
hypotheses at all.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- A global band eigenfunction is globally bounded. -/
theorem exists_bound_of_bandTransform_eigen {c lam : ℝ} {Φ : ℝ → ℝ} (hlam : lam ≠ 0)
    (hΦ : Continuous Φ) (hband : ∀ x : ℝ, bandTransform c Φ x = lam * Φ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |Φ x| ≤ C := by
  set I : ℝ := ∫ y in (-1 : ℝ)..1, |Φ y| with hI
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hI]
    refine intervalIntegral.integral_nonneg (by norm_num) fun y _ => abs_nonneg _
  refine ⟨|lam|⁻¹ * (|c| / Real.pi * I), by positivity, fun x => ?_⟩
  have hker : ∀ y : ℝ, |sincKernelSmooth c x y| ≤ |c| / Real.pi := fun y =>
    GaloisForLFunctions.RHTower.abs_sincSmooth_le c (x - y)
  have hint1 : IntervalIntegrable (fun y : ℝ => sincKernelSmooth c x y * Φ y) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact (continuous_sincKernelSmooth_snd c x).mul hΦ
  have hint2 : IntervalIntegrable (fun y : ℝ => |c| / Real.pi * |Φ y|) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul hΦ.abs
  have hstep : |bandTransform c Φ x| ≤ |c| / Real.pi * I := by
    rw [bandTransform]
    have habs := intervalIntegral.abs_integral_le_integral_abs
      (f := fun y : ℝ => sincKernelSmooth c x y * Φ y) (μ := volume)
      (by norm_num : (-1 : ℝ) ≤ 1)
    refine le_trans habs ?_
    have hmono : (∫ y in (-1 : ℝ)..1, |sincKernelSmooth c x y * Φ y|)
        ≤ ∫ y in (-1 : ℝ)..1, |c| / Real.pi * |Φ y| := by
      refine intervalIntegral.integral_mono_on (by norm_num) hint1.abs hint2 fun y _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hker y) (abs_nonneg _)
    refine le_trans hmono (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, hI]
  have hval : |Φ x| = |lam|⁻¹ * |bandTransform c Φ x| := by
    rw [hband x, abs_mul]
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hstep (by positivity)

/-- **`(11)` for an explicitly constructed prolate source, with no hypotheses.** -/
theorem exists_prolate_source_polar_primitive_bound :
    ∃ (a : ℝ) (Φ : ℝ → ℝ) (Cf B : ℝ), 0 < a ∧ 0 ≤ B ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ Function.Even Φ ∧
      (∀ x : ℝ, |Φ x| ≤ Cf) ∧ 0 ≤ Cf ∧
      ∀ lam t : ℝ, 2 * a ≤ lam → 0 ≤ t →
        |HTGeometry.halfLineExpPrimitive
            (HTGeometry.radialFullLogSource (prolateMeanZeroSource a 2 Φ) lam) t|
          ≤ B / Real.sqrt lam := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have ha : (0 : ℝ) < 10 := by norm_num
  have hka : (0 : ℝ) < (10 : ℝ) ^ (2 : ℕ) := by norm_num
  have hc : (400 : ℝ) ≤ 2 * Real.pi * (10 : ℝ) ^ (2 : ℕ) := by nlinarith [hpi]
  have hc1 : (1 : ℝ) ≤ 2 * Real.pi * (10 : ℝ) ^ (2 : ℕ) := by linarith
  obtain ⟨lamB, eta, Φ, hlamB, hsm, hne, heven, hband, heig, hsep⟩ :=
    exists_even_joint_prolate_eigen_separation_lt_half hc
  have hΦc : Continuous Φ := hsm.continuous
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  have hΦ1 : Φ 1 ≠ 0 := value_one_ne_of_joint_prolate_band_eigen hsm hne hlamB hband heig
  obtain ⟨C, hC0, hC⟩ := exists_bound_of_bandTransform_eigen hlamB hΦc hband
  obtain ⟨mu, hmune, hmusq, hmu⟩ :=
    exists_realFourierBandTransform_eigen (κ := (10 : ℝ) ^ (2 : ℕ)) hka hsm hne heven hlamB hband heig
  -- the normalized radial profile
  set R : ℝ → ℝ := prolateEndpointNormalize Φ with hRdef
  have hRsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := contDiff_prolateEndpointNormalize hsm
  have hRd1 : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hRsm).1
  have hRd2 : Differentiable ℝ (deriv R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hRsm).2).1
  have hReig : ∀ x : ℝ, prolateSLAction (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) R x = eta * R x :=
    prolateSLAction_endpointNormalize hd1 hd2 heig
  have hchi : eta ≤ 0 :=
    GaloisForLFunctions.RHTower.prolateSeparation_nonpos_of_global_joint hlamB hsm hne hband heig
  have hs0 : 0 ≤ radialSeparationRatio (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) eta :=
    div_nonneg (neg_nonneg.mpr hchi) (sq_nonneg _)
  have hs1 : radialSeparationRatio (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) eta ≤ 1 / 2 := le_of_lt hsep
  have hode := radialProlate_ode_of_prolateSLAction_eq
    (by positivity : (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) ≠ 0) hReig
  have hΦR : ∀ u : ℝ, Φ u = Φ 1 * R u := by
    intro u
    rw [hRdef, prolateEndpointNormalize]
    field_simp
  -- the source
  set F : ℝ → ℝ := prolateMeanZeroSource 10 2 Φ with hF
  set M : ℝ := GaloisForLFunctions.RHTower.exactEnergyBudget
    (radialSeparationRatio (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) eta)
    (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) R (deriv R) 2 with hM
  have hM0 : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  set B : ℝ := 2 * ((10 : ℝ) ^ (2 : ℕ) * |mu| * |Φ 1| *
    (2 * (4500 * M / (Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) *
      (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * 2)))) with hB
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    positivity
  refine ⟨10, Φ, C, B, ha, hB0, hsm, heven, hC, hC0, ?_⟩
  · intro lam t hlam ht
    have hlam0 : (0 : ℝ) < lam := by linarith
    have hbeta : (2 : ℝ) ≤ lam / 10 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
      linarith
    obtain ⟨hsum, hbnd⟩ := tsum_abs_channelPrimitive_prolateMeanZeroSource
      (a := 10) (lamDil := 2) (lamR := lam) (mu := mu) (C := C) (Φ := Φ)
      (s := radialSeparationRatio (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) eta)
      (cc := 2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) (R := R) (DR := deriv R) (DDR := deriv (deriv R))
      ha (by norm_num) hlam0 hΦc heven hC hC0 hmu hΦR hs0 hs1 hc1
      (fun u => (hRd1 u).hasDerivAt) (fun u => (hRd2 u).hasDerivAt) hode hbeta ht
    have hmono : 2 * ((10 : ℝ) ^ (2 : ℕ) * |mu| * |Φ 1| *
        (2 * (4500 * M / (Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) *
          (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * (lam / 10))))) ≤ B := by
      rw [hB]
      have hden : (0 : ℝ) < Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) *
          (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * 2 := by
        have : (0 : ℝ) < Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) :=
          Real.sqrt_pos.mpr (by positivity)
        positivity
      have hle : Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * 2
          ≤ Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) * (lam / 10) := by
        have hpos : (0 : ℝ) < Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) *
            (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) := by
          have : (0 : ℝ) < Real.sqrt (2 * Real.pi * (10 : ℝ) ^ (2 : ℕ)) :=
            Real.sqrt_pos.mpr (by positivity)
          positivity
        nlinarith [mul_nonneg hpos.le (by linarith [hbeta] : (0 : ℝ) ≤ lam / 10 - 2)]
      have hdiv := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 4500 * M) hden hle
      have hAnn : (0 : ℝ) ≤ (10 : ℝ) ^ (2 : ℕ) * |mu| * |Φ 1| := by positivity
      nlinarith [hdiv, hAnn]
    exact abs_halfLineExpPrimitive_radialFullLogSource_le_of_channel_bound
      (integrable_prolateMeanZeroSource ha (by norm_num) hΦc hC hC0)
      (even_prolateMeanZeroSource heven)
      (hasCompactSupport_prolateMeanZeroSource ha (by norm_num))
      (fun y => abs_prolateMeanZeroSource_le (by norm_num) hC hC0 y)
      (integral_prolateMeanZeroSource ha (by norm_num) hΦc heven hC hC0)
      hlam0
      (fun b hb => tendsto_symmetricLebesgue_prolateMeanZeroSource ha (by norm_num) hb
        hΦc heven hC hC0)
      ht hsum (le_trans hbnd hmono)

end RHTower
