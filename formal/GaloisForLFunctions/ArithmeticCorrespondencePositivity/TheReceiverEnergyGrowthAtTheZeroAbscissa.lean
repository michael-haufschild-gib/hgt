import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCenteredReceiverSymbolIsHardy
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelEscapeAtomsOfZetaAreItsDominantZeros
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCofactorGramIsATranslationGram
import GaloisForLFunctions.ArithmeticCompensationTheory.TheReceiverEnergyEscapesToTheHorizon
import GaloisForLFunctions.RHTower.MobiusDampingJetsOnTheAdmittedRange

/-!
# Receiver energy beyond the translated zero abscissa

The Hardy datum of the centered symbol is the actual receiver, by uniqueness on
one absolutely convergent Laplace line. Its weighted square mass then controls
every finite pronic horizon.
-/

open Complex Set Filter Topology MeasureTheory
open RHTower RHTower.Sieve GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The elementary source estimate supplies an initial Laplace line below `1`. -/
theorem exists_receiver_energy_le_trivial_power {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ (1 - 2 * ε) := by
  obtain ⟨D, hD, h⟩ := ArithmeticCompensationTheory.exists_dampedMobiusEnergy_le hε hεhalf
  refine ⟨2 * D, by positivity, fun T => (h T).trans ?_⟩
  have hκ : 0 ≤ 1 - 2 * ε := by linarith
  have hp : (T : ℝ) ^ (1 - 2 * ε) ≤ ((T : ℝ) + 1) ^ (1 - 2 * ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg T) (by linarith) hκ
  have h1 : 1 ≤ ((T : ℝ) + 1) ^ (1 - 2 * ε) :=
    Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg T)) hκ
  nlinarith

/-- The real centering constant is the regular reciprocal at `1+ε`. -/
theorem invZeta_one_add_eq_dampedDensity {ε : ℝ} (hε : 0 < ε) :
    invZeta (1 + (ε : ℂ)) = (dampedDensity ε : ℂ) := by
  have hne : 1 + (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, ofReal_re] at this
    linarith
  rw [invZeta_eq_inv hne]
  simpa only [dampedDensity, pmPowerDampedDivisorDensity, one_div] using
    pmPowerDampedDivisorDensity_eq_ofReal_re hε

/-- Multiplying a step Laplace profile by an exponential shifts its parameter. -/
theorem stepLaplaceIntegrand_mul_expRay (f : ℕ → ℝ) (s w : ℂ) (u : ℝ) :
    stepLaplaceIntegrand f s u * expRay w u = stepLaplaceIntegrand f (w + s) u := by
  simp only [stepLaplaceIntegrand, expRay]
  rw [mul_right_comm, ← Complex.exp_add]
  congr 2
  ring

/-- The weighted actual receiver is the Hardy datum; no receiver-energy premise is used. -/
theorem memLp_stepLaplace_receiver {ε σ : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hΘ : zetaZeroAbscissa < σ + ε) :
    MemLp (stepLaplaceIntegrand (receiver ε) (σ : ℂ)) 2 (volume.restrict (Ioi 0)) := by
  obtain ⟨M, hM⟩ := exists_isHalfPlaneHardy_centeredReceiverSymbol hε hσ hΘ
  obtain ⟨C, hC, hE⟩ := exists_receiver_energy_le_trivial_power hε hεhalf
  let b : ℝ := (max σ (1 - ε) + 1) / 2
  have hbσ : σ < b := by
    have h := max_lt hσ1 (by linarith : 1 - ε < 1)
    have := le_max_left σ (1 - ε)
    dsimp [b]
    linarith
  have hbε : 1 - ε < b := by
    have h := max_lt hσ1 (by linarith : 1 - ε < 1)
    have := le_max_right σ (1 - ε)
    dsimp [b]
    linarith
  have hb1 : b < 1 := by dsimp [b]; have := max_lt hσ1 (by linarith : 1 - ε < 1); linarith
  have hb0 : 0 < b := by linarith
  have hA0 : receiver ε 0 = 0 := weightCenteredPrefix_zero _ _
  have hEA : ∀ T : ℕ, ∑ n ∈ Finset.Icc 1 T,
      receiver ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ C * ((T : ℝ) + 1) ^ (1 - 2 * ε) :=
    fun T => by rw [receiver_energy_eq]; exact hE T
  have hsum : ∀ ξ : ℝ, Summable fun n : ℕ => |receiver ε n| *
      (n : ℝ) ^ (-(rayLine (b - σ) ξ + (σ : ℂ)).re - 1) := by
    intro ξ
    apply ArithmeticCorrelationGeometry.summable_abs_mul_rpow_of_energy_growth hA0 hC
      (by linarith : 0 ≤ 1 - 2 * ε) _ hEA
    simp only [add_re, rayLine_re, ofReal_re]
    linarith
  have hi : ∀ ξ : ℝ, IntegrableOn
      (fun u => stepLaplaceIntegrand (receiver ε) (σ : ℂ) u * expRay (rayLine (b - σ) ξ) u)
        (Ioi 0) := by
    intro ξ
    simp_rw [stepLaplaceIntegrand_mul_expRay]
    exact (integrable_stepLaplaceIntegrand hA0
      (by simp only [add_re, rayLine_re, ofReal_re]; linarith) (hsum ξ)).integrableOn
  have heq : ∀ ξ : ℝ,
      laplaceRay (stepLaplaceIntegrand (receiver ε) (σ : ℂ)) (rayLine (b - σ) ξ) =
        centeredReceiverSymbol ε (rayLine (b - σ) ξ + (σ : ℂ)) := by
    intro ξ
    let s : ℂ := rayLine (b - σ) ξ + (σ : ℂ)
    have hsre : s.re = b := by simp [s]
    have hs1 : s ≠ 1 := fun h => by have := congrArg Complex.re h; rw [hsre, one_re] at this; linarith
    have hsε : s + (ε : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [add_re, ofReal_re, one_re, hsre] at this
      linarith
    have hζ : riemannZeta (s + ε) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp only [add_re, ofReal_re, hsre]; linarith)
    have hΦ := complexMellinPairing_receiver_eq hε (by linarith) hC
      (by linarith : 0 ≤ 1 - 2 * ε) hE (s := s)
      (by rw [hsre]; linarith) (by rw [hsre]; exact hb1) hζ hsε
    rw [laplaceRay]
    simp_rw [stepLaplaceIntegrand_mul_expRay]
    change (∫ u in Ioi (0 : ℝ), stepLaplaceIntegrand (receiver ε) s u) = centeredReceiverSymbol ε s
    have hfull : (∫ u, stepLaplaceIntegrand (receiver ε) s u) =
        ∫ u in Ici (0 : ℝ), stepLaplaceIntegrand (receiver ε) s u := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro u hu
      exact stepLaplaceIntegrand_of_neg hA0 s (not_le.mp hu)
    rw [← integral_Ici_eq_integral_Ioi, ← hfull,
      integral_stepLaplaceIntegrand hA0 (by rw [hsre]; exact hb0) (hsum ξ), hΦ,
      centeredReceiverSymbol_eq hs1, invZeta_eq_inv hsε, invZeta_one_add_eq_dampedDensity hε]
    ring
  exact (memLp_and_mass_le_of_laplaceRay_line hM (sub_pos.mpr hbσ) hi heq).1

/-- The pronic energy is the square mass of the log profile up to the horizon. -/
theorem receiver_energy_eq_log_integral (ε : ℝ) (T : ℕ) :
    dampedMobiusEnergy ε T =
      ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), receiverLogProfile ε u ^ 2 := by
  rw [← receiver_energy_eq]
  have h := pronicPairing_rowDilate_eq_translationGram (receiver ε)
    (j := 1) (k := 1) le_rfl le_rfl T
  simpa only [ArithmeticContinuationAndCriticalEnergy.pronicPairing,
    ArithmeticContinuationAndCriticalEnergy.rowDilate, Nat.div_one, Nat.cast_one,
    Real.sqrt_one, mul_one, inv_one, one_mul, Real.log_one, sub_zero,
    ArithmeticDefectRigidity.logProfile, receiverLogProfile, pow_two] using h

/-- Removing the exponential weight on a finite horizon costs its endpoint value. -/
theorem receiver_energy_le_of_memLp_step {ε σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hL : MemLp (stepLaplaceIntegrand (receiver ε) (σ : ℂ)) 2
      (volume.restrict (Ioi 0))) (T : ℕ) :
    dampedMobiusEnergy ε T ≤
      (∫ u in Ioi (0 : ℝ), ‖stepLaplaceIntegrand (receiver ε) (σ : ℂ) u‖ ^ 2) *
        ((T : ℝ) + 1) ^ (2 * σ - 1) := by
  let F : ℝ → ℝ := fun u => ‖stepLaplaceIntegrand (receiver ε) (σ : ℂ) u‖ ^ 2
  have hF : IntegrableOn F (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm hL.aestronglyMeasurable).mp hL
  have hT0 : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg T))
  have hκ : 0 ≤ 2 * σ - 1 := by linarith
  have hpoint : ∀ u : ℝ, receiverLogProfile ε u ^ 2 = Real.exp ((2 * σ - 1) * u) * F u := by
    intro u
    dsimp only [F]
    rw [norm_stepLaplaceIntegrand, ofReal_re, mul_pow, sq_abs,
      ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add,
      receiverLogProfile, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hbound : ∀ u ∈ Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1)),
      receiverLogProfile ε u ^ 2 ≤
        Real.exp ((2 * σ - 1) * Real.log ((T : ℝ) + 1)) * F u := by
    intro u hu
    rw [hpoint]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hκ)) (sq_nonneg _)
  have hsub : Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1)) ⊆ Ioi 0 := fun u hu => hu.1
  have hsmall := hF.mono_set hsub
  have hscaled := hsmall.const_mul (Real.exp ((2 * σ - 1) * Real.log ((T : ℝ) + 1)))
  have hmeas : Measurable (receiverLogProfile ε) := by
    unfold receiverLogProfile
    exact (by fun_prop : Measurable fun u : ℝ => Real.exp (-(u / 2))).mul
      ((measurable_from_nat (f := receiver ε)).comp Real.measurable_exp.nat_floor)
  have hg : IntegrableOn (fun u => receiverLogProfile ε u ^ 2)
      (Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1))) := by
    refine hscaled.mono' (hmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound u hu
  rw [receiver_energy_eq_log_integral, intervalIntegral.integral_of_le hT0]
  calc (∫ u in Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1)), receiverLogProfile ε u ^ 2)
      ≤ ∫ u in Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1)),
          Real.exp ((2 * σ - 1) * Real.log ((T : ℝ) + 1)) * F u :=
        setIntegral_mono_on hg hscaled measurableSet_Ioc hbound
    _ = Real.exp ((2 * σ - 1) * Real.log ((T : ℝ) + 1)) *
          ∫ u in Ioc (0 : ℝ) (Real.log ((T : ℝ) + 1)), F u := integral_const_mul _ _
    _ ≤ Real.exp ((2 * σ - 1) * Real.log ((T : ℝ) + 1)) * ∫ u in Ioi (0 : ℝ), F u := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact setIntegral_mono_set hF (Eventually.of_forall fun u => sq_nonneg _)
          (Eventually.of_forall hsub)
    _ = _ := by
        rw [Real.rpow_def_of_pos (by positivity),
          mul_comm (2 * σ - 1) (Real.log ((T : ℝ) + 1))]
        dsimp only [F]
        ring

/-- The actual receiver has every growth exponent strictly above the translated
zero width. This is an upper bound at the actual abscissa, without an RH premise. -/
theorem exists_receiver_energy_le_of_zeroAbscissa {ε κ : ℝ} (hε : 0 < ε)
    (hκ : max 0 (2 * zetaZeroAbscissa - 2 * ε - 1) < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ := by
  have hκ0 : 0 < κ := (le_max_left _ _).trans_lt hκ
  by_cases hhalf : 1 / 2 ≤ ε
  · obtain ⟨B, hB⟩ := ArithmeticContinuationAndCriticalEnergy.admits_dampedMobiusEnergy_of_half_le hhalf
    refine ⟨max B 0, le_max_right _ _, fun T => ?_⟩
    exact (hB T).trans ((le_max_left B 0).trans (le_mul_of_one_le_right (le_max_right B 0)
      (Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg T)) hκ0.le)))
  have hεhalf : ε < 1 / 2 := not_le.mp hhalf
  by_cases ht : 1 - 2 * ε ≤ κ
  · obtain ⟨C, hC, hE⟩ := exists_receiver_energy_le_trivial_power hε hεhalf
    refine ⟨C, hC, fun T => (hE T).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg T)) ht) hC
  have hσ : 1 / 2 ≤ (1 + κ) / 2 := by linarith
  have hσ1 : (1 + κ) / 2 < 1 := by linarith
  have hΘ : zetaZeroAbscissa < (1 + κ) / 2 + ε := by
    have := (le_max_right 0 (2 * zetaZeroAbscissa - 2 * ε - 1)).trans_lt hκ
    linarith
  have hL := memLp_stepLaplace_receiver hε hεhalf hσ hσ1 hΘ
  refine ⟨∫ u in Ioi (0 : ℝ),
    ‖stepLaplaceIntegrand (receiver ε) (((1 + κ) / 2 : ℝ) : ℂ) u‖ ^ 2,
    integral_nonneg fun u => sq_nonneg _, fun T => ?_⟩
  simpa only [show 2 * ((1 + κ) / 2) - 1 = κ by ring] using receiver_energy_le_of_memLp_step hσ hL T

/-- Every attained rightmost zero is dominant for the receiver whenever its
translate lies right of the critical line. -/
theorem receiver_dominance_at_zeroAbscissa {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hmax : ρ.re = zetaZeroAbscissa) (hre : 1 / 2 + ε < ρ.re) :
    ∀ κ : ℝ, 2 * (ρ.re - ε) - 1 < κ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
        dampedMobiusEnergy ε T ≤ C * ((T : ℝ) + 1) ^ κ := by
  intro κ hκ
  apply exists_receiver_energy_le_of_zeroAbscissa hε
  rw [max_eq_right (by rw [← hmax]; linarith)]
  rw [← hmax]
  linarith

/-- A simple zero on the actual rightmost line gives its Abel atom without a
separate energy-growth assumption. -/
theorem tendsto_receiver_window_atom_at_zeroAbscissa {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) (hmax : ρ.re = zetaZeroAbscissa) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (w : ℝ → ℝ) (L W : ℝ), 0 ≤ L → Continuous w →
      (∀ y, |w y - w ρ.im| ≤ L * |y - ρ.im|) → (∀ y, |w y| ≤ W) →
      Tendsto (fun e : ℝ => e * ∫ y in (ρ.im - δ)..(ρ.im + δ),
          ‖lineSymbol (receiverLogProfile ε) (ρ.re - ε - 1 / 2 + e) y‖ ^ 2 * w y) (𝓝[>] 0)
        (𝓝 (Real.pi * ‖riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε))‖ ^ 2 * w ρ.im)) :=
  tendsto_receiver_window_atom hε hρ hd hre hre1 (receiver_dominance_at_zeroAbscissa hε hmax hre)

/-- An uncancelled simple rightmost zero forces actual Abel-energy divergence. -/
theorem tendsto_receiver_abelGram_atTop_at_zeroAbscissa {ε : ℝ} (hε : 0 < ε) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hd : deriv riemannZeta ρ ≠ 0)
    (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) (hmax : ρ.re = zetaZeroAbscissa)
    (hcan : riemannZeta (ρ - ε) ≠ 0) :
    Tendsto (fun e : ℝ => abelGram (receiverLogProfile ε) (ρ.re - ε - 1 / 2 + e) 0 0)
      (𝓝[>] 0) atTop :=
  tendsto_receiver_abelGram_atTop hε hρ hd hre hre1 hcan
    (receiver_dominance_at_zeroAbscissa hε hmax hre)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.exists_isHalfPlaneHardy_centeredReceiverSymbol
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.exists_receiver_energy_le_of_zeroAbscissa
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.tendsto_receiver_window_atom_at_zeroAbscissa
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.tendsto_receiver_abelGram_atTop_at_zeroAbscissa
