import GaloisForLFunctions.HTGeometry.BoundedRelationProfileRealization
import GaloisForLFunctions.HTGeometry.RoughSubleadingPolynomialMagnitudeHypertranscendence

/-!
# Polynomial-magnitude mechanism nonidentifiability

The private-prime and rough-subleading constructions use incompatible confinement mechanisms, but
their magnitude profiles can have the same asymptotic value, slope, and curvature.  Thus the first
two finite-difference jets of a polynomial magnitude do not identify the mechanism producing
phase-uniform hypertranscendence.
-/

open Filter PowerSeries Set Asymptotics MeasureTheory

namespace GaloisForLFunctions

noncomputable section

/-- Two real sequences have the same asymptotic magnitude signature through second forward
difference. -/
def AsymptoticMagnitudeTwoJetEquivalent (f g : ℕ → ℝ) : Prop :=
  f ~[atTop] g ∧
    (fun n => boundedRelationFirstDifference f n) ~[atTop]
      (fun n => boundedRelationFirstDifference g n) ∧
    (fun n => boundedRelationSecondDifference f n) ~[atTop]
      (fun n => boundedRelationSecondDifference g n)

/-- A unit shift is invisible in every real power at infinity. -/
theorem isEquivalent_natCast_succ_rpow (γ : ℝ) :
    (fun n : ℕ => (((n : ℝ) + 1) ^ γ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ γ) := by
  apply (isEquivalent_iff_tendsto_one (v := fun n : ℕ => (n : ℝ) ^ γ) ?_).2
  · simpa [Nat.cast_add, Nat.cast_one] using!
      (tendsto_natCast_add_rpow_div_rpow (β := γ) 1)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) γ)

/-- Multiplication by the same constant preserves the invisible unit shift. -/
theorem isEquivalent_const_mul_natCast_succ_rpow (c γ : ℝ) :
    (fun n : ℕ => c * (((n : ℝ) + 1) ^ γ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ γ) := by
  simpa only [smul_eq_mul] using
    (IsEquivalent.refl (u := fun _ : ℕ => c)).smul (isEquivalent_natCast_succ_rpow γ)

/-- Every bounded rough subleading perturbation is asymptotically equivalent to its leading pure
power. -/
theorem roughPolynomialProfile_isEquivalent_purePower
    {β α : ℝ} (hαβ : α < β)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    (fun n => roughPolynomialProfile β α u n) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ β) := by
  apply (isEquivalent_iff_tendsto_one (v := fun n : ℕ => (n : ℝ) ^ β) ?_).2
  · exact tendsto_roughPolynomialProfile_div_purePower hαβ hu0 hu2
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) β)

/-- A single polynomial two-jet magnitude signature supports both deterministic private-prime
confinement for every algebraic unit phase and almost-everywhere rough confinement for every real
phase.  Consequently value/slope/curvature asymptotics cannot identify which mechanism is active. -/
theorem exists_privatePrime_ae_roughPolynomial_asymptoticMagnitudeTwoJetEquivalent
    {β α : ℝ} (hβ : 3 < β) (hα1 : 1 < α) (hαcurv : α < β - 2) :
    ∃ (b : ℕ → ℚ) (p : ℕ → ℕ),
      IsPrivatePrimeSuperlinearApproximation
          (boundedRelationShiftedPolynomialProfile 1 β)
          (fun n => Real.exp (-(n : ℝ))) b p ∧
      (∀ v : ℕ → ℂ,
        (∀ n, IsAlgebraic ℚ (v n)) →
        (∀ n, ‖v n‖ = 1) →
        ContDiff ℂ (⊤ : ℕ∞)
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) v) ∧
          (∀ n, PowerSeries.coeff n
            (taylorPS (boundedRelationExponentialFunction (fun n => (b n : ℝ)) v)) ≠ 0) ∧
          Hypertranscendental
            (boundedRelationExponentialFunction (fun n => (b n : ℝ)) v)) ∧
      ∀ᵐ u ∂intervalUnitProductProbability,
        (∀ i, u i ∈ Icc (1 : ℝ) 2) ∧
        AsymptoticMagnitudeTwoJetEquivalent
          (fun n => (b n : ℝ)) (roughPolynomialProfile β α u) ∧
        ∀ θ : ℕ → ℝ, Hypertranscendental (roughPolynomialPhaseFunction β α u θ) := by
  obtain ⟨b, p, hprivate, hvalue, hfirst, hsecond, hphase⟩ :=
    exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental
      (B := 1) (β := β) one_pos (by linarith)
  refine ⟨b, p, hprivate, hphase, ?_⟩
  filter_upwards [ae_intervalUnitProductProbability_mem_Icc,
    ae_forall_phase_hypertranscendental_roughPolynomialPhaseFunction hβ hα1 hαcurv]
      with u hu hroughPhase
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hu n).1.trans' zero_le_one
  have hu2 : ∀ n, u n ≤ 2 := fun n => (hu n).2
  have hroughValue : (roughPolynomialProfile β α u) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ β) :=
    roughPolynomialProfile_isEquivalent_purePower (by linarith) hu0 hu2
  have hshiftValue : boundedRelationShiftedPolynomialProfile 1 β ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ β) := by
    have heq : boundedRelationShiftedPolynomialProfile 1 β =
        (fun n : ℕ => ((n : ℝ) + 1) ^ β) := by
      funext n
      simp [boundedRelationShiftedPolynomialProfile]
    rw [heq]
    exact isEquivalent_natCast_succ_rpow β
  have hroughFirst := roughPolynomialFirstDifference_isEquivalent
    hβ (by linarith : 0 ≤ α) hαcurv hu0 hu2
  have hroughSecond := roughPolynomialSecondDifference_isEquivalent
    hβ (by linarith : 0 ≤ α) hαcurv hu0 hu2
  refine ⟨hu, ⟨hvalue.trans (hshiftValue.trans hroughValue.symm), ?_, ?_⟩, hroughPhase⟩
  · have hshiftFirst := isEquivalent_const_mul_natCast_succ_rpow β (β - 1)
    have htoRough := hshiftFirst.trans hroughFirst.symm
    exact hfirst.trans (by
      simpa [boundedRelationFirstDifference, roughPolynomialFirstDifference] using htoRough)
  · have hshiftSecond :=
      isEquivalent_const_mul_natCast_succ_rpow (β * (β - 1)) (β - 2)
    have htoRough := hshiftSecond.trans hroughSecond.symm
    exact hsecond.trans (by
      simpa [boundedRelationSecondDifference, roughPolynomialSecondDifference] using htoRough)

end

end GaloisForLFunctions
