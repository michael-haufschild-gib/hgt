import GaloisForLFunctions.RHTower.XiMassLevinsonComovingZeroJetLanding
import GaloisForLFunctions.RHTower.SmoothAFEZetaCriticalDetectorLongCoefficientDecomposition

/-!
# Symmetric reciprocal Levinson landing

Opposite reciprocal detector jets recover the zero-jet value channel exactly.  This polarization
holds before the finite-head cutoff: both full and omitted coefficients retain the same identity.
After co-moving the aperture, the paired differentiated source therefore lands exactly on the
critical prime-power cone and fixed Weil pairing.
-/

open Complex Finset

namespace RHTower

noncomputable section

namespace Sieve

/-- Opposite detector jets recover the value channel before any cutoff or asymptotic passage. -/
theorem levinsonLinearMollifiedCriticalDetectorCoeff_add_neg
    (lam : ℝ) (M n : ℕ) :
    levinsonLinearMollifiedCriticalDetectorCoeff lam M n +
        levinsonLinearMollifiedCriticalDetectorCoeff (-lam) M n =
      2 * levinsonLinearMollifiedCriticalDetectorCoeff 0 M n := by
  rcases n with _ | n
  · simp [levinsonLinearMollifiedCriticalDetectorCoeff]
  · rw [levinsonLinearMollifiedCriticalDetectorCoeff_eq (Nat.succ_pos n),
      levinsonLinearMollifiedCriticalDetectorCoeff_eq (Nat.succ_pos n),
      levinsonLinearMollifiedCriticalDetectorCoeff_eq (Nat.succ_pos n)]
    push_cast
    ring

/-- Reciprocal opposite jets, with the source normalization restored. -/
def levinsonSymmetricReciprocalRescaledCoeff (M n : ℕ) : ℂ :=
  let lam := (1 / 2 : ℝ) / Real.log M
  ((Real.log M / 2 : ℝ) : ℂ) *
    (levinsonLinearMollifiedCriticalDetectorCoeff lam M n +
      levinsonLinearMollifiedCriticalDetectorCoeff (-lam) M n)

/-- Symmetric reciprocal tuning is exactly the zero-jet coefficient, globally in the index. -/
theorem levinsonSymmetricReciprocalRescaledCoeff_eq_zeroJet
    (M n : ℕ) :
    levinsonSymmetricReciprocalRescaledCoeff M n =
      levinsonZeroJetRescaledCoeff M n := by
  rw [levinsonSymmetricReciprocalRescaledCoeff,
    levinsonLinearMollifiedCriticalDetectorCoeff_add_neg,
    levinsonZeroJetRescaledCoeff]
  push_cast
  ring

end Sieve

/-- Co-moving source packet formed from the two reciprocal Levinson jets. -/
def xiMassLevinsonComovingSymmetricReciprocalCone
    (a sigma d u : ℝ) : ℂ :=
  let X := ⌊Real.exp (d * u / (d - 1 / 2))⌋₊
  let M := xiMassLevinsonComovingZeroJetAperture d u
  ∑ k ∈ Finset.range (X - 1),
    Sieve.levinsonSymmetricReciprocalRescaledCoeff M (k + 2) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I))
        (Real.log ((k : ℝ) + 2) : ℂ)

/-- The symmetric reciprocal source lands exactly on the zero jet before short-range evaluation. -/
theorem xiMassLevinsonComovingSymmetricReciprocalCone_eq_zeroJet
    (a sigma d u : ℝ) :
    xiMassLevinsonComovingSymmetricReciprocalCone a sigma d u =
      xiMassLevinsonComovingZeroJetCone a sigma d u := by
  simp only [xiMassLevinsonComovingSymmetricReciprocalCone,
    xiMassLevinsonComovingZeroJetCone]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Sieve.levinsonSymmetricReciprocalRescaledCoeff_eq_zeroJet]

/-- The paired reciprocal source is exactly the prime-power cone. -/
theorem xiMassLevinsonComovingSymmetricReciprocalCone_eq_primeAtomConeSum
    (a sigma d u : ℝ) :
    xiMassLevinsonComovingSymmetricReciprocalCone a sigma d u =
      xiMassCriticalPrimeAtomConeSum a sigma d u := by
  rw [xiMassLevinsonComovingSymmetricReciprocalCone_eq_zeroJet,
    xiMassLevinsonComovingZeroJetCone_eq_primeAtomConeSum]

/-- Line-bound predicate for the paired reciprocal source. -/
def XiMassLevinsonComovingSymmetricReciprocalConeLineBound
    (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassLevinsonComovingSymmetricReciprocalCone a sigma d u‖ ≤ C

/-- The paired reciprocal source has the same boundedness class as the zero jet. -/
theorem xiMassLevinsonComovingSymmetricReciprocalConeLineBound_iff_zeroJet
    (a sigma d : ℝ) :
    XiMassLevinsonComovingSymmetricReciprocalConeLineBound a sigma d ↔
      XiMassLevinsonComovingZeroJetConeLineBound a sigma d := by
  rw [XiMassLevinsonComovingSymmetricReciprocalConeLineBound,
    XiMassLevinsonComovingZeroJetConeLineBound]
  simp_rw [xiMassLevinsonComovingSymmetricReciprocalCone_eq_zeroJet]

/-- RH criterion retaining both reciprocal differentiated source jets. -/
theorem riemannHypothesis_iff_xiMassLevinsonComovingSymmetricReciprocalConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔
      XiMassLevinsonComovingSymmetricReciprocalConeLineBound a sigma d := by
  rw [xiMassLevinsonComovingSymmetricReciprocalConeLineBound_iff_zeroJet]
  exact riemannHypothesis_iff_xiMassLevinsonComovingZeroJetConeLineBound
    hhalf hca hsigma hdhalf hda

namespace Sieve

/-- Opposite detector heads recover the value head pointwise. -/
theorem levinsonCriticalDetectorHeadCoeff_add_neg
    (lam : ℝ) (n : ℕ) :
    levinsonCriticalDetectorHeadCoeff lam n +
        levinsonCriticalDetectorHeadCoeff (-lam) n =
      2 * levinsonCriticalDetectorHeadCoeff 0 n := by
  unfold levinsonCriticalDetectorHeadCoeff
  push_cast
  ring

/-- The omitted boundary keeps the same opposite-jet polarization. -/
theorem levinsonCriticalDetectorOmittedHeadCoeff_add_neg
    (lam : ℝ) (L M n : ℕ) :
    RHTower.levinsonCriticalDetectorOmittedHeadCoeff lam L M n +
        RHTower.levinsonCriticalDetectorOmittedHeadCoeff (-lam) L M n =
      2 * RHTower.levinsonCriticalDetectorOmittedHeadCoeff 0 L M n := by
  unfold RHTower.levinsonCriticalDetectorOmittedHeadCoeff
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← add_mul, levinsonCriticalDetectorHeadCoeff_add_neg]
  ring

/-- Opposite jets recover the value channel for every exact finite product coefficient. -/
theorem levinsonCriticalDetectorMollifiedFinCoeff_add_neg
    (lam : ℝ) (L M : ℕ) (r : Fin (L * M)) :
    levinsonCriticalDetectorMollifiedFinCoeff lam L M r +
        levinsonCriticalDetectorMollifiedFinCoeff (-lam) L M r =
      2 * levinsonCriticalDetectorMollifiedFinCoeff 0 L M r := by
  rw [RHTower.levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted,
    RHTower.levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted,
    RHTower.levinsonCriticalDetectorMollifiedFinCoeff_eq_full_sub_omitted]
  calc
    levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1) -
          RHTower.levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1) +
        (levinsonLinearMollifiedCriticalDetectorCoeff (-lam) M ((r : ℕ) + 1) -
          RHTower.levinsonCriticalDetectorOmittedHeadCoeff (-lam) L M ((r : ℕ) + 1)) =
      (levinsonLinearMollifiedCriticalDetectorCoeff lam M ((r : ℕ) + 1) +
          levinsonLinearMollifiedCriticalDetectorCoeff (-lam) M ((r : ℕ) + 1)) -
        (RHTower.levinsonCriticalDetectorOmittedHeadCoeff lam L M ((r : ℕ) + 1) +
          RHTower.levinsonCriticalDetectorOmittedHeadCoeff (-lam) L M ((r : ℕ) + 1)) := by ring
    _ = 2 * levinsonLinearMollifiedCriticalDetectorCoeff 0 M ((r : ℕ) + 1) -
        2 * RHTower.levinsonCriticalDetectorOmittedHeadCoeff 0 L M ((r : ℕ) + 1) := by
      rw [levinsonLinearMollifiedCriticalDetectorCoeff_add_neg,
        levinsonCriticalDetectorOmittedHeadCoeff_add_neg]
    _ = 2 * (levinsonLinearMollifiedCriticalDetectorCoeff 0 M ((r : ℕ) + 1) -
        RHTower.levinsonCriticalDetectorOmittedHeadCoeff 0 L M ((r : ℕ) + 1)) := by ring

end Sieve

end

end RHTower
