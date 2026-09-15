import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalDetectorShortRange
import GaloisForLFunctions.RHTower.XiMassCriticalWeilPairingCriterion

open Complex Finset
open scoped ArithmeticFunction

namespace RHTower

noncomputable section

namespace Sieve

/-- The zero-jet detector with its harmless `log M` normalization restored. -/
def levinsonZeroJetRescaledCoeff (M n : ℕ) : ℂ :=
  (Real.log M : ℂ) * levinsonLinearMollifiedCriticalDetectorCoeff 0 M n

/-- Inside its aperture, the rescaled zero-jet detector is exactly the von Mangoldt
half-density coefficient. -/
theorem levinsonZeroJetRescaledCoeff_eq_vonMangoldt
    {M n : ℕ} (hM : 1 < M) (hn : 1 < n) (hnM : n ≤ M) :
    levinsonZeroJetRescaledCoeff M n =
      (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)) := by
  rw [levinsonZeroJetRescaledCoeff,
    levinsonLinearMollifiedCriticalDetectorCoeff_eq_vonMangoldt hn hnM]
  have hlog : Real.log (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hM))
  simp only [zero_mul, sub_zero, one_mul]
  norm_cast
  field_simp [hlog]

end Sieve

/-- Natural aperture following the moving Xi-mass cone; the floor `2` only keeps detector
normalization nonsingular before the first cone atom appears. -/
def xiMassLevinsonComovingZeroJetAperture (d u : ℝ) : ℕ :=
  max 2 ⌊Real.exp (d * u / (d - 1 / 2))⌋₊

/-- Source-native co-moving zero-jet detector packet, with no supplied prime projection. -/
def xiMassLevinsonComovingZeroJetCone (a sigma d u : ℝ) : ℂ :=
  let X := ⌊Real.exp (d * u / (d - 1 / 2))⌋₊
  let M := xiMassLevinsonComovingZeroJetAperture d u
  ∑ k ∈ Finset.range (X - 1),
    Sieve.levinsonZeroJetRescaledCoeff M (k + 2) *
      stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I))
        (Real.log ((k : ℝ) + 2) : ℂ)

/-- One short-range zero-jet atom is exactly the critical damped von Mangoldt atom. -/
theorem levinsonZeroJetRescaledCoeff_mul_stripFourier_eq_primeAtom
    {M n : ℕ} (hM : 1 < M) (hn : 1 < n) (hnM : n ≤ M)
    (a sigma u : ℝ) :
    Sieve.levinsonZeroJetRescaledCoeff M n *
        stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + u * I))
          (Real.log n : ℂ) =
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        xiMassCriticalDampedFourierProfile a sigma u (Real.log n) := by
  rw [Sieve.levinsonZeroJetRescaledCoeff_eq_vonMangoldt hM hn hnM,
    xiMassCriticalDampedFourierProfile]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hexp : Real.exp (-Real.log (n : ℝ) / 2) = 1 / Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  push_cast
  ring

/-- **Source-native prime-power landing.** The co-moving zero-jet Levinson packet is exactly the
moving von Mangoldt cone, without true-prime projection or prime-power subtraction. -/
theorem xiMassLevinsonComovingZeroJetCone_eq_primeAtomConeSum
    (a sigma d u : ℝ) :
    xiMassLevinsonComovingZeroJetCone a sigma d u =
      xiMassCriticalPrimeAtomConeSum a sigma d u := by
  classical
  simp only [xiMassLevinsonComovingZeroJetCone,
    xiMassCriticalPrimeAtomConeSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1 :=
    Finset.mem_range.mp hk
  have hnX : k + 2 ≤ ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ := by omega
  have hM : 1 < xiMassLevinsonComovingZeroJetAperture d u := by
    rw [xiMassLevinsonComovingZeroJetAperture]
    omega
  have hnM : k + 2 ≤ xiMassLevinsonComovingZeroJetAperture d u := by
    rw [xiMassLevinsonComovingZeroJetAperture]
    omega
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (levinsonZeroJetRescaledCoeff_mul_stripFourier_eq_primeAtom
      hM (by omega) hnM a sigma u)

/-- Uniform forward-line bound for the literal co-moving zero-jet detector packet. -/
def XiMassLevinsonComovingZeroJetConeLineBound (a sigma d : ℝ) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
    ‖xiMassLevinsonComovingZeroJetCone a sigma d u‖ ≤ C

/-- Co-moving zero-jet boundedness is exactly fixed-Weil-pairing boundedness. -/
theorem xiMassLevinsonComovingZeroJetConeLineBound_iff_fixedWeilPairing
    {a sigma d : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma)
    (hdhalf : 1 / 2 < d) (hda : d < a) :
    XiMassLevinsonComovingZeroJetConeLineBound a sigma d ↔
      XiMassCriticalHalfDensityWeilPairingLineBound a sigma := by
  rw [XiMassLevinsonComovingZeroJetConeLineBound,
    XiMassCriticalHalfDensityWeilPairingLineBound]
  have hcone : ∀ u : ℝ,
      xiMassLevinsonComovingZeroJetCone a sigma d u =
        xiMassCriticalPrimeAtomConeSum a sigma d u :=
    xiMassLevinsonComovingZeroJetCone_eq_primeAtomConeSum a sigma d
  simp_rw [hcone]
  exact (xiMassCriticalHalfDensityWeilPairingLineBound_iff_primeAtomCone
    ha hsigma hdhalf hda).symm

/-- **T1 zero-jet landing criterion.** RH is equivalent to boundedness of the literal co-moving
zero-jet Levinson source, with no external prime projection. -/
theorem riemannHypothesis_iff_xiMassLevinsonComovingZeroJetConeLineBound
    {a c sigma d : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    (hsigma : 0 < sigma) (hdhalf : 1 / 2 < d) (hda : d < a) :
    RiemannHypothesis ↔ XiMassLevinsonComovingZeroJetConeLineBound a sigma d := by
  exact (riemannHypothesis_iff_xiMassCriticalHalfDensityWeilPairingLineBound
    hhalf hca hsigma hdhalf hda).trans
      (xiMassLevinsonComovingZeroJetConeLineBound_iff_fixedWeilPairing
        (lt_trans hhalf hca) hsigma hdhalf hda).symm

end

end RHTower
