import GaloisForLFunctions.HTGeometry.FormationClockTransmutation
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiCompletedRieszGraphEnergy

/-!
# Suzuki harmonic--Riesz clock transmutation

The completed prime--polar--Gamma density is placed in two literal observer clocks.  Its harmonic
clock charge is absolutely summable and closes at zero.  Its square-root clock response is the
completed Riesz/Suzuki moment.  Their relative rate is the existing Riesz harmonic clock ratio and
is provably unbounded, so neutral fixed-mass charges escape under this clock change.  Universal
operator compactness is therefore impossible; the remaining arithmetic theorem is exceptional
source regularity under this unbounded transmutation.
-/

open Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Literal completed prime--polar--Gamma source density before a clock is chosen. -/
def completedPrimePolarGammaFormationDensity (k : ℕ) : ℝ :=
  psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant

/-- Bounded harmonic observer clock in which completed source charge closes at zero. -/
def completedPrimePolarGammaHarmonicClock (k : ℕ) : ℝ :=
  -(1 / ((k : ℝ) + 1))

/-- Square-root observer clock producing the critical Riesz/Suzuki response. -/
def completedPrimePolarGammaSquareRootClock (k : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) + 1)

/-- Edge of the literal harmonic clock. -/
theorem completedPrimePolarGammaHarmonicClock_edge (k : ℕ) :
    formationClockEdge completedPrimePolarGammaHarmonicClock k =
      1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
  rw [formationClockEdge, completedPrimePolarGammaHarmonicClock,
    completedPrimePolarGammaHarmonicClock]
  push_cast
  ring

/-- Edge of the literal square-root clock. -/
theorem completedPrimePolarGammaSquareRootClock_edge (k : ℕ) :
    formationClockEdge completedPrimePolarGammaSquareRootClock k =
      Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ) := by
  rw [formationClockEdge, completedPrimePolarGammaSquareRootClock,
    completedPrimePolarGammaSquareRootClock]
  push_cast
  ring_nf

/-- Generic harmonic-clock charge is exactly the existing completed source charge. -/
theorem completedPrimePolarGammaHarmonicFormationCharge_eq (k : ℕ) :
    formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaHarmonicClock k =
      completedPrimePolarGammaHarmonicCharge k := by
  rw [formationClockCharge, completedPrimePolarGammaHarmonicClock_edge,
    completedPrimePolarGammaFormationDensity,
    completedPrimePolarGammaHarmonicCharge]

/-- Generic square-root-clock charge is the literal completed Riesz edge. -/
theorem completedPrimePolarGammaSquareRootFormationCharge_eq (k : ℕ) :
    formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaSquareRootClock k =
      (psiRemainder (k + 1) + 2 * Real.eulerMascheroniConstant) *
        (Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ)) := by
  rw [formationClockCharge, completedPrimePolarGammaSquareRootClock_edge,
    completedPrimePolarGammaFormationDensity]

/-- Generic relative rate is the literal harmonic-to-Riesz clock ratio. -/
theorem completedPrimePolarGamma_relativeClockRate_eq (k : ℕ) :
    relativeFormationClockRate completedPrimePolarGammaHarmonicClock
        completedPrimePolarGammaSquareRootClock k =
      completedRieszHarmonicClockRatio k := by
  rw [relativeFormationClockRate,
    completedPrimePolarGammaHarmonicClock_edge,
    completedPrimePolarGammaSquareRootClock_edge,
    completedRieszHarmonicClockRatio]

/-- Harmonic-clock formation is absolutely summable and closes with total charge zero. -/
theorem hasSum_completedPrimePolarGammaHarmonicFormationCharge_zero :
    HasSum
      (formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaHarmonicClock) 0 := by
  have hfun :
      formationClockCharge completedPrimePolarGammaFormationDensity
          completedPrimePolarGammaHarmonicClock =
        completedPrimePolarGammaHarmonicCharge := by
    funext k
    exact completedPrimePolarGammaHarmonicFormationCharge_eq k
  rw [hfun]
  exact hasSum_completedPrimePolarGammaHarmonicCharge_zero

/-- The literal harmonic-clock formation charge is absolutely summable. -/
theorem summable_completedPrimePolarGammaHarmonicFormationCharge :
    Summable
      (formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaHarmonicClock) := by
  have hfun :
      formationClockCharge completedPrimePolarGammaFormationDensity
          completedPrimePolarGammaHarmonicClock =
        completedPrimePolarGammaHarmonicCharge := by
    funext k
    exact completedPrimePolarGammaHarmonicFormationCharge_eq k
  rw [hfun]
  exact summable_completedPrimePolarGammaHarmonicCharge

/-- Square-root-clock response is exactly the literal completed Riesz moment. -/
theorem completedPrimePolarGammaSquareRootFormationResponse_eq_rieszMoment
    {M : ℕ} (hM : 2 ≤ M) :
    formationClockResponse completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaSquareRootClock (M - 2) =
      mobiusDivisorSquareRootAbelMoment M := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedPrefixMesh (by omega : 1 ≤ M)]
  unfold formationClockResponse
  rw [show M - 2 + 1 = M - 1 by omega]
  apply Finset.sum_congr rfl
  intro k hk
  exact completedPrimePolarGammaSquareRootFormationCharge_eq k

private theorem sqrt_nat_le_half {n : ℕ} (hn : 4 ≤ n) :
    Real.sqrt n ≤ (n : ℝ) / 2 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsquare : Real.sqrt n ^ (2 : ℕ) = (n : ℝ) := Real.sq_sqrt hn0
  have hsge : (2 : ℝ) ≤ Real.sqrt n := by
    have hs := Real.sqrt_le_sqrt (show (4 : ℝ) ≤ n by exact_mod_cast hn)
    norm_num at hs ⊢
    exact hs
  nlinarith

/-- Literal harmonic-to-square-root rate dominates the scale index from scale three onward. -/
theorem completedRieszHarmonicClockRatio_ge_index
    {k : ℕ} (hk : 3 ≤ k) :
    (k + 1 : ℕ) ≤ completedRieszHarmonicClockRatio k := by
  let a : ℝ := (k + 1 : ℕ)
  let b : ℝ := (k + 2 : ℕ)
  let d : ℝ := Real.sqrt b - Real.sqrt a
  let s : ℝ := Real.sqrt b + Real.sqrt a
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hab : a < b := by dsimp only [a, b]; push_cast; linarith
  have hsa : Real.sqrt a ^ (2 : ℕ) = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ (2 : ℕ) = b := Real.sq_sqrt hb.le
  have hd0 : 0 ≤ d := sub_nonneg.mpr (Real.sqrt_le_sqrt hab.le)
  have hds : d * s = 1 := by
    calc
      d * s = Real.sqrt b ^ (2 : ℕ) - Real.sqrt a ^ (2 : ℕ) := by
        dsimp only [d, s]
        ring
      _ = b - a := by rw [hsb, hsa]
      _ = 1 := by dsimp only [a, b]; push_cast; ring
  have hsaHalf : Real.sqrt a ≤ a / 2 := by
    simpa only [a, Nat.cast_add, Nat.cast_one] using
      (sqrt_nat_le_half (n := k + 1) (by omega))
  have hsbHalf : Real.sqrt b ≤ b / 2 := by
    simpa only [b, Nat.cast_add, Nat.cast_one] using
      (sqrt_nat_le_half (n := k + 2) (by omega))
  have hsle : s ≤ b := by
    dsimp only [s]
    have habone : b = a + 1 := by dsimp only [a, b]; push_cast; ring
    nlinarith
  have hdb : 1 ≤ d * b := by
    calc
      1 = d * s := hds.symm
      _ ≤ d * b := mul_le_mul_of_nonneg_left hsle hd0
  rw [completedRieszHarmonicClockRatio]
  have hgap : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = 1 / (a * b) := by
    dsimp only [a, b]
    push_cast
    field_simp
    ring
  have hdEq : Real.sqrt (k + 2 : ℕ) - Real.sqrt (k + 1 : ℕ) = d := by
    dsimp only [d, a, b]
  rw [hgap, hdEq]
  have habne : a * b ≠ 0 := mul_ne_zero ha.ne' hb.ne'
  have heq : d / (1 / (a * b)) = a * (d * b) := by
    field_simp [habne]
  rw [heq]
  calc
    a = a * 1 := by ring
    _ ≤ a * (d * b) := mul_le_mul_of_nonneg_left hdb ha.le

/-- Harmonic-to-square-root clock transmutation is globally nonproper. -/
theorem not_completedRieszHarmonicClockRatio_uniformlyBounded :
    ¬ FormationClockRateUniformlyBounded completedRieszHarmonicClockRatio := by
  rintro ⟨B, hB⟩
  obtain ⟨n : ℕ, hn : B < n⟩ := exists_nat_gt B
  have hlower := completedRieszHarmonicClockRatio_ge_index
    (k := n + 3) (by omega)
  have hpos : 0 ≤ completedRieszHarmonicClockRatio (n + 3) :=
    le_trans (by positivity : (0 : ℝ) ≤ (n + 3 + 1 : ℕ)) hlower
  have hupper := hB (n + 3)
  rw [abs_of_nonneg hpos] at hupper
  push_cast at hlower
  linarith

/-- Fixed-mass neutral harmonic charges have arbitrarily large square-root-clock response. -/
theorem exists_completedRieszNeutralDipole_escape (A : ℝ) :
    ∃ n : ℕ,
      (∑ k ∈ Finset.range (n + 2), formationNeutralUnitDipole (n + 1) k) = 0 ∧
      (∑ k ∈ Finset.range (n + 2),
        |formationNeutralUnitDipole (n + 1) k|) = 2 ∧
      A < |formationClockTransmutedResponse
        (formationNeutralUnitDipole (n + 1))
        completedRieszHarmonicClockRatio (n + 1)| :=
  exists_neutralUnitDipole_escape_of_rate_not_bounded
    completedRieszHarmonicClockRatio
    not_completedRieszHarmonicClockRatio_uniformlyBounded A

/-- Zero-argument literal certificate for harmonic closure, square-root response, unbounded
relative rate, and fixed-mass neutral escape. -/
theorem suzukiHarmonicRieszClockTransmutation_certificate :
    Summable
      (formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaHarmonicClock) ∧
    HasSum
      (formationClockCharge completedPrimePolarGammaFormationDensity
        completedPrimePolarGammaHarmonicClock) 0 ∧
    (∀ M : ℕ, 2 ≤ M →
      formationClockResponse completedPrimePolarGammaFormationDensity
          completedPrimePolarGammaSquareRootClock (M - 2) =
        mobiusDivisorSquareRootAbelMoment M) ∧
    (∀ k : ℕ,
      relativeFormationClockRate completedPrimePolarGammaHarmonicClock
          completedPrimePolarGammaSquareRootClock k =
        completedRieszHarmonicClockRatio k) ∧
    (∀ k : ℕ, 3 ≤ k →
      (k + 1 : ℕ) ≤ completedRieszHarmonicClockRatio k) ∧
    (¬ FormationClockRateUniformlyBounded completedRieszHarmonicClockRatio) ∧
    (∀ A : ℝ, ∃ n : ℕ,
      (∑ k ∈ Finset.range (n + 2), formationNeutralUnitDipole (n + 1) k) = 0 ∧
      (∑ k ∈ Finset.range (n + 2),
        |formationNeutralUnitDipole (n + 1) k|) = 2 ∧
      A < |formationClockTransmutedResponse
        (formationNeutralUnitDipole (n + 1))
        completedRieszHarmonicClockRatio (n + 1)|) := by
  exact ⟨summable_completedPrimePolarGammaHarmonicFormationCharge,
    hasSum_completedPrimePolarGammaHarmonicFormationCharge_zero,
    fun _ hM => completedPrimePolarGammaSquareRootFormationResponse_eq_rieszMoment hM,
    completedPrimePolarGamma_relativeClockRate_eq,
    fun _ hk => completedRieszHarmonicClockRatio_ge_index hk,
    not_completedRieszHarmonicClockRatio_uniformlyBounded,
    exists_completedRieszNeutralDipole_escape⟩

end

end GaloisForLFunctions.RHTower
