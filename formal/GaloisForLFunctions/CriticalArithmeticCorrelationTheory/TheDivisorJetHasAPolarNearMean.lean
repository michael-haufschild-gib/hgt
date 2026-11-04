import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGramRetainsOnlyThePolarConductor
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel

/-!
# The divisor jet has a polar near mean

The exact conductor expansion of the divisor jet commutes with the near
kernel. At growing overlap, its fixed-conductor mean retains only the
conductor-one coefficient, given by the von Mangoldt function.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedIntersectionTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis BezoutValuationIncidence SuccessorShellArithmetic SignedArithmeticHodgeTheory

/-- The normalized divisor jet is an exact finite lowering of conductor profiles. -/
theorem ramanujanLogDivisorJet_div_sqrt_eq {l : ℕ} (hl : 0 < l) (j : ℕ) :
    ramanujanLogDivisorJet l j / Real.sqrt (l.totient : ℝ) / Real.sqrt j =
      ∑ k ∈ l.divisors, ramanujanJetConductorWeight l k *
        (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)) * ramanujanPoleProfile k j := by
  rw [ramanujanLogDivisorJet_eq_weighted_conductors hl, sum_div, sum_div]
  apply sum_congr rfl
  intro k hk
  have hk0 := Nat.pos_of_mem_divisors hk
  have hφk : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk0
  have hs : Real.sqrt (k.totient : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hφk).ne'
  rw [ramanujanPoleProfile, normalizedRamanujanMode,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hk0]
  have hcancel : Real.sqrt (k.totient : ℝ) *
      (ramanujanLagCoefficient k j / Real.sqrt (k.totient : ℝ)) =
      ramanujanLagCoefficient k j := by field_simp [hs]
  symm
  calc
    _ = (ramanujanJetConductorWeight l k / Real.sqrt (l.totient : ℝ) / Real.sqrt j) *
        (Real.sqrt (k.totient : ℝ) *
          (ramanujanLagCoefficient k j / Real.sqrt (k.totient : ℝ))) := by ring
    _ = _ := by rw [hcancel]; ring

/-- The near-pair form with the divisor jet on its receiving index. -/
def fixedWidthNearJetPair (φ : ℝ → ℝ) (w : ℝ) (m l n j : ℕ) : ℝ :=
  if j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * w then
    ramanujanPoleProfile m n *
      (ramanujanLogDivisorJet l j / Real.sqrt (l.totient : ℝ) / Real.sqrt j) *
        (shellAutocorr φ (|Real.log j - Real.log n| / w) / ∫ u, φ u ^ 2)
  else 0

/-- Conductor lowering commutes exactly with the near-pair kernel. -/
theorem fixedWidthNearJetPair_eq_conductor_sum (φ : ℝ → ℝ) (w : ℝ)
    (m : ℕ) {l : ℕ} (hl : 0 < l) (n j : ℕ) :
    fixedWidthNearJetPair φ w m l n j =
      ∑ k ∈ l.divisors, ramanujanJetConductorWeight l k *
        (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)) *
          fixedWidthNearPair φ w m k n j := by
  by_cases hnear : j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * w
  · simp only [fixedWidthNearJetPair, fixedWidthNearPair, if_pos hnear,
      ramanujanLogDivisorJet_div_sqrt_eq hl j]
    rw [mul_sum, sum_mul]
    exact sum_congr rfl fun k _ => by ring
  · simp only [fixedWidthNearJetPair, fixedWidthNearPair, if_neg hnear, mul_zero,
      sum_const_zero]

/-- The jet pairing is a finite combination of the same-width conductor Grams. -/
theorem sum_fixedWidthNearJetPair_eq (φ : ℝ → ℝ) (w : ℝ) (N m : ℕ)
    {l : ℕ} (hl : 0 < l) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, fixedWidthNearJetPair φ w m l n j) =
      ∑ k ∈ l.divisors, ramanujanJetConductorWeight l k *
        (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)) *
          fixedWidthNearGram φ w N m k := by
  simp_rw [fixedWidthNearJetPair_eq_conductor_sum φ w m hl]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ k ∈ l.divisors, ∑ j ∈ Icc 1 N,
        ramanujanJetConductorWeight l k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)) *
            fixedWidthNearPair φ w m k n j :=
      sum_congr rfl fun n _ => sum_comm
    _ = ∑ k ∈ l.divisors, ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        ramanujanJetConductorWeight l k *
          (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)) *
            fixedWidthNearPair φ w m k n j := sum_comm
    _ = _ := by simp only [fixedWidthNearGram, mul_sum]

/-- Only the polar conductor survives in the growing near-jet mean. -/
theorem tendsto_fixedWidthNearJetPair_sum_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (he : Tendsto (fun N : ℕ => c N ^ 4 * Real.log N / N) atTop (𝓝 0))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      fixedWidthNearJetPair φ (c N / N) m l n j) / c N) atTop
      (𝓝 (if m = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (ArithmeticFunction.vonMangoldt l : ℝ) / Real.sqrt (l.totient : ℝ) else 0)) := by
  have hterms := fun k (hk : k ∈ l.divisors) =>
    (tendsto_fixedWidthNearGram_div_overlap hφ hsupp hM hc hcinf he hm
      (Nat.pos_of_mem_divisors hk)).const_mul
      (ramanujanJetConductorWeight l k * (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ)))
  have hsum := tendsto_finset_sum l.divisors hterms
  have hweight : ramanujanJetConductorWeight l 1 = (ArithmeticFunction.vonMangoldt l : ℝ) := by
    unfold ramanujanJetConductorWeight
    rw [Nat.div_one]
    by_cases hl1 : 1 = l
    · subst l
      simp
    · simp only [if_neg hl1, zero_add]
  have hsumlim : (∑ k ∈ l.divisors,
      (ramanujanJetConductorWeight l k * (Real.sqrt (k.totient : ℝ) / Real.sqrt (l.totient : ℝ))) *
        (if m = k then if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0 else 0)) =
      (if m = 1 then ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) *
        (ArithmeticFunction.vonMangoldt l : ℝ) / Real.sqrt (l.totient : ℝ) else 0) := by
    by_cases hm1 : m = 1
    · subst m
      have h1 : 1 ∈ l.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hl.ne'⟩
      simp only [if_pos rfl, mul_ite, mul_zero, eq_comm (a := 1), sum_ite_eq', if_pos h1,
        Nat.totient_one, Nat.cast_one, Real.sqrt_one, hweight]
      ring
    · simp only [if_neg hm1, ite_self, mul_zero, sum_const_zero]
  rw [hsumlim] at hsum
  apply hsum.congr
  intro N
  rw [sum_fixedWidthNearJetPair_eq φ (c N / N) N m hl, sum_div]
  exact sum_congr rfl fun k _ => by ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_fixedWidthNearJetPair_eq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_fixedWidthNearJetPair_sum_div_overlap
