import GaloisForLFunctions.BezoutValuationIncidence.DilationClockSuccessorSeedCoupling

/-!
# Relative-gap size of the physical clock-successor sector

For a successor seed `p*a=q*b+1`, the integer geometry forces
`q-1 <= |p-q|*a` except at the reverse consecutive pair `p=q+1`.
Combining this with the existing least-seed coupling bounds the normalized
physical lag `r/rad(r)` by a relative-gap term and an inverse-scale term.

The original rational dilation profile is approximated by every other signed
sector at the same aligned physical horizon. The complement remains a literal
finite sum over the realized Bézout jump gaps. No sign or cancellation
assumption on that complement is made.
-/

open Finset RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

private theorem successor_seed_denominator_lower {p q a b : ℕ}
    (hsep : p < q ∨ q + 1 < p) (ha : 1 ≤ a) (hab : p * a = q * b + 1) :
    (q : ℝ) - 1 ≤ |(p : ℝ) - q| * (a : ℝ) := by
  have habR : (p : ℝ) * a = (q : ℝ) * b + 1 := by exact_mod_cast hab
  rcases hsep with hpq | hqp
  · have hba : b + 1 ≤ a := by
      by_contra hn
      have hmul := Nat.mul_le_mul hpq.le (show a ≤ b by omega)
      omega
    have hmul : (q : ℝ) * ((b : ℝ) + 1) ≤ (q : ℝ) * a := by
      exact_mod_cast Nat.mul_le_mul_left q hba
    have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq.le
    rw [abs_of_nonpos (sub_nonpos.mpr hpqR)]
    nlinarith
  · have hab' : a + 1 ≤ b := by
      by_contra hn
      have hba : b ≤ a := by omega
      have hmul := Nat.mul_le_mul_left q hba
      have hgap := Nat.mul_le_mul_right a (show q + 2 ≤ p by omega)
      nlinarith
    have hmul : (q : ℝ) * ((a : ℝ) + 1) ≤ (q : ℝ) * b := by
      exact_mod_cast Nat.mul_le_mul_left q hab'
    have hqpR : (q : ℝ) ≤ p := by exact_mod_cast (show q ≤ p by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr hqpR)]
    nlinarith

/-- The reciprocal least-seed amplitude is controlled by the relative scale gap. -/
theorem abs_successorLeastSeedResonance_le_relativeGap
    (Q : CGLPositiveModulus) {p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hsep : p < q ∨ q + 1 < p) :
    |successorLeastSeedResonance Q.value p q| ≤
      (Q.value.totient : ℝ) ^ 2 * |(p : ℝ) - q| / ((q : ℝ) - 1) := by
  classical
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  by_cases hc : Nat.Coprime p q
  · obtain ⟨ha, _, _, hab⟩ := leastSuccessorSeed_spec hp hq hc
    have haR : (0 : ℝ) < (leastSuccessorSeed p q).1 := by
      exact_mod_cast (show 0 < (leastSuccessorSeed p q).1 by omega)
    have hamp := abs_successorFiberAmplitude_le_totient_sq Q p q
      (leastSuccessorSeed p q).1 (leastSuccessorSeed p q).2 0
    simp only [successorFiberAmplitude, mul_zero, add_zero] at hamp
    have hweighted : |successorLeastSeedResonance Q.value p q| *
        ((leastSuccessorSeed p q).1 : ℝ) ≤ (Q.value.totient : ℝ) ^ 2 := by
      rw [successorLeastSeedResonance, abs_div, abs_of_pos haR, div_mul_cancel₀ _ haR.ne']
      exact hamp
    have hgap := successor_seed_denominator_lower hsep ha hab
    apply (le_div_iff₀ hq0).mpr
    calc
      _ ≤ |successorLeastSeedResonance Q.value p q| *
          (|(p : ℝ) - q| * ((leastSuccessorSeed p q).1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hgap (abs_nonneg _)
      _ = |(p : ℝ) - q| * (|successorLeastSeedResonance Q.value p q| *
          ((leastSuccessorSeed p q).1 : ℝ)) := by ring
      _ ≤ |(p : ℝ) - q| * (Q.value.totient : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hweighted (abs_nonneg _)
      _ = _ := by ring
  · have hz : successorLeastSeedResonance Q.value p q = 0 := by
      simp [successorLeastSeedResonance, leastSuccessorSeed, hc]
    rw [hz, abs_zero]
    positivity

/-- The physical horizon whose last complete clock block has endpoint `p*q*rad(r)`. -/
def ramanujanClockSuccessorHorizon (r p q : ℕ) : ℕ :=
  lagVisibilityClock r * (p * q * primeRadical r + 1) - 1

/-- The normalized physical lag equal to the modulus's visibility clock. -/
def ramanujanClockSuccessorSector (r p q : ℕ) : ℝ :=
  Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
    ramanujanDilationLagSector r p q (ramanujanClockSuccessorHorizon r p q)
      (lagVisibilityClock r : ℤ)

/-- Every other signed jump sector, kept at the same physical horizon. -/
def ramanujanClockSignedComplement (r p q : ℕ) : ℝ :=
  let H := ramanujanClockSuccessorHorizon r p q
  Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
    ((∑ h ∈ (dilationJumpPairs H p q).image (dilationJumpGap p q),
      ramanujanDilationLagSector r p q H h) -
        ramanujanDilationLagSector r p q H (lagVisibilityClock r : ℤ))

/-- Relative-gap and inverse-scale costs for a single clock-successor sector. -/
def ramanujanClockSuccessorRelativeGapBudget (r p q : ℕ) : ℝ :=
  let s := primeRadical r
  let v := lagVisibilityClock r
  (v : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
      ((s.totient : ℝ) ^ 2 * |(p : ℝ) - q| / ((q : ℝ) - 1)) +
    (v : ℝ) * ((s : ℝ) * (s.totient : ℝ) ^ 2 /
      (Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ)))

private theorem abs_clock_seed_le {r p q : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hsep : p < q ∨ q + 1 < p) :
    |(lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
      successorLeastSeedResonance (primeRadical r) p q| ≤
      (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
        (((primeRadical r).totient : ℝ) ^ 2 * |(p : ℝ) - q| / ((q : ℝ) - 1)) := by
  have hspos : 0 < primeRadical r :=
    prod_pos fun _ hp => (Nat.mem_primeFactors.mp hp).1.pos
  have hb := abs_successorLeastSeedResonance_le_relativeGap ⟨primeRadical r, hspos⟩ hp hq hsep
  have hc : 0 ≤ (lagVisibilityClock r : ℝ) *
      (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) := by positivity
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left hb hc

/-- An isolated clock-successor sector is small at high, nearby scales. -/
theorem abs_ramanujanClockSuccessorSector_le_relativeGap {r p q : ℕ}
    (hr : r ≠ 0) (hp : 1 < p) (hq : 1 < q) (hsep : p < q ∨ q + 1 < p) :
    |ramanujanClockSuccessorSector r p q| ≤ ramanujanClockSuccessorRelativeGapBudget r p q := by
  let z := (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
    successorLeastSeedResonance (primeRadical r) p q
  have he := abs_normalized_clock_successor_sector_sub_radicalSeed_le hr hp hq
  have hb := abs_clock_seed_le (r := r) hp hq hsep
  change |ramanujanClockSuccessorSector r p q - z| ≤ _ at he
  change |z| ≤ _ at hb
  calc
    _ = |(ramanujanClockSuccessorSector r p q - z) + z| := by congr 1; ring
    _ ≤ |ramanujanClockSuccessorSector r p q - z| + |z| := abs_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add he hb
      simpa only [ramanujanClockSuccessorRelativeGapBudget, add_comm] using hh

/-- The original profile is approximated by its full retained signed complement. -/
theorem abs_dilationProfile_sub_clockSignedComplement_le_relativeGap {r p q : ℕ}
    (hr : 1 < r) (hp : 1 < p) (hq : 1 < q) (hsep : p < q ∨ q + 1 < p) :
    |pmRamanujanDilationProfile r hr ((p : ℝ) / q) - ramanujanClockSignedComplement r p q| ≤
      Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
          (pmRamanujanPrimitiveBound r ^ 2 / ((ramanujanClockSuccessorHorizon r p q : ℝ) + 1)) +
        ramanujanClockSuccessorRelativeGapBudget r p q := by
  let x := pmRamanujanDilationProfile r hr ((p : ℝ) / q) -
    ramanujanClockSignedComplement r p q
  let z := (lagVisibilityClock r : ℝ) * (Real.sqrt (q : ℝ) / Real.sqrt (p : ℝ)) *
    successorLeastSeedResonance (primeRadical r) p q
  have he := abs_dilationProfile_sub_clockSeed_and_other_sectors_le hr hp hq
  have hb := abs_clock_seed_le (r := r) hp hq hsep
  change |x - z| ≤ _ at he
  change |z| ≤ _ at hb
  change |x| ≤ _
  calc
    _ = |(x - z) + z| := by congr 1; ring
    _ ≤ |x - z| + |z| := abs_add_le _ _
    _ ≤ _ := by
      have hh := add_le_add he hb
      simpa only [ramanujanClockSuccessorRelativeGapBudget, ramanujanClockSuccessorHorizon,
        add_assoc, add_left_comm, add_comm] using hh

/-- Every ordered pair of integer scales has an explicit clock-sector/complement bound. -/
theorem dilation_clock_relative_gap_and_signed_complement (r n d : ℕ) :
    let R := r + 2
    let p := n + 2
    let q := p + d + 1
    |ramanujanClockSuccessorSector R p q| ≤ ramanujanClockSuccessorRelativeGapBudget R p q ∧
      |pmRamanujanDilationProfile R (by omega) ((p : ℝ) / q) -
          ramanujanClockSignedComplement R p q| ≤
        Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) *
            (pmRamanujanPrimitiveBound R ^ 2 /
              ((ramanujanClockSuccessorHorizon R p q : ℝ) + 1)) +
          ramanujanClockSuccessorRelativeGapBudget R p q := by
  dsimp only
  exact ⟨abs_ramanujanClockSuccessorSector_le_relativeGap (by omega) (by omega)
    (by omega) (Or.inl (by omega)),
    abs_dilationProfile_sub_clockSignedComplement_le_relativeGap (by omega) (by omega)
      (by omega) (Or.inl (by omega))⟩

end
end GaloisForLFunctions.BezoutValuationIncidence

