import GaloisForLFunctions.RHTower.XiPhysicalPrimeEndpointDipoleMultipoleBound
import GaloisForLFunctions.RHTower.GammaInvGrowth

/-!
# Primewise dipole inverse-square energy for physical endpoints

The physical endpoint moment has complementary bounds `‖U_n‖ ≤ n D` and `‖U_n‖ ≤ 2 W`.
Splitting the inverse-square energy at the source scale `⌊2 W / D⌋₊` converts them into the
global transport-energy estimate `∑_{n>N} ‖U_n‖² / n² ≤ 4 W D`.  No phase separation or
auxiliary cluster partition is required.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete differentiated endpoint energy above character cutoff `N`. -/
def xiPhysicalPrimeLogEndpointDipoleInvSqTail
    (P : Finset Nat.Primes) (A m k : ℝ) (N : ℕ) : ℝ :=
  ∑' r : ℕ,
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
      ((N + 1 + r : ℕ) : ℝ) ^ 2

theorem xiPhysicalPrimeLogEndpointTotalWeight_nonneg
    (P : Finset Nat.Primes) :
    0 ≤ xiPhysicalPrimeLogEndpointTotalWeight P := by
  rw [xiPhysicalPrimeLogEndpointTotalWeight]
  exact Finset.sum_nonneg fun p _ => (physicalPrimeEndpointWeight_pos p).le

theorem xiPhysicalPrimeLogEndpointDipoleChordMass_nonneg
    (P : Finset Nat.Primes) (A m k : ℝ) :
    0 ≤ xiPhysicalPrimeLogEndpointDipoleChordMass P A m k := by
  rw [xiPhysicalPrimeLogEndpointDipoleChordMass]
  exact Finset.sum_nonneg fun p _ => mul_nonneg
    (physicalPrimeEndpointWeight_pos p).le (norm_nonneg _)

/-- Every primewise chord is at most the diameter two of the unit circle. -/
theorem xiPhysicalPrimeLogEndpointDipoleChordMass_le_two_mul_totalWeight
    (P : Finset Nat.Primes) (A m k : ℝ) :
    xiPhysicalPrimeLogEndpointDipoleChordMass P A m k ≤
      2 * xiPhysicalPrimeLogEndpointTotalWeight P := by
  rw [xiPhysicalPrimeLogEndpointDipoleChordMass]
  calc
    ∑ p ∈ P, physicalPrimeEndpointWeight p *
        ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureEnd A k p)) -
          fourier 1 (xiPhysicalPrimeLogEndpointNode A
            (xiPhysicalPrimeLogApertureStart m p))‖ ≤
      ∑ p ∈ P, 2 * physicalPrimeEndpointWeight p := by
        apply Finset.sum_le_sum
        intro p hp
        have hchord :
            ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
                (xiPhysicalPrimeLogApertureEnd A k p)) -
              fourier 1 (xiPhysicalPrimeLogEndpointNode A
                (xiPhysicalPrimeLogApertureStart m p))‖ ≤ 2 := by
          calc
            _ ≤ ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
                  (xiPhysicalPrimeLogApertureEnd A k p))‖ +
                ‖fourier 1 (xiPhysicalPrimeLogEndpointNode A
                  (xiPhysicalPrimeLogApertureStart m p))‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        nlinarith [physicalPrimeEndpointWeight_pos p]
    _ = 2 * xiPhysicalPrimeLogEndpointTotalWeight P := by
      rw [xiPhysicalPrimeLogEndpointTotalWeight, Finset.mul_sum]

private theorem summable_shifted_reciprocal_square (M : ℕ) :
    Summable fun r : ℕ => 1 / ((M + 1 + r : ℕ) : ℝ) ^ 2 := by
  have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (M + 1)).2 h
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift

private theorem summable_xiPhysicalPrimeLogEndpointDipoleInvSqTerm
    (P : Finset Nat.Primes) (A m k : ℝ) (N : ℕ) :
    Summable fun r : ℕ =>
      ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
        ((N + 1 + r : ℕ) : ℝ) ^ 2 := by
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hrecip := summable_shifted_reciprocal_square N
  have hmajor : Summable fun r : ℕ => (2 * W) ^ 2 *
      (1 / ((N + 1 + r : ℕ) : ℝ) ^ 2) := hrecip.mul_left _
  refine Summable.of_norm_bounded hmajor fun r => ?_
  have hW : 0 ≤ W := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hmoment :=
    norm_xiPhysicalPrimeLogEndpointCircleMoment_le_two_mul_totalWeight P A m k
      (N + 1 + r)
  have hsquare :
      ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 ≤
        (2 * W) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hmoment
  have hden : 0 < ((N + 1 + r : ℕ) : ℝ) ^ 2 := by positivity
  rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hden.le)]
  rw [div_eq_mul_inv]
  simpa [one_div] using
    mul_le_mul_of_nonneg_right hsquare (inv_nonneg.mpr hden.le)

private theorem xiPhysicalPrimeLogEndpointDipoleInvSqTerm_le_chord_sq
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      xiPhysicalPrimeLogEndpointDipoleChordMass P A m k ^ 2 := by
  let D := xiPhysicalPrimeLogEndpointDipoleChordMass P A m k
  have hD : 0 ≤ D := xiPhysicalPrimeLogEndpointDipoleChordMass_nonneg P A m k
  have hmoment :=
    norm_xiPhysicalPrimeLogEndpointCircleMoment_le_nat_mul_dipoleChordMass
      P A m k n
  have hsquare : ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 ≤
      ((n : ℝ) * D) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg n) hD)).2 hmoment
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [div_le_iff₀ (sq_pos_of_pos hnR)]
  nlinarith

private theorem xiPhysicalPrimeLogEndpointDipoleInvSqTerm_le_totalWeight
    (P : Finset Nat.Primes) (A m k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      4 * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 / (n : ℝ) ^ 2 := by
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hW : 0 ≤ W := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  have hmoment :=
    norm_xiPhysicalPrimeLogEndpointCircleMoment_le_two_mul_totalWeight P A m k n
  have hsquare : ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 ≤
      (2 * W) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hmoment
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [div_le_div_iff₀ (sq_pos_of_pos hnR) (sq_pos_of_pos hnR)]
  dsimp only [W] at hsquare ⊢
  nlinarith

/-- Exact low/high split.  `L` low modes cost chord mass squared; remaining modes cost total
variation times the reciprocal-square tail. -/
theorem xiPhysicalPrimeLogEndpointDipoleInvSqTail_le_split
    (P : Finset Nat.Primes) (A m k : ℝ) (N L : ℕ) (hN : 1 ≤ N) :
    xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N ≤
      (L : ℝ) * xiPhysicalPrimeLogEndpointDipoleChordMass P A m k ^ 2 +
        4 * xiPhysicalPrimeLogEndpointTotalWeight P ^ 2 / (N + L : ℕ) := by
  let f : ℕ → ℝ := fun r =>
    ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
      ((N + 1 + r : ℕ) : ℝ) ^ 2
  let D := xiPhysicalPrimeLogEndpointDipoleChordMass P A m k
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hf : Summable f :=
    summable_xiPhysicalPrimeLogEndpointDipoleInvSqTerm P A m k N
  have hsplit := hf.sum_add_tsum_nat_add L
  have hprefix : ∑ r ∈ Finset.range L, f r ≤ (L : ℝ) * D ^ 2 := by
    calc
      ∑ r ∈ Finset.range L, f r ≤ ∑ _r ∈ Finset.range L, D ^ 2 := by
        apply Finset.sum_le_sum
        intro r hr
        dsimp only [f, D]
        exact xiPhysicalPrimeLogEndpointDipoleInvSqTerm_le_chord_sq
          P A m k (N + 1 + r) (by omega)
      _ = (L : ℝ) * D ^ 2 := by simp
  have htailPoint (r : ℕ) : f (r + L) ≤
      4 * W ^ 2 * (1 / (((N + L + r : ℕ) : ℝ) + 1) ^ 2) := by
    have h := xiPhysicalPrimeLogEndpointDipoleInvSqTerm_le_totalWeight
      P A m k (N + 1 + (r + L)) (by omega)
    dsimp only [f, W]
    convert h using 1
    all_goals push_cast; ring
  have htailSummable : Summable fun r : ℕ =>
      4 * W ^ 2 * (1 / (((N + L + r : ℕ) : ℝ) + 1) ^ 2) := by
    have hbase : Summable fun r : ℕ =>
        1 / (((N + L + r : ℕ) : ℝ) + 1) ^ 2 := by
      have h := summable_shifted_reciprocal_square (N + L)
      convert h using 1
      funext r
      congr 3
      push_cast
      ring
    exact hbase.mul_left _
  have htail : (∑' r : ℕ, f (r + L)) ≤ 4 * W ^ 2 / (N + L : ℕ) := by
    calc
      ∑' r : ℕ, f (r + L) ≤
          ∑' r : ℕ, 4 * W ^ 2 *
            (1 / (((N + L + r : ℕ) : ℝ) + 1) ^ 2) :=
        (hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
          htailPoint htailSummable
      _ = 4 * W ^ 2 * ∑' r : ℕ,
          1 / (((N + L + r : ℕ) : ℝ) + 1) ^ 2 := by rw [tsum_mul_left]
      _ ≤ 4 * W ^ 2 * (1 / (N + L : ℕ)) := by
        exact mul_le_mul_of_nonneg_left
          (HilbertSchmidt.tsum_reciprocal_square_tail_le (by omega)) (by positivity)
      _ = 4 * W ^ 2 / (N + L : ℕ) := by ring
  rw [xiPhysicalPrimeLogEndpointDipoleInvSqTail]
  change (∑' r : ℕ, f r) ≤ _
  rw [← hsplit]
  exact add_le_add hprefix htail

/-- Physical transport-energy law: complete inverse-square endpoint energy is bounded by total
prime weight times literal primewise endpoint chord. -/
theorem xiPhysicalPrimeLogEndpointDipoleInvSqTail_le_four_mul_weight_chord
    (P : Finset Nat.Primes) (A m k : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N ≤
      4 * xiPhysicalPrimeLogEndpointTotalWeight P *
        xiPhysicalPrimeLogEndpointDipoleChordMass P A m k := by
  let D := xiPhysicalPrimeLogEndpointDipoleChordMass P A m k
  let W := xiPhysicalPrimeLogEndpointTotalWeight P
  have hD : 0 ≤ D := xiPhysicalPrimeLogEndpointDipoleChordMass_nonneg P A m k
  have hW : 0 ≤ W := xiPhysicalPrimeLogEndpointTotalWeight_nonneg P
  by_cases hD0 : D = 0
  · have htermZero : ∀ r : ℕ,
        ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ ^ 2 /
            ((N + 1 + r : ℕ) : ℝ) ^ 2 = 0 := by
      intro r
      have hmoment :=
        norm_xiPhysicalPrimeLogEndpointCircleMoment_le_nat_mul_dipoleChordMass
          P A m k (N + 1 + r)
      have hnorm : ‖xiPhysicalPrimeLogEndpointCircleMoment P A m k (N + 1 + r)‖ = 0 := by
        apply le_antisymm
        · simpa [D, hD0] using hmoment
        · exact norm_nonneg _
      rw [hnorm, zero_pow (by norm_num), zero_div]
    rw [xiPhysicalPrimeLogEndpointDipoleInvSqTail, tsum_congr htermZero]
    simp [D, hD0]
  · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hD0)
    let L : ℕ := ⌊2 * W / D⌋₊
    have hratio : 0 ≤ 2 * W / D := div_nonneg (by positivity) hD
    have hLlow : (L : ℝ) * D ≤ 2 * W := by
      have hfloor : (L : ℝ) ≤ 2 * W / D := by
        exact Nat.floor_le hratio
      exact (le_div_iff₀ hDpos).mp (by simpa [mul_comm] using hfloor)
    have hLhigh : 2 * W ≤ ((N + L : ℕ) : ℝ) * D := by
      have hfloorSucc : 2 * W / D < (L : ℝ) + 1 := by
        exact Nat.lt_floor_add_one _
      have hNcast : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hratioLt : 2 * W / D < ((N + L : ℕ) : ℝ) := by
        push_cast
        linarith
      exact (div_le_iff₀ hDpos).mp (le_of_lt hratioLt)
    have hsplit := xiPhysicalPrimeLogEndpointDipoleInvSqTail_le_split
      P A m k N L hN
    have hlow : (L : ℝ) * D ^ 2 ≤ 2 * W * D := by
      nlinarith
    have hNLpos : (0 : ℝ) < (N + L : ℕ) := by positivity
    have hhigh : 4 * W ^ 2 / (N + L : ℕ) ≤ 2 * W * D := by
      rw [div_le_iff₀ hNLpos]
      nlinarith
    exact hsplit.trans (by nlinarith)

/-- Scaled differentiated tail bound used by moving-frequency FCRJ packets. -/
theorem natCast_mul_xiPhysicalPrimeLogEndpointDipoleInvSqTail_le
    (P : Finset Nat.Primes) (A m k : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N ≤
      4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
        xiPhysicalPrimeLogEndpointDipoleChordMass P A m k := by
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [mul_le_mul_of_nonneg_left
    (xiPhysicalPrimeLogEndpointDipoleInvSqTail_le_four_mul_weight_chord
      P A m k N hN) hNnonneg]

private theorem normSq_xiPhysicalApertureCharacterRate_nat_for_dipoleEnergy
    {A : ℝ} (hA : 0 < A) (n : ℕ) :
    Complex.normSq (xiPhysicalApertureCharacterRate A (n : ℤ)) =
      4 * Real.pi ^ 2 * (n : ℝ) ^ 2 / A ^ 2 := by
  rw [xiPhysicalApertureCharacterRate, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_I]
  field_simp [hA.ne']
  norm_cast
  ring

private theorem normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_dipoleInvSqTerm
    {P : Finset Nat.Primes} {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    {n : ℕ} (hn : n ≠ 0) :
    Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A (n : ℤ) m k) =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        (‖xiPhysicalPrimeLogEndpointCircleMoment P A m k n‖ ^ 2 / (n : ℝ) ^ 2) := by
  rw [xiPhysicalPrimeLogEndpointCircleMoment_eq_rate_mul_amplitude hA hn hactive,
    Complex.sq_norm, Complex.normSq_mul,
    normSq_xiPhysicalApertureCharacterRate_nat_for_dipoleEnergy hA]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [hA.ne', hnR, hpi]

/-- Raw FCRJ ultraviolet energy inherits the exact primewise transport-energy bound. -/
theorem natCast_mul_tsum_normSq_xiPhysicalPrimeLogCharacterAmplitude_le_weight_chord
    (P : Finset Nat.Primes) {A m k : ℝ} (hA : 0 < A)
    (hactive : ∀ p ∈ P, 0 < xiPhysicalPrimeLogApertureLength A m k p)
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * ∑' r : ℕ,
        Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k) ≤
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        (4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
          xiPhysicalPrimeLogEndpointDipoleChordMass P A m k) := by
  have htsum :
      (∑' r : ℕ, Complex.normSq (xiPhysicalPrimeLogCharacterAmplitude P A
          ((N + 1 + r : ℕ) : ℤ) m k)) =
        (A ^ 2 / (4 * Real.pi ^ 2)) *
          xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N := by
    rw [xiPhysicalPrimeLogEndpointDipoleInvSqTail, ← tsum_mul_left]
    apply tsum_congr
    intro r
    exact normSq_xiPhysicalPrimeLogCharacterAmplitude_eq_dipoleInvSqTerm
      hA hactive (by omega)
  have hcoef : 0 ≤ A ^ 2 / (4 * Real.pi ^ 2) := by positivity
  rw [htsum]
  calc
    (N : ℝ) * ((A ^ 2 / (4 * Real.pi ^ 2)) *
        xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N) =
      (A ^ 2 / (4 * Real.pi ^ 2)) *
        ((N : ℝ) * xiPhysicalPrimeLogEndpointDipoleInvSqTail P A m k N) := by ring
    _ ≤ (A ^ 2 / (4 * Real.pi ^ 2)) *
        (4 * (N : ℝ) * xiPhysicalPrimeLogEndpointTotalWeight P *
          xiPhysicalPrimeLogEndpointDipoleChordMass P A m k) :=
      mul_le_mul_of_nonneg_left
        (natCast_mul_xiPhysicalPrimeLogEndpointDipoleInvSqTail_le P A m k N hN) hcoef

end

end RHTower
