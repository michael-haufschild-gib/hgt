import GaloisForLFunctions.RHTower.SoninEulerFiniteL2Lower
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Reciprocal-prime pair energy of the canonical Xi seam

The two-particle Sonin route naturally controls finite sums of

`|a_p-a_q|^(2 : ℕ) / (p q)`.

This module proves the exact arithmetic endpoint of that route.  Uniform boundedness of those
finite pair energies forces every prime potential to be equal, because the reciprocal-prime
measure has infinite mass.  Applied to the canonical FE--Schwarz seam potential, cofinal decay
then identifies bounded pair energy with the critical-line equation.  Over the complete Xi
divisor this condition is equivalent to RH.

No operator-side upper bound is asserted here.  The remaining source problem is to construct the
two-particle Sonin operator whose uniform Calkin estimate supplies the bounded-energy premise.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The reciprocal-prime weighted difference row based at one prime. -/
def primePairDifferenceRow (a : Nat.Primes → ℂ) (p : Nat.Primes)
    (s : Finset Nat.Primes) : ℝ :=
  ∑ q ∈ s, ‖a p - a q‖ ^ (2 : ℕ) / (q : ℝ)

/-- The ordered finite reciprocal-prime pair energy of a prime-indexed potential. -/
def primePairDifferenceEnergy (a : Nat.Primes → ℂ)
    (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, primePairDifferenceRow a p s / (p : ℝ)

/-- One common finite upper bound controls every finite reciprocal-prime pair energy. -/
def PrimePairDifferenceEnergyBounded (a : Nat.Primes → ℂ) : Prop :=
  ∃ B : ℝ, ∀ s : Finset Nat.Primes, primePairDifferenceEnergy a s ≤ B

private theorem norm_sub_sq_le_two_add_two (x y z : ℂ) :
    ‖x - y‖ ^ (2 : ℕ) ≤ 2 * ‖x - z‖ ^ (2 : ℕ) + 2 * ‖y - z‖ ^ (2 : ℕ) := by
  have hnorm : ‖x - y‖ ≤ ‖x - z‖ + ‖y - z‖ := by
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ = ‖x - z‖ + ‖y - z‖ :=
        congrArg (fun u : ℝ => ‖x - z‖ + u) (norm_sub_rev z y)
  have hsq : ‖x - y‖ ^ (2 : ℕ) ≤ (‖x - z‖ + ‖y - z‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  nlinarith [sq_nonneg (‖x - z‖ - ‖y - z‖)]

/-- Every finite difference row is nonnegative. -/
theorem primePairDifferenceRow_nonneg (a : Nat.Primes → ℂ)
    (p : Nat.Primes) (s : Finset Nat.Primes) :
    0 ≤ primePairDifferenceRow a p s := by
  unfold primePairDifferenceRow
  apply Finset.sum_nonneg
  intro q hq
  exact div_nonneg (sq_nonneg _) (by exact_mod_cast q.prop.pos.le)

/-- Every finite pair energy is nonnegative. -/
theorem primePairDifferenceEnergy_nonneg (a : Nat.Primes → ℂ)
    (s : Finset Nat.Primes) :
    0 ≤ primePairDifferenceEnergy a s := by
  unfold primePairDifferenceEnergy
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (primePairDifferenceRow_nonneg a p s)
    (by exact_mod_cast p.prop.pos.le)

/-- Enlarging the finite prime set can only increase a fixed difference row. -/
theorem primePairDifferenceRow_mono (a : Nat.Primes → ℂ)
    (p : Nat.Primes) {s t : Finset Nat.Primes} (hst : s ⊆ t) :
    primePairDifferenceRow a p s ≤ primePairDifferenceRow a p t := by
  unfold primePairDifferenceRow
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (by
    intro q hqt hqs
    exact div_nonneg (sq_nonneg _) (by exact_mod_cast q.prop.pos.le))

/-- A row occurring in a finite pair energy is bounded by its prime scale times the total
energy. -/
theorem primePairDifferenceRow_le_prime_mul_energy
    (a : Nat.Primes → ℂ) {p : Nat.Primes} {s : Finset Nat.Primes}
    (hp : p ∈ s) :
    primePairDifferenceRow a p s ≤
      (p : ℝ) * primePairDifferenceEnergy a s := by
  have hsingle : primePairDifferenceRow a p s / (p : ℝ) ≤
      primePairDifferenceEnergy a s := by
    unfold primePairDifferenceEnergy
    refine Finset.single_le_sum
      (s := s) (f := fun q : Nat.Primes =>
        primePairDifferenceRow a q s / (q : ℝ)) ?_ hp
    intro q hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.prop.pos
    exact div_nonneg (primePairDifferenceRow_nonneg a q s) hqpos.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have h := (div_le_iff₀ hp0).mp hsingle
  nlinarith

/-- The triangle inequality converts a common pair difference into the two corresponding
reciprocal-prime rows. -/
theorem primePairDifference_weighted_triangle
    (a : Nat.Primes → ℂ) (p r : Nat.Primes) (s : Finset Nat.Primes) :
    ‖a p - a r‖ ^ (2 : ℕ) * (∑ q ∈ s, 1 / (q : ℝ)) ≤
      2 * primePairDifferenceRow a p s +
        2 * primePairDifferenceRow a r s := by
  calc
    ‖a p - a r‖ ^ (2 : ℕ) * (∑ q ∈ s, 1 / (q : ℝ)) =
        ∑ q ∈ s, ‖a p - a r‖ ^ (2 : ℕ) / (q : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [div_eq_mul_inv]
      ring
    _ ≤ ∑ q ∈ s,
        (2 * ‖a p - a q‖ ^ (2 : ℕ) / (q : ℝ) +
          2 * ‖a r - a q‖ ^ (2 : ℕ) / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q _
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast q.prop.pos.le
      simpa only [add_div] using div_le_div_of_nonneg_right
        (norm_sub_sq_le_two_add_two (a p) (a r) (a q)) hq0
    _ = 2 * primePairDifferenceRow a p s +
        2 * primePairDifferenceRow a r s := by
      simp only [Finset.sum_add_distrib, primePairDifferenceRow]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro q _
        ring
      · apply Finset.sum_congr rfl
        intro q _
        ring

/-- Bounded reciprocal-prime pair energy forces equality of every two prime potentials. -/
theorem primePairDifference_eq_of_energyBounded
    {a : Nat.Primes → ℂ} (hbounded : PrimePairDifferenceEnergyBounded a)
    (p r : Nat.Primes) : a p = a r := by
  obtain ⟨B, hB⟩ := hbounded
  have hB0 : 0 ≤ B :=
    (primePairDifferenceEnergy_nonneg a ∅).trans (hB ∅)
  by_contra hne
  have hnorm : 0 < ‖a p - a r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsq : 0 < ‖a p - a r‖ ^ (2 : ℕ) := sq_pos_of_pos hnorm
  let threshold : ℝ :=
    2 * ((p : ℝ) + (r : ℝ)) * B / ‖a p - a r‖ ^ (2 : ℕ)
  obtain ⟨s, hs⟩ := exists_finset_primes_sum_one_div_gt threshold
  let t : Finset Nat.Primes := insert p (insert r s)
  have hst : s ⊆ t := by
    intro q hq
    simp [t, hq]
  have hpt : p ∈ t := by simp [t]
  have hrt : r ∈ t := by simp [t]
  have hrowp : primePairDifferenceRow a p s ≤ (p : ℝ) * B :=
    (primePairDifferenceRow_mono a p hst).trans
      ((primePairDifferenceRow_le_prime_mul_energy a hpt).trans
        (mul_le_mul_of_nonneg_left (hB t) (by positivity)))
  have hrowr : primePairDifferenceRow a r s ≤ (r : ℝ) * B :=
    (primePairDifferenceRow_mono a r hst).trans
      ((primePairDifferenceRow_le_prime_mul_energy a hrt).trans
        (mul_le_mul_of_nonneg_left (hB t) (by positivity)))
  have hupper :
      ‖a p - a r‖ ^ (2 : ℕ) * (∑ q ∈ s, 1 / (q : ℝ)) ≤
        2 * ((p : ℝ) + (r : ℝ)) * B := by
    calc
      ‖a p - a r‖ ^ (2 : ℕ) * (∑ q ∈ s, 1 / (q : ℝ)) ≤
          2 * primePairDifferenceRow a p s +
            2 * primePairDifferenceRow a r s :=
        primePairDifference_weighted_triangle a p r s
      _ ≤ 2 * ((p : ℝ) + (r : ℝ)) * B := by nlinarith
  have hlower :
      2 * ((p : ℝ) + (r : ℝ)) * B <
        ‖a p - a r‖ ^ (2 : ℕ) * (∑ q ∈ s, 1 / (q : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_left hs hsq
    dsimp only [threshold] at hmul
    field_simp [hsq.ne'] at hmul
    nlinarith
  exact (not_lt_of_ge hupper) hlower

/-- A prime potential has bounded reciprocal-prime pair energy exactly when it is constant. -/
theorem primePairDifferenceEnergyBounded_iff_constant
    (a : Nat.Primes → ℂ) :
    PrimePairDifferenceEnergyBounded a ↔ ∃ c : ℂ, ∀ p, a p = c := by
  constructor
  · intro h
    refine ⟨a ⟨2, by norm_num⟩, ?_⟩
    intro p
    exact primePairDifference_eq_of_energyBounded h p ⟨2, by norm_num⟩
  · rintro ⟨c, hc⟩
    refine ⟨0, ?_⟩
    intro s
    have hzero : primePairDifferenceEnergy a s = 0 := by
      simp [primePairDifferenceEnergy, primePairDifferenceRow, hc]
    rw [hzero]

/-- Reciprocal-prime pair-energy boundedness for the canonical FE--Schwarz seam on one strip
fibre. -/
def OrbitwisePrimeSeamPairEnergyBounded (rho : ℂ) : Prop :=
  PrimePairDifferenceEnergyBounded
    (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho)

/-- The critical line is exactly the bounded pair-energy locus of the canonical prime seam. -/
theorem orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    OrbitwisePrimeSeamPairEnergyBounded rho ↔ rho.re = 1 / 2 := by
  constructor
  · intro hbounded
    apply (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mp
    intro p q hp hq
    exact primePairDifference_eq_of_energyBounded hbounded
      ⟨p, hp⟩ ⟨q, hq⟩
  · intro hre
    have hcoh : OrbitwisePrimeSeamChargesCoherent rho :=
      (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half hstrip).mpr hre
    apply (primePairDifferenceEnergyBounded_iff_constant
      (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho)).mpr
    refine ⟨orbitwiseNatPrimeSeamCharge 2 rho, ?_⟩
    intro p
    exact hcoh (p : ℕ) 2 p.prop (by norm_num)

/-- Positive no-go: every off-line strip fibre has arbitrarily large finite reciprocal-prime
pair energy. -/
theorem orbitwisePrimeSeamPairEnergy_unbounded_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hoff : rho.re ≠ 1 / 2) :
    ∀ B : ℝ, ∃ s : Finset Nat.Primes,
      B < primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s := by
  have hnot : ¬ OrbitwisePrimeSeamPairEnergyBounded rho := by
    intro hbounded
    exact hoff ((orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half hstrip).mp hbounded)
  intro B
  by_contra hnone
  apply hnot
  refine ⟨B, ?_⟩
  intro s
  exact le_of_not_gt (fun hgt => hnone ⟨s, hgt⟩)

/-- Bounded pair energy on every Xi divisor fibre. -/
def XiPrimeSeamPairEnergyBounded : Prop :=
  ∀ rho : XiDivisorSupport, OrbitwisePrimeSeamPairEnergyBounded (rho : ℂ)

/-- Exact pair-energy criterion for RH. -/
theorem xiPrimeSeamPairEnergyBounded_iff_riemannHypothesis :
    XiPrimeSeamPairEnergyBounded ↔ RiemannHypothesis := by
  constructor
  · intro hbounded
    apply riemannHypothesis_of_xiPrimeSeamChargesCoherent
    intro rho
    apply (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mp (hbounded rho)
  · intro hRH rho
    apply (orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mp
        (xiPrimeSeamChargesCoherent_iff_riemannHypothesis.mpr hRH rho)

/-- Contradiction form: if RH fails, one actual Xi divisor fibre has unbounded finite pair
energy. -/
theorem exists_xiPrimeSeamPairEnergy_unbounded_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ rho : XiDivisorSupport, ∀ B : ℝ, ∃ s : Finset Nat.Primes,
      B < primePairDifferenceEnergy
        (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) (rho : ℂ)) s := by
  have hnot : ¬ XiPrimeSeamPairEnergyBounded := by
    intro hbounded
    exact hRH (xiPrimeSeamPairEnergyBounded_iff_riemannHypothesis.mp hbounded)
  simp only [XiPrimeSeamPairEnergyBounded] at hnot
  push Not at hnot
  obtain ⟨rho, hrho⟩ := hnot
  refine ⟨rho, ?_⟩
  have hoff : (rho : ℂ).re ≠ 1 / 2 := by
    intro hre
    exact hrho ((orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).mpr hre)
  exact orbitwisePrimeSeamPairEnergy_unbounded_of_re_ne_half
    (xi_divisor_support_re_mem_open_unit rho) hoff

end

end RHTower
