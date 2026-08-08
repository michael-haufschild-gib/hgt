import GaloisForLFunctions.RHTower.MobiusCofactorAmplifiedToken
import GaloisForLFunctions.RHTower.MobiusReciprocalAllocationJacobian
import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# Whole-anchor arithmetic and physical-capacity conservation

This file isolates unconditional finite core of whole-anchor Route E audit.

* coprime multiplication adds exact three-prime token breadth;
* separated prime bands decode reservoir from physical terminal;
* Möbius parity reversal and cofactor gap scaling hold simultaneously;
* full reservoir representation mass is exact finite Euler product;
* every row-stochastic physical kernel obeys source-cardinality / terminal-cardinality
  column lower bound, independent of representation multiplicity.

Analytic global E3 count and moving-parameter asymptotics are separate results. No arithmetic
matching or cancellation hypothesis is introduced here.
-/

namespace RHTower

open Finset

/-- Prime factors of a natural number lying in the half-open reservoir band W < p <= Z. -/
def wholeAnchorReservoirBand (W Z n : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p => W < p ∧ p ≤ Z

/-- Coprime multiplication by an exact-three-prime token adds exactly three distinct prime
factors. -/
theorem wholeAnchorE3_primeFactorCard
    {t m : ℕ} (htm : t.Coprime m) (hm : m.primeFactors.card = 3) :
    (t * m).primeFactors.card = t.primeFactors.card + 3 := by
  rw [htm.primeFactors_mul, Finset.card_union_of_disjoint htm.disjoint_primeFactors, hm]

/-- Exact band decoding. If every reservoir prime lies in band and every token prime lies
outside it, band factors of physical product recover reservoir support exactly. -/
theorem wholeAnchorReservoirBand_mul_eq
    {W Z t m : ℕ} (htm : t.Coprime m)
    (htBand : ∀ p ∈ t.primeFactors, W < p ∧ p ≤ Z)
    (hmOutside : ∀ p ∈ m.primeFactors, ¬ (W < p ∧ p ≤ Z)) :
    wholeAnchorReservoirBand W Z (t * m) = t.primeFactors := by
  rw [wholeAnchorReservoirBand, htm.primeFactors_mul, Finset.filter_union]
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.1 hp with hpt | hpm
    · exact (Finset.mem_filter.1 hpt).1
    · obtain ⟨hpmem, hpBand⟩ := Finset.mem_filter.1 hpm
      exact False.elim (hmOutside p hpmem hpBand)
  · intro hpt
    apply Finset.mem_union_left
    exact Finset.mem_filter.2 ⟨hpt, htBand p hpt⟩

/-- Exact full-subset reciprocal reservoir mass. This identity counts allocation labels;
physical projection can only merge their terminal columns. -/
theorem wholeAnchor_fullReservoirMass_eq_eulerProduct (P : Finset ℕ) :
    ∑ R ∈ P.powerset, ∏ p ∈ R, 1 / (p : ℝ) =
      ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by
  exact (Finset.prod_one_add (R := ℝ) (f := fun p : ℕ => 1 / (p : ℝ)) P).symm

/-- Combined exact arithmetic packet used by whole-anchor construction: breadth, band decoding,
opposite Möbius sign, and cofactor-scaled physical displacement. -/
theorem wholeAnchorE3_exact_packet
    {u t m : ℕ} {W Z y h : ℝ}
    (htm : t.Coprime m)
    (hmCard : m.primeFactors.card = 3)
    (htBand : ∀ p ∈ t.primeFactors, (W : ℝ) < p ∧ (p : ℝ) ≤ Z)
    (hmOutside : ∀ p ∈ m.primeFactors, ¬ ((W : ℝ) < p ∧ (p : ℝ) ≤ Z))
    (htSign : mobiusComplexCoefficient t = mobiusComplexCoefficient u)
    (hmSign : mobiusComplexCoefficient m = -(1 : ℂ))
    (hmGap : |(m : ℝ) - y| ≤ h) :
    (t * m).primeFactors.card = t.primeFactors.card + 3 ∧
      (t * m).primeFactors.filter
          (fun p : ℕ => W < (p : ℝ) ∧ (p : ℝ) ≤ Z) = t.primeFactors ∧
      mobiusComplexCoefficient (t * m) = -mobiusComplexCoefficient u ∧
      |(t : ℝ) * m - (t : ℝ) * y| ≤ (t : ℝ) * h := by
  refine ⟨wholeAnchorE3_primeFactorCard htm hmCard, ?_, ?_, ?_⟩
  · rw [htm.primeFactors_mul, Finset.filter_union]
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.1 hp with hpt | hpm
      · exact (Finset.mem_filter.1 hpt).1
      · obtain ⟨hpmem, hpBand⟩ := Finset.mem_filter.1 hpm
        exact False.elim (hmOutside p hpmem hpBand)
    · intro hpt
      apply Finset.mem_union_left
      exact Finset.mem_filter.2 ⟨hpt, htBand p hpt⟩
  · exact mobiusCofactorToken_reverses htm htSign hmSign
  · exact abs_cofactor_scaled_gap_le (Nat.cast_nonneg t) hmGap

namespace FiniteRowStochasticKernel

variable {Anchor Target : Type*} [Fintype Anchor] [Fintype Target]
  (P : FiniteRowStochasticKernel Anchor Target)

/-- Exact capacity conservation under a uniform physical-column ceiling. -/
theorem card_anchor_le_columnCeiling_mul_card_target
    (C : ℝ) (hcolumn : ∀ v : Target, ∑ n : Anchor, P.weight n v ≤ C) :
    (Fintype.card Anchor : ℝ) ≤ C * Fintype.card Target := by
  calc
    (Fintype.card Anchor : ℝ) =
        ∑ v : Target, ∑ n : Anchor, P.weight n v := P.total_mass.symm
    _ ≤ ∑ _v : Target, C := Finset.sum_le_sum fun v _ => hcolumn v
    _ = C * Fintype.card Target := by
      simp [mul_comm]

/-- A terminal set strictly smaller than source set forces a physical column above unit load. -/
theorem exists_one_lt_column_of_card_target_lt
    [Nonempty Target]
    (hcard : Fintype.card Target < Fintype.card Anchor) :
    ∃ v : Target, 1 < ∑ n : Anchor, P.weight n v := by
  obtain ⟨v, hv⟩ := P.exists_average_le_column
  refine ⟨v, ?_⟩
  have hTarget : (0 : ℝ) < Fintype.card Target := by positivity
  have hratio :
      (1 : ℝ) < (Fintype.card Anchor : ℝ) / Fintype.card Target := by
    rw [lt_div_iff₀ hTarget]
    have hcardReal :
        (Fintype.card Target : ℝ) < Fintype.card Anchor := by
      exact_mod_cast hcard
    simpa using hcardReal
  exact hratio.trans_le hv

/-- Quantitative capacity conservation. If target cardinality is at most epsilon times source
cardinality, some physical column has load at least 1 / epsilon. -/
theorem exists_inv_epsilon_le_column_of_target_capacity
    [Nonempty Target] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hcapacity :
      (Fintype.card Target : ℝ) ≤ epsilon * Fintype.card Anchor) :
    ∃ v : Target, 1 / epsilon ≤ ∑ n : Anchor, P.weight n v := by
  obtain ⟨v, hv⟩ := P.exists_average_le_column
  refine ⟨v, ?_⟩
  have hTarget : (0 : ℝ) < Fintype.card Target := by positivity
  have hratio :
      1 / epsilon ≤ (Fintype.card Anchor : ℝ) / Fintype.card Target := by
    rw [div_le_div_iff₀ hepsilon hTarget]
    simpa [mul_comm] using hcapacity
  exact hratio.trans hv

/-- No row-stochastic physical kernel can have all column loads at most one when target
cardinality is strictly smaller than source cardinality. -/
theorem not_all_columns_le_one_of_card_target_lt
    [Nonempty Target]
    (hcard : Fintype.card Target < Fintype.card Anchor) :
    ¬ ∀ v : Target, ∑ n : Anchor, P.weight n v ≤ 1 := by
  obtain ⟨v, hv⟩ := P.exists_one_lt_column_of_card_target_lt hcard
  intro h
  exact (not_lt_of_ge (h v)) hv

end FiniteRowStochasticKernel

end RHTower
