import GaloisForLFunctions.HTGeometry.DiscreteValuationHaar
import Mathlib.Algebra.Order.Disjointed
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exact additive measures of nonarchimedean shells

Inverse uniformizer dilates of the integer ring exhaust the local field. Their
successive differences form a measurable partition, with measures determined
by the actual residue cardinality and the proved Haar scaling character.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

open MeasureTheory MeasureTheory.Measure
open scoped WithZero WithZeroMulInt Pointwise ENNReal NNReal

noncomputable section

variable (K : Type*) [Field K] [Valued K ℤᵐ⁰]
  [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)]

local instance : (Valued.v : Valuation K ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)
local instance : NormedField K := Valued.toNormedField K ℤᵐ⁰
local instance : ProperSpace K :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr inferInstance
local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩
local instance : IsDiscreteValuationRing (Integer K) :=
  (Valued.v : Valuation K ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

variable (π : Integer K) (hπ : Irreducible π)

/-- Radius `n` means the inverse `n`th uniformizer dilate of the integer ring. -/
def integralDilate (n : ℕ) : Set K :=
  (uniformizerUnit K π hπ)⁻¹ ^ n • ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K)

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
@[simp] theorem integralDilate_zero :
    integralDilate K π hπ 0 = ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) := by
  simp only [integralDilate, pow_zero, one_smul]

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem mem_integralDilate (n : ℕ) (x : K) :
    x ∈ integralDilate K π hπ n ↔
      (π : K) ^ n * x ∈ (Valued.v : Valuation K ℤᵐ⁰).integer := by
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  rw [integralDilate, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (Valued.v : Valuation K ℤᵐ⁰)
      ((π : K) ^ n * ((π : K)⁻¹ ^ n * y)) ≤ 1
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, one_mul]
    exact hy
  · intro hx
    refine ⟨(π : K) ^ n * x, hx, ?_⟩
    change (π : K)⁻¹ ^ n * ((π : K) ^ n * x) = x
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hπ0, one_pow, one_mul]

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem integralDilate_monotone : Monotone (integralDilate K π hπ) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  rw [mem_integralDilate] at hx ⊢
  simpa only [pow_succ', mul_assoc] using
    mul_mem π.2 hx

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem integralDilate_isOpen (n : ℕ) : IsOpen (integralDilate K π hπ n) := by
  have he : integralDilate K π hπ n =
      (fun x : K => (π : K) ^ n * x) ⁻¹'
        ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) := by
    ext x
    exact mem_integralDilate K π hπ n x
  rw [he]
  exact (Valued.isOpen_valuationSubring K).preimage (continuous_const.mul continuous_id)

omit [CompactSpace (Integer K)] in
/-- Every field element has a finite denominator power of a uniformizer. -/
theorem exists_mem_integralDilate (x : K) : ∃ n, x ∈ integralDilate K π hπ n := by
  by_cases hx : x ∈ (Valued.v : Valuation K ℤᵐ⁰).integer
  · refine ⟨0, ?_⟩
    rw [integralDilate_zero]
    exact hx
  have hxv : 1 < (Valued.v : Valuation K ℤᵐ⁰) x := lt_of_not_ge hx
  have hx0 : x ≠ 0 := by
    intro h
    simp only [h, map_zero, not_lt_zero] at hxv
  have hi : (Valued.v : Valuation K ℤᵐ⁰) x⁻¹ ≤ 1 := by
    rw [map_inv₀]
    exact inv_le_one₀ (zero_lt_one.trans hxv) |>.mpr hxv.le
  let r : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring := ⟨x⁻¹, hi⟩
  have hr : r ≠ 0 := fun h => inv_ne_zero hx0 (congrArg Subtype.val h)
  have huni : (Valued.v : Valuation K ℤᵐ⁰).IsUniformizer (π : K) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span _ hπ.maximalIdeal_eq
  obtain ⟨n, u, hu⟩ := Valuation.exists_pow_Uniformizer hr
    (⟨π, huni⟩ : (Valued.v : Valuation K ℤᵐ⁰).Uniformizer)
  refine ⟨n, (mem_integralDilate K π hπ n x).mpr ?_⟩
  have he : x⁻¹ = (π : K) ^ n * (u : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) := hu
  have hu0 : ((u : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) : K) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  have he' : (π : K) ^ n * x =
      (((u⁻¹ : (Valued.v : Valuation K ℤᵐ⁰).valuationSubringˣ) :
        (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) : K) := by
    have huinv :
        (((u⁻¹ : (Valued.v : Valuation K ℤᵐ⁰).valuationSubringˣ) :
          (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) : K) =
          (((u : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) : K))⁻¹ := by
      apply mul_right_cancel₀ hu0
      rw [inv_mul_cancel₀ hu0]
      exact congrArg
        (fun z : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring => (z : K))
        (Units.inv_mul u)
    rw [huinv]
    apply mul_right_cancel₀ hu0
    rw [inv_mul_cancel₀ hu0]
    calc
      (π : K) ^ n * x * (u : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring) =
          ((π : K) ^ n * (u : (Valued.v : Valuation K ℤᵐ⁰).valuationSubring)) * x := by ring
      _ = 1 := by rw [← he, inv_mul_cancel₀ hx0]
  rw [he']
  exact (u⁻¹).val.2

omit [CompactSpace (Integer K)] in
theorem iUnion_integralDilate : (⋃ n, integralDilate K π hπ n) = Set.univ := by
  exact Set.eq_univ_of_forall (fun x => Set.mem_iUnion.mpr (exists_mem_integralDilate K π hπ x))

/-- Haar measure of every inverse uniformizer dilate is its exact residue-field power. -/
theorem measure_integralDilate (n : ℕ) :
    normalizedHaar K (integralDilate K π hπ n) = (Nat.card (Residue K) : ℝ≥0∞) ^ n := by
  rw [integralDilate, ← distribHaarChar_mul (normalizedHaar K),
    normalizedHaar_integer, mul_one, map_pow, map_inv,
    uniformizer_distribHaarChar, inv_inv, ENNReal.coe_pow, ENNReal.coe_natCast]

/-- The disjoint valuation shells include the integer ring as shell zero. -/
def valuationShell (n : ℕ) : Set K := disjointed (integralDilate K π hπ) n

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem valuationShell_measurable (n : ℕ) : MeasurableSet (valuationShell K π hπ n) :=
  MeasurableSet.disjointed (fun n => (integralDilate_isOpen K π hπ n).measurableSet) n

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem valuationShell_disjoint :
    Pairwise (fun m n => Disjoint (valuationShell K π hπ m) (valuationShell K π hπ n)) :=
  disjoint_disjointed _

omit [CompactSpace (Integer K)] in
theorem iUnion_valuationShell : (⋃ n, valuationShell K π hπ n) = Set.univ := by
  change (⋃ n, disjointed (integralDilate K π hπ) n) = Set.univ
  rw [iUnion_disjointed, iUnion_integralDilate]

@[simp] theorem measure_valuationShell_zero :
    normalizedHaar K (valuationShell K π hπ 0) = 1 := by
  simp only [valuationShell, disjointed_zero, integralDilate_zero, normalizedHaar_integer]

theorem measure_valuationShell_succ (n : ℕ) :
    normalizedHaar K (valuationShell K π hπ (n + 1)) =
      (Nat.card (Residue K) : ℝ≥0∞) ^ (n + 1) - (Nat.card (Residue K) : ℝ≥0∞) ^ n := by
  rw [valuationShell, (integralDilate_monotone K π hπ).disjointed_add_one]
  calc
    _ = normalizedHaar K (integralDilate K π hπ (n + 1)) -
        normalizedHaar K (integralDilate K π hπ n) := by
      exact measure_sdiff (integralDilate_monotone K π hπ (Nat.le_succ n))
        (integralDilate_isOpen K π hπ n).measurableSet.nullMeasurableSet
        (by rw [measure_integralDilate]; finiteness)
    _ = _ := by rw [measure_integralDilate, measure_integralDilate]

end
end GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

