import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadicalMass
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Rational-exponent subgroup reduction for weighted real-periodic phases. -/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

/-- Exponents whose positive real scale is rational form an additive subgroup. -/
def quantizationRationalExponents (r : ℝ) : AddSubgroup ℤ where
  carrier := {k | ∃ q : ℚ, (q : ℝ) = Real.exp ((k : ℝ) * Real.log r)}
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro a b ⟨q, hq⟩ ⟨s, hs⟩
    refine ⟨q * s, ?_⟩
    rw [Rat.cast_mul, hq, hs, ← Real.exp_add, Int.cast_add, add_mul]
  neg_mem' := by
    rintro a ⟨q, hq⟩
    refine ⟨q⁻¹, ?_⟩
    rw [Rat.cast_inv, hq, ← Real.exp_neg, Int.cast_neg, neg_mul]

/-- A nontrivial rational-exponent subgroup has a positive generator. -/
theorem quantization_rational_exponent_generator {r : ℝ} {N : ℕ}
    (hN : 0 < N) {q : ℚ} (hq : r ^ N = q) (hr : 0 < r) :
    ∃ a : ℤ, 0 < a ∧
      (∃ s : ℚ, (s : ℝ) = Real.exp ((a : ℝ) * Real.log r)) ∧
      ∀ k : ℤ, (∃ s : ℚ, (s : ℝ) = Real.exp ((k : ℝ) * Real.log r)) ↔ a ∣ k := by
  let H := quantizationRationalExponents r
  have hmem : (N : ℤ) ∈ H := by
    refine ⟨q, ?_⟩
    rw [Int.cast_natCast, Real.exp_nat_mul, Real.exp_log hr, hq]
  obtain ⟨g, hg⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp inferInstance
  have hg0 : g ≠ 0 := by
    intro he
    rw [← hg, Int.mem_zmultiples_iff, he, zero_dvd_iff] at hmem
    exact (Nat.cast_ne_zero.mpr hN.ne') hmem
  let a : ℤ := g.natAbs
  have ha : 0 < a := by dsimp [a]; exact_mod_cast Int.natAbs_pos.mpr hg0
  have hgen : AddSubgroup.zmultiples a = H := (Int.zmultiples_natAbs g).trans hg
  refine ⟨a, ha, ?_, ?_⟩
  · change a ∈ H
    rw [← hgen]
    exact AddSubgroup.mem_zmultiples a
  · intro k
    change k ∈ H ↔ a ∣ k
    rw [← hgen, Int.mem_zmultiples_iff]

/-- Reindex a weighted periodic series along its rational-exponent generator. -/
theorem quantization_periodic_reindex {r : ℝ} {a : ℤ} (ha : 0 < a)
    {q : ℚ} (hq : (q : ℝ) = Real.exp ((a : ℝ) * Real.log r))
    {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log r| / 2))
    (hs : ∀ k : ℤ, p k ≠ 0 → a ∣ k) :
    (Summable fun j : ℤ => ‖p (a * j)‖ *
      Real.exp (|2 * (j : ℝ) * Real.log (q : ℝ)| / 2)) ∧
    ∀ t : ℝ,
      (∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) =
        ∑' j : ℤ, p (a * j) *
          cexp (((2 * (j : ℝ) * Real.log (q : ℝ) * t : ℝ) : ℂ) * I) := by
  have hi : Function.Injective (fun j : ℤ => a * j) := mul_right_injective₀ ha.ne'
  have hlog : Real.log (q : ℝ) = (a : ℝ) * Real.log r := by rw [hq, Real.log_exp]
  have he (j : ℤ) : 2 * (a * j : ℤ) * Real.log r =
      2 * (j : ℝ) * Real.log (q : ℝ) := by rw [Int.cast_mul, hlog]; ring
  constructor
  · simpa only [Function.comp_def, he] using hp.comp_injective hi
  · intro t
    have hsupp : Function.support (fun k : ℤ =>
        p k * cexp (((2 * (k : ℝ) * Real.log r * t : ℝ) : ℂ) * I)) ⊆
        Set.range (fun j : ℤ => a * j) := by
      intro k hk
      have hk' : p k ≠ 0 := by
        intro hz
        exact hk (by simp only [hz, zero_mul])
      obtain ⟨j, hj⟩ := hs k hk'
      exact ⟨j, hj.symm⟩
    simpa only [he] using (hi.tsum_eq hsupp).symm

end RHTower.WeilSpectral
