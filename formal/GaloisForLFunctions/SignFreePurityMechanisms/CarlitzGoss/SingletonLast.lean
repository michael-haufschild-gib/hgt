import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DeficientOrder
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CyclicOrder
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.MinimalCounterexamples

/-!
# Singleton last parts of minimal nongreedy optima

Each last-part digit determines a deficient deletion coordinate. Two distinct
last-part digits would force opposite cyclic orders around the same larger
greedy digit. Cyclic orientation excludes this, so the optimal last part is
a single digit power.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s k : ℕ} [NeZero s] {S : Finset (Digit p)}

/-- If deleting any last-part digit together with a larger available digit crosses a
feasibility boundary, an optimal last part consists of a single digit. -/
theorem IsOptimal.last_eq_singleton_of_deficient_deletions
    {C D : DigitComposition p s (k + 2) S} (hC : C.IsOptimal) (hp : 2 ≤ p)
    {y : Digit p} (hy : y ∈ D.parts (Fin.last (k + 1)))
    (hbelow : ∀ z ∈ C.parts (Fin.last (k + 1)), z.1 < y.1)
    (hdef : ∀ x ∈ C.parts (Fin.last (k + 1)), ∃ h : ZMod s,
      inverseContent (p : ℚ)
        (fun j => (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (S \ {x, y}) j : ℚ)) h <
          ((k + 1 : ℕ) : ℚ)) :
    ∃ x : Digit p, C.parts (Fin.last (k + 1)) = {x} := by
  obtain ⟨x, hx⟩ := C.nonempty (Fin.last (k + 1))
  refine ⟨x, Subset.antisymm ?_ (singleton_subset_iff.mpr hx)⟩
  intro z hz
  apply mem_singleton.mpr
  by_contra hzx
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have htwo (h : ZMod s) :
      (p : ℤ) ^ ((x.1 : ZMod s) - h).val + (p : ℤ) ^ ((z.1 : ZMod s) - h).val ≤
        cyclicWeighted (p : ℤ) (C.content (Fin.last (k + 1))) h := by
    simp only [content, cyclicWeighted_tokenContent_at]
    have hsub : {x, z} ⊆ C.parts (Fin.last (k + 1)) := by
      intro t ht
      rcases mem_insert.mp ht with he | he
      · exact he.symm ▸ hx
      · exact (mem_singleton.mp he).symm ▸ hz
    have hh := sum_le_sum_of_subset_of_nonneg hsub
      (fun t _ _ => pow_nonneg (show (0 : ℤ) ≤ p by omega) (((t.1 : ZMod s) - h).val))
    rw [sum_insert (by simpa only [mem_singleton] using Ne.symm hzx), sum_singleton] at hh
    exact hh
  have hxy : x ≠ y := by
    intro he
    have hh := hbelow x hx
    rw [he] at hh
    exact lt_irrefl _ hh
  have hzy : z ≠ y := by
    intro he
    have hh := hbelow z hz
    rw [he] at hh
    exact lt_irrefl _ hh
  obtain ⟨h, hh⟩ := hdef x hx
  obtain ⟨r, hr⟩ := hdef z hz
  have hyx := hC.rotated_exponent_lt_of_deficient_deletion (D := D) hp hx hy hbelow h hh
  have hyz := hC.rotated_exponent_lt_of_deficient_deletion (D := D) hp hz hy hbelow r hr
  have hzlt : ((z.1 : ZMod s) - h).val < ((y.1 : ZMod s) - h).val := by
    have hupper := (C.weighted_last_eq_and_lt_of_deficient_deletion D hp hx hy hxy h hh).2
    have hsum := htwo h
    have hpw : (p : ℤ) ^ ((z.1 : ZMod s) - h).val <
        (p : ℤ) ^ ((y.1 : ZMod s) - h).val := by linarith only [hupper, hsum]
    by_contra hn
    exact (not_lt_of_ge (pow_le_pow_right₀ hpZ (le_of_not_gt hn))) hpw
  have hxlt : ((x.1 : ZMod s) - r).val < ((y.1 : ZMod s) - r).val := by
    have hupper := (C.weighted_last_eq_and_lt_of_deficient_deletion D hp hz hy hzy r hr).2
    have hsum := htwo r
    have hpw : (p : ℤ) ^ ((x.1 : ZMod s) - r).val <
        (p : ℤ) ^ ((y.1 : ZMod s) - r).val := by linarith only [hupper, hsum]
    by_contra hn
    exact (not_lt_of_ge (pow_le_pow_right₀ hpZ (le_of_not_gt hn))) hpw
  exact not_reversed_cyclic_order (z.1 : ZMod s) (x.1 : ZMod s) (y.1 : ZMod s)
    h r hzlt hyx ⟨hxlt, hyz⟩

/-- The last part of a minimal nongreedy optimum is a single digit power. -/
theorem last_eq_singleton_of_minimal
    {O G : DigitComposition p s (k + 2) S} (hp : 2 ≤ p)
    (hO : O.IsOptimal) (hG : G.IsGreedy) (hne : O.value ≠ G.value)
    (hmin : ∀ n (T : Finset (Digit p)) (A B : DigitComposition p s n T),
      A.IsOptimal → B.IsGreedy → A.value ≠ B.value →
      k + 2 ≤ n ∧ (n = k + 2 → S.card ≤ T.card)) :
    ∃ x : Digit p, O.parts (Fin.last (k + 1)) = {x} := by
  have hsep := last_residue_disjoint_of_minimal hp hO hG hne hmin
  obtain ⟨y, hy, hmax⟩ := exists_max_image (G.parts (Fin.last (k + 1))) Prod.fst
    (G.nonempty (Fin.last (k + 1)))
  have hbelow := hG.last_exponent_gt_of_disjoint_residues (C := O) hp hy hmax (by
    intro x hx z hz he
    exact hsep (x.1 : ZMod s) ⟨⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩,
      ⟨z, mem_filter.mpr ⟨hz, he.symm⟩⟩⟩)
  apply hO.last_eq_singleton_of_deficient_deletions (D := G) hp hy hbelow
  intro x hx
  exact exists_deficient_coordinate_of_minimal hp hO hmin hx (G.subset _ hy) hbelow

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.last_eq_singleton_of_minimal
