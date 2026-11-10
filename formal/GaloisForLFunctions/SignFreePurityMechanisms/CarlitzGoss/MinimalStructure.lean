import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.SingletonLast
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.NormalizedLast

/-!
# Structure of a normalized nongreedy optimum

Any counterexample reduces to an optimum whose last part is a single power.
The greedy last part contains a larger power, has the same zeroth cyclic
weight, and uses only residue representatives strictly below the singleton's.
All proper optimal parts have zeroth inverse coordinate one.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition
variable {p s : ℕ} [NeZero s]

/-- Any nongreedy optimum produces one with a singleton last part, a common zeroth
inverse coordinate, and a competing greedy last part supported below its residue. -/
theorem exists_singleton_normalized_counterexample (hp : 2 ≤ p)
    (hbad : ∃ (m : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s m S),
      O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value) :
    ∃ (k : ℕ) (S : Finset (Digit p)) (O G : DigitComposition p s (k + 2) S) (x y : Digit p),
      1 ≤ k ∧ 2 ≤ s ∧ O.IsOptimal ∧ G.IsGreedy ∧ O.value ≠ G.value ∧
      (∀ i : Fin (k + 1), inverseContent (p : ℚ) (fun j => (O.content i.castSucc j : ℚ)) 0 = 1) ∧
      O.parts (Fin.last (k + 1)) = {x} ∧ y ∈ G.parts (Fin.last (k + 1)) ∧
      x.1 < y.1 ∧ (∀ z ∈ G.parts (Fin.last (k + 1)), z.1 ≤ y.1) ∧
      cyclicWeighted (p : ℤ) (G.content (Fin.last (k + 1))) 0 = (p : ℤ) ^ (x.1 : ZMod s).val ∧
      (∀ z ∈ G.parts (Fin.last (k + 1)), (z.1 : ZMod s).val < (x.1 : ZMod s).val) := by
  obtain ⟨k, S, O, G, hk, hs, hO, hG, hne, hnorm, hmin⟩ :=
    exists_normalized_minimal_counterexample hp hbad
  obtain ⟨x, hx⟩ := last_eq_singleton_of_minimal hp hO hG hne hmin
  have hxO : x ∈ O.parts (Fin.last (k + 1)) := by rw [hx]; exact mem_singleton_self x
  have hsep := last_residue_disjoint_of_minimal hp hO hG hne hmin
  obtain ⟨y, hy, hmax⟩ := exists_max_image (G.parts (Fin.last (k + 1))) Prod.fst
    (G.nonempty (Fin.last (k + 1)))
  have hsep' : ∀ a ∈ O.parts (Fin.last (k + 1)), ∀ b ∈ G.parts (Fin.last (k + 1)),
      (a.1 : ZMod s) ≠ (b.1 : ZMod s) := by
    intro a ha b hb he
    exact hsep (a.1 : ZMod s) ⟨⟨a, mem_filter.mpr ⟨ha, rfl⟩⟩,
      ⟨b, mem_filter.mpr ⟨hb, he.symm⟩⟩⟩
  have hdeg := hG.last_exponent_gt_of_disjoint_residues (C := O) hp hy hmax hsep' x hxO
  have hyx : y ≠ x := by intro he; rw [he] at hdeg; exact lt_irrefl _ hdeg
  have heq := O.weighted_last_eq_of_singleton_normalized G hp hx hnorm hy hyx
  refine ⟨k, S, O, G, x, y, hk, hs, hO, hG, hne, hnorm, hx, hy, hdeg, hmax, heq, ?_⟩
  intro z hz
  have hpZ : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
  have hsum : (p : ℤ) ^ (z.1 : ZMod s).val ≤ (p : ℤ) ^ (x.1 : ZMod s).val := by
    rw [← heq]
    simp only [content, cyclicWeighted_tokenContent_at]
    simpa only [sub_zero] using
      (single_le_sum (fun t _ => pow_nonneg (show (0 : ℤ) ≤ p by omega)
        (((t.1 : ZMod s) - 0).val)) hz)
  have hle : (z.1 : ZMod s).val ≤ (x.1 : ZMod s).val := (pow_le_pow_iff_right₀ hpZ).mp hsum
  have hneq : (z.1 : ZMod s).val ≠ (x.1 : ZMod s).val := by
    intro he
    have hc : (z.1 : ZMod s) = (x.1 : ZMod s) := by
      calc
        (z.1 : ZMod s) = (((z.1 : ZMod s).val : ℕ) : ZMod s) := (ZMod.natCast_zmod_val _).symm
        _ = (((x.1 : ZMod s).val : ℕ) : ZMod s) := congrArg (fun n : ℕ => (n : ZMod s)) he
        _ = (x.1 : ZMod s) := ZMod.natCast_zmod_val _
    exact hsep' x hxO z hz hc.symm
  exact lt_of_le_of_ne hle hneq

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_singleton_normalized_counterexample
