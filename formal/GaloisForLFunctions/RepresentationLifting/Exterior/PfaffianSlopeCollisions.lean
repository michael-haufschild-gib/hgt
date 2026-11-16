import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-!
# Arithmetic collisions of Pfaffian slopes

The rational slope `2d + 2a - 1 + choose(a,2)/d`, at positive integer `d`,
has coincident values exactly on pairs with `2de = choose(a,2)`.
Every fiber has at most two points. These collisions characterize singularity
of the modal Hankel matrix built from the slope nodes.
-/

open scoped BigOperators
open HTGeometry
namespace GaloisForLFunctions.RepresentationLifting.Exterior
noncomputable section

/-- The positive slope index is `d + 1`. -/
def pfaffianSlope (a d : ℕ) : ℚ :=
  2 * (d + 1 : ℚ) + 2 * a - 1 + (a.choose 2 : ℚ) / (d + 1)

theorem pfaffianSlope_collision (a d e : ℕ) :
    pfaffianSlope a d = pfaffianSlope a e ↔
      d = e ∨ a.choose 2 = 2 * (d + 1) * (e + 1) := by
  have hd : (d + 1 : ℚ) ≠ 0 := by positivity
  have he : (e + 1 : ℚ) ≠ 0 := by positivity
  have hf : (pfaffianSlope a d - pfaffianSlope a e) * ((d + 1 : ℚ) * (e + 1)) =
      ((d : ℚ) - e) * (2 * (d + 1) * (e + 1) - (a.choose 2 : ℚ)) := by
    unfold pfaffianSlope
    field_simp
    ring
  constructor
  · intro h
    have hz : ((d : ℚ) - e) * (2 * (d + 1) * (e + 1) - (a.choose 2 : ℚ)) = 0 := by
      rw [← hf, h, sub_self, zero_mul]
    rcases mul_eq_zero.mp hz with hde | hc
    · left
      exact_mod_cast sub_eq_zero.mp hde
    · right
      have hc' := (sub_eq_zero.mp hc).symm
      exact_mod_cast hc'
  · rintro (rfl | h)
    · rfl
    · have hc : (a.choose 2 : ℚ) = 2 * (d + 1) * (e + 1) := by exact_mod_cast h
      have hz : (pfaffianSlope a d - pfaffianSlope a e) * ((d + 1 : ℚ) * (e + 1)) = 0 := by
        rw [hf, hc, sub_self, mul_zero]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (mul_ne_zero hd he))

theorem pfaffianSlope_fiber_at_most_two (a d e f : ℕ) :
    (pfaffianSlope a d = pfaffianSlope a e ∧ pfaffianSlope a d = pfaffianSlope a f) →
      d = e ∨ d = f ∨ e = f := by
  rintro ⟨hde, hdf⟩
  rcases (pfaffianSlope_collision a d e).mp hde with h | he
  · exact Or.inl h
  rcases (pfaffianSlope_collision a d f).mp hdf with h | hf
  · exact Or.inr (Or.inl h)
  right; right
  have hcast : (2 * (d + 1) : ℚ) * (e + 1) = (2 * (d + 1) : ℚ) * (f + 1) := by
    exact_mod_cast he.symm.trans hf
  have heq := mul_left_cancel₀ (by positivity : (2 * (d + 1) : ℚ) ≠ 0) hcast
  have : (e : ℚ) = f := by linarith only [heq]
  exact_mod_cast this

/-- Nonzero modal weights and absence of arithmetic slope collisions are exact criteria. -/
theorem pfaffianSlope_hankel_nonsingular (a n : ℕ) (w : Fin n → ℚ) :
    (algebraicHankelMatrix (finiteModalSequence w (fun i => pfaffianSlope a i.val)) n).det ≠ 0 ↔
      (∀ i, w i ≠ 0) ∧
        ∀ i j : Fin n, i ≠ j → a.choose 2 ≠ 2 * (i.val + 1) * (j.val + 1) := by
  rw [det_algebraicHankelMatrix_finiteModalSequence]
  have hi : Function.Injective (fun i : Fin n => pfaffianSlope a i.val) ↔
      ∀ i j : Fin n, i ≠ j → a.choose 2 ≠ 2 * (i.val + 1) * (j.val + 1) := by
    constructor
    · intro hinj i j hij hc
      exact hij (hinj ((pfaffianSlope_collision a i.val j.val).mpr (Or.inr hc)))
    · intro hc i j heq
      rcases (pfaffianSlope_collision a i.val j.val).mp heq with h | h
      · exact Fin.ext h
      · by_contra hij
        exact hc i j hij h
  rw [mul_ne_zero_iff, pow_ne_zero_iff (by omega : 2 ≠ 0),
    Matrix.det_vandermonde_ne_zero_iff, hi, Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_const, and_comm]

#print axioms pfaffianSlope_collision
#print axioms pfaffianSlope_fiber_at_most_two
#print axioms pfaffianSlope_hankel_nonsingular

end
end GaloisForLFunctions.RepresentationLifting.Exterior
