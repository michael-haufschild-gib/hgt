import GaloisForLFunctions.HTGeometry.RatFuncOrderSquare
import GaloisForLFunctions.HTGeometry.RatFuncFieldShift

/-!
# A rational function whose shift differs from it by a square is a square

If `σf · g² = f` with `σ` the unit shift, then at every point the order of `f` and the order of its
shift differ by an even number.  Along one integer orbit the order of `f` vanishes from some index
on, because a rational function has finitely many zeros and poles; descending the orbit from there,
every order is obtained from the next by adding an even number.  So the order of `f` is even
everywhere, and over an algebraically closed field that makes `f` a square.

This is the global step that no degree count at infinity can supply: it uses the whole integer
orbit, not the point at infinity.

* `rootMultiplicity_comp_X_add_one`, `ratOrd_ratShift`;
* `finite_ratOrd_support`;
* `even_ratOrd_of_ratShift_mul_sq`;
* `isSquare_of_ratShift_mul_sq`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem rootMultiplicity_comp_X_add_one (P : Polynomial K) (c : K) :
    (P.comp (X + C 1)).rootMultiplicity c = P.rootMultiplicity (c + 1) := by
  have h := Polynomial.rootMultiplicity_comp_C_mul_X_add_C P (1 : K) 1 c isUnit_one
  simpa using h

omit [CharZero K] in
/-- **The shift moves the order along the orbit.** -/
theorem ratOrd_ratShift {g : RatFunc K} (hg : g ≠ 0) (c : K) :
    ratOrd (FieldShift.ratShift g) c = ratOrd g (c + 1) := by
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hA : g.num.comp (X + C 1) ≠ 0 := FieldShift.comp_X_add_C_one_ne_zero hnum
  have hB : g.denom.comp (X + C 1) ≠ 0 := FieldShift.comp_X_add_C_one_ne_zero hden
  have hrep : FieldShift.ratShift g
      * algebraMap (Polynomial K) (RatFunc K) (g.denom.comp (X + C 1))
      = algebraMap (Polynomial K) (RatFunc K) (g.num.comp (X + C 1)) := by
    have h := congrArg (FieldShift.ratShift (F := K)) (algebraMap_num_eq g)
    rw [map_mul, FieldShift.ratShift_algebraMap, FieldShift.ratShift_algebraMap] at h
    exact h.symm
  rw [ratOrd_of_rep hA hB hrep c, rootMultiplicity_comp_X_add_one,
    rootMultiplicity_comp_X_add_one, ratOrd]

omit [CharZero K] in
theorem finite_ratOrd_support {g : RatFunc K} (hg : g ≠ 0) :
    {c : K | ratOrd g c ≠ 0}.Finite := by
  classical
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  refine Set.Finite.subset
    ((Polynomial.finite_setOf_isRoot hnum).union (Polynomial.finite_setOf_isRoot hden)) ?_
  intro c hc
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hcon
  have h1 : g.num.rootMultiplicity c = 0 := by
    by_contra h
    exact hcon.1 ((Polynomial.rootMultiplicity_pos hnum).mp (Nat.pos_of_ne_zero h))
  have h2 : g.denom.rootMultiplicity c = 0 := by
    by_contra h
    exact hcon.2 ((Polynomial.rootMultiplicity_pos hden).mp (Nat.pos_of_ne_zero h))
  exact hc (by rw [ratOrd, h1, h2]; ring)

/-- **The order of `f` is even everywhere.** -/
theorem even_ratOrd_of_ratShift_mul_sq {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (heq : FieldShift.ratShift f * g ^ 2 = f) (c : K) : Even (ratOrd f c) := by
  classical
  have hsf : FieldShift.ratShift f ≠ 0 := by
    intro h0
    exact hf (FieldShift.ratShift_injective (by rw [h0, map_zero]))
  have hrel : ∀ a : K, ratOrd f (a + 1) + 2 * ratOrd g a = ratOrd f a := by
    intro a
    have h : ratOrd (FieldShift.ratShift f * g ^ 2) a = ratOrd f a := by rw [heq]
    rw [ratOrd_mul hsf (pow_ne_zero 2 hg) a, ratOrd_ratShift hf a,
      show g ^ 2 = g * g from sq g, ratOrd_mul hg hg a] at h
    omega
  set D : ℤ → ℤ := fun n => ratOrd f (c + (n : K)) with hD
  set E : ℤ → ℤ := fun n => ratOrd g (c + (n : K)) with hE
  have hrel' : ∀ n : ℤ, D (n + 1) + 2 * E n = D n := by
    intro n
    have h := hrel (c + (n : K))
    have hcast : c + (n : K) + 1 = c + (((n + 1 : ℤ)) : K) := by push_cast; ring
    rw [hcast] at h
    exact h
  have hfin : {m : ℤ | D m ≠ 0}.Finite := by
    have hinj : Function.Injective (fun m : ℤ => c + (m : K)) := by
      intro m n hmn
      have hc : (m : K) = (n : K) := by simpa using hmn
      exact_mod_cast hc
    exact Set.Finite.preimage hinj.injOn (finite_ratOrd_support hf)
  obtain ⟨N, hN⟩ := hfin.bddAbove
  set M : ℕ := (max N 0).toNat + 1 with hM
  have hMcast : (M : ℤ) = max N 0 + 1 := by
    rw [hM]
    push_cast
    rw [Int.toNat_of_nonneg (le_max_right N 0)]
  have hvanish : ∀ n : ℤ, (M : ℤ) ≤ n → D n = 0 := by
    intro n hn
    by_contra hne
    have hle : n ≤ N := hN hne
    have : N ≤ max N 0 := le_max_left N 0
    omega
  have hdesc : ∀ j : ℕ, Even (D ((M : ℤ) - (j : ℤ))) := by
    intro j
    induction j with
    | zero =>
        have harg : ((M : ℤ) - ((0 : ℕ) : ℤ)) = (M : ℤ) := by push_cast; ring
        rw [harg, hvanish _ le_rfl]
        exact ⟨0, rfl⟩
    | succ j ih =>
        have h := hrel' ((M : ℤ) - ((j : ℤ) + 1))
        have harg : (M : ℤ) - ((j : ℤ) + 1) + 1 = (M : ℤ) - (j : ℤ) := by ring
        rw [harg] at h
        have hval : D ((M : ℤ) - ((j : ℤ) + 1))
            = D ((M : ℤ) - (j : ℤ)) + 2 * E ((M : ℤ) - ((j : ℤ) + 1)) := by omega
        have hcast : (((j + 1 : ℕ)) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
        rw [hcast, hval]
        obtain ⟨t, ht⟩ := ih
        exact ⟨t + E ((M : ℤ) - ((j : ℤ) + 1)), by rw [ht]; ring⟩
  have hc := hdesc M
  have hzero : ((M : ℤ) - ((M : ℕ) : ℤ)) = 0 := by ring
  rw [hzero] at hc
  have hD0 : D 0 = ratOrd f c := by
    rw [hD]
    norm_num
  rwa [hD0] at hc

/-- **A rational function whose shift differs from it by a square is a square.** -/
theorem isSquare_of_ratShift_mul_sq [IsAlgClosed K] {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (heq : FieldShift.ratShift f * g ^ 2 = f) : IsSquare f :=
  isSquare_of_even_ratOrd hf (even_ratOrd_of_ratShift_mul_sq hf hg heq)

end GaloisForLFunctions.HTGeometry
