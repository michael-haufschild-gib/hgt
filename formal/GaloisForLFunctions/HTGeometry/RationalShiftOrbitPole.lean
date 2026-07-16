import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# A rational shift coboundary cannot have one pole on an orbit

This is the arbitrary-center, arbitrary-denominator form of the pole obstruction used by the
multi-orbit Gamma charge theorem.  If `A/B` has a genuine pole at `a` and `B` has no other zero on
`a + Z`, it cannot equal `w(X+1)-w(X)` for a rational function `w`.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial nonZeroDivisors

/-- **Single-orbit rational shift obstruction.** -/
theorem ratShift_sub_ne_of_single_orbit_pole
    (a : ℂ) {A B : Polynomial ℂ}
    (hB : B ≠ 0) (hAa : A.eval a ≠ 0)
    (hBorbit : ∀ n : ℤ, B.eval (a + (n : ℂ)) = 0 ↔ n = 0)
    (w : RatFunc ℂ) :
    ratShift w - w ≠
      algebraMap (Polynomial ℂ) (RatFunc ℂ) A /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) B := by
  intro h
  let p := w.num
  let q := w.denom
  have hq : q ≠ 0 := w.denom_ne_zero
  have hco : IsCoprime p q := w.isCoprime_num_denom
  have hpz : ∀ z : ℂ, q.eval z = 0 → p.eval z ≠ 0 := by
    intro z hqz hpz
    obtain ⟨u, v, huv⟩ := hco
    have he := congrArg (Polynomial.eval z) huv
    simp only [eval_add, eval_mul, eval_one, hpz, hqz, mul_zero, add_zero] at he
    exact one_ne_zero he.symm
  have hqK : algebraMap (Polynomial ℂ) (RatFunc ℂ) q ≠ 0 := fun h0 =>
    hq (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hqcK : algebraMap (Polynomial ℂ) (RatFunc ℂ)
      (q.comp (X + C 1)) ≠ 0 := fun h0 =>
    comp_X_add_C_one_ne_zero hq
      (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hBK : algebraMap (Polynomial ℂ) (RatFunc ℂ) B ≠ 0 := fun h0 =>
    hB (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hw : algebraMap (Polynomial ℂ) (RatFunc ℂ) p /
      algebraMap (Polynomial ℂ) (RatFunc ℂ) q = w :=
    RatFunc.num_div_denom w
  have hshiftw : ratShift w =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (X + C 1)) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.comp (X + C 1)) := by
    rw [← hw, map_div₀, ratShift_algebraMap, ratShift_algebraMap]
  have hcross :
      B * (p.comp (X + C 1) * q - p * q.comp (X + C 1)) =
        A * (q * q.comp (X + C 1)) := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul]
    rw [hshiftw, ← hw] at h
    field_simp at h
    linear_combination h
  have hnoint : ∀ n : ℤ, q.eval (a + (n : ℂ)) ≠ 0 := by
    by_contra hcon
    simp only [not_forall, ne_eq, not_not] at hcon
    obtain ⟨n₀, hn₀⟩ := hcon
    have hfin : {n : ℤ | q.eval (a + (n : ℂ)) = 0}.Finite := by
      have hroots : {z : ℂ | q.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hq
      exact Set.Finite.preimage (fun x _ y _ hxy => by
        have := congrArg (fun z : ℂ => z - a) hxy
        have hcast : (x : ℂ) = (y : ℂ) := by simpa using this
        exact Int.cast_injective hcast) hroots
    have hne : hfin.toFinset.Nonempty := ⟨n₀, by simpa using hn₀⟩
    let M : ℤ := hfin.toFinset.max' hne
    let mu : ℤ := hfin.toFinset.min' hne
    have hMroot : q.eval (a + (M : ℂ)) = 0 := by
      have := hfin.toFinset.max'_mem hne
      simpa [M] using this
    have hmuroot : q.eval (a + (mu : ℂ)) = 0 := by
      have := hfin.toFinset.min'_mem hne
      simpa [mu] using this
    have hM1 : q.eval (a + ((M + 1 : ℤ) : ℂ)) ≠ 0 := by
      intro hr
      have hmem : M + 1 ∈ hfin.toFinset := by simpa using hr
      have := hfin.toFinset.le_max' _ hmem
      omega
    have hmu1 : q.eval (a + ((mu - 1 : ℤ) : ℂ)) ≠ 0 := by
      intro hr
      have hmem : mu - 1 ∈ hfin.toFinset := by simpa using hr
      have := hfin.toFinset.min'_le _ hmem
      omega
    have hMzero : M = 0 := by
      have he := congrArg (Polynomial.eval (a + (M : ℂ))) hcross
      simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_C] at he
      have hcast : a + (M : ℂ) + 1 = a + ((M + 1 : ℤ) : ℂ) := by
        push_cast
        ring
      rw [hMroot, hcast] at he
      simp only [mul_zero, zero_mul, zero_sub, mul_neg] at he
      have hBzero : B.eval (a + (M : ℂ)) = 0 := by
        rcases mul_eq_zero.mp (neg_eq_zero.mp he) with hBz | hrest
        · exact hBz
        · exact absurd hrest (mul_ne_zero (hpz _ hMroot) hM1)
      exact (hBorbit M).mp hBzero
    have hmuone : mu = 1 := by
      have he := congrArg (Polynomial.eval (a + ((mu - 1 : ℤ) : ℂ))) hcross
      simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_C] at he
      have hcast : a + ((mu - 1 : ℤ) : ℂ) + 1 = a + (mu : ℂ) := by
        push_cast
        ring
      rw [hcast, hmuroot] at he
      simp only [mul_zero, sub_zero] at he
      have hBzero : B.eval (a + ((mu - 1 : ℤ) : ℂ)) = 0 := by
        rcases mul_eq_zero.mp he with hBz | hrest
        · exact hBz
        · exact absurd hrest (mul_ne_zero (hpz _ hmuroot) hmu1)
      have hz := (hBorbit (mu - 1)).mp hBzero
      omega
    have hle := hfin.toFinset.min'_le _ (hfin.toFinset.max'_mem hne)
    omega
  have hqa : q.eval a ≠ 0 := by simpa using hnoint 0
  have hqa1 : q.eval (a + 1) ≠ 0 := by simpa using hnoint 1
  have he := congrArg (Polynomial.eval a) hcross
  simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_C] at he
  have hBa : B.eval a = 0 := by
    have := (hBorbit 0).mpr rfl
    simpa using this
  rw [hBa, zero_mul] at he
  exact mul_ne_zero hAa (mul_ne_zero hqa hqa1) he.symm

end

end GaloisForLFunctions
