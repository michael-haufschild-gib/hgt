import Mathlib

/-!
# Drift propagates total ramification

A primitive of a periodic entire function with nonzero additive period drift satisfies
`W(z + T) = W(z) + C`.  Differentiating shows `W'` is `T`-periodic, and the drift identity moves
every `a`-point to an `(a + nC)`-point.  Consequently a single totally ramified value produces the
whole arithmetic progression `a + Cℤ` of totally ramified values — arbitrarily many of them.

* `TotallyRamified` — every `a`-point of `f` is a critical point.
* `drift_zsmul`, `deriv_drift_periodic` — the drift identity and the periodicity of `W'`.
* `totallyRamified_add_zsmul` — the propagation.
* `exists_finset_totallyRamified_card_ge` — arbitrarily large finite sets of totally ramified
  values, the exact input the Nevanlinna ramification bound contradicts.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Total ramification.**  Every `a`-point of `f` is a critical point, so every solution of
`f z = a` is a multiple root. -/
def TotallyRamified (f : ℂ → ℂ) (a : ℂ) : Prop := ∀ z : ℂ, f z = a → deriv f z = 0

variable {W : ℂ → ℂ} {T C : ℂ}

/-- The drift identity iterated over the integers. -/
theorem drift_zsmul (hdrift : ∀ z, W (z + T) = W z + C) (z : ℂ) :
    ∀ n : ℤ, W (z + n • T) = W z + n • C := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hstep : W (z + ((k : ℤ) + 1) • T) = W (z + (k : ℤ) • T + T) := by
        congr 1
        ring
      rw [hstep, hdrift, ih]
      ring
  | pred k ih =>
      have hstep : W (z + (-(k : ℤ) - 1) • T + T) = W (z + (-(k : ℤ)) • T) := by
        congr 1
        ring
      have hd := hdrift (z + (-(k : ℤ) - 1) • T)
      rw [hstep, ih] at hd
      rw [← sub_eq_iff_eq_add] at hd
      rw [← hd]
      simp only [zsmul_eq_mul]
      push_cast
      ring

/-- **The derivative is periodic.**  Differentiating `W(z+T) = W(z)+C` removes the drift. -/
theorem deriv_drift_periodic (hdrift : ∀ z, W (z + T) = W z + C) (z : ℂ) :
    deriv W (z + T) = deriv W z := by
  have hfun : (fun w : ℂ => W (w + T)) = fun w : ℂ => W w + C := funext hdrift
  have h1 : deriv (fun w : ℂ => W (w + T)) z = deriv W (z + T) := deriv_comp_add_const W T z
  have h2 : deriv (fun w : ℂ => W w + C) z = deriv W z := deriv_add_const C
  rw [← h1, hfun, h2]

/-- The derivative is periodic along the whole lattice `Tℤ`. -/
theorem deriv_drift_zsmul (hdrift : ∀ z, W (z + T) = W z + C) (z : ℂ) :
    ∀ n : ℤ, deriv W (z + n • T) = deriv W z := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hstep : z + ((k : ℤ) + 1) • T = (z + (k : ℤ) • T) + T := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [hstep, deriv_drift_periodic hdrift, ih]
  | pred k ih =>
      have hstep : (z + (-(k : ℤ) - 1) • T) + T = z + (-(k : ℤ)) • T := by
        simp only [zsmul_eq_mul]; push_cast; ring
      have h := deriv_drift_periodic (W := W) (T := T) (C := C) hdrift (z + (-(k : ℤ) - 1) • T)
      rw [hstep, ih] at h
      exact h.symm

/-- **Drift propagates total ramification.**  If `W(z+T) = W(z)+C` and `a` is totally ramified,
then so is `a + nC` for every integer `n`. -/
theorem totallyRamified_add_zsmul (hdrift : ∀ z, W (z + T) = W z + C)
    {a : ℂ} (ha : TotallyRamified W a) (n : ℤ) :
    TotallyRamified W (a + n • C) := by
  intro z hz
  have hshift : W (z + (-n) • T) = a := by
    have h := drift_zsmul (W := W) (T := T) (C := C) hdrift z (-n)
    rw [h, hz]
    simp
  have hcrit : deriv W (z + (-n) • T) = 0 := ha _ hshift
  have hper := deriv_drift_zsmul (W := W) (T := T) (C := C) hdrift z (-n)
  rw [hper] at hcrit
  exact hcrit

/-- The drifted values are pairwise distinct when the drift is nonzero. -/
theorem drift_values_injective (hC : C ≠ 0) {a : ℂ} :
    Function.Injective (fun n : ℤ => a + n • C) := by
  intro m n hmn
  simp only [zsmul_eq_mul, add_right_inj] at hmn
  have hcast : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ hC hmn
  exact_mod_cast hcast

/-- **Arbitrarily many totally ramified values.**  A single totally ramified value of a drifting
periodic primitive already forces, for every `N`, a set of `N` distinct totally ramified finite
values. -/
theorem exists_finset_totallyRamified_card_ge (hC : C ≠ 0)
    (hdrift : ∀ z, W (z + T) = W z + C) {a : ℂ} (ha : TotallyRamified W a) (N : ℕ) :
    ∃ S : Finset ℂ, N ≤ S.card ∧ ∀ b ∈ S, TotallyRamified W b := by
  classical
  refine ⟨(Finset.range N).image (fun k : ℕ => a + (k : ℤ) • C), ?_, ?_⟩
  · have hinj : Set.InjOn (fun k : ℕ => a + (k : ℤ) • C) (Finset.range N) := by
      intro i _ j _ hij
      have := drift_values_injective (C := C) hC (a := a) hij
      exact_mod_cast this
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · intro b hb
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
    exact totallyRamified_add_zsmul (W := W) (T := T) (C := C) hdrift ha (k : ℤ)

end GaloisForLFunctions.HTGeometry
