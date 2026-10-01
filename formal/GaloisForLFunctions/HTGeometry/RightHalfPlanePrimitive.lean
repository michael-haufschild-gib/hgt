import Mathlib.Analysis.Complex.HasPrimitives

/-!
# Primitives on a right half-plane

A holomorphic function on `{Re s > a}` has a primitive there (`isExactOn_rightHalfPlane`).

**Proof.**  The half-plane is the increasing union of the discs `B(a + k, k)`, `k ≥ 1`, all of
which contain `a + 1`.  The primitives on these discs normalized to vanish at `a + 1` agree on
overlaps (identity theorem for functions with equal derivatives on a disc), so they glue.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

theorem halfPlaneDisc_subset (a : ℝ) (k : ℕ) : ball (((a + k : ℝ)) : ℂ) k ⊆ {s : ℂ | a < s.re} := by
  intro s hs
  rw [mem_ball_iff_norm] at hs
  have h := Complex.abs_re_le_norm (s - ((a + k : ℝ) : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at h
  have := neg_abs_le (s.re - (a + k))
  show a < s.re
  linarith

theorem halfPlaneDisc_mono (a : ℝ) {k m : ℕ} (h : k ≤ m) :
    ball (((a + k : ℝ)) : ℂ) k ⊆ ball (((a + m : ℝ)) : ℂ) m := by
  intro s hs
  rw [mem_ball_iff_norm] at hs ⊢
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast h
  have hc : ‖(((a + k : ℝ)) : ℂ) - ((a + m : ℝ) : ℂ)‖ = m - k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show a + k - (a + m) = -((m : ℝ) - k) by ring, abs_neg, abs_of_nonneg (by linarith)]
  calc ‖s - ((a + m : ℝ) : ℂ)‖
      ≤ ‖s - ((a + k : ℝ) : ℂ)‖ + ‖(((a + k : ℝ)) : ℂ) - ((a + m : ℝ) : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < k + (m - k) := by rw [hc]; linarith
    _ = m := by ring

theorem base_mem_halfPlaneDisc (a : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (((a + 1 : ℝ)) : ℂ) ∈ ball (((a + k : ℝ)) : ℂ) k := by
  rw [mem_ball_iff_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show a + 1 - (a + k) = -((k : ℝ) - 1) by ring, abs_neg]
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem exists_mem_halfPlaneDisc {a : ℝ} {s : ℂ} (hs : a < s.re) :
    ∃ k : ℕ, 1 ≤ k ∧ s ∈ ball (((a + k : ℝ)) : ℂ) k := by
  set x := s.re - a with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((x ^ 2 + s.im ^ 2) / (2 * x)))
  refine ⟨k, by exact_mod_cast (le_max_left _ _).trans hk.le, ?_⟩
  rw [mem_ball_iff_norm]
  have hk2 : (x ^ 2 + s.im ^ 2) / (2 * x) < k := (le_max_right _ _).trans_lt hk
  rw [div_lt_iff₀ (by positivity)] at hk2
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hk.le)
  have hsq : ‖s - ((a + k : ℝ) : ℂ)‖ ^ 2 < (k : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have : s.re - (a + k) = x - k := by rw [hx]; ring
    rw [this]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 hk0.le hsq

/-- **Primitives on a right half-plane.** -/
theorem isExactOn_rightHalfPlane {f : ℂ → ℂ} {a : ℝ}
    (hf : DifferentiableOn ℂ f {s : ℂ | a < s.re}) : IsExactOn f {s : ℂ | a < s.re} := by
  have hP : ∀ k : ℕ, ∃ g : ℂ → ℂ, g ((a + 1 : ℝ) : ℂ) = 0 ∧
      ∀ x ∈ ball (((a + k : ℝ)) : ℂ) k, HasDerivAt g (f x) x := fun k =>
    ((hf.mono (halfPlaneDisc_subset a k)).isExactOn_ball).with_val_at _ 0
  choose P hP0 hPd using hP
  have hcompat : ∀ k m : ℕ, 1 ≤ k → k ≤ m →
      EqOn (P k) (P m) (ball (((a + k : ℝ)) : ℂ) k) := by
    intro k m hk hkm
    have hsub := halfPlaneDisc_mono a hkm
    exact isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
      (fun x hx => (hPd k x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hPd m x (hsub hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [(hPd k x hx).deriv, (hPd m x (hsub hx)).deriv])
      (base_mem_halfPlaneDisc a hk) (by rw [hP0 k, hP0 m])
  classical
  set K : ℂ → ℕ := fun s => if h : a < s.re then Classical.choose (exists_mem_halfPlaneDisc h)
    else 0 with hK
  refine ⟨fun s => P (K s) s, fun s hs => ?_⟩
  have hs' : a < s.re := hs
  have hKs := Classical.choose_spec (exists_mem_halfPlaneDisc hs')
  have hKdef : K s = Classical.choose (exists_mem_halfPlaneDisc hs') := by rw [hK]; simp [hs']
  rw [← hKdef] at hKs
  refine (hPd (K s) s hKs.2).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hKs.2] with y hy
  have hy' : a < y.re := halfPlaneDisc_subset a (K s) hy
  have hKy := Classical.choose_spec (exists_mem_halfPlaneDisc hy')
  have hKydef : K y = Classical.choose (exists_mem_halfPlaneDisc hy') := by rw [hK]; simp [hy']
  rw [← hKydef] at hKy
  show P (K y) y = P (K s) y
  rcases le_total (K y) (K s) with h | h
  · exact hcompat _ _ hKy.1 h hKy.2
  · exact (hcompat _ _ hKs.1 h hy).symm

end GaloisForLFunctions.HTGeometry
