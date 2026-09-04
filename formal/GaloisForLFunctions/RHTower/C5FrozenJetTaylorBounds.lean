import Mathlib

/-!
# Frozen-jet Taylor bounds (stage 1 of the small-`t` growth bound)

Elementary Taylor-type bounds obtained by monotonicity: if `h 0 = 0` and `|h'(s)| ≤ K s^k` on
`[0, t]` then `|h s| ≤ K s^(k+1)/(k+1)`.  Iterating along a `C⁵` chain `c → c₁ → … → c₅` gives the
frozen-jet expansions of `c, c₁, c₂, c₃` around a centre `u` on `[u − t, u + t]`, with remainders
controlled by sup-norms `S₄`, `S₅` of `c₄`, `c₅`.  Even/odd combinations
`e(s) = (c(u+s) + c(u−s))/2`, `o(s) = (c(u+s) − c(u−s))/2` inherit the bounds with the odd/even
terms cancelling.
-/

open Set

namespace RHTower

/-- Monotone comparison: `h 0 = 0` and `|h'| ≤ K s^k` on `[0,t]` give `|h s| ≤ K s^(k+1)/(k+1)`. -/
theorem abs_le_pow_div_of_abs_deriv_le {h h' : ℝ → ℝ} {K t : ℝ} {k : ℕ} (ht : 0 ≤ t)
    (h0 : h 0 = 0) (hd : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt h (h' s) s)
    (hb : ∀ s ∈ Icc (0 : ℝ) t, |h' s| ≤ K * s ^ k) :
    ∀ s ∈ Icc (0 : ℝ) t, |h s| ≤ K * s ^ (k + 1) / (k + 1) := by
  have hpow : ∀ s : ℝ, HasDerivAt (fun s => K * s ^ (k + 1) / (k + 1)) (K * s ^ k) s := by
    intro s
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    have := ((hasDerivAt_pow (k + 1) s).const_mul K).div_const ((k : ℝ) + 1)
    refine this.congr_deriv ?_
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  -- `g₊ = K s^(k+1)/(k+1) − h` is nondecreasing on `[0,t]`
  have hmonoP : MonotoneOn (fun s => K * s ^ (k + 1) / (k + 1) - h s) (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · intro s hs
      exact ((hpow s).sub (hd s hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact ((hpow s).sub (hd s (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hg : HasDerivAt (fun s => K * s ^ (k + 1) / (k + 1) - h s) (K * s ^ k - h' s) s :=
        (hpow s).sub (hd s (Ioo_subset_Icc_self hs))
      rw [hg.deriv]
      have := hb s (Ioo_subset_Icc_self hs)
      linarith [(abs_le.mp this).2]
  have hmonoM : MonotoneOn (fun s => K * s ^ (k + 1) / (k + 1) + h s) (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) ?_ ?_ ?_
    · intro s hs
      exact ((hpow s).add (hd s hs)).continuousAt.continuousWithinAt
    · intro s hs
      exact ((hpow s).add (hd s (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hg : HasDerivAt (fun s => K * s ^ (k + 1) / (k + 1) + h s) (K * s ^ k + h' s) s :=
        (hpow s).add (hd s (Ioo_subset_Icc_self hs))
      rw [hg.deriv]
      have := hb s (Ioo_subset_Icc_self hs)
      linarith [(abs_le.mp this).1]
  intro s hs
  have hP := hmonoP (left_mem_Icc.2 ht) hs hs.1
  have hM := hmonoM (left_mem_Icc.2 ht) hs hs.1
  simp only [h0, zero_pow (Nat.succ_ne_zero k), mul_zero, zero_div, sub_zero, add_zero] at hP hM
  rw [abs_le]
  constructor <;> linarith

/-- Reflected version on `[−t, 0]`, stated through `|s|`. -/
theorem abs_le_pow_div_of_abs_deriv_le_neg {h h' : ℝ → ℝ} {K t : ℝ} {k : ℕ} (ht : 0 ≤ t)
    (h0 : h 0 = 0) (hd : ∀ s ∈ Icc (-t) (0 : ℝ), HasDerivAt h (h' s) s)
    (hb : ∀ s ∈ Icc (-t) (0 : ℝ), |h' s| ≤ K * |s| ^ k) :
    ∀ s ∈ Icc (-t) (0 : ℝ), |h s| ≤ K * |s| ^ (k + 1) / (k + 1) := by
  intro s hs
  have hs' : -s ∈ Icc (0 : ℝ) t := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have key := abs_le_pow_div_of_abs_deriv_le (h := fun r => h (-r)) (h' := fun r => -h' (-r))
    (K := K) (k := k) ht (by simpa using h0) ?_ ?_ (-s) hs'
  · rw [abs_of_nonpos hs.2]
    simpa using key
  · intro r hr
    have hr' : -r ∈ Icc (-t) (0 : ℝ) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have := (hd (-r) hr').comp r (hasDerivAt_neg r)
    convert this using 1 <;> first | rfl | simp | ring
  · intro r hr
    have hr' : -r ∈ Icc (-t) (0 : ℝ) := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have := hb (-r) hr'
    simpa [abs_neg, abs_of_nonneg hr.1] using this

/-- Two-sided version on `[−t, t]`. -/
theorem abs_le_pow_div_of_abs_deriv_le_Icc {h h' : ℝ → ℝ} {K t : ℝ} {k : ℕ} (ht : 0 ≤ t)
    (h0 : h 0 = 0) (hd : ∀ s ∈ Icc (-t) t, HasDerivAt h (h' s) s)
    (hb : ∀ s ∈ Icc (-t) t, |h' s| ≤ K * |s| ^ k) :
    ∀ s ∈ Icc (-t) t, |h s| ≤ K * |s| ^ (k + 1) / (k + 1) := by
  intro s hs
  rcases le_or_gt 0 s with hs0 | hs0
  · have := abs_le_pow_div_of_abs_deriv_le ht h0
      (fun r hr => hd r ⟨by linarith [hr.1], hr.2⟩)
      (fun r hr => by simpa [abs_of_nonneg hr.1] using hb r ⟨by linarith [hr.1], hr.2⟩)
      s ⟨hs0, hs.2⟩
    simpa [abs_of_nonneg hs0] using this
  · exact abs_le_pow_div_of_abs_deriv_le_neg ht h0
      (fun r hr => hd r ⟨hr.1, by linarith [hr.2]⟩)
      (fun r hr => hb r ⟨hr.1, by linarith [hr.2]⟩) s ⟨hs.1, hs0.le⟩

/-- Sup-norm bound of a derivative gives a linear bound on the increment. -/
theorem abs_sub_le_of_abs_deriv_le {f f' : ℝ → ℝ} {S u t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hS : ∀ x ∈ Icc (u - t) (u + t), |f' x| ≤ S) :
    ∀ s ∈ Icc (-t) t, |f (u + s) - f u| ≤ S * |s| := by
  have := abs_le_pow_div_of_abs_deriv_le_Icc (h := fun s => f (u + s) - f u)
    (h' := fun s => f' (u + s)) (K := S) (k := 0) ht (by simp) ?_ ?_
  · intro s hs
    simpa using this s hs
  · intro s _
    have := ((hd (u + s)).comp s ((hasDerivAt_id s).const_add u)).sub_const (f u)
    convert this using 1 <;> first | rfl | simp | ring
  · intro s hs
    simp only [pow_zero, mul_one]
    exact hS (u + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- Frozen-jet expansion of a `C⁴`-chain `c → c₁ → c₂ → c₃ → c₄` around `u` with sup-norm `S₄`
of `c₄` on `[u−t, u+t]`.  All four remainders at once. -/
theorem frozenJet_bounds_four {c c₁ c₂ c₃ c₄ : ℝ → ℝ} {S₄ u t : ℝ} (ht : 0 ≤ t)
    (hc : ∀ x, HasDerivAt c (c₁ x) x) (hc₁ : ∀ x, HasDerivAt c₁ (c₂ x) x)
    (hc₂ : ∀ x, HasDerivAt c₂ (c₃ x) x) (hc₃ : ∀ x, HasDerivAt c₃ (c₄ x) x)
    (hS : ∀ x ∈ Icc (u - t) (u + t), |c₄ x| ≤ S₄) :
    ∀ s ∈ Icc (-t) t,
      |c₃ (u + s) - c₃ u| ≤ S₄ * |s| ∧
      |c₂ (u + s) - (c₂ u + c₃ u * s)| ≤ S₄ * |s| ^ 2 / 2 ∧
      |c₁ (u + s) - (c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2)| ≤ S₄ * |s| ^ 3 / 6 ∧
      |c (u + s) - (c u + c₁ u * s + c₂ u * s ^ 2 / 2 + c₃ u * s ^ 3 / 6)| ≤
        S₄ * |s| ^ 4 / 24 := by
  have h3 := abs_sub_le_of_abs_deriv_le ht hc₃ hS
  have h2 := abs_le_pow_div_of_abs_deriv_le_Icc (h := fun s => c₂ (u + s) - (c₂ u + c₃ u * s))
    (h' := fun s => c₃ (u + s) - c₃ u) (K := S₄) (k := 1) ht (by simp) ?_ ?_
  rotate_left
  · intro s _
    have := ((hc₂ (u + s)).comp s ((hasDerivAt_id s).const_add u)).sub
      (((hasDerivAt_id s).const_mul (c₃ u)).const_add (c₂ u))
    convert this using 1 <;> first | rfl | simp
  · intro s hs
    simpa using h3 s hs
  have h1 := abs_le_pow_div_of_abs_deriv_le_Icc
    (h := fun s => c₁ (u + s) - (c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2))
    (h' := fun s => c₂ (u + s) - (c₂ u + c₃ u * s)) (K := S₄ / 2) (k := 2) ht (by simp) ?_ ?_
  rotate_left
  · intro s _
    have hp : HasDerivAt (fun s : ℝ => c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2) (c₂ u + c₃ u * s) s := by
      have := (((hasDerivAt_id s).const_mul (c₂ u)).const_add (c₁ u)).add
        (((hasDerivAt_pow 2 s).const_mul (c₃ u)).div_const 2)
      convert this using 1 <;> first | rfl | (simp; ring) | simp
    have := ((hc₁ (u + s)).comp s ((hasDerivAt_id s).const_add u)).sub hp
    convert this using 1 <;> first | rfl | simp
  · intro s hs
    have := h2 s hs
    calc |c₂ (u + s) - (c₂ u + c₃ u * s)| ≤ S₄ * |s| ^ (1 + 1) / (((1 : ℕ) : ℝ) + 1) := this
      _ = S₄ / 2 * |s| ^ 2 := by push_cast; ring
  have h0 := abs_le_pow_div_of_abs_deriv_le_Icc
    (h := fun s => c (u + s) - (c u + c₁ u * s + c₂ u * s ^ 2 / 2 + c₃ u * s ^ 3 / 6))
    (h' := fun s => c₁ (u + s) - (c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2)) (K := S₄ / 6) (k := 3)
    ht (by simp) ?_ ?_
  rotate_left
  · intro s _
    have hp : HasDerivAt (fun s : ℝ => c u + c₁ u * s + c₂ u * s ^ 2 / 2 + c₃ u * s ^ 3 / 6)
        (c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2) s := by
      have := ((((hasDerivAt_id s).const_mul (c₁ u)).const_add (c u)).add
        (((hasDerivAt_pow 2 s).const_mul (c₂ u)).div_const 2)).add
        (((hasDerivAt_pow 3 s).const_mul (c₃ u)).div_const 6)
      convert this using 1 <;> first | rfl | (simp; ring) | simp
    have := ((hc (u + s)).comp s ((hasDerivAt_id s).const_add u)).sub hp
    convert this using 1 <;> first | rfl | simp
  · intro s hs
    have := h1 s hs
    calc |c₁ (u + s) - (c₁ u + c₂ u * s + c₃ u * s ^ 2 / 2)| ≤
        S₄ / 2 * |s| ^ (2 + 1) / (((2 : ℕ) : ℝ) + 1) := this
      _ = S₄ / 6 * |s| ^ 3 := by push_cast; ring
  intro s hs
  refine ⟨h3 s hs, ?_, ?_, ?_⟩
  · have := h2 s hs
    calc _ ≤ S₄ * |s| ^ (1 + 1) / (((1 : ℕ) : ℝ) + 1) := this
      _ = S₄ * |s| ^ 2 / 2 := by push_cast; ring
  · have := h1 s hs
    calc _ ≤ S₄ / 2 * |s| ^ (2 + 1) / (((2 : ℕ) : ℝ) + 1) := this
      _ = S₄ * |s| ^ 3 / 6 := by push_cast; ring
  · have := h0 s hs
    calc _ ≤ S₄ / 6 * |s| ^ (3 + 1) / (((3 : ℕ) : ℝ) + 1) := this
      _ = S₄ * |s| ^ 4 / 24 := by push_cast; ring

end RHTower
