import Mathlib

/-!
# Separation of logarithmic frequencies of bounded-degree integer monomials

Distinct positive integers have well-separated logarithms: `|log a - log b| ≥ (max a b)⁻¹`,
because `log x ≥ 1 - x⁻¹` and consecutive integers differ by at least one.

Consequently, a linear form `∑ᵢ mᵢ log nᵢ` with integer exponents of total degree
`∑ᵢ |mᵢ| ≤ D` and bases `nᵢ ≤ N` either vanishes identically or is at least `N^(-D)` in
absolute value: writing the form as `log a - log b` with `a`, `b` the positive and negative
parts of the monomial, both are at most `N ^ D`.

This is the separation an exponential sum over a time interval needs.  Paired with the
oscillatory bound `‖∫_T^{T+U} e^{iδt} dt‖ ≤ 2/|δ|`
(`GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue.oscInt_norm_le`), it says that
the time average of a bounded-degree monomial in `(t log nᵢ)ᵢ` over `[0,T]` is `O(N^D / T)`, so
all such averages are accurate as soon as `N ^ D = o(T)`.  Unlike a bound from linear forms in
logarithms, the constant here does not degrade with the number of bases, which is what makes it
usable when the number of bases grows with `T`.
-/

open Finset

namespace HTGeometry

/-- `log x ≥ 1 - x⁻¹` for `x > 0`, the elementary inequality behind the separation. -/
theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (by positivity)
  rw [Real.log_inv] at h
  linarith

/-- **Separation of logarithms of distinct positive integers.** -/
theorem inv_max_le_abs_log_sub_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ((max a b : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b| := by
  -- reduce to the case `b < a`
  have key : ∀ c d : ℕ, 0 < d → d < c → ((c : ℕ) : ℝ)⁻¹ ≤ Real.log c - Real.log d := by
    intro c d hd hdc
    have hc : (0 : ℝ) < c := by exact_mod_cast lt_trans hd hdc
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hratio : (0 : ℝ) < (c : ℝ) / d := by positivity
    have hlog : Real.log c - Real.log d = Real.log ((c : ℝ) / d) := by
      rw [Real.log_div (ne_of_gt hc) (ne_of_gt hd')]
    have h1 : 1 - ((c : ℝ) / d)⁻¹ ≤ Real.log ((c : ℝ) / d) := one_sub_inv_le_log hratio
    have h2 : ((c : ℝ) / d)⁻¹ = (d : ℝ) / c := by
      field_simp
    have h3 : (1 : ℝ) - (d : ℝ) / c = ((c : ℝ) - d) / c := by field_simp
    have h4 : (1 : ℝ) ≤ (c : ℝ) - d := by
      have : (d : ℕ) + 1 ≤ c := hdc
      have : ((d : ℕ) : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast this
      linarith
    have h5 : ((c : ℝ))⁻¹ ≤ ((c : ℝ) - d) / c := by
      rw [inv_eq_one_div, div_le_div_iff_of_pos_right hc]
      exact h4
    rw [hlog]
    calc ((c : ℝ))⁻¹ ≤ ((c : ℝ) - d) / c := h5
      _ = 1 - (d : ℝ) / c := h3.symm
      _ = 1 - ((c : ℝ) / d)⁻¹ := by rw [h2]
      _ ≤ Real.log ((c : ℝ) / d) := h1
  rcases lt_or_gt_of_ne hab with h | h
  · have hmax : max a b = b := max_eq_right (le_of_lt h)
    rw [hmax, abs_sub_comm]
    have := key b a ha h
    rw [abs_of_nonneg (by linarith [this, inv_pos.mpr (show (0:ℝ) < b by exact_mod_cast hb)])]
    exact this
  · have hmax : max a b = a := max_eq_left (le_of_lt h)
    rw [hmax]
    have := key a b hb h
    rw [abs_of_nonneg (by linarith [this, inv_pos.mpr (show (0:ℝ) < a by exact_mod_cast ha)])]
    exact this

/-- Separation for logarithms of distinct positive integers bounded by `M`. -/
theorem inv_le_abs_log_sub_log_of_le {a b M : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haM : a ≤ M) (hbM : b ≤ M) :
    ((M : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b| := by
  have hM : 0 < M := lt_of_lt_of_le ha haM
  refine le_trans ?_ (inv_max_le_abs_log_sub_log ha hb hab)
  have hle : ((max a b : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast max_le haM hbM
  have hpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le ha (le_max_left a b)
  exact one_div_le_one_div_of_le hpos hle |>.trans_eq (by rw [one_div]) |>.trans_eq rfl
    |>.trans (le_of_eq rfl) |>.trans (le_of_eq rfl)

/-- **Bounded-degree monomial separation.**  A linear form in the logarithms of integers
`nᵢ ≤ N` with integer coefficients of total degree at most `D` either vanishes or exceeds
`N ^ (-D)` in absolute value.  The bound is independent of the number of bases. -/
theorem monomial_log_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (m : ι → ℤ) (N D : ℕ)
    (hn : ∀ i, 0 < n i) (hnN : ∀ i, n i ≤ N) (hdeg : ∑ i, (m i).natAbs ≤ D) :
    ∑ i, (m i : ℝ) * Real.log (n i) = 0 ∨
      (((N : ℕ) : ℝ) ^ D)⁻¹ ≤ |∑ i, (m i : ℝ) * Real.log (n i)| := by
  classical
  set a : ℕ := ∏ i, n i ^ (m i).toNat with ha
  set b : ℕ := ∏ i, n i ^ (-(m i)).toNat with hb
  have hapos : 0 < a := Finset.prod_pos fun i _ => pow_pos (hn i) _
  have hbpos : 0 < b := Finset.prod_pos fun i _ => pow_pos (hn i) _
  -- the form is `log a - log b`
  have hloga : Real.log a = ∑ i, ((m i).toNat : ℝ) * Real.log (n i) := by
    rw [ha]
    push_cast
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun i _ => by
        rw [Real.log_pow]
    · intro i _
      have : (0 : ℝ) < (n i : ℝ) ^ (m i).toNat := by
        have : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast hn i
        positivity
      exact ne_of_gt this
  have hlogb : Real.log b = ∑ i, (((-(m i)).toNat : ℕ) : ℝ) * Real.log (n i) := by
    rw [hb]
    push_cast
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun i _ => by
        rw [Real.log_pow]
    · intro i _
      have : (0 : ℝ) < (n i : ℝ) ^ (-(m i)).toNat := by
        have : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast hn i
        positivity
      exact ne_of_gt this
  have hform : ∑ i, (m i : ℝ) * Real.log (n i) = Real.log a - Real.log b := by
    rw [hloga, hlogb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((m i).toNat : ℝ) - (((-(m i)).toNat : ℕ) : ℝ) = (m i : ℝ) := by
      rcases le_or_lt 0 (m i) with h | h
      · rw [Int.toNat_of_nonneg h |> congrArg (fun z : ℤ => (z : ℝ)) |>.symm] <;> skip
        simp [Int.toNat_of_nonneg h, Int.toNat_eq_zero.mpr (by omega : -(m i) ≤ 0)]
      · simp [Int.toNat_eq_zero.mpr (by omega : m i ≤ 0), Int.toNat_of_nonneg (by omega : 0 ≤ -(m i))]
        push_cast
        ring
    rw [← this]
    ring
  -- both parts are at most `N ^ D`
  have hN : 0 < N := lt_of_lt_of_le (hn (Classical.arbitrary ι)) (hnN (Classical.arbitrary ι))
    |>.trans_le (le_refl N)
  have hbound : ∀ f : ι → ℕ, (∑ i, f i ≤ D) → (∏ i, n i ^ f i) ≤ N ^ D := by
    intro f hf
    calc (∏ i, n i ^ f i) ≤ ∏ i, N ^ f i :=
          Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hnN i) _
      _ = N ^ (∑ i, f i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ N ^ D := Nat.pow_le_pow_right hN hf
  have haD : a ≤ N ^ D := by
    refine hbound _ (le_trans (Finset.sum_le_sum fun i _ => ?_) hdeg)
    exact Int.toNat_le.mpr (by omega)
  have hbD : b ≤ N ^ D := by
    refine hbound _ (le_trans (Finset.sum_le_sum fun i _ => ?_) hdeg)
    exact Int.toNat_le.mpr (by omega)
  by_cases hab : a = b
  · left
    rw [hform, hab]
    ring
  · right
    rw [hform]
    have := inv_le_abs_log_sub_log_of_le hapos hbpos hab haD hbD
    simpa using this

end HTGeometry
