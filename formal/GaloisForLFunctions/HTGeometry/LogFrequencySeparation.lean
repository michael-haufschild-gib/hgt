import Mathlib

/-!
# Separation of logarithmic frequencies of bounded-degree integer monomials

Distinct positive integers have well-separated logarithms: `|log a - log b| ≥ (max a b)⁻¹`,
because `log x ≥ 1 - x⁻¹` and distinct integers differ by at least one.

Consequently, a linear form `∑ᵢ mᵢ log nᵢ` with integer exponents of total degree
`∑ᵢ |mᵢ| ≤ D` and bases `nᵢ ≤ N` either vanishes or is at least `N ^ (-D)` in absolute value:
writing the form as `log a - log b` with `a`, `b` the positive and negative parts of the
monomial, both are at most `N ^ D`.

This is the separation an exponential sum over a time interval needs.  Paired with the
oscillatory bound `‖∫_T^{T+U} e^{iδt} dt‖ ≤ 2/|δ|`
(`GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue.oscInt_norm_le`), it says that
the time average over `[0,T]` of a bounded-degree monomial in `(t log nᵢ)ᵢ` is `O(N ^ D / T)`,
so all such averages are accurate as soon as `N ^ D = o(T)`.  Unlike a bound coming from linear
forms in logarithms, the constant here does not degrade with the number of bases, which is what
makes it usable when the number of bases grows with `T`.
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
  have key : ∀ c d : ℕ, 0 < d → d < c → ((c : ℕ) : ℝ)⁻¹ ≤ Real.log c - Real.log d := by
    intro c d hd hdc
    have hc : (0 : ℝ) < c := by exact_mod_cast lt_trans hd hdc
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hratio : (0 : ℝ) < (c : ℝ) / d := by positivity
    have hlog : Real.log c - Real.log d = Real.log ((c : ℝ) / d) :=
      (Real.log_div (ne_of_gt hc) (ne_of_gt hd')).symm
    have h1 : 1 - ((c : ℝ) / d)⁻¹ ≤ Real.log ((c : ℝ) / d) := one_sub_inv_le_log hratio
    have h2 : ((c : ℝ) / d)⁻¹ = (d : ℝ) / c := by field_simp
    have h3 : (1 : ℝ) - (d : ℝ) / c = ((c : ℝ) - d) / c := by field_simp
    have h4 : (1 : ℝ) ≤ (c : ℝ) - d := by
      have hstep : (d : ℕ) + 1 ≤ c := hdc
      have : ((d : ℕ) : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hstep
      linarith
    have h5 : ((c : ℝ))⁻¹ ≤ ((c : ℝ) - d) / c := by
      rw [div_eq_mul_inv, ← sub_nonneg]
      have hrw : ((c : ℝ) - d) * (c : ℝ)⁻¹ - (c : ℝ)⁻¹ = ((c : ℝ) - d - 1) * (c : ℝ)⁻¹ := by ring
      rw [hrw]
      exact mul_nonneg (by linarith) (le_of_lt (inv_pos.mpr hc))
    rw [hlog]
    calc ((c : ℝ))⁻¹ ≤ ((c : ℝ) - d) / c := h5
      _ = 1 - (d : ℝ) / c := h3.symm
      _ = 1 - ((c : ℝ) / d)⁻¹ := by rw [h2]
      _ ≤ Real.log ((c : ℝ) / d) := h1
  rcases Nat.lt_or_ge a b with h | h
  · have hmax : max a b = b := max_eq_right (le_of_lt h)
    have hkey := key b a ha h
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
    rw [hmax, abs_sub_comm,
      abs_of_nonneg (le_trans (le_of_lt (inv_pos.mpr hbpos)) hkey)]
    exact hkey
  · have hne : b < a := lt_of_le_of_ne h (Ne.symm hab)
    have hmax : max a b = a := max_eq_left (le_of_lt hne)
    have hkey := key a b hb hne
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha
    rw [hmax, abs_of_nonneg (le_trans (le_of_lt (inv_pos.mpr hapos)) hkey)]
    exact hkey

/-- Separation for logarithms of distinct positive integers bounded by `M`. -/
theorem inv_le_abs_log_sub_log_of_le {a b M : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haM : a ≤ M) (hbM : b ≤ M) :
    ((M : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b| := by
  refine le_trans ?_ (inv_max_le_abs_log_sub_log ha hb hab)
  have hle : ((max a b : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast max_le haM hbM
  have hpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le ha (le_max_left a b)
  gcongr

/-- **Bounded-degree monomial separation.**  A linear form in the logarithms of positive
integers `nᵢ ≤ N` with integer coefficients of total degree at most `D` either vanishes or
exceeds `N ^ (-D)` in absolute value.  The bound does not depend on the number of bases. -/
theorem monomial_log_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (m : ι → ℤ) (N D : ℕ) (hN : 0 < N)
    (hn : ∀ i, 0 < n i) (hnN : ∀ i, n i ≤ N) (hdeg : ∑ i, (m i).natAbs ≤ D) :
    ∑ i, (m i : ℝ) * Real.log (n i) = 0 ∨
      (((N : ℕ) : ℝ) ^ D)⁻¹ ≤ |∑ i, (m i : ℝ) * Real.log (n i)| := by
  classical
  set a : ℕ := ∏ i, n i ^ (m i).toNat with ha
  set b : ℕ := ∏ i, n i ^ (-(m i)).toNat with hb
  have hapos : 0 < a := Finset.prod_pos fun i _ => pow_pos (hn i) _
  have hbpos : 0 < b := Finset.prod_pos fun i _ => pow_pos (hn i) _
  have hlogpow : ∀ (e : ι → ℕ), Real.log ((∏ i, n i ^ e i : ℕ) : ℝ)
      = ∑ i, (e i : ℝ) * Real.log (n i) := by
    intro e
    push_cast
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun i _ => by rw [Real.log_pow]
    · intro i _
      have hni : (0 : ℝ) < (n i : ℝ) := by exact_mod_cast hn i
      positivity
  have hsplit : ∀ i, ((m i).toNat : ℝ) - (((-(m i)).toNat : ℕ) : ℝ) = (m i : ℝ) := by
    intro i
    by_cases h : 0 ≤ m i
    · have h1 : ((m i).toNat : ℤ) = m i := Int.toNat_of_nonneg h
      have h2 : (((-(m i)).toNat : ℕ) : ℤ) = 0 := by omega
      have e1 : ((m i).toNat : ℝ) = (m i : ℝ) := by exact_mod_cast h1
      have e2 : (((-(m i)).toNat : ℕ) : ℝ) = 0 := by exact_mod_cast h2
      rw [e1, e2]; ring
    · have hneg : m i < 0 := by omega
      have h1 : ((m i).toNat : ℤ) = 0 := by omega
      have h2 : (((-(m i)).toNat : ℕ) : ℤ) = -(m i) := by omega
      have e1 : ((m i).toNat : ℝ) = 0 := by exact_mod_cast h1
      have e2 : (((-(m i)).toNat : ℕ) : ℝ) = -(m i : ℝ) := by exact_mod_cast h2
      rw [e1, e2]; ring
  have hform : ∑ i, (m i : ℝ) * Real.log (n i) = Real.log a - Real.log b := by
    rw [ha, hb, hlogpow, hlogpow, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_mul, hsplit i]
  have hbound : ∀ f : ι → ℕ, (∑ i, f i ≤ D) → (∏ i, n i ^ f i) ≤ N ^ D := by
    intro f hf
    calc (∏ i, n i ^ f i) ≤ ∏ i, N ^ f i :=
          Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (hnN i) _
      _ = N ^ (∑ i, f i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ N ^ D := Nat.pow_le_pow_right hN hf
  have haD : a ≤ N ^ D := by
    refine hbound _ (le_trans (Finset.sum_le_sum fun i _ => ?_) hdeg)
    omega
  have hbD : b ≤ N ^ D := by
    refine hbound _ (le_trans (Finset.sum_le_sum fun i _ => ?_) hdeg)
    omega
  by_cases hab : a = b
  · left
    rw [hform, hab]
    ring
  · right
    rw [hform]
    have hsep := inv_le_abs_log_sub_log_of_le hapos hbpos hab haD hbD
    have hcast : (((N ^ D : ℕ) : ℝ)) = ((N : ℕ) : ℝ) ^ D := by push_cast; ring
    rw [hcast] at hsep
    exact hsep

end HTGeometry
