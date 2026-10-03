import GaloisForLFunctions.HTGeometry.BeukersZetaTwoLinearForms

/-!
# Integrality of Beukers' linear forms

With `dₙ = lcm(1, …, n)`, every `dₙ² J(r, s)` (`r, s ≤ n`) is `[r = s] dₙ² π²/6` minus an
explicit integer, so

`dₙ² Σ_{r,s} p_r q_s J(r, s) = Aₙ π²/6 + Bₙ`, `Aₙ = dₙ² Σ_r p_r q_r`, `Bₙ ∈ ℤ`,

with `|Aₙ| ≤ dₙ² (n + 1) 16ⁿ`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.BeukersZetaTwo

/-- `j ∣ lcm(1, …, n)` for `1 ≤ j ≤ n`. -/
theorem dvd_lcmUpto {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) : j ∣ Nat.lcmUpto n :=
  Finset.dvd_lcm (s := Icc 1 n) (f := id) (mem_Icc.mpr ⟨hj1, hjn⟩)

theorem cast_div_lcmUpto {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    ((Nat.lcmUpto n / j : ℕ) : ℝ) = (Nat.lcmUpto n : ℝ) / j :=
  Nat.cast_div (dvd_lcmUpto hj1 hjn) (Nat.cast_ne_zero.mpr (by omega))

/-- The integer `dₙ² ([r = s] π²/6 − J(r, s))`. -/
noncomputable def rhoZ (n r s : ℕ) : ℤ :=
  if r = s then
    ((∑ j ∈ range (r + 1), (Nat.lcmUpto n / j) ^ 2 : ℕ) : ℤ)
  else if s < r then
    -((∑ j ∈ Ico (s + 1) (r + 1), (Nat.lcmUpto n / j) * (Nat.lcmUpto n / (r - s)) : ℕ) : ℤ)
  else
    -((∑ j ∈ Ico (r + 1) (s + 1), (Nat.lcmUpto n / j) * (Nat.lcmUpto n / (s - r)) : ℕ) : ℤ)

theorem lcm_sq_mul_kernelPair_of_lt {n r s : ℕ} (hsr : s < r) (hrn : r ≤ n) :
    (Nat.lcmUpto n : ℝ) ^ 2 * kernelPair r s =
      ∑ j ∈ Ico (s + 1) (r + 1),
        (((Nat.lcmUpto n / j) * (Nat.lcmUpto n / (r - s)) : ℕ) : ℝ) := by
  rw [kernelPair_of_lt hsr, mul_div_assoc', mul_sum, sum_div]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_Ico] at hj
  push_cast
  rw [cast_div_lcmUpto (by omega) (by omega), cast_div_lcmUpto (by omega) (by omega)]
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hrs : ((r - s : ℕ) : ℝ) = (r : ℝ) - s := by push_cast [hsr.le]; ring
  rw [hrs]
  have hrs0 : (r : ℝ) - s ≠ 0 := by
    have : (s : ℝ) < r := by exact_mod_cast hsr
    linarith
  field_simp

/-- **Integrality of the kernel values.** -/
theorem lcm_sq_mul_kernelPair {n r s : ℕ} (hrn : r ≤ n) (hsn : s ≤ n) :
    (Nat.lcmUpto n : ℝ) ^ 2 * kernelPair r s =
      (if r = s then (Nat.lcmUpto n : ℝ) ^ 2 * (Real.pi ^ 2 / 6) else 0) - rhoZ n r s := by
  unfold rhoZ
  by_cases hrs : r = s
  · subst hrs
    rw [if_pos rfl, if_pos rfl, kernelPair_self, mul_sub, mul_sum, Int.cast_natCast,
      Nat.cast_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [Nat.cast_pow]
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    · rw [mem_range] at hj
      rw [cast_div_lcmUpto (n := n) hpos (by omega)]
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
  · rw [if_neg hrs, if_neg hrs, zero_sub]
    rcases lt_or_gt_of_ne hrs with hlt | hgt
    · rw [if_neg (by omega), kernelPair_comm, lcm_sq_mul_kernelPair_of_lt hlt hsn,
        Int.cast_neg, Int.cast_natCast, neg_neg, Nat.cast_sum]
    · rw [if_pos hgt, lcm_sq_mul_kernelPair_of_lt hgt hrn, Int.cast_neg, Int.cast_natCast,
        neg_neg, Nat.cast_sum]

/-- `Aₙ = dₙ² Σ_r p_r q_r`. -/
noncomputable def beukersA (n : ℕ) : ℤ :=
  (Nat.lcmUpto n : ℤ) ^ 2 * ∑ r ∈ range (n + 1), legCoeff n r * binCoeff n r

/-- `Bₙ = −Σ_{r,s} p_r q_s ρ(r, s)`. -/
noncomputable def beukersB (n : ℕ) : ℤ :=
  -∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1), legCoeff n r * binCoeff n s * rhoZ n r s

/-- **Beukers' linear form.**  `dₙ² Σ_{r,s} p_r q_s J(r, s) = Aₙ π²/6 + Bₙ`. -/
theorem lcm_sq_mul_sum_eq (n : ℕ) :
    (Nat.lcmUpto n : ℝ) ^ 2 * ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
        (legCoeff n r : ℝ) * binCoeff n s * kernelPair r s =
      (beukersA n : ℝ) * (Real.pi ^ 2 / 6) + beukersB n := by
  set D : ℝ := (Nat.lcmUpto n : ℝ) ^ 2 * (Real.pi ^ 2 / 6) with hD
  have hterm : ∀ r ∈ range (n + 1), ∀ s ∈ range (n + 1),
      (Nat.lcmUpto n : ℝ) ^ 2 * ((legCoeff n r : ℝ) * binCoeff n s * kernelPair r s) =
        (legCoeff n r : ℝ) * binCoeff n s * (if r = s then D else 0) -
          (legCoeff n r : ℝ) * binCoeff n s * rhoZ n r s := by
    intro r hr s hs
    have h := lcm_sq_mul_kernelPair (Nat.lt_succ_iff.mp (mem_range.mp hr))
      (Nat.lt_succ_iff.mp (mem_range.mp hs))
    rw [← hD] at h
    linear_combination ((legCoeff n r : ℝ) * binCoeff n s) * h
  rw [mul_sum]
  simp_rw [mul_sum]
  rw [sum_congr rfl fun r hr => sum_congr rfl fun s hs => hterm r hr s hs]
  simp only [sum_sub_distrib]
  have hdiag : ∑ r ∈ range (n + 1), ∑ s ∈ range (n + 1),
      (legCoeff n r : ℝ) * binCoeff n s * (if r = s then D else 0) =
        ∑ r ∈ range (n + 1), (legCoeff n r : ℝ) * binCoeff n r * D := by
    refine sum_congr rfl fun r hr => ?_
    rw [sum_eq_single r (fun s _ hsr => by rw [if_neg (Ne.symm hsr), mul_zero])
      (fun h => absurd hr h), if_pos rfl]
  rw [hdiag, ← sum_mul]
  unfold beukersA beukersB
  push_cast
  rw [hD]
  ring

theorem abs_legCoeff_mul_binCoeff_le (n r : ℕ) (hr : r ≤ n) :
    |(legCoeff n r : ℝ) * binCoeff n r| ≤ 16 ^ n := by
  unfold legCoeff binCoeff
  push_cast
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have h1 : (n.choose r : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n r
  have h2 : ((n + r).choose n : ℝ) ≤ 4 ^ n := by
    have := Nat.choose_le_two_pow (n + r) n
    have h' : 2 ^ (n + r) ≤ 4 ^ n := by
      calc 2 ^ (n + r) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 ^ n := by rw [pow_mul]; norm_num
    exact_mod_cast this.trans h'
  have e : (16 : ℝ) ^ n = 2 ^ n * 4 ^ n * 2 ^ n := by
    rw [← mul_pow, ← mul_pow]; norm_num
  rw [e]
  have h0 : (0 : ℝ) ≤ n.choose r := Nat.cast_nonneg _
  have h0' : (0 : ℝ) ≤ (n + r).choose n := Nat.cast_nonneg _
  calc (n.choose r : ℝ) * ((n + r).choose n) * (n.choose r) ≤ 2 ^ n * 4 ^ n * 2 ^ n := by
        gcongr

/-- `|Aₙ| ≤ dₙ² (n + 1) 16ⁿ`. -/
theorem abs_beukersA_le (n : ℕ) :
    |(beukersA n : ℝ)| ≤ (Nat.lcmUpto n : ℝ) ^ 2 * ((n + 1) * 16 ^ n) := by
  unfold beukersA
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ range (n + 1), |(legCoeff n r : ℝ) * binCoeff n r| ≤
      ∑ _r ∈ range (n + 1), (16 : ℝ) ^ n :=
        sum_le_sum fun r hr => abs_legCoeff_mul_binCoeff_le n r
          (Nat.lt_succ_iff.mp (mem_range.mp hr))
    _ = (n + 1) * 16 ^ n := by simp

end GaloisForLFunctions.HTGeometry.BeukersZetaTwo
