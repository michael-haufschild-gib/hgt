import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing

/-!
# The literal prime pairing of separated logarithmic atoms

Below the integer logarithmic spacing, an atom and a Hecke translate meet only
at an exact integer ratio. The infinite prime pairing therefore reduces to the
literal finite prime kernel, entry by entry, with the common atom mass retained.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticLorentzianGeometry ArithmeticElectrostatics
  ArithmeticEffectivityTheory

variable {g : ℝ → ℝ} {w : ℝ}

/-- Separated translated atoms have exactly diagonal mass pairing. -/
theorem integral_atom_mul_atom {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    (∫ u, atom g m u * atom g n u) = if m = n then (∫ u, g u ^ 2) else 0 := by
  by_cases hmn : m = n
  · subst n
    simp only [if_true, atom, ← pow_two]
    exact integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log m)
  · rw [if_neg hmn]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun u =>
      bump_mul_eq_zero hsupp hw (mem_Icc.mp hm).1 (mem_Icc.mp hn).1
        ((min_le_left _ _).trans (mem_Icc.mp hm).2) hmn u

/-- A negative Hecke shift meets a pair of atoms exactly when `m=nk`. -/
theorem integral_atom_mul_shift_neg {N m n k : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hk : 1 ≤ k) :
    (∫ u, atom g m u * atom g n (u - Real.log k)) =
      if m = n * k then (∫ u, g u ^ 2) else 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have h := mem_Icc.mp hn; omega)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hlog (u : ℝ) : u - Real.log k - Real.log n = u - Real.log ((n * k : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hn0 hk0]
    ring
  simp only [atom, hlog]
  by_cases hmn : m = n * k
  · rw [if_pos hmn, ← hmn]
    simp only [← pow_two]
    exact integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log m)
  · rw [if_neg hmn]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun u =>
      bump_mul_eq_zero hsupp hw (mem_Icc.mp hm).1
        (Nat.mul_pos (mem_Icc.mp hn).1 hk)
        ((min_le_left _ _).trans (mem_Icc.mp hm).2) hmn u

/-- A positive Hecke shift is the reverse pairing at the negative shift. -/
theorem integral_atom_mul_shift_pos {N m n k : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) (hk : 1 ≤ k) :
    (∫ u, atom g m u * atom g n (u + Real.log k)) =
      if n = m * k then (∫ u, g u ^ 2) else 0 := by
  rw [← integral_atom_mul_shift_neg hsupp hw hn hm hk,
    ← integral_sub_right_eq_self
      (fun u => atom g m u * atom g n (u + Real.log k)) (Real.log k)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by
    simp only [sub_add_cancel]
    ring)

/-- Every literal prime-pair entry is the atom mass times the full prime kernel. -/
theorem primePair_atom_eq {N m n : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : w < atomSpacing N)
    (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N) :
    primePair (atom g m) (atom g n) = (∫ u, g u ^ 2) * weilPrimeKernel m n := by
  let G := ∫ u, g u ^ 2
  have hterm (k : ℕ) :
      vonMangoldtAtom k * ((∫ u, atom g m u * atom g n (u - Real.log k)) +
        ∫ u, atom g m u * atom g n (u + Real.log k)) =
      G * (vonMangoldtAtom k * ((if m = n * k then 1 else 0) +
        (if n = m * k then 1 else 0))) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [vonMangoldtAtom, show ¬ 2 ≤ (0 : ℕ) by omega, if_false, zero_mul, mul_zero]
    · rw [integral_atom_mul_shift_neg hsupp hw hm hn hk,
        integral_atom_mul_shift_pos hsupp hw hm hn hk]
      dsimp only [G]
      split_ifs <;> ring
  have hvanish : ∀ k ∉ range (N + 1),
      vonMangoldtAtom k * ((∫ u, atom g m u * atom g n (u - Real.log k)) +
        ∫ u, atom g m u * atom g n (u + Real.log k)) = 0 := by
    intro k hk
    have hkN : N < k := Nat.lt_of_succ_le (by simpa only [mem_range, not_lt] using hk)
    have hm' := mem_Icc.mp hm
    have hn' := mem_Icc.mp hn
    rw [hterm, if_neg (by intro h; nlinarith only [h, hm'.1, hm'.2, hn'.1, hkN]),
      if_neg (by intro h; nlinarith only [h, hn'.1, hn'.2, hm'.1, hkN]),
      zero_add, mul_zero, mul_zero]
  rw [primePair, tsum_eq_sum hvanish, sum_congr rfl (fun k _ => hterm k),
    ← mul_sum, sum_vonMangoldtAtom_hecke hm hn]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

