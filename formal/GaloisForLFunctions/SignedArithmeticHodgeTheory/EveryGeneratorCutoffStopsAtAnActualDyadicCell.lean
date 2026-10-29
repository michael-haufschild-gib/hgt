import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneGammaReserveControlsTheDyadicEulerTail

/-!
# Whole-orbit cutoffs stop at actual dyadic cells

The inverse weighted Haar rotation describes the generator cutoff on every
original cell. Small cells are fixed. A larger cell ascends its dyadic tree
until its integer label lies below twice the generator cutoff. Its projected
vector is the orthogonal component along that actual translated cell.
The stopping rule retains every translation level and uses no Gamma estimate
for the projected source.
-/

noncomputable section
open RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "W" => logCellShift 2
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)
local notation "P" => logCellGeneratorHead

/-- The cutoff keeps or removes each unshifted balanced detail according to its label. -/
theorem logCellGeneratorHead_detail (A : ℕ) (a : ℕ+) :
    P A (logCellDyadicDetail a) =
      if (a : ℕ) < A then logCellDyadicDetail a else 0 := by
  simpa only [logCellDyadicOrbit, pow_zero, one_apply_eq_self,
    logCellDyadicGenerator, retainedLogCellGenerator] using
      logCellGeneratorHead_orbit A (0, some a)

/-- Every original cell below twice the generator threshold is retained exactly. -/
theorem logCellGeneratorHead_single_of_lt (A : ℕ) (n : ℕ+) (hn : (n : ℕ) < 2 * A) :
    P A (e n) = e n := by
  have h : ∀ m : ℕ, ∀ hm : 0 < m, m < 2 * A → P A (e ⟨m, hm⟩) = e ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm hcut
      by_cases hm1 : m = 1
      · subst m
        rw [show (⟨1, hm⟩ : ℕ+) = 1 from PNat.eq rfl]
        exact logCellGeneratorHead_root A 0
      let a : ℕ+ := ⟨m / 2, by omega⟩
      have ha : (a : ℕ) < A := by change m / 2 < A; omega
      have hp : P A (e a) = e a := ih (m / 2) (Nat.div_lt_self hm (by norm_num)) (by omega) (by omega)
      have hd : P A (logCellDyadicDetail a) = logCellDyadicDetail a := by
        rw [logCellGeneratorHead_detail, if_pos ha]
      have hcases : m = 2 * (a : ℕ) ∨ m = 2 * (a : ℕ) + 1 := by
        change m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1
        omega
      rcases hcases with hl | hr
      · have he : (⟨m, hm⟩ : ℕ+) = dyadicLeftCell a := PNat.eq hl
        rw [he, dyadicLeftCell_eq_coarse_add_detail, map_add, map_smul, map_smul,
          logCellGeneratorHead_shift, hp, hd]
      · have he : (⟨m, hm⟩ : ℕ+) = dyadicRightCell a := PNat.eq hr
        rw [he, dyadicRightCell_eq_coarse_sub_detail, map_sub, map_smul, map_smul,
          logCellGeneratorHead_shift, hp, hd]
  exact h n n.pos hn

/-- Ascend the integer dyadic tree until the label is below twice the cutoff. -/
def logCellStoppingAncestor (A n : ℕ+) : ℕ × ℕ+ :=
  if hn : (n : ℕ) < 2 * (A : ℕ) then (0, n)
  else
    let a : ℕ+ := ⟨(n : ℕ) / 2, by have := A.pos; omega⟩
    let b := logCellStoppingAncestor A a
    (b.1 + 1, b.2)
termination_by (n : ℕ)
decreasing_by
  change (n : ℕ) / 2 < (n : ℕ)
  exact Nat.div_lt_self n.pos (by norm_num)

theorem logCellStoppingAncestor_of_lt (A n : ℕ+) (hn : (n : ℕ) < 2 * (A : ℕ)) :
    logCellStoppingAncestor A n = (0, n) := by
  rw [logCellStoppingAncestor, dif_pos hn]

theorem logCellStoppingAncestor_of_ge (A n : ℕ+) (hn : 2 * (A : ℕ) ≤ (n : ℕ)) :
    let a : ℕ+ := ⟨(n : ℕ) / 2, by have := A.pos; omega⟩
    logCellStoppingAncestor A n =
      ((logCellStoppingAncestor A a).1 + 1, (logCellStoppingAncestor A a).2) := by
  rw [logCellStoppingAncestor, dif_neg (not_lt.mpr hn)]

/-- The terminal label is always below twice the cutoff. -/
theorem logCellStoppingAncestor_label_lt (A n : ℕ+) :
    ((logCellStoppingAncestor A n).2 : ℕ) < 2 * (A : ℕ) := by
  have h : ∀ m : ℕ, ∀ hm : 0 < m,
      ((logCellStoppingAncestor A ⟨m, hm⟩).2 : ℕ) < 2 * (A : ℕ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hcut : m < 2 * (A : ℕ)
      · rw [logCellStoppingAncestor_of_lt A ⟨m, hm⟩ hcut]
        exact hcut
      · rw [logCellStoppingAncestor_of_ge A ⟨m, hm⟩ (by change 2 * (A : ℕ) ≤ m; omega)]
        exact ih (m / 2) (by omega) (by have := A.pos; omega)
  exact h n n.pos

/-- A cell beyond the initial head stops between the cutoff and twice the cutoff. -/
theorem le_logCellStoppingAncestor_label (A n : ℕ+) (hn : (A : ℕ) ≤ (n : ℕ)) :
    (A : ℕ) ≤ ((logCellStoppingAncestor A n).2 : ℕ) := by
  have h : ∀ m : ℕ, ∀ hm : 0 < m, (A : ℕ) ≤ m →
      (A : ℕ) ≤ ((logCellStoppingAncestor A ⟨m, hm⟩).2 : ℕ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm hAm
      by_cases hcut : m < 2 * (A : ℕ)
      · rw [logCellStoppingAncestor_of_lt A ⟨m, hm⟩ hcut]
        exact hAm
      · rw [logCellStoppingAncestor_of_ge A ⟨m, hm⟩ (by change 2 * (A : ℕ) ≤ m; omega)]
        exact ih (m / 2) (by omega) (by have := A.pos; omega) (by omega)
  exact h n n.pos hn

/-- The normalized actual cell at the stopping ancestor and its full translation level. -/
def logCellStoppingVector (A n : ℕ+) : CellH :=
  (W ^ (logCellStoppingAncestor A n).1) (e (logCellStoppingAncestor A n).2)

theorem logCellStoppingVector_of_lt (A n : ℕ+) (hn : (n : ℕ) < 2 * (A : ℕ)) :
    logCellStoppingVector A n = e n := by
  rw [logCellStoppingVector, logCellStoppingAncestor_of_lt A n hn]
  rfl

theorem logCellStoppingVector_of_ge (A n : ℕ+) (hn : 2 * (A : ℕ) ≤ (n : ℕ)) :
    let a : ℕ+ := ⟨(n : ℕ) / 2, by have := A.pos; omega⟩
    logCellStoppingVector A n = W (logCellStoppingVector A a) := by
  dsimp only
  rw [logCellStoppingVector, logCellStoppingAncestor_of_ge A n hn]
  change (W ^ ((logCellStoppingAncestor A _).1 + 1)) _ = _
  rw [pow_succ', mul_apply_eq_comp]
  rfl

/-- Every stopping cell belongs to the retained whole-orbit space. -/
theorem logCellGeneratorHead_stoppingVector (A n : ℕ+) :
    P A (logCellStoppingVector A n) = logCellStoppingVector A n := by
  unfold logCellStoppingVector
  rw [logCellGeneratorHead_dyadic_pow,
    logCellGeneratorHead_single_of_lt A _ (logCellStoppingAncestor_label_lt A n)]

/-- A stopped cell is normalized in the original logarithmic-cell Hilbert space. -/
theorem norm_logCellStoppingVector (A n : ℕ+) : ‖logCellStoppingVector A n‖ = 1 := by
  rw [logCellStoppingVector, norm_logCellDyadic_pow,
    lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

private theorem inner_logCellStoppingVector_self (A n : ℕ+) :
    inner ℂ (logCellStoppingVector A n) (logCellStoppingVector A n) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_logCellStoppingVector]
  norm_num

/-- The original-cell cutoff is self-adjoint, before any physical source identification. -/
theorem inner_logCellGeneratorHead (A : ℕ) (x y : CellH) :
    inner ℂ (P A x) y = inner ℂ x (P A y) := by
  have hxy := inner_logCellGeneratorHead_tail A x y
  have hyx := inner_eq_zero_symm.mp (inner_logCellGeneratorHead_tail A y x)
  rw [inner_sub_right] at hxy
  rw [inner_sub_left] at hyx
  exact (sub_eq_zero.mp hxy).trans (sub_eq_zero.mp hyx).symm

/-- A projected original cell has one real coefficient along its actual stopping cell. -/
theorem exists_real_logCellGeneratorHead_single (A n : ℕ+) :
    ∃ c : ℝ, P A (e n) = (c : ℂ) • logCellStoppingVector A n := by
  have h : ∀ m : ℕ, ∀ hm : 0 < m,
      ∃ c : ℝ, P A (e ⟨m, hm⟩) = (c : ℂ) • logCellStoppingVector A ⟨m, hm⟩ := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hcut : m < 2 * (A : ℕ)
      · refine ⟨1, ?_⟩
        rw [logCellGeneratorHead_single_of_lt A ⟨m, hm⟩ hcut,
          logCellStoppingVector_of_lt A ⟨m, hm⟩ hcut, Complex.ofReal_one, one_smul]
      · let a : ℕ+ := ⟨m / 2, by have := A.pos; omega⟩
        obtain ⟨c, hc⟩ := ih (m / 2) (by omega) (by have := A.pos; omega)
        have hAa : (A : ℕ) ≤ (a : ℕ) := by change (A : ℕ) ≤ m / 2; omega
        have hd : P A (logCellDyadicDetail a) = 0 := by
          rw [logCellGeneratorHead_detail, if_neg (not_lt.mpr hAa)]
        have hv : logCellStoppingVector A ⟨m, hm⟩ = W (logCellStoppingVector A a) :=
          logCellStoppingVector_of_ge A ⟨m, hm⟩ (by change 2 * (A : ℕ) ≤ m; omega)
        have hcases : m = 2 * (a : ℕ) ∨ m = 2 * (a : ℕ) + 1 := by
          change m = 2 * (m / 2) ∨ m = 2 * (m / 2) + 1
          omega
        rcases hcases with hl | hr
        · have he : (⟨m, hm⟩ : ℕ+) = dyadicLeftCell a := PNat.eq hl
          refine ⟨dyadicLeftWeight a * c, ?_⟩
          calc
            _ = ((dyadicLeftWeight a * c : ℝ) : ℂ) • W (logCellStoppingVector A a) := by
              rw [he, dyadicLeftCell_eq_coarse_add_detail, map_add, map_smul, map_smul,
                logCellGeneratorHead_shift, hc, hd, smul_zero, add_zero, map_smul,
                smul_smul, Complex.ofReal_mul]
            _ = _ := by rw [hv]
        · have he : (⟨m, hm⟩ : ℕ+) = dyadicRightCell a := PNat.eq hr
          refine ⟨dyadicRightWeight a * c, ?_⟩
          calc
            _ = ((dyadicRightWeight a * c : ℝ) : ℂ) • W (logCellStoppingVector A a) := by
              rw [he, dyadicRightCell_eq_coarse_sub_detail, map_sub, map_smul, map_smul,
                logCellGeneratorHead_shift, hc, hd, smul_zero, sub_zero, map_smul,
                smul_smul, Complex.ofReal_mul]
            _ = _ := by rw [hv]
  exact h n n.pos

/-- The cutoff on each original cell is exactly its orthogonal component along the stopping cell. -/
theorem logCellGeneratorHead_single_eq_stopping (A n : ℕ+) :
    P A (e n) =
      inner ℂ (logCellStoppingVector A n) (e n) • logCellStoppingVector A n := by
  obtain ⟨c, hc⟩ := exists_real_logCellGeneratorHead_single A n
  have hi : inner ℂ (logCellStoppingVector A n) (P A (e n)) =
      inner ℂ (logCellStoppingVector A n) (e n) := by
    rw [← inner_logCellGeneratorHead, logCellGeneratorHead_stoppingVector]
  rw [hc, inner_smul_right, inner_logCellStoppingVector_self, mul_one] at hi
  rw [hc, hi]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_single_of_lt
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellStoppingAncestor_label_lt
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.le_logCellStoppingAncestor_label
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_real_logCellGeneratorHead_single
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_single_eq_stopping
