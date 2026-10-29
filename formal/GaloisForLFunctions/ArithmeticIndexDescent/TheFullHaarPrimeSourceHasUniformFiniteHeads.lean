import GaloisForLFunctions.ArithmeticIndexDescent.TheHaarPrimeMultiplierTailIsGammaSmall

/-!
# Uniform finite heads for the entire Haar prime source

The large prime multipliers are small in logarithmic detail energy. For each
remaining multiplier, a sufficiently high target has a high source as well.
The actual detail mass then controls the finite remainder. Upward incidence
identifies this pairing with the original prime quadratic form minus its
coefficient head, including every first prime and every higher power.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Total weight of the finite set of original prime multipliers through `N`. -/
def finiteHaarPrimeWeight (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 2 N, 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m

theorem finiteHaarPrimeWeight_nonneg (N : ℕ) : 0 ≤ finiteHaarPrimeWeight N :=
  sum_nonneg fun _ _ => div_nonneg
    (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)

theorem haarPrimeEnergy_eq_pairOn (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy d X = haarPrimePairOn (Icc 2 (2 * X + 1)) d d X := by
  rw [haarPrimeEnergy_eq, haarPrimePairOn]
  apply sum_congr rfl
  intro m hm
  rw [inner_shift_haarSection d d X (mem_Icc.mp hm).1]

/-- Only a high target contributes to the exact error of a coefficient head. -/
theorem inner_shift_haar_head_error (d : ℕ → ℝ) (A X : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection d X)) (haarSection d X)).re -
      (inner ℂ (halfLineRightShift (Real.log m)
        (haarSection (fun a => if a < A then d a else 0) X))
          (haarSection (fun a => if a < A then d a else 0) X)).re =
      (inner ℂ (halfLineRightShift (Real.log m) (haarSection d X))
        (haarSection (fun a => if A ≤ a then d a else 0) X)).re := by
  rw [inner_shift_haarSection _ _ X hm, inner_shift_haarSection _ _ X hm,
    inner_shift_haarSection _ _ X hm, ← sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro b _
  by_cases he : (2 * a + 1) * m = 2 * b + 1
  · have hab : a ≤ b := by
      have h := Nat.mul_le_mul_left (2 * a + 1) (show 1 ≤ m by omega)
      rw [Nat.mul_one, he] at h
      omega
    by_cases hb : b < A
    · have ha : a < A := hab.trans_lt hb
      simp only [if_pos he, if_pos ha, if_pos hb, if_neg (by omega : ¬A ≤ b),
        sub_self, mul_zero, zero_mul]
    · simp only [if_pos he, if_neg hb, if_pos (by omega : A ≤ b), mul_zero, zero_mul, sub_zero]
  · simp only [if_neg he, mul_zero, sub_self]

/-- The complete source error is one oriented pairing with the literal high detail. -/
theorem haarPrimeEnergy_sub_head_eq_pairOn (d : ℕ → ℝ) (A X : ℕ) :
    haarPrimeEnergy d X - haarPrimeEnergy (fun a => if a < A then d a else 0) X =
      haarPrimePairOn (Icc 2 (2 * X + 1)) d (fun a => if A ≤ a then d a else 0) X := by
  rw [haarPrimeEnergy_eq_pairOn, haarPrimeEnergy_eq_pairOn]
  simp only [haarPrimePairOn]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [← mul_sub, inner_shift_haar_head_error d A X (mem_Icc.mp hm).1]

/-- A bounded multiplier cannot carry a low source index into an arbitrarily high target. -/
theorem inner_shift_haar_high_target_eq_high_input (d : ℕ → ℝ) (X : ℕ)
    {A B N m : ℕ} (hA : N * (B + 1) ≤ A) (hm : 2 ≤ m) (hmN : m ≤ N) :
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection d X))
      (haarSection (fun a => if A ≤ a then d a else 0) X)).re =
      (inner ℂ (halfLineRightShift (Real.log m)
        (haarSection (fun a => if B ≤ a then d a else 0) X))
          (haarSection (fun a => if A ≤ a then d a else 0) X)).re := by
  rw [inner_shift_haarSection _ _ X hm, inner_shift_haarSection _ _ X hm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hb : A ≤ b
  · rw [if_pos hb]
    by_cases he : (2 * a + 1) * m = 2 * b + 1
    · have hBa : B ≤ a := by
        by_contra ha
        have hprod := Nat.mul_le_mul (show 2 * a + 1 ≤ 2 * B + 1 by omega) hmN
        rw [he] at hprod
        have hbottom := hA.trans hb
        nlinarith only [hprod, hbottom, Nat.zero_le N]
      rw [if_pos hBa]
    · simp only [if_neg he, mul_zero]
  · simp only [if_neg hb, mul_zero, zero_mul]

/-- A fixed multiplier is small after a fixed target head in the original detail norm. -/
theorem cellGammaWeight_mul_abs_bounded_haar_pair_le_logMass (d : ℕ → ℝ) (X : ℕ)
    {A B N m : ℕ} (hB : 1 ≤ B) (hA : N * (B + 1) ≤ A)
    (hm : 2 ≤ m) (hmN : m ≤ N) :
    cellGammaWeight B * |(inner ℂ (halfLineRightShift (Real.log m) (haarSection d X))
      (haarSection (fun a => if A ≤ a then d a else 0) X)).re| ≤ haarLogarithmicMass d X := by
  rw [inner_shift_haar_high_target_eq_high_input d X hA hm hmN]
  have hBA : B ≤ A := by
    have h := Nat.mul_le_mul_right (B + 1) (show 1 ≤ N by omega)
    simp only [Nat.one_mul] at h
    exact (Nat.le_succ B).trans (h.trans hA)
  have hU := cellGammaWeight_mul_norm_haar_tail_sq_le_logMass d hB X
  have hV : cellGammaWeight B *
      ‖haarSection (fun a => if A ≤ a then d a else 0) X‖ ^ 2 ≤ haarLogarithmicMass d X :=
    (mul_le_mul_of_nonneg_right (cellGammaWeight_mono hB hBA) (sq_nonneg _)).trans
      (cellGammaWeight_mul_norm_haar_tail_sq_le_logMass d (hB.trans hBA) X)
  have hpair : |(inner ℂ (halfLineRightShift (Real.log m)
      (haarSection (fun a => if B ≤ a then d a else 0) X))
        (haarSection (fun a => if A ≤ a then d a else 0) X)).re| ≤
      ‖haarSection (fun a => if B ≤ a then d a else 0) X‖ *
        ‖haarSection (fun a => if A ≤ a then d a else 0) X‖ := by
    exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_halfLineRightShift_le _ _) (norm_nonneg _)))
  have hscaled := mul_le_mul_of_nonneg_left hpair (cellGammaWeight_pos hB).le
  have hyoung := mul_nonneg (cellGammaWeight_pos hB).le
    (sq_nonneg (‖haarSection (fun a => if B ≤ a then d a else 0) X‖ -
      ‖haarSection (fun a => if A ≤ a then d a else 0) X‖))
  nlinarith only [hscaled, hyoung, hU, hV]

/-- The whole finite multiplier set has the same high-target payment. -/
theorem cellGammaWeight_mul_abs_finite_haarPrimePair_le (d : ℕ → ℝ) (X : ℕ)
    {s : Finset ℕ} {A B N : ℕ} (hB : 1 ≤ B) (hA : N * (B + 1) ≤ A)
    (hs : s ⊆ Icc 2 N) :
    cellGammaWeight B * |haarPrimePairOn s d (fun a => if A ≤ a then d a else 0) X| ≤
      finiteHaarPrimeWeight N * haarLogarithmicMass d X := by
  have hw (m : ℕ) : 0 ≤ 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m :=
    div_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
      (Real.sqrt_nonneg _)
  rw [haarPrimePairOn]
  calc
    _ ≤ cellGammaWeight B * ∑ m ∈ s,
        |(2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
          (inner ℂ (halfLineRightShift (Real.log m) (haarSection d X))
            (haarSection (fun a => if A ≤ a then d a else 0) X)).re| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (cellGammaWeight_pos hB).le
    _ ≤ ∑ m ∈ s, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        haarLogarithmicMass d X := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      rw [abs_mul, abs_of_nonneg (hw m)]
      calc
        _ = (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
            (cellGammaWeight B * |(inner ℂ (halfLineRightShift (Real.log m) (haarSection d X))
              (haarSection (fun a => if A ≤ a then d a else 0) X)).re|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (cellGammaWeight_mul_abs_bounded_haar_pair_le_logMass d X hB hA
            (mem_Icc.mp (hs hm)).1 (mem_Icc.mp (hs hm)).2) (hw m)
    _ = (∑ m ∈ s, 2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
        haarLogarithmicMass d X := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => hw m)) (haarLogarithmicMass_nonneg d X)

/-- The full all-prime Haar form admits uniform finite coefficient heads in logarithmic energy. -/
theorem exists_haarPrime_finite_head_logMass (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d : ℕ → ℝ) (X : ℕ),
      |haarPrimeEnergy d X - haarPrimeEnergy (fun a => if a < A then d a else 0) X| ≤
        ε * haarLogarithmicMass d X := by
  classical
  obtain ⟨N, hN, hlarge⟩ := exists_haarPrime_multiplier_tail_small (show 0 < ε / 2 by positivity)
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.exp (2 * finiteHaarPrimeWeight N / ε))
  have hB1 : 1 ≤ B := by
    have hp : (0 : ℝ) < B := (Real.exp_pos _).trans hB
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hcap : finiteHaarPrimeWeight N ≤ (ε / 2) * cellGammaWeight B := by
    have hl := Real.log_lt_log (Real.exp_pos _) hB
    rw [Real.log_exp] at hl
    have h := (div_le_iff₀ hε).mp (hl.le.trans (log_le_cellGammaWeight hB1))
    linarith only [h]
  let A := N * (B + 1)
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    have h := Nat.mul_le_mul (show 1 ≤ N by omega) (show 1 ≤ B + 1 by omega)
    simpa only [Nat.one_mul] using h
  refine ⟨A, hA1, ?_⟩
  intro d X
  let lo := (Icc 2 (2 * X + 1)).filter (fun m => m < N)
  let hi := (Icc 2 (2 * X + 1)).filter (fun m => ¬m < N)
  have hlo : lo ⊆ Icc 2 N := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hm).1).1, (mem_filter.mp hm).2.le⟩
  have hhi : hi ⊆ Icc 2 (2 * X + 1) := filter_subset _ _
  have hhlarge : ∀ m ∈ hi, N ≤ m := fun _ hm => le_of_not_gt (mem_filter.mp hm).2
  have hsmall : |haarPrimePairOn lo d (fun a => if A ≤ a then d a else 0) X| ≤
      (ε / 2) * haarLogarithmicMass d X := by
    apply le_of_mul_le_mul_left (a := cellGammaWeight B) ?_ (cellGammaWeight_pos hB1)
    calc
      _ ≤ finiteHaarPrimeWeight N * haarLogarithmicMass d X :=
        cellGammaWeight_mul_abs_finite_haarPrimePair_le d X hB1 (le_refl A) hlo
      _ ≤ ((ε / 2) * cellGammaWeight B) * haarLogarithmicMass d X :=
        mul_le_mul_of_nonneg_right hcap (haarLogarithmicMass_nonneg d X)
      _ = _ := by ring
  have hbig := hlarge d A X hi hhi hhlarge
  have hsplit : haarPrimePairOn lo d (fun a => if A ≤ a then d a else 0) X +
      haarPrimePairOn hi d (fun a => if A ≤ a then d a else 0) X =
        haarPrimePairOn (Icc 2 (2 * X + 1)) d (fun a => if A ≤ a then d a else 0) X :=
    sum_filter_add_sum_filter_not _ (fun m => m < N) _
  rw [haarPrimeEnergy_sub_head_eq_pairOn, ← hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hsmall hbig).trans_eq (by ring))

/-- The finite-head threshold is uniform over all original complete profiles and horizons. -/
theorem exists_uniform_finite_head_for_haar_prime (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |haarPrimeEnergy d X - haarPrimeEnergy (fun a => if a < A then d a else 0) X| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hhead⟩ := exists_haarPrime_finite_head_logMass ε hε
  exact ⟨A, hA, fun q d X => (hhead d X).trans
    (mul_le_mul_of_nonneg_left (haarLogarithmicMass_le_completeGamma q d X) hε.le)⟩

theorem haarLogarithmicMass_tail_le (d : ℕ → ℝ) (A X : ℕ) :
    haarLogarithmicMass (fun a => if A ≤ a then d a else 0) X ≤ haarLogarithmicMass d X := by
  apply sum_le_sum
  intro a ha
  by_cases hAa : A ≤ a
  · simp only [if_pos hAa, le_refl]
  · simp only [if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact mul_nonneg (mul_nonneg (cellGammaWeight_pos (mem_Icc.mp ha).1).le
      (haarMass_pos (mem_Icc.mp ha).1).le) (sq_nonneg _)

/-- The entire first-prime and higher-power detail diagonal is small in the untruncated Gamma source. -/
theorem exists_haarPrime_tail_small_originalGamma (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      |haarPrimeEnergy (fun a => if A ≤ a then d a else 0) X| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA, hhead⟩ := exists_haarPrime_finite_head_logMass ε hε
  refine ⟨A, hA, ?_⟩
  intro q d X
  have he : (fun a => if a < A then (if A ≤ a then d a else 0) else 0) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext a
    by_cases ha : a < A
    · rw [if_pos ha, if_neg (by omega : ¬A ≤ a)]
    · rw [if_neg ha]
  have hz : haarPrimeEnergy (fun _ : ℕ => (0 : ℝ)) X = 0 := by
    rw [haarPrimeEnergy_matrix]
    simp only [mul_zero, sum_const_zero]
  have h := hhead (fun a => if A ≤ a then d a else 0) X
  rw [he, hz, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    ((haarLogarithmicMass_tail_le d A X).trans (haarLogarithmicMass_le_completeGamma q d X)) hε.le)

end GaloisForLFunctions.ArithmeticIndexDescent
