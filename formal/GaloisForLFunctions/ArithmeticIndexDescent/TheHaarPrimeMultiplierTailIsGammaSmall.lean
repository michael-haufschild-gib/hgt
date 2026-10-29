import GaloisForLFunctions.ArithmeticIndexDescent.EveryIntegerPrimeLagHasGammaSmallMixedTails
import GaloisForLFunctions.ArithmeticIndexDescent.TheFullDetailSourceRetainsCoarseGamma

/-!
# Small multiplier tails of the full Haar prime source

Odd-boundary incidence has uniformly bounded outgoing mass. Above a large
multiplier, its incoming divisor sum has a small logarithmic coefficient.
Weighted Young payment combines these two directions in the original
logarithmic detail norm, retaining every actual von Mangoldt coefficient.
-/

noncomputable section
open MeasureTheory Finset
open scoped InnerProductSpace
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The literal directed prime matrix on a selected finite set of multipliers. -/
def haarPrimeMatrixOn (s : Finset ℕ) (a b : ℕ) : ℝ :=
  ∑ m ∈ s, haarPrimeEntry a b m

/-- The original translated Haar pairing on the same multiplier set. -/
def haarPrimePairOn (s : Finset ℕ) (d e : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ m ∈ s, (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
    (inner ℂ (halfLineRightShift (Real.log m) (haarSection d X)) (haarSection e X)).re

theorem haarPrimePairOn_eq_matrix {s : Finset ℕ}
    (hs : ∀ m ∈ s, 2 ≤ m) (d e : ℕ → ℝ) (X : ℕ) :
    haarPrimePairOn s d e X = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
      2 * haarPrimeMatrixOn s a b * d a * e b := by
  classical
  unfold haarPrimePairOn
  calc
    _ = ∑ m ∈ s, ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        2 * haarPrimeEntry a b m * d a * e b := by
      apply sum_congr rfl
      intro m hm
      rw [inner_shift_haarSection d e X (hs m hm), mul_sum]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      unfold haarPrimeEntry
      split_ifs <;> ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      simp only [haarPrimeMatrixOn, sum_mul, mul_sum]

theorem haarPrimeMatrixOn_nonneg (s : Finset ℕ) (a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    0 ≤ haarPrimeMatrixOn s a b :=
  sum_nonneg fun m _ => haarPrimeEntry_nonneg a m hb

/-- Restricting multipliers preserves the horizon-independent outgoing bound. -/
theorem haarPrimeMatrixOn_row_le {s : Finset ℕ} {U a : ℕ}
    (hs : s ⊆ Icc 2 U) (ha : 1 ≤ a) (X : ℕ) :
    ∑ b ∈ Icc 1 X, haarPrimeMatrixOn s a b ≤ 16 * haarMass a := by
  apply le_trans ?_ (haarPrimeMatrix_row_le ha X U)
  apply sum_le_sum
  intro b hb
  exact sum_le_sum_of_subset_of_nonneg hs
    (fun m _ _ => haarPrimeEntry_nonneg a m (mem_Icc.mp hb).1)

private theorem sum_unique_indicator_le (s : Finset ℕ) (p : ℕ → Prop)
    [DecidablePred p] (f : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j)
    (hf : ∀ i ∈ s, p i → f i ≤ C) :
    (∑ i ∈ s, if p i then f i else 0) ≤ C := by
  by_cases h : ∃ i ∈ s, p i
  · obtain ⟨i, hi, hp⟩ := h
    rw [sum_eq_single i]
    · exact (if_pos hp).trans_le (hf i hi hp)
    · intro j hj hji
      exact if_neg (fun hpj => hji (hu j hj i hi hpj hp))
    · exact fun hn => False.elim (hn hi)
  · have hz : ∀ i ∈ s, (if p i then f i else 0) = 0 := by
      intro i hi
      exact if_neg (fun hp => h ⟨i, hi, hp⟩)
    rw [sum_eq_zero hz]
    exact hC

/-- Large multipliers have a small incoming coefficient by the exact divisor identity. -/
theorem haarPrimeMatrixOn_column_le {s : Finset ℕ} {N b : ℕ}
    (hN : 2 ≤ N) (hs : ∀ m ∈ s, N ≤ m) (hb : 1 ≤ b) (X : ℕ) :
    ∑ a ∈ Icc 1 X, haarPrimeMatrixOn s a b ≤
      (Real.log ((2 * b + 1 : ℕ) : ℝ) / Real.sqrt N) * haarMass b := by
  classical
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
  have hm (m : ℕ) (hm : m ∈ s) :
      (∑ a ∈ Icc 1 X, haarPrimeEntry a b m) ≤
        if m ∣ 2 * b + 1 then
          ArithmeticFunction.vonMangoldt m / Real.sqrt N * haarMass b else 0 := by
    have hmN := hs m hm
    have hm0 : 0 < m := by omega
    by_cases hd : m ∣ 2 * b + 1
    · rw [if_pos hd]
      unfold haarPrimeEntry
      apply sum_unique_indicator_le
      · exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hsqrt.le)
          (haarMass_pos hb).le
      · intro a _ a' _ he he'
        have h := Nat.eq_of_mul_eq_mul_right hm0 (he.trans he'.symm)
        omega
      · intro a _ _
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hsqrt
            (Real.sqrt_le_sqrt (by exact_mod_cast hmN))) (haarMass_pos hb).le
    · rw [if_neg hd]
      apply le_of_eq
      apply sum_eq_zero
      intro a _
      apply if_neg
      intro he
      exact hd ⟨2 * a + 1, by simpa only [Nat.mul_comm] using he.symm⟩
  let D := s.filter (fun m => m ∣ 2 * b + 1)
  have hD : D ⊆ (2 * b + 1).divisors := by
    intro m hm
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hm).2, by omega⟩
  have hsum : ∑ m ∈ D, ArithmeticFunction.vonMangoldt m ≤
      Real.log ((2 * b + 1 : ℕ) : ℝ) := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    exact sum_le_sum_of_subset_of_nonneg hD fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
  unfold haarPrimeMatrixOn
  rw [sum_comm]
  calc
    _ ≤ ∑ m ∈ s, if m ∣ 2 * b + 1 then
        ArithmeticFunction.vonMangoldt m / Real.sqrt N * haarMass b else 0 :=
      sum_le_sum hm
    _ = ∑ m ∈ D, ArithmeticFunction.vonMangoldt m / Real.sqrt N * haarMass b := by
      simp only [D, sum_filter]
    _ = ((∑ m ∈ D, ArithmeticFunction.vonMangoldt m) / Real.sqrt N) * haarMass b := by
      rw [← sum_mul, ← sum_div]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hsum hsqrt.le) (haarMass_pos hb).le

/-- The exact detail norm is paid by its logarithmic coefficient mass. -/
theorem cellGammaWeight_mul_norm_haar_tail_sq_le_logMass (d : ℕ → ℝ)
    {A : ℕ} (hA : 1 ≤ A) (X : ℕ) :
    cellGammaWeight A * ‖haarSection (fun a => if A ≤ a then d a else 0) X‖ ^ 2 ≤
      haarLogarithmicMass d X := by
  rw [norm_haarSection_sq, haarLogarithmicMass, mul_sum]
  apply sum_le_sum
  intro a ha
  have ha1 := (mem_Icc.mp ha).1
  have hmass := (haarMass_pos ha1).le
  by_cases hAa : A ≤ a
  · rw [if_pos hAa]
    convert mul_le_mul_of_nonneg_right (cellGammaWeight_mono hA hAa)
      (mul_nonneg hmass (sq_nonneg (d a))) using 1
    ring
  · rw [if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero, mul_zero]
    exact mul_nonneg (mul_nonneg (cellGammaWeight_pos ha1).le hmass) (sq_nonneg _)

theorem cellGammaWeight_one_mul_norm_haar_sq_le_logMass (d : ℕ → ℝ) (X : ℕ) :
    cellGammaWeight 1 * ‖haarSection d X‖ ^ 2 ≤ haarLogarithmicMass d X := by
  have he : haarSection (fun a => if 1 ≤ a then d a else 0) X = haarSection d X := by
    apply sum_congr rfl
    intro a ha
    simp only [if_pos (mem_Icc.mp ha).1]
  simpa only [he] using cellGammaWeight_mul_norm_haar_tail_sq_le_logMass d (le_refl 1) X

/-- Arbitrary pair averages do not erase any of the original logarithmic detail norm. -/
theorem haarLogarithmicMass_le_completeGamma (q d : ℕ → ℝ) (X : ℕ) :
    haarLogarithmicMass d X ≤ levyEnergy (completePairProfile q d X) := by
  apply le_trans ?_ (sum_cellGammaWeight_variance_le_gamma
    (completePairProfile_bv q d X) (completePairProfile_compact q d X) X)
  apply sum_le_sum
  intro a ha
  rw [intervalVariance_completePairProfile q d (mem_Icc.mp ha).1 (mem_Icc.mp ha).2]
  exact le_of_eq (mul_assoc _ _ _)

private theorem log_odd_le_cellGammaWeight_add_two {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ cellGammaWeight a + 2 := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ho : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos ho ha0)
  rw [Real.log_div ho.ne' ha0.ne'] at h
  have hd : ((2 * a + 1 : ℕ) : ℝ) / (a : ℝ) ≤ 3 := by
    rw [div_le_iff₀ ha0]
    exact_mod_cast (show 2 * a + 1 ≤ 3 * a by omega)
  linarith only [h, hd, log_le_cellGammaWeight ha]

/-- The logarithm appearing in the divisor sum is bounded in the actual detail norm. -/
theorem haarOddLogMass_le_logMass (d : ℕ → ℝ) (A X : ℕ) :
    (∑ a ∈ Icc 1 X, Real.log ((2 * a + 1 : ℕ) : ℝ) * haarMass a *
      (if A ≤ a then d a else 0) ^ 2) ≤
        (1 + 2 / cellGammaWeight 1) * haarLogarithmicMass d X := by
  have hM := (le_div_iff₀ (cellGammaWeight_pos (le_refl 1))).mpr
    (show ‖haarSection d X‖ ^ 2 * cellGammaWeight 1 ≤ haarLogarithmicMass d X by
      simpa only [mul_comm] using cellGammaWeight_one_mul_norm_haar_sq_le_logMass d X)
  calc
    _ ≤ ∑ a ∈ Icc 1 X, (cellGammaWeight a + 2) * haarMass a * d a ^ 2 := by
      apply sum_le_sum
      intro a ha
      have ha1 := (mem_Icc.mp ha).1
      by_cases hAa : A ≤ a
      · rw [if_pos hAa]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (log_odd_le_cellGammaWeight_add_two ha1)
            (haarMass_pos ha1).le) (sq_nonneg _)
      · rw [if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
        exact mul_nonneg (mul_nonneg (by have := cellGammaWeight_pos ha1; positivity)
          (haarMass_pos ha1).le) (sq_nonneg _)
    _ = haarLogarithmicMass d X + 2 * ‖haarSection d X‖ ^ 2 := by
      rw [haarLogarithmicMass, norm_haarSection_sq, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ haarLogarithmicMass d X + 2 * (haarLogarithmicMass d X / cellGammaWeight 1) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

private theorem weighted_matrix_young (s : Finset ℕ) (K : ℕ → ℕ → ℝ)
    (x y : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hK : ∀ a ∈ s, ∀ b ∈ s, 0 ≤ K a b) :
    t * |∑ a ∈ s, ∑ b ∈ s, 2 * K a b * x a * y b| ≤
      t ^ 2 * (∑ a ∈ s, (∑ b ∈ s, K a b) * x a ^ 2) +
        ∑ b ∈ s, (∑ a ∈ s, K a b) * y b ^ 2 := by
  have habs : |∑ a ∈ s, ∑ b ∈ s, 2 * K a b * x a * y b| ≤
      ∑ a ∈ s, ∑ b ∈ s, 2 * K a b * |x a| * |y b| := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro a ha
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro b hb
    exact le_of_eq (by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (hK a ha b hb)])
  calc
    _ ≤ t * ∑ a ∈ s, ∑ b ∈ s, 2 * K a b * |x a| * |y b| :=
      mul_le_mul_of_nonneg_left habs ht
    _ ≤ ∑ a ∈ s, ∑ b ∈ s, K a b * (t ^ 2 * x a ^ 2 + y b ^ 2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro a ha
      rw [mul_sum]
      apply sum_le_sum
      intro b hb
      have h := mul_nonneg (hK a ha b hb) (sq_nonneg (t * |x a| - |y b|))
      simp only [sub_sq, mul_pow, sq_abs] at h
      nlinarith only [h]
    _ = _ := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      · simp only [sum_mul, mul_sum]
        apply sum_congr rfl
        intro a _
        apply sum_congr rfl
        intro b _
        ring
      · rw [sum_comm]
        simp only [sum_mul]

/-- Weighted outgoing and incoming payments retain all large-multiplier signs. -/
theorem haarPrimePairOn_tail_young {s : Finset ℕ} {N X : ℕ}
    (hN : 2 ≤ N) (hs : s ⊆ Icc 2 (2 * X + 1)) (hlarge : ∀ m ∈ s, N ≤ m)
    (d : ℕ → ℝ) (A : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t * |haarPrimePairOn s d (fun a => if A ≤ a then d a else 0) X| ≤
      (16 * t ^ 2 / cellGammaWeight 1 +
        (1 + 2 / cellGammaWeight 1) / Real.sqrt N) * haarLogarithmicMass d X := by
  have hM : ‖haarSection d X‖ ^ 2 ≤ haarLogarithmicMass d X / cellGammaWeight 1 := by
    apply (le_div_iff₀ (cellGammaWeight_pos (le_refl 1))).mpr
    simpa only [mul_comm] using cellGammaWeight_one_mul_norm_haar_sq_le_logMass d X
  have hrow : (∑ a ∈ Icc 1 X, (∑ b ∈ Icc 1 X, haarPrimeMatrixOn s a b) * d a ^ 2) ≤
      16 * ‖haarSection d X‖ ^ 2 := by
    rw [norm_haarSection_sq, mul_sum]
    apply sum_le_sum
    intro a ha
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (haarPrimeMatrixOn_row_le hs (mem_Icc.mp ha).1 X) (sq_nonneg (d a))
  have hcol : (∑ b ∈ Icc 1 X, (∑ a ∈ Icc 1 X, haarPrimeMatrixOn s a b) *
      (if A ≤ b then d b else 0) ^ 2) ≤
        ((1 + 2 / cellGammaWeight 1) * haarLogarithmicMass d X) / Real.sqrt N := by
    calc
      _ ≤ (∑ b ∈ Icc 1 X, Real.log ((2 * b + 1 : ℕ) : ℝ) * haarMass b *
          (if A ≤ b then d b else 0) ^ 2) / Real.sqrt N := by
        rw [sum_div]
        apply sum_le_sum
        intro b hb
        convert mul_le_mul_of_nonneg_right
          (haarPrimeMatrixOn_column_le hN hlarge (mem_Icc.mp hb).1 X)
            (sq_nonneg (if A ≤ b then d b else 0)) using 1 <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (haarOddLogMass_le_logMass d A X) (Real.sqrt_nonneg _)
  rw [haarPrimePairOn_eq_matrix (fun m hm => (mem_Icc.mp (hs hm)).1)]
  have h := weighted_matrix_young (Icc 1 X) (haarPrimeMatrixOn s) d
    (fun a => if A ≤ a then d a else 0) ht
    (fun a _ b hb => haarPrimeMatrixOn_nonneg s a (mem_Icc.mp hb).1)
  calc
    _ ≤ t ^ 2 * (16 * ‖haarSection d X‖ ^ 2) +
        ((1 + 2 / cellGammaWeight 1) * haarLogarithmicMass d X) / Real.sqrt N :=
      h.trans (add_le_add (mul_le_mul_of_nonneg_left hrow (sq_nonneg t)) hcol)
    _ ≤ t ^ 2 * (16 * (haarLogarithmicMass d X / cellGammaWeight 1)) +
        ((1 + 2 / cellGammaWeight 1) * haarLogarithmicMass d X) / Real.sqrt N :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 16)) (sq_nonneg t)) (le_refl _)
    _ = _ := by ring

/-- One large-multiplier cutoff works for every signed profile, detail cutoff and horizon. -/
theorem exists_haarPrime_multiplier_tail_small {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d : ℕ → ℝ) (A X : ℕ) (s : Finset ℕ),
      s ⊆ Icc 2 (2 * X + 1) → (∀ m ∈ s, N ≤ m) →
      |haarPrimePairOn s d (fun a => if A ≤ a then d a else 0) X| ≤
        ε * haarLogarithmicMass d X := by
  let w := cellGammaWeight 1
  have hw : 0 < w := cellGammaWeight_pos (le_refl 1)
  let C := 1 + 2 / w
  have hC : 0 < C := by dsimp only [C]; positivity
  let t := ε * w / 32
  have ht : 0 < t := by dsimp only [t]; positivity
  let B := 2 * C / (t * ε)
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 2 (B ^ 2))
  have hN2 : 2 ≤ N := by
    have hn : (2 : ℝ) ≤ N := (le_max_left _ _).trans hN.le
    exact_mod_cast hn
  have hNsqrt : B ≤ Real.sqrt (N : ℝ) :=
    (Real.le_sqrt hB.le (Nat.cast_nonneg N)).mpr ((le_max_right _ _).trans hN.le)
  have hlarge : C / Real.sqrt N ≤ t * ε / 2 := by
    have hnpos : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))
    apply (div_le_iff₀ hnpos).mpr
    have h := (div_le_iff₀ (mul_pos ht hε)).mp hNsqrt
    nlinarith only [h]
  have hrow : 16 * t ^ 2 / w = t * ε / 2 := by
    dsimp only [t]
    field_simp [hw.ne']
    ring
  refine ⟨N, hN2, ?_⟩
  intro d A X s hs hm
  have h := haarPrimePairOn_tail_young hN2 hs hm d A ht.le
  change t * |haarPrimePairOn s d (fun a => if A ≤ a then d a else 0) X| ≤
    (16 * t ^ 2 / w + C / Real.sqrt N) * haarLogarithmicMass d X at h
  rw [hrow] at h
  apply le_of_mul_le_mul_left (a := t) ?_ ht
  calc
    _ ≤ (t * ε / 2 + C / Real.sqrt N) * haarLogarithmicMass d X := h
    _ ≤ (t * ε / 2 + t * ε / 2) * haarLogarithmicMass d X :=
      mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hlarge) (haarLogarithmicMass_nonneg d X)
    _ = _ := by ring

end GaloisForLFunctions.ArithmeticIndexDescent
