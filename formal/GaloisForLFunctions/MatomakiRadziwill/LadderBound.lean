import GaloisForLFunctions.MatomakiRadziwill.LadderTopTerms
import GaloisForLFunctions.MatomakiRadziwill.LadderMasterOn

/-!
# The mean square of the concrete ladder

For `L = log h ≥ 2^{20}` and `X` with `J ≥ 2` ladder scales, at frequencies `e ≤ W ≤ X e^{-L/2}`:

* the rough part (`ladder_rough_le`), integrated over any measurable `A ⊆ [−W, W]` with the top-scale
  bound needed on `A` only (`ladder_master_on`): the master inequality with the first step
  (`first_term_le`), the moment steps (the `j`-th at most `e^{-b_{j−1}} ≤ e^{-2^{j−1} L/2}`, summing to
  `≤ 2e^{-L/2}`), the Ramaré errors of the ladder scales (`≤ 256 · 52/a_0` in total), the top Ramaré
  error and the exceptional term with a pointwise bound `ρ` for the top blocks;
* the non-rough part (`ladder_nonrough_le`): `≤ 216 (4/log L + 4/log L + 1/(0.03 log log X − C_M))`,
  the harmonic masses of the ladder scales being `≥ log(b_j/a_j) − C_M` (Mertens), with
  `Σ_j 1/(log(b_j/a_j) − C_M) ≤ 4/log L + 4/log L` (`sum_inv_density_le`).
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The Ramaré error rate `10/H_j + 16/P_j` of ladder scale `j`. -/
def ladderRamG (L : ℝ) (j : ℕ) : ℝ :=
  10 / seqH L j + 16 / ((⌊Real.exp (seqA L j)⌋₊ + 1 : ℕ) : ℝ)

/-- The lower bounds `log(b_j/a_j) − C_M` for the harmonic masses are positive. -/
theorem ladder_density_pos {L : ℝ} (hL : 2 ^ 20 ≤ L) {D0 D1 : ℝ} (hD0 : 0 < D0) (hD1 : 0 < D1)
    (h0 : D0 ≤ Real.log (seqB L 0 / seqA L 0) - mertensScaleConst)
    (h1 : 2 * mertensScaleConst + 2 * D1 ≤ Real.log (seqA L 1)) (j : ℕ) :
    0 < Real.log (seqB L j / seqA L j) - mertensScaleConst := by
  have hCM0 := mertensScaleConst_nonneg
  cases j with
  | zero => linarith
  | succ k =>
    have hb : seqB L (k + 1) / seqA L (k + 1) = seqA L (k + 1) := by
      rw [seqB_succ_eq]
      have := one_le_seqA hL (k + 1)
      field_simp
    rw [hb]
    have hlog := log_seqA_ge hL k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hla1 : 0 ≤ Real.log (seqA L 1) := by linarith
    have : Real.log (seqA L 1) ≤ 2 ^ k * Real.log (seqA L 1) := le_mul_of_one_le_left hla1 h2k
    linarith

/-- `log ⌊e^s⌋ ≥ s − 1` for `s ≥ 1`. -/
theorem log_floor_exp_ge {s : ℝ} (hs : 1 ≤ s) : s - 1 ≤ Real.log (⌊Real.exp s⌋₊ : ℝ) := by
  have he : 1 ≤ Real.exp s := Real.one_le_exp (by linarith)
  have h1 : 1 ≤ ⌊Real.exp s⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact he)
  have h1' : (1 : ℝ) ≤ ⌊Real.exp s⌋₊ := by exact_mod_cast h1
  have h2 : Real.exp s < ⌊Real.exp s⌋₊ + 1 := Nat.lt_floor_add_one _
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : Real.exp (s - 1) ≤ Real.exp s / 2 := by
    rw [Real.exp_sub]
    exact div_le_div_of_nonneg_left (Real.exp_pos s).le (by norm_num) h2e
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- **The rough part of the concrete ladder.** -/
theorem ladder_rough_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hmul : ∀ a b, f (a * b) = f a * f b)
    {L : ℝ} (hL : 2 ^ 20 ≤ L)
    (hstep : ∀ x : ℝ, L / 2 ≤ x →
      144 * Real.exp 1 * 2 ^ 48 * x ^ 66 * Real.exp (-(152 / 100) * x) ≤ Real.exp (-x))
    {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) (hJ : 2 ≤ ladderJ hL (X : ℝ))
    (hlarge : 864 * Real.log X
      ≤ (Real.log X ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * Real.log X ^ (93 / 100 : ℝ))
    {W : ℝ} (hWe : Real.exp 1 ≤ W) (hWX : W ≤ X * Real.exp (-(L / 2))) {A : Set ℝ}
    (hAm : MeasurableSet A) (hAs : A ⊆ Icc (-W) W) {ρ : ℝ}
    (hρ : ∀ v ∈ (ladderConfig hL (X : ℝ)).topBlocks (Real.log X), ∀ w ∈ A,
      ‖blockQ f (ladderConfig hL (X : ℝ)).top (Real.log X) v w‖ ≤ ρ) :
    (∫ w in A, ‖logPoly (coefA f) ((ladderConfig hL (X : ℝ)).ladderS X) w‖ ^ 2)
      ≤ (2 * (256 * (52 / seqA L 0)) + 2 * (L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
            + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)))
          + 2 * (2 * Real.exp (-(L / 2))))
        + (2 * (256 * (10 / Real.log X + 16 * Real.exp (-ladderTopLow X)))
          + 2 * ((Real.log X ^ 2 + 2) ^ 2 * ρ ^ 2
            * (6 + 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
              * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
              + 384 * (Real.log X + 3)))) := by
  classical
  set C := ladderConfig hL (X : ℝ) with hC
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hX1' : 1 ≤ X := by exact_mod_cast hX1
  have hW1 : 1 ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hW0 : 0 ≤ W := by linarith
  have hexpL : Real.exp (-(L / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hWX' : W ≤ X := le_trans hWX (by nlinarith)
  have hCJ : C.J = ladderJ hL (X : ℝ) := rfl
  -- `log X ≥ b_0 = L/2 ≥ 2`
  have hlogX2 : 2 ≤ Real.log (X : ℝ) := by
    have h0 := seqB_le_of_lt_ladderJ hL (X : ℝ) (show 0 < ladderJ hL (X : ℝ) by omega)
    obtain ⟨hlh, hhX⟩ := ladderTop_le (one_le_log_of_exp_le hX)
    have : seqB L 0 = L / 2 := rfl
    linarith
  -- the hypotheses of the master inequality
  have hP2 : ∀ j, 2 ≤ ⌊Real.exp (seqA L j)⌋₊ + 1 := fun j => by
    have : 1 ≤ ⌊Real.exp (seqA L j)⌋₊ := Nat.le_floor (by
      rw [Nat.cast_one]; exact Real.one_le_exp (by linarith [one_le_seqA hL j]))
    omega
  have hPmin : ∀ j, ∀ p ∈ C.scale j, ⌊Real.exp (seqA L j)⌋₊ + 1 ≤ p := by
    intro j p hp
    have hp' : p ∈ ladderScale hL (X : ℝ) j := hp
    unfold ladderScale at hp'
    split_ifs at hp'
    · exact Nat.succ_le_of_lt (mem_primesIoc.mp hp').1
    · simp at hp'
  have hPtop2 : 2 ≤ ⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ + 1 := by
    have : 1 ≤ ⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ := Nat.le_floor (by
      rw [Nat.cast_one]; exact Real.one_le_exp (ladderTopLow_nonneg (by linarith)))
    omega
  have hPtopmin : ∀ p ∈ C.top, ⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ + 1 ≤ p := by
    intro p hp
    have hp' : p ∈ topScale (X : ℝ) := hp
    exact Nat.succ_le_of_lt (mem_primesIoc.mp hp').1
  have hmaster := C.ladder_master_on hf hmul (by rw [hCJ]; omega) hX1' hW1 hAm hAs (H := seqH L)
    (fun j => by linarith [(seqH_props hL j).1]) (Htop := Real.log X) hlogX2
    (P := fun j => ⌊Real.exp (seqA L j)⌋₊ + 1) hP2 hPmin hPtop2 hPtopmin
    (ladderC L) (fun j u => Real.exp_pos _) (ladderEll L) hρ
  -- the Ramaré errors
  have hram : ∀ j, ramErr W X (seqH L j) (⌊Real.exp (seqA L j)⌋₊ + 1) ≤ 256 * ladderRamG L j :=
    fun j => ramErr_le hX1' hW0 hWX' (by linarith [(seqH_props hL j).1]) (Nat.succ_pos _)
  have hsumram : ∑ j ∈ range C.J, ladderRamG L j ≤ 52 / seqA L 0 :=
    sum_ramare_le hL C.J (P := fun j => ((⌊Real.exp (seqA L j)⌋₊ + 1 : ℕ) : ℝ)) (fun j => by
      have h1 : seqA L j ≤ Real.exp (seqA L j) := by linarith [Real.add_one_le_exp (seqA L j)]
      have h2 : Real.exp (seqA L j) ≤ ((⌊Real.exp (seqA L j)⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; exact (Nat.lt_floor_add_one _).le
      exact le_trans h1 h2)
  have hsplit : ∑ j ∈ range C.J, ladderRamG L j
      = ladderRamG L 0 + ∑ j ∈ Finset.Ico 1 C.J, ladderRamG L j :=
    Finset.sum_range_eq_add_Ico _ (by rw [hCJ]; omega)
  -- the first step
  have hfirst : ((C.blocks (seqH L) 0).card : ℝ) * ∑ v ∈ C.blocks (seqH L) 0, ladderC L 0 v ^ 2
        * (∫ w in Icc (-W) W, ‖blockR f (C.scale 0) (C.restAt 0) X (seqH L 0) v w‖ ^ 2)
      ≤ L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)) :=
    first_term_le hf hL hX (by omega) hW1 hWX (C.restAt 0)
  have hA0 : 2 * ramErr W X (seqH L 0) (⌊Real.exp (seqA L 0)⌋₊ + 1)
        + 2 * (((C.blocks (seqH L) 0).card : ℝ) * ∑ v ∈ C.blocks (seqH L) 0, ladderC L 0 v ^ 2
          * (∫ w in Icc (-W) W, ‖blockR f (C.scale 0) (C.restAt 0) X (seqH L 0) v w‖ ^ 2))
      ≤ 2 * (256 * ladderRamG L 0) + 2 * (L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L))) :=
    add_le_add (mul_le_mul_of_nonneg_left (hram 0) (by norm_num))
      (mul_le_mul_of_nonneg_left hfirst (by norm_num))
  -- the moment steps
  have hstepj : ∀ j ∈ Finset.Ico 1 C.J,
      ((C.blocks (seqH L) j).card : ℝ) * ∑ v ∈ C.blocks (seqH L) j,
          ∑ u ∈ C.blocks (seqH L) (j - 1),
          ladderC L j v ^ 2 / ladderC L (j - 1) u ^ (2 * ladderEll L j u v)
          * (∫ w in Icc (-W) W, ‖blockQ f (C.scale (j - 1)) (seqH L (j - 1)) u w ^ ladderEll L j u v
              * blockR f (C.scale j) (C.restAt j) X (seqH L j) v w‖ ^ 2)
        ≤ Real.exp (-(2 ^ (j - 1) * (L / 2))) := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Ico.mp hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h := step_term_le hf hL hX hW1 hWX' (j := k) (by rw [← hCJ]; exact hjJ) (C.restAt (k + 1))
    refine le_trans h ?_
    have hbk : L / 2 ≤ seqB L k := seqB_mono hL (Nat.zero_le k)
    refine le_trans (hstep _ hbk) (Real.exp_le_exp.mpr ?_)
    have := seqB_ge (by linarith : (2 : ℝ) ≤ L) k
    linarith
  have hsumexp : ∑ j ∈ Finset.Ico 1 C.J, Real.exp (-(2 ^ (j - 1) * (L / 2)))
      ≤ 2 * Real.exp (-(L / 2)) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    exact sum_exp_neg_two_pow_le (by linarith) _
  have hIco : ∑ j ∈ Finset.Ico 1 C.J, (2 * ramErr W X (seqH L j) (⌊Real.exp (seqA L j)⌋₊ + 1)
        + 2 * (((C.blocks (seqH L) j).card : ℝ) * ∑ v ∈ C.blocks (seqH L) j,
          ∑ u ∈ C.blocks (seqH L) (j - 1),
          ladderC L j v ^ 2 / ladderC L (j - 1) u ^ (2 * ladderEll L j u v)
          * (∫ w in Icc (-W) W, ‖blockQ f (C.scale (j - 1)) (seqH L (j - 1)) u w ^ ladderEll L j u v
              * blockR f (C.scale j) (C.restAt j) X (seqH L j) v w‖ ^ 2)))
      ≤ 2 * (256 * ∑ j ∈ Finset.Ico 1 C.J, ladderRamG L j)
        + 2 * ∑ j ∈ Finset.Ico 1 C.J, Real.exp (-(2 ^ (j - 1) * (L / 2))) := by
    calc _ ≤ ∑ j ∈ Finset.Ico 1 C.J, (2 * (256 * ladderRamG L j)
            + 2 * Real.exp (-(2 ^ (j - 1) * (L / 2)))) :=
          sum_le_sum fun j hj => add_le_add (mul_le_mul_of_nonneg_left (hram j) (by norm_num))
            (mul_le_mul_of_nonneg_left (hstepj j hj) (by norm_num))
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the top scale
  have htopram := top_ramErr_le hX hW0 hWX'
  have hexc := top_exceptional_le hf hL hX hJ hlarge hWe hWX' ρ
  have hTop : 2 * ramErr W X (Real.log X) (⌊Real.exp (ladderTopLow (X : ℝ))⌋₊ + 1)
        + 2 * ((C.topBlocks (Real.log X)).card * ρ ^ 2 * ∑ v ∈ C.topBlocks (Real.log X),
          (∫ w in Icc (-W) W ∩ (C.smallSet f (seqH L) (ladderC L) (C.J - 1))ᶜ,
            ‖blockR f C.top C.restTop X (Real.log X) v w‖ ^ 2))
      ≤ 2 * (256 * (10 / Real.log X + 16 * Real.exp (-ladderTopLow X)))
        + 2 * ((Real.log X ^ 2 + 2) ^ 2 * ρ ^ 2
          * (6 + 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
            * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
            + 384 * (Real.log X + 3))) :=
    add_le_add (mul_le_mul_of_nonneg_left htopram (by norm_num))
      (mul_le_mul_of_nonneg_left hexc (by norm_num))
  refine le_trans hmaster (le_trans (add_le_add (add_le_add hA0 hIco) hTop) ?_)
  linarith

/-- **The integers outside the rough set, for the concrete ladder.** -/
theorem ladder_nonrough_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℝ} (hL : 2 ^ 20 ≤ L)
    (hlogL : 0 < Real.log L)
    (h0 : Real.log L / 4 ≤ Real.log (seqB L 0 / seqA L 0) - mertensScaleConst)
    (h1 : 2 * mertensScaleConst + 2 * (Real.log L / 2) ≤ Real.log (seqA L 1))
    {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) (htop1 : 1 ≤ ladderTopLow X)
    (htop2 : ladderTopLow X + 1 ≤ ladderTopHigh X)
    (htop3 : 0 < 3 / 100 * Real.log (Real.log X) - mertensScaleConst)
    {W : ℝ} (hW : 1 ≤ W) (hWX : W ≤ X) :
    (∫ w in Icc (-W) W,
        ‖fullPoly f X w - logPoly (coefA f) ((ladderConfig hL (X : ℝ)).ladderS X) w‖ ^ 2)
      ≤ 216 * (1 / (Real.log L / 4) + 2 / (Real.log L / 2)
        + 1 / (3 / 100 * Real.log (Real.log X) - mertensScaleConst)) := by
  set C := ladderConfig hL (X : ℝ) with hC
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hX1' : 1 ≤ X := by exact_mod_cast hX1
  have hlogX := one_le_log_of_exp_le hX
  have hD0 : 0 < Real.log L / 4 := by positivity
  have hD1 : 0 < Real.log L / 2 := by positivity
  have hApos := ladder_density_pos hL hD0 hD1 h0 h1
  have hA : ∀ j ∈ range C.J,
      Real.log (seqB L j / seqA L j) - mertensScaleConst ≤ ∑ p ∈ C.scale j, (1 : ℝ) / (p : ℝ) := by
    intro j hj
    have hjJ : j < ladderJ hL (X : ℝ) := Finset.mem_range.mp hj
    have hs : C.scale j = primesIoc ⌊Real.exp (seqA L j)⌋₊ ⌊Real.exp (seqB L j)⌋₊ := by
      show ladderScale hL (X : ℝ) j = _
      unfold ladderScale; rw [if_pos hjJ]
    rw [hs]
    exact sum_primesIoc_exp_ge (one_le_seqA hL j) (seqA_add_one_le_seqB hL j)
  have h := C.nonrough_le hf hX1' hW hWX (fun j _ => card_ladderScale_le hL hX j)
    (card_topScale_le hX) (A := fun j => Real.log (seqB L j / seqA L j) - mertensScaleConst)
    (fun j _ => hApos j) hA htop3 (top_density_ge (by linarith) htop1 htop2)
  refine le_trans h ?_
  have hsum := sum_inv_density_le hL C.J
    (A := fun j => Real.log (seqB L j / seqA L j) - mertensScaleConst) (fun j => le_rfl)
    hD0 hD1 h0 h1
  linarith

end

end GaloisForLFunctions.MatomakiRadziwill
