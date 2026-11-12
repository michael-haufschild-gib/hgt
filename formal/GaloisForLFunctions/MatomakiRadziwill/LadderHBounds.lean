import GaloisForLFunctions.MatomakiRadziwill.LadderConfig

/-!
# The `h`-dependent terms of the ladder

For `L = log h ≥ 2^{20}`, summed over any number `J` of ladder scales:

* growth: `a_j ≥ 2^j a_0` (`seqA_ge`), and `log a_{j+1} ≥ 2^j log a_1` (`log_seqA_ge`);
* the Ramaré errors: `Σ_{j<J} (10/H_j + 16/P_j) ≤ 52/a_0` whenever `P_j ≥ a_j` (`sum_ramare_le`);
* the moment steps: with `b = b_{j−1}`, each step is at most `C b^{66} e^{-1.52 b}`, which is
  `≤ e^{-b}` for `b ≥ b*` (`exists_poly_exp_le`), and `Σ_k e^{-2^k b_0} ≤ 2e^{-b_0}`
  (`sum_exp_neg_two_pow_le`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem seqA_ge {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) : 2 ^ j * seqA L 0 ≤ seqA L j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := seqA_add_one_le_seqB hL j
    have hb := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
    have h2 : seqA L (j + 1) = 2 * seqB L j ^ 2 := rfl
    have h3 : seqB L j ≤ seqB L j ^ 2 := by nlinarith
    rw [pow_succ, h2]
    nlinarith

theorem seqA_zero_pos {L : ℝ} (hL : 2 ^ 20 ≤ L) : 0 < seqA L 0 := by
  have := one_le_seqA hL 0; linarith

/-- **The Ramaré errors of the ladder scales.** -/
theorem sum_ramare_le {L : ℝ} (hL : 2 ^ 20 ≤ L) (J : ℕ) {P : ℕ → ℝ}
    (hP : ∀ j, seqA L j ≤ P j) :
    ∑ j ∈ range J, (10 / seqH L j + 16 / P j) ≤ 52 / seqA L 0 := by
  have ha0 := seqA_zero_pos hL
  have hterm : ∀ j ∈ range J, 10 / seqH L j + 16 / P j ≤ 26 / seqA L 0 * (1 / 2) ^ j := by
    intro j _
    have hA := seqA_ge hL j
    have ha1 := one_le_seqA hL j
    have hHa : seqA L j ≤ seqH L j := by
      cases j with
      | zero =>
        simp only [seqH, seqA]
        have hlog : Real.log L ≤ L := le_trans (Real.log_le_sub_one_of_pos (by linarith))
          (by linarith)
        have hL25 : L ≤ L ^ 25 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 25 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have hlog2 : 200 * Real.log L ≤ L := by
          have := log_le_div_of_large hL
          linarith
        linarith
      | succ j =>
        simp only [seqH]
        calc seqA L (j + 1) = seqA L (j + 1) ^ 1 := (pow_one _).symm
          _ ≤ seqA L (j + 1) ^ 8 := pow_le_pow_right₀ ha1 (by norm_num)
    have h1 : 10 / seqH L j ≤ 10 / seqA L j := div_le_div_of_nonneg_left (by norm_num) (by linarith) hHa
    have h2 : 16 / P j ≤ 16 / seqA L j :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (hP j)
    have h3 : 26 / seqA L j ≤ 26 / (2 ^ j * seqA L 0) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hA
    have h4 : 26 / (2 ^ j * seqA L 0) = 26 / seqA L 0 * (1 / 2) ^ j := by
      rw [one_div_pow]; field_simp
    have h5 : 10 / seqA L j + 16 / seqA L j = 26 / seqA L j := by ring
    linarith
  calc ∑ j ∈ range J, (10 / seqH L j + 16 / P j)
      ≤ ∑ j ∈ range J, 26 / seqA L 0 * (1 / 2) ^ j := sum_le_sum hterm
    _ = 26 / seqA L 0 * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ 26 / seqA L 0 * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)
        rw [Finset.range_eq_Ico]
        calc ∑ i ∈ Ico 0 J, (1 / 2 : ℝ) ^ i ≤ (1 / 2) ^ 0 / (1 - 1 / 2) := this
          _ = 2 := by norm_num
    _ = 52 / seqA L 0 := by ring

/-- **A polynomial times `e^{-1.52x}` is eventually at most `e^{-x}`.** -/
theorem exists_poly_exp_le (C : ℝ) (n : ℕ) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → C * x ^ n * Real.exp (-(152 / 100) * x) ≤ Real.exp (-x) := by
  have hlim := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 52 / 100))
  have hpos : (0 : ℝ) < (52 / 100) ^ n / (|C| + 1) := by positivity
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨max x₁ 1, by positivity, fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have h := hx₁ x hx1
  simp only [Function.comp, id] at h
  -- `(0.52 x)^n e^{-0.52x} < 0.52^n/(|C|+1)`, so `x^n e^{-0.52x} < 1/(|C|+1)`
  have h52 : (0 : ℝ) < (52 / 100) ^ n := by positivity
  have h2 : x ^ n * Real.exp (-(52 / 100 * x)) * (|C| + 1) < 1 := by
    rw [mul_pow] at h
    have h3 : (52 / 100 : ℝ) ^ n * (x ^ n * Real.exp (-(52 / 100 * x)))
        < (52 / 100) ^ n / (|C| + 1) := by linarith
    rw [lt_div_iff₀ (by positivity)] at h3
    nlinarith
  have hexp : Real.exp (-(152 / 100) * x) = Real.exp (-(52 / 100 * x)) * Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  have hE := Real.exp_pos (-x)
  have hxn : 0 ≤ x ^ n * Real.exp (-(52 / 100 * x)) := by positivity
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * x ^ n * (Real.exp (-(52 / 100 * x)) * Real.exp (-x))
      = C * (x ^ n * Real.exp (-(52 / 100 * x))) * Real.exp (-x) := by ring
    _ ≤ (|C| + 1) * (x ^ n * Real.exp (-(52 / 100 * x))) * Real.exp (-x) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hxn) hE.le
    _ ≤ 1 * Real.exp (-x) := by
        refine mul_le_mul_of_nonneg_right ?_ hE.le
        linarith
    _ = Real.exp (-x) := one_mul _

/-- `Σ_{k<J} e^{-2^k b} ≤ 2 e^{-b}` for `b ≥ 1`. -/
theorem sum_exp_neg_two_pow_le {b : ℝ} (hb : 1 ≤ b) (J : ℕ) :
    ∑ k ∈ range J, Real.exp (-(2 ^ k * b)) ≤ 2 * Real.exp (-b) := by
  have hterm : ∀ k ∈ range J, Real.exp (-(2 ^ k * b)) ≤ Real.exp (-b) * (1 / 2) ^ k := by
    intro k _
    have hk : (k + 1 : ℝ) ≤ 2 ^ k := by
      have := Nat.lt_two_pow_self (n := k)
      exact_mod_cast this
    have h1 : Real.exp (-(2 ^ k * b)) ≤ Real.exp (-((k + 1) * b)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (-((k + 1) * b)) = Real.exp (-b) * Real.exp (-(k * b)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-(k * b)) ≤ (1 / 2) ^ k := by
      rw [show -((k : ℝ) * b) = (k : ℝ) * (-b) by ring, Real.exp_nat_mul]
      refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ k
      have : Real.exp (-b) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have he : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    rw [h2] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)
  calc ∑ k ∈ range J, Real.exp (-(2 ^ k * b)) ≤ ∑ k ∈ range J, Real.exp (-b) * (1 / 2) ^ k :=
        sum_le_sum hterm
    _ = Real.exp (-b) * ∑ k ∈ range J, (1 / 2 : ℝ) ^ k := by rw [mul_sum]
    _ ≤ Real.exp (-b) * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)
        rw [Finset.range_eq_Ico]
        calc ∑ i ∈ Ico 0 J, (1 / 2 : ℝ) ^ i ≤ (1 / 2) ^ 0 / (1 - 1 / 2) := this
          _ = 2 := by norm_num
    _ = 2 * Real.exp (-b) := by ring

/-- `log a_{j+1} ≥ 2^j log a_1`: from `a_{j+2} = 2a_{j+1}^4`. -/
theorem log_seqA_ge {L : ℝ} (hL : 2 ^ 20 ≤ L) (j : ℕ) :
    2 ^ j * Real.log (seqA L 1) ≤ Real.log (seqA L (j + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ha1 := one_le_seqA hL (j + 1)
    have h1 : seqA L (j + 1 + 1) = 2 * seqA L (j + 1) ^ 4 := by
      rw [seqA, seqB_succ_eq]; ring
    have hlog0 : 0 ≤ Real.log (seqA L (j + 1)) := Real.log_nonneg ha1
    have h2 : 2 * Real.log (seqA L (j + 1)) ≤ Real.log (seqA L (j + 1 + 1)) := by
      rw [h1, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      push_cast
      linarith
    rw [pow_succ]
    linarith

/-- **The density of the ladder scales.**  With `A_j ≥ log(b_j/a_j) − C_M` and
`log(b_0/a_0) − C_M ≥ D_0 > 0`, `log a_1 ≥ 2C_M + 2D_1`, `D_1 > 0`:
`Σ_{j<J} 1/A_j ≤ 1/D_0 + 2/D_1`. -/
theorem sum_inv_density_le {L : ℝ} (hL : 2 ^ 20 ≤ L) (J : ℕ) {A : ℕ → ℝ}
    (hA : ∀ j, Real.log (seqB L j / seqA L j) - mertensScaleConst ≤ A j)
    {D0 D1 : ℝ} (hD0 : 0 < D0) (hD1 : 0 < D1)
    (h0 : D0 ≤ Real.log (seqB L 0 / seqA L 0) - mertensScaleConst)
    (h1 : 2 * mertensScaleConst + 2 * D1 ≤ Real.log (seqA L 1)) :
    ∑ j ∈ range J, 1 / A j ≤ 1 / D0 + 2 / D1 := by
  have hMC : 0 ≤ mertensScaleConst + D1 := by
    have : 0 ≤ Real.log (seqA L 1) := Real.log_nonneg (one_le_seqA hL 1)
    by_contra h
    push Not at h
    have : Real.log (seqA L 1) < 0 := by linarith
    linarith
  -- for `j ≥ 1`: `A_j ≥ log a_j − C_M ≥ 2^{j−1} D_1`
  have hj1 : ∀ j, 2 ^ j * D1 ≤ A (j + 1) := by
    intro j
    have hb : seqB L (j + 1) / seqA L (j + 1) = seqA L (j + 1) := by
      rw [seqB_succ_eq]
      have := one_le_seqA hL (j + 1)
      field_simp
    have hAj := hA (j + 1)
    rw [hb] at hAj
    have hlog := log_seqA_ge hL j
    have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    -- `2^j log a_1 − C_M ≥ 2^j (2C_M + 2D_1) − C_M ≥ 2^j D_1`
    have h3 : 2 ^ j * (2 * mertensScaleConst + 2 * D1) ≤ 2 ^ j * Real.log (seqA L 1) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hpos : ∀ j, 0 < A j := by
    intro j
    cases j with
    | zero => linarith [hA 0]
    | succ j => have := hj1 j; have : (0 : ℝ) < 2 ^ j * D1 := by positivity
                linarith
  cases J with
  | zero => simp; positivity
  | succ J =>
    rw [sum_range_succ']
    have hfirst : 1 / A 0 ≤ 1 / D0 := one_div_le_one_div_of_le hD0 (le_trans h0 (hA 0))
    have hrest : ∑ j ∈ range J, 1 / A (j + 1) ≤ 2 / D1 := by
      have hterm : ∀ j ∈ range J, 1 / A (j + 1) ≤ 1 / D1 * (1 / 2) ^ j := by
        intro j _
        have h := hj1 j
        calc 1 / A (j + 1) ≤ 1 / (2 ^ j * D1) := one_div_le_one_div_of_le (by positivity) h
          _ = 1 / D1 * (1 / 2) ^ j := by rw [one_div_pow]; field_simp
      calc ∑ j ∈ range J, 1 / A (j + 1) ≤ ∑ j ∈ range J, 1 / D1 * (1 / 2) ^ j := sum_le_sum hterm
        _ = 1 / D1 * ∑ j ∈ range J, (1 / 2 : ℝ) ^ j := by rw [mul_sum]
        _ ≤ 1 / D1 * 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (1 / 2 : ℝ)) (by norm_num)
              (by norm_num)
            rw [Finset.range_eq_Ico]
            calc ∑ i ∈ Ico 0 J, (1 / 2 : ℝ) ^ i ≤ (1 / 2) ^ 0 / (1 - 1 / 2) := this
              _ = 2 := by norm_num
        _ = 2 / D1 := by ring
    linarith

end

end GaloisForLFunctions.MatomakiRadziwill
