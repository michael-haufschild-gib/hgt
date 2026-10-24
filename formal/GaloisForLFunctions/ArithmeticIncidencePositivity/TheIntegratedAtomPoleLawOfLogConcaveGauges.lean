import GaloisForLFunctions.ArithmeticCriticalityTheory.SignChangingTwoMomentAndAtomPoleIntegralLaw

/-!
# The integrated atom-against-pole law of log-concave gauges

Along the anti-diagonal of `n`, `L = log n`, the prime atom `c = Λ(n)/√n` competes with the polar
weight `P(x) = 2 sinh(x/2) sinh((L − x)/2) = cosh(L/2) − cosh(L/2 − x)`. Pointwise the atom wins
everywhere exactly for `n ∈ {2, 3, 4, 5, 7}` (`atomDominatedModuli`); for every other `n` the pole
wins at the midpoint and the atom near the two axes. Against a gauge `M` the comparison is
integrated along the collar product `M(x) M(L − x)` (`collarAtomMass`, `collarPolarMass`).

For a **log-concave** gauge the collar product is symmetric and unimodal
(`collar_le_collar_of_abs_le`), and the sign change of `P − c` is single: the integrated law is
decided by the average of the polar weight, `∫₀ᴸ P = L cosh(L/2) − 2 sinh(L/2)`
(`integral_crossingPolarWeight`). Hence (`forall_logConcave_collarAtomMass_lt_iff`)

  the pole pays the atom of every positive log-concave gauge  ⟺  `n ∉ {2, 3, 4, 5, 7, 11, 13}`.

The two moduli beyond the pointwise five are the primes at which the atom beats the average of the
polar weight but not its maximum, `log n (n + 1 − 2Λ(n)) < 2(n − 1)`
(`two_mul_sqrt_mul_polarAverage_sub`): the constant gauge leaves their atom unpaid
(`collarPolarMass_one_lt_collarAtomMass_one`), while a gauge concentrated near the midpoint pays it
(`exists_window_collarAtomMass_lt_collarPolarMass`). The arithmetic input is
`2(n − 1) < log n (n + 1 − 2Λ(n))` for every other prime power
(`two_mul_sub_one_lt_log_mul_vonMangoldt`).
-/

open RHTower Set MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The average of the polar weight -/

/-- `∫₀ᴸ P = L cosh(L/2) − 2 sinh(L/2)`, with antiderivative `x cosh(L/2) + sinh(L/2 − x)`. -/
theorem integral_crossingPolarWeight (L : ℝ) :
    ∫ x in (0 : ℝ)..L, crossingPolarWeight L x =
      L * Real.cosh (L / 2) - 2 * Real.sinh (L / 2) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) L, HasDerivAt
      (fun y => Real.cosh (L / 2) * y + Real.sinh (L / 2 - y)) (crossingPolarWeight L x) x := by
    intro x _
    rw [crossingPolarWeight_eq]
    have h1 := (hasDerivAt_id' x).const_mul (Real.cosh (L / 2))
    have h2 := ((hasDerivAt_id' x).const_sub (L / 2)).sinh
    exact (h1.add h2).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_crossingPolarWeight L).intervalIntegrable 0 L)]
  simp only [mul_zero, zero_add, sub_zero, show L / 2 - L = -(L / 2) by ring, Real.sinh_neg]
  ring

theorem setIntegral_Ioo_eq_intervalIntegral {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in Ioo (0 : ℝ) L, g x = ∫ x in (0 : ℝ)..L, g x := by
  rw [intervalIntegral.integral_of_le hL, integral_Ioc_eq_integral_Ioo]

/-- The integrated law as one integral: `polar − atom = ∫ M(x) M(L − x) (P(x) − c)`. -/
theorem collarPolarMass_sub_collarAtomMass {M : ℝ → ℝ} (hM : Continuous M) (n : ℕ) :
    collarPolarMass M n - collarAtomMass M n =
      ∫ x in Ioo (0 : ℝ) (Real.log n), M x * M (Real.log n - x) *
        (crossingPolarWeight (Real.log n) x - vonMangoldtAtom n) := by
  unfold collarPolarMass collarAtomMass
  have hMr : Continuous fun x => M (Real.log n - x) :=
    hM.comp (continuous_const.sub continuous_id)
  have h1 : IntegrableOn (fun x => M x * M (Real.log n - x) * crossingPolarWeight (Real.log n) x)
      (Ioo (0 : ℝ) (Real.log n)) :=
    ((hM.mul hMr).mul (continuous_crossingPolarWeight _)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have h2 : IntegrableOn (fun x => vonMangoldtAtom n * (M x * M (Real.log n - x)))
      (Ioo (0 : ℝ) (Real.log n)) :=
    (continuous_const.mul (hM.mul hMr)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← integral_const_mul, ← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  ring

/-! ### Log-concave gauges have unimodal collars -/

/-- For `φ` concave on `(0, L)`, the symmetric sum `φ(L/2 + s) + φ(L/2 − s)` decreases in `|s|`. -/
theorem add_le_add_of_concaveOn {φ : ℝ → ℝ} {L : ℝ} (hφ : ConcaveOn ℝ (Ioo 0 L) φ) {d s : ℝ}
    (hd : 0 < d) (hdL : d < L / 2) (hs : |s| ≤ d) :
    φ (L / 2 - d) + φ (L / 2 + d) ≤ φ (L / 2 + s) + φ (L / 2 - s) := by
  have ha : L / 2 - d ∈ Ioo 0 L := ⟨by linarith, by linarith⟩
  have hb : L / 2 + d ∈ Ioo 0 L := ⟨by linarith, by linarith⟩
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have hd2 : (0 : ℝ) < 2 * d := by linarith
  have hA : 0 ≤ (d - s) / (2 * d) := div_nonneg (by linarith) hd2.le
  have hB : 0 ≤ (d + s) / (2 * d) := div_nonneg (by linarith) hd2.le
  have hAB : (d - s) / (2 * d) + (d + s) / (2 * d) = 1 := by
    rw [← add_div, div_eq_one_iff_eq hd2.ne']; ring
  have hBA : (d + s) / (2 * d) + (d - s) / (2 * d) = 1 := by rw [add_comm]; exact hAB
  have h1 := hφ.2 ha hb hA hB hAB
  have h2 := hφ.2 ha hb hB hA hBA
  simp only [smul_eq_mul] at h1 h2
  have e1 : (d - s) / (2 * d) * (L / 2 - d) + (d + s) / (2 * d) * (L / 2 + d) = L / 2 + s := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd2.ne']; ring
  have e2 : (d + s) / (2 * d) * (L / 2 - d) + (d - s) / (2 * d) * (L / 2 + d) = L / 2 - s := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd2.ne']; ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 : (d - s) / (2 * d) * φ (L / 2 - d) + (d + s) / (2 * d) * φ (L / 2 - d) =
      φ (L / 2 - d) := by rw [← add_mul, hAB, one_mul]
  have h4 : (d - s) / (2 * d) * φ (L / 2 + d) + (d + s) / (2 * d) * φ (L / 2 + d) =
      φ (L / 2 + d) := by rw [← add_mul, hAB, one_mul]
  linarith

/-- **The collar product of a log-concave gauge is symmetric and unimodal**: closer to the
midpoint, larger. -/
theorem collar_le_collar_of_abs_le {M : ℝ → ℝ} {L : ℝ} (hpos : ∀ x ∈ Ioo 0 L, 0 < M x)
    (hcc : ConcaveOn ℝ (Ioo 0 L) fun x => Real.log (M x)) {x y : ℝ} (hx : x ∈ Ioo 0 L)
    (hxy : |y - L / 2| ≤ |x - L / 2|) : M x * M (L - x) ≤ M y * M (L - y) := by
  obtain ⟨hx0, hxL⟩ := hx
  have hxm : |x - L / 2| < L / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hy1, hy2⟩ := abs_lt.mp (lt_of_le_of_lt hxy hxm)
  have key : Real.log (M x) + Real.log (M (L - x)) ≤ Real.log (M y) + Real.log (M (L - y)) := by
    rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with hd | hd
    · have hx' : x = L / 2 := by have := abs_eq_zero.mp hd.symm; linarith
      have hy' : y = L / 2 := by
        have h0 : |y - L / 2| = 0 := le_antisymm (hd ▸ hxy) (abs_nonneg _)
        have := abs_eq_zero.mp h0; linarith
      rw [hx', hy']
    · have h := add_le_add_of_concaveOn hcc hd hxm (s := y - L / 2) hxy
      beta_reduce at h
      rw [show L / 2 + (y - L / 2) = y by ring, show L / 2 - (y - L / 2) = L - y by ring] at h
      rcases le_total x (L / 2) with hxl | hxl
      · rw [abs_of_nonpos (by linarith), show L / 2 - -(x - L / 2) = x by ring,
          show L / 2 + -(x - L / 2) = L - x by ring] at h
        exact h
      · rw [abs_of_nonneg (by linarith), show L / 2 - (x - L / 2) = L - x by ring,
          show L / 2 + (x - L / 2) = x by ring] at h
        linarith
  have hMx := hpos x ⟨hx0, hxL⟩
  have hMLx := hpos (L - x) ⟨by linarith, by linarith⟩
  have hMy := hpos y ⟨by linarith, by linarith⟩
  have hMLy := hpos (L - y) ⟨by linarith, by linarith⟩
  calc M x * M (L - x) = Real.exp (Real.log (M x) + Real.log (M (L - x))) := by
        rw [Real.exp_add, Real.exp_log hMx, Real.exp_log hMLx]
    _ ≤ Real.exp (Real.log (M y) + Real.log (M (L - y))) := Real.exp_le_exp.mpr key
    _ = M y * M (L - y) := by rw [Real.exp_add, Real.exp_log hMy, Real.exp_log hMLy]

/-! ### The arithmetic of the average -/

/-- The seven moduli whose atom is not paid by every log-concave gauge. -/
def integratedAtomDominatedModuli : Finset ℕ := {2, 3, 4, 5, 7, 11, 13}

theorem mem_integratedAtomDominatedModuli_of_mem {n : ℕ} (hn : n ∈ atomDominatedModuli) :
    n ∈ integratedAtomDominatedModuli := by
  simp only [atomDominatedModuli, integratedAtomDominatedModuli, Finset.mem_insert,
    Finset.mem_singleton] at hn ⊢
  omega

/-- `2(x − 1) < log x (x + 1 − 2 log x)` for `x ≥ 17`: with `ℓ = log x` the difference is
`(ℓ − 2)(x − 2ℓ − 3) − 4`, and `ℓ ≥ log 16`, `ℓ = 2 log √x ≤ 2√x/e`. -/
theorem two_mul_sub_one_lt_log_mul {x : ℝ} (hx : 17 ≤ x) :
    2 * (x - 1) < Real.log x * (x + 1 - 2 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨s, hs_def⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hx0
  have hs2 : s ^ 2 = x := by rw [hs_def]; exact Real.sq_sqrt hx0.le
  have hs41 : (41 / 10 : ℝ) ≤ s := by
    rw [hs_def]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hlogs : Real.log s ≤ s / Real.exp 1 := by
    have h := Real.add_one_le_exp (Real.log s - 1)
    rw [Real.exp_sub, Real.exp_log hs0] at h
    linarith
  have hlogx : Real.log x = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]; push_cast; ring
  have he : (27 / 10 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have hse : s / Real.exp 1 ≤ s / (27 / 10) :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) he.le
  have hup : Real.log x ≤ 20 / 27 * s := by
    rw [hlogx]; rw [div_div_eq_mul_div] at hse; linarith
  have hlow : 2.77 ≤ Real.log x := by
    have h16 : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    rw [log_sixteen_eq] at h16
    linarith [Real.log_two_gt_d9]
  have hX : 7.5 ≤ x - 2 * Real.log x - 3 := by
    have h1 : 2 * Real.log x ≤ 40 / 27 * s := by linarith
    have h2 : 10.66 + 1.5 * s ≤ s ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs41) (show (0 : ℝ) ≤ s + 2.6 by linarith)]
    linarith
  have hprod : 0.77 * 7.5 ≤ (Real.log x - 2) * (x - 2 * Real.log x - 3) :=
    mul_le_mul (by linarith) hX (by norm_num) (by linarith)
  nlinarith

/-- **The average condition.** For every prime power `n ∉ {2, 3, 4, 5, 7, 11, 13}`,
`2(n − 1) < log n (n + 1 − 2Λ(n))`: the atom is below the average of the polar weight. -/
theorem two_mul_sub_one_lt_log_mul_vonMangoldt {n : ℕ} (hpp : IsPrimePow n)
    (hn' : n ∉ integratedAtomDominatedModuli) :
    2 * ((n : ℝ) - 1) < Real.log n * ((n : ℝ) + 1 - 2 * ArithmeticFunction.vonMangoldt n) := by
  have hn2 : 2 ≤ n := hpp.two_le
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  rcases Nat.lt_or_ge n 17 with h17 | h17
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hp2 := hp.two_le
    have hp17 : p < 17 := lt_of_le_of_lt (Nat.le_self_pow hk.ne' p) h17
    have hk5 : k < 5 := by
      by_contra hk5
      push Not at hk5
      have : 2 ^ 5 ≤ p ^ k :=
        (Nat.pow_le_pow_left hp2 5).trans (Nat.pow_le_pow_right (by omega) hk5)
      omega
    have hcases : (p = 2 ∧ k = 3) ∨ (p = 2 ∧ k = 4) ∨ (p = 3 ∧ k = 2) := by
      interval_cases p <;> interval_cases k <;>
        first
        | (left; exact ⟨rfl, rfl⟩)
        | (right; left; exact ⟨rfl, rfl⟩)
        | (right; right; exact ⟨rfl, rfl⟩)
        | (exfalso; revert hp; decide)
        | (exfalso; revert h17; decide)
        | (exfalso; revert hn'; decide)
    have hl2 := Real.log_two_gt_d9
    have hl2' := Real.log_two_lt_d9
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · push_cast
      rw [log_eight_eq]
      nlinarith
    · push_cast
      rw [log_sixteen_eq]
      nlinarith
    · push_cast
      rw [show Real.log 9 = 2 * Real.log 3 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
      have h32 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have h3up : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have h3low : 1.0264 ≤ Real.log 3 := by norm_num at h32; linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr h3low) (sub_nonneg.mpr h3up)]
  · have hle : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log n :=
      ArithmeticFunction.vonMangoldt_le_log
    have h := two_mul_sub_one_lt_log_mul (x := (n : ℝ)) (by exact_mod_cast h17)
    nlinarith

/-- `cosh(log n / 2) = (√n + 1/√n)/2` and `sinh(log n / 2) = (√n − 1/√n)/2`. -/
theorem cosh_sinh_log_div_two {n : ℕ} (hn : 0 < n) :
    Real.cosh (Real.log n / 2) = (Real.sqrt n + (Real.sqrt n)⁻¹) / 2 ∧
      Real.sinh (Real.log n / 2) = (Real.sqrt n - (Real.sqrt n)⁻¹) / 2 := by
  have h : Real.exp (Real.log n / 2) = Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hn)]
    congr 1; ring
  exact ⟨by rw [Real.cosh_eq, Real.exp_neg, h], by rw [Real.sinh_eq, Real.exp_neg, h]⟩

/-- **The average against the atom**:
`2√n (L cosh(L/2) − 2 sinh(L/2) − L Λ(n)/√n) = L (n + 1 − 2Λ(n)) − 2(n − 1)`, `L = log n`. -/
theorem two_mul_sqrt_mul_polarAverage_sub {n : ℕ} (hn : 2 ≤ n) :
    2 * Real.sqrt n * (Real.log n * Real.cosh (Real.log n / 2) - 2 * Real.sinh (Real.log n / 2) -
      Real.log n * vonMangoldtAtom n) =
      Real.log n * ((n : ℝ) + 1 - 2 * ArithmeticFunction.vonMangoldt n) - 2 * ((n : ℝ) - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hcosh, hsinh⟩ := cosh_sinh_log_div_two (n := n) (by omega)
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  unfold vonMangoldtAtom
  rw [if_pos hn, hcosh, hsinh]
  have hss : Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  calc 2 * Real.sqrt n * (Real.log n * ((Real.sqrt n + (Real.sqrt n)⁻¹) / 2) -
        2 * ((Real.sqrt n - (Real.sqrt n)⁻¹) / 2) -
          Real.log n * (ArithmeticFunction.vonMangoldt n / Real.sqrt n))
      = Real.log n * (Real.sqrt n ^ 2 + Real.sqrt n * (Real.sqrt n)⁻¹) -
          2 * (Real.sqrt n ^ 2 - Real.sqrt n * (Real.sqrt n)⁻¹) -
            2 * Real.log n * ArithmeticFunction.vonMangoldt n *
              (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
    _ = _ := by rw [hss, hs2]; ring

/-- For the prime powers outside the seven moduli the atom is below the average polar weight. -/
theorem log_mul_vonMangoldtAtom_lt {n : ℕ} (hpp : IsPrimePow n)
    (hn' : n ∉ integratedAtomDominatedModuli) :
    Real.log n * vonMangoldtAtom n <
      Real.log n * Real.cosh (Real.log n / 2) - 2 * Real.sinh (Real.log n / 2) := by
  have hn2 := hpp.two_le
  have h := two_mul_sqrt_mul_polarAverage_sub hn2
  have hpos := two_mul_sub_one_lt_log_mul_vonMangoldt hpp hn'
  have hs0 : 0 < 2 * Real.sqrt n :=
    mul_pos two_pos (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))
  have : 0 < Real.log n * Real.cosh (Real.log n / 2) - 2 * Real.sinh (Real.log n / 2) -
      Real.log n * vonMangoldtAtom n := by
    by_contra hle
    push Not at hle
    have := mul_nonpos_of_nonneg_of_nonpos hs0.le hle
    linarith
  linarith

/-! ### The integrated law -/

theorem integral_Ioo_pos_of_pos {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hg : Continuous g)
    (hpos : ∀ x ∈ Ioo 0 L, 0 < g x) : 0 < ∫ x in Ioo (0 : ℝ) L, g x := by
  rw [setIntegral_Ioo_eq_intervalIntegral hL.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on (hg.intervalIntegrable 0 L) hpos hL

/-- **The pole pays the atom of every log-concave gauge outside seven moduli.** For a continuous
gauge, positive and log-concave on `(0, log n)`, and `n ∉ {2, 3, 4, 5, 7, 11, 13}`, the integrated
polar mass exceeds the integrated atom. With `x₀` the crossing of `P = c` on `[0, L/2]`,
`(f(x) − f(x₀))(P(x) − c) ≥ 0` pointwise, so `∫ f (P − c) ≥ f(x₀) ∫ (P − c) > 0`. -/
theorem collarAtomMass_lt_collarPolarMass_of_logConcave {M : ℝ → ℝ} (hM : Continuous M)
    {n : ℕ} (hn : 2 ≤ n) (hn' : n ∉ integratedAtomDominatedModuli)
    (hpos : ∀ x ∈ Ioo 0 (Real.log n), 0 < M x)
    (hcc : ConcaveOn ℝ (Ioo 0 (Real.log n)) fun x => Real.log (M x)) :
    collarAtomMass M n < collarPolarMass M n := by
  rw [← sub_pos, collarPolarMass_sub_collarAtomMass hM]
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hL_def] at hpos hcc ⊢
  have hL : 0 < L := by rw [hL_def]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hMr : Continuous fun x => M (L - x) := hM.comp (continuous_const.sub continuous_id)
  have hw : Continuous fun x => crossingPolarWeight L x - vonMangoldtAtom n :=
    (continuous_crossingPolarWeight L).sub continuous_const
  have hfw : Continuous fun x => M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom n) :=
    (hM.mul hMr).mul hw
  have hc0 : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    rw [if_pos hn]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hc0 with hc | hc
  · -- no atom: the polar mass is positive
    refine integral_Ioo_pos_of_pos hL hfw fun x hx => ?_
    rw [← hc, sub_zero]
    have hP : 0 < crossingPolarWeight L x :=
      mul_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr (by linarith [hx.1])))
        (Real.sinh_pos_iff.mpr (by linarith [hx.2]))
    exact mul_pos (mul_pos (hpos x hx) (hpos (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)) hP
  -- an atom: `n` is a prime power, and the crossing `x₀ ∈ (0, L/2]`
  have hpp : IsPrimePow n := by
    by_contra h
    unfold vonMangoldtAtom at hc
    rw [if_pos hn, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, zero_div] at hc
    exact lt_irrefl _ hc
  have hn5 : n ∉ atomDominatedModuli := fun h => hn' (mem_integratedAtomDominatedModuli_of_mem h)
  have hmid := vonMangoldtAtom_le_crossingPolarWeight_midpoint hn hn5
  rw [← hL_def] at hmid
  have hzero : crossingPolarWeight L 0 = 0 := by simp [crossingPolarWeight]
  obtain ⟨x₀, ⟨hx₀0, hx₀m⟩, hx₀⟩ : ∃ x₀ ∈ Icc (0 : ℝ) (L / 2),
      crossingPolarWeight L x₀ - vonMangoldtAtom n = 0 := by
    have h := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ L / 2) hw.continuousOn
    exact h ⟨show crossingPolarWeight L 0 - vonMangoldtAtom n ≤ 0 by rw [hzero]; linarith,
      show 0 ≤ crossingPolarWeight L (L / 2) - vonMangoldtAtom n by linarith⟩
  have hx₀pos : 0 < x₀ := by
    rcases eq_or_lt_of_le hx₀0 with h | h
    · rw [← h, hzero] at hx₀; linarith
    · exact h
  have hx₀I : x₀ ∈ Ioo 0 L := ⟨hx₀pos, by linarith⟩
  have hf₀ : 0 < M x₀ * M (L - x₀) :=
    mul_pos (hpos x₀ hx₀I) (hpos (L - x₀) ⟨by linarith, by linarith⟩)
  -- the polar weight decreases away from the midpoint
  have hwcmp : ∀ x, |x - L / 2| ≤ |x₀ - L / 2| →
      crossingPolarWeight L x₀ ≤ crossingPolarWeight L x := fun x h => by
    rw [crossingPolarWeight_eq, crossingPolarWeight_eq]
    have : Real.cosh (L / 2 - x) ≤ Real.cosh (L / 2 - x₀) := by
      rw [Real.cosh_le_cosh, abs_sub_comm, abs_sub_comm (L / 2)]; exact h
    linarith
  have hpt : ∀ x ∈ Ioo 0 L, M x₀ * M (L - x₀) * (crossingPolarWeight L x - vonMangoldtAtom n) ≤
      M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom n) := by
    intro x hx
    by_cases h : |x - L / 2| ≤ |x₀ - L / 2|
    · have hf := collar_le_collar_of_abs_le hpos hcc hx₀I h
      have hwx : 0 ≤ crossingPolarWeight L x - vonMangoldtAtom n := by
        have := hwcmp x h; linarith
      exact mul_le_mul_of_nonneg_right hf hwx
    · push Not at h
      have hf := collar_le_collar_of_abs_le hpos hcc hx h.le
      have hwx : crossingPolarWeight L x - vonMangoldtAtom n ≤ 0 := by
        have hc' : Real.cosh (L / 2 - x₀) ≤ Real.cosh (L / 2 - x) := by
          rw [Real.cosh_le_cosh, abs_sub_comm, abs_sub_comm (L / 2)]; exact h.le
        rw [crossingPolarWeight_eq] at hx₀ ⊢
        linarith
      exact mul_le_mul_of_nonpos_right hf hwx
  -- the average of `P − c` is positive
  have havg : 0 < ∫ x in Ioo (0 : ℝ) L, (crossingPolarWeight L x - vonMangoldtAtom n) := by
    rw [setIntegral_Ioo_eq_intervalIntegral hL.le, intervalIntegral.integral_sub
      ((continuous_crossingPolarWeight L).intervalIntegrable 0 L) intervalIntegrable_const,
      integral_crossingPolarWeight, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have h := log_mul_vonMangoldtAtom_lt hpp hn'
    rw [← hL_def] at h
    linarith
  have hint₀ : IntegrableOn (fun x => M x₀ * M (L - x₀) *
      (crossingPolarWeight L x - vonMangoldtAtom n)) (Ioo (0 : ℝ) L) :=
    (continuous_const.mul hw).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint : IntegrableOn (fun x => M x * M (L - x) *
      (crossingPolarWeight L x - vonMangoldtAtom n)) (Ioo (0 : ℝ) L) :=
    hfw.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  calc (0 : ℝ) < M x₀ * M (L - x₀) * ∫ x in Ioo (0 : ℝ) L,
        (crossingPolarWeight L x - vonMangoldtAtom n) := mul_pos hf₀ havg
    _ = ∫ x in Ioo (0 : ℝ) L, M x₀ * M (L - x₀) *
          (crossingPolarWeight L x - vonMangoldtAtom n) := (integral_const_mul _ _).symm
    _ ≤ _ := setIntegral_mono_on hint₀ hint measurableSet_Ioo hpt

/-! ### Sharpness: the constant gauge, and gauges at the midpoint -/

theorem collarAtomMass_one (n : ℕ) :
    collarAtomMass (fun _ => 1) n = Real.log n * vonMangoldtAtom n := by
  unfold collarAtomMass
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vonMangoldtAtom]
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  simp only [mul_one]
  rw [setIntegral_Ioo_eq_intervalIntegral hL, intervalIntegral.integral_const, smul_eq_mul,
    sub_zero, mul_one, mul_comm]

theorem collarPolarMass_one (n : ℕ) :
    collarPolarMass (fun _ => 1) n =
      Real.log n * Real.cosh (Real.log n / 2) - 2 * Real.sinh (Real.log n / 2) := by
  unfold collarPolarMass
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  simp only [one_mul]
  rw [setIntegral_Ioo_eq_intervalIntegral hL, integral_crossingPolarWeight]

/-- **The seven moduli leave the atom of the constant gauge unpaid.** -/
theorem collarPolarMass_one_lt_collarAtomMass_one {n : ℕ}
    (hn : n ∈ integratedAtomDominatedModuli) :
    collarPolarMass (fun _ => 1) n < collarAtomMass (fun _ => 1) n := by
  rw [collarAtomMass_one, collarPolarMass_one]
  have hn2 : 2 ≤ n := by
    simp only [integratedAtomDominatedModuli, Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  by_cases h5 : n ∈ atomDominatedModuli
  · -- pointwise: `c > cosh(L/2) − 1`, and `2 sinh(L/2) ≥ L`
    have hc := crossingPolarWeight_lt_vonMangoldtAtom h5 (Real.log n / 2)
    rw [crossingPolarWeight_midpoint, ← cosh_half_sub_one] at hc
    have hsinh : Real.log n / 2 ≤ Real.sinh (Real.log n / 2) :=
      Real.self_le_sinh_iff.mpr (by linarith)
    nlinarith
  · -- `n ∈ {11, 13}`: the atom beats the average of the polar weight
    have h1113 : n = 11 ∨ n = 13 := by
      simp only [integratedAtomDominatedModuli, atomDominatedModuli, Finset.mem_insert,
        Finset.mem_singleton] at hn h5
      omega
    have hlt : Real.log n * ((n : ℝ) + 1 - 2 * ArithmeticFunction.vonMangoldt n) <
        2 * ((n : ℝ) - 1) := by
      have hl2 := Real.log_two_lt_d9
      rcases h1113 with rfl | rfl
      · rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
        push_cast
        nlinarith [sq_nonneg (Real.log 11 - 3)]
      · rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
        push_cast
        have h16 : Real.log 13 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
        rw [log_sixteen_eq] at h16
        nlinarith [mul_nonneg (show 0 ≤ 2.78 - Real.log 13 by linarith)
          (show 0 ≤ 14 - 2 * (2.78 + Real.log 13) by linarith)]
    have h := two_mul_sqrt_mul_polarAverage_sub hn2
    have hs0 : 0 < 2 * Real.sqrt n :=
      mul_pos two_pos (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n)))
    by_contra hle
    push Not at hle
    have := mul_nonneg hs0.le (sub_nonneg.mpr hle)
    linarith

/-- **Classification of the integrated law for log-concave gauges.** For `n ≥ 2`, the pole pays
the atom of every continuous gauge that is positive and log-concave on `(0, log n)` if and only if
`n ∉ {2, 3, 4, 5, 7, 11, 13}`. -/
theorem forall_logConcave_collarAtomMass_lt_iff {n : ℕ} (hn : 2 ≤ n) :
    (∀ M : ℝ → ℝ, Continuous M → (∀ x ∈ Ioo 0 (Real.log n), 0 < M x) →
        ConcaveOn ℝ (Ioo 0 (Real.log n)) (fun x => Real.log (M x)) →
          collarAtomMass M n < collarPolarMass M n) ↔
      n ∉ integratedAtomDominatedModuli := by
  constructor
  · intro h hmem
    have h1 := h (fun _ => 1) continuous_const (fun _ _ => one_pos)
      (by simpa using concaveOn_const (𝕜 := ℝ) (0 : ℝ) (convex_Ioo (0 : ℝ) (Real.log n)))
    exact lt_asymm h1 (collarPolarMass_one_lt_collarAtomMass_one hmem)
  · intro hn' M hM hpos hcc
    exact collarAtomMass_lt_collarPolarMass_of_logConcave hM hn hn' hpos hcc

/-- **At the two new moduli the integrated law depends on the gauge.** For `n ∈ {11, 13}` there is
a window around the midpoint where the pole beats the atom pointwise; every nonnegative gauge
supported in it and positive at the midpoint has its atom paid. -/
theorem exists_window_collarAtomMass_lt_collarPolarMass {n : ℕ} (hn : 2 ≤ n)
    (hstrict : vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2)) :
    ∃ r : ℝ, 0 < r ∧ ∀ M : ℝ → ℝ, Continuous M → (∀ x, 0 ≤ M x) →
      (∀ x, r ≤ |x - Real.log n / 2| → M x = 0) → 0 < M (Real.log n / 2) →
        collarAtomMass M n < collarPolarMass M n := by
  obtain ⟨L, hL_def⟩ : ∃ L, L = Real.log n := ⟨_, rfl⟩
  rw [← hL_def] at hstrict ⊢
  have hL : 0 < L := by rw [hL_def]; exact Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hw : Continuous fun x => crossingPolarWeight L x - vonMangoldtAtom n :=
    (continuous_crossingPolarWeight L).sub continuous_const
  -- the pole wins on a window `|x − L/2| < r`, `r ≤ L/2`
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp
    (hw.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) <
      crossingPolarWeight L (L / 2) - vonMangoldtAtom n by linarith)))
  refine ⟨min r₀ (L / 2), lt_min hr₀ (by linarith), fun M hM hM0 hsupp hMm => ?_⟩
  rw [← sub_pos, collarPolarMass_sub_collarAtomMass hM, ← hL_def]
  have hMr : Continuous fun x => M (L - x) := hM.comp (continuous_const.sub continuous_id)
  have hfw : Continuous fun x => M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom n) :=
    (hM.mul hMr).mul hw
  have hnn : ∀ x, 0 ≤ M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom n) := by
    intro x
    by_cases hx : |x - L / 2| < min r₀ (L / 2)
    · have hwx := hball (show dist x (L / 2) < r₀ by
        rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_left _ _))
      exact mul_nonneg (mul_nonneg (hM0 x) (hM0 _)) hwx.le
    · push Not at hx
      rw [hsupp x hx, zero_mul, zero_mul]
  -- positive at the midpoint, hence on a neighbourhood
  have hmidpos : 0 < M (L / 2) * M (L - L / 2) *
      (crossingPolarWeight L (L / 2) - vonMangoldtAtom n) := by
    rw [show L - L / 2 = L / 2 by ring]
    exact mul_pos (mul_pos hMm hMm) (by linarith)
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp
    (hfw.continuousAt.eventually (lt_mem_nhds hmidpos))
  set δ := min ε (L / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hint : IntegrableOn (fun x => M x * M (L - x) *
      (crossingPolarWeight L x - vonMangoldtAtom n)) (Ioo (0 : ℝ) L) :=
    hfw.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hsub : Ioo (L / 2 - δ) (L / 2 + δ) ⊆ Ioo (0 : ℝ) L := fun x hx =>
    ⟨by linarith [hx.1, min_le_right ε (L / 2)], by linarith [hx.2, min_le_right ε (L / 2)]⟩
  have hsmall : 0 < ∫ x in Ioo (L / 2 - δ) (L / 2 + δ),
      M x * M (L - x) * (crossingPolarWeight L x - vonMangoldtAtom n) := by
    have h := intervalIntegral.intervalIntegral_pos_of_pos_on (hfw.intervalIntegrable
      (L / 2 - δ) (L / 2 + δ)) (fun x hx => hεball (show dist x (L / 2) < ε by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hx.1, hx.2, min_le_left ε (L / 2)])) (by linarith)
    rwa [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at h
  exact lt_of_lt_of_le hsmall (setIntegral_mono_set hint
    (Filter.Eventually.of_forall fun x => hnn x) hsub.eventuallyLE)

/-- At `11` and `13` the pole beats the atom at the midpoint strictly: `2 log n < (√n − 1)²`. -/
theorem vonMangoldtAtom_lt_crossingPolarWeight_midpoint {n : ℕ} (hn : n = 11 ∨ n = 13) :
    vonMangoldtAtom n < crossingPolarWeight (Real.log n) (Real.log n / 2) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  unfold vonMangoldtAtom
  rw [if_pos hn2, crossingPolarWeight_midpoint, sinh_log_div_four_sq (by omega),
    div_lt_iff₀ hs0]
  have e : 2 * ((Real.sqrt n - 1) ^ 2 / (4 * Real.sqrt n)) * Real.sqrt n =
      (Real.sqrt n - 1) ^ 2 / 2 := by field_simp; ring
  rw [e]
  have hl2 := Real.log_two_lt_d9
  rcases hn with rfl | rfl
  · rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    push_cast
    have hs : (3.3 : ℝ) < Real.sqrt 11 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hq := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 16 / 11 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), log_sixteen_eq] at hq
    nlinarith
  · rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    push_cast
    have hs : (3.6 : ℝ) < Real.sqrt 13 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hq := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 16 / 13 by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num), log_sixteen_eq] at hq
    nlinarith

/-- **At `11` and `13` the integrated law depends on the gauge**: the constant gauge leaves the
atom unpaid, while every nonnegative gauge supported in a window around the midpoint and positive
there has it paid. -/
theorem integratedAtomPoleLaw_eleven_thirteen {n : ℕ} (hn : n = 11 ∨ n = 13) :
    collarPolarMass (fun _ => 1) n < collarAtomMass (fun _ => 1) n ∧
      ∃ r : ℝ, 0 < r ∧ ∀ M : ℝ → ℝ, Continuous M → (∀ x, 0 ≤ M x) →
        (∀ x, r ≤ |x - Real.log n / 2| → M x = 0) → 0 < M (Real.log n / 2) →
          collarAtomMass M n < collarPolarMass M n := by
  have hmem : n ∈ integratedAtomDominatedModuli := by
    rcases hn with rfl | rfl <;> simp [integratedAtomDominatedModuli]
  exact ⟨collarPolarMass_one_lt_collarAtomMass_one hmem,
    exists_window_collarAtomMass_lt_collarPolarMass (by omega)
      (vonMangoldtAtom_lt_crossingPolarWeight_midpoint hn)⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity
