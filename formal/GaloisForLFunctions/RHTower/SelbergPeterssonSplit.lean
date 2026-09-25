import GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman
import GaloisForLFunctions.RHTower.SelbergPoincarePole
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

open Complex MeasureTheory UpperHalfPlane Set
open scoped FourierTransform

/-!
# The Petersson formula for `Γ(N)` split into diagonal and Kloosterman parts

With the `n`-uniform bound `|B_{c,k}(y)| ≤ c^{-2σ'}(y/N)^{1-σ'} C_{σ'} kmaxU` (`norm_kcoef_le'`) the Kloosterman integrands
`Fc` are dominated by `cw(c) · y^{σ-1-σ'} e^{-2πmy/N}` (`norm_Fc_le`), integrable for `Re s > Re s'`, with summable
integrals. The diagonal is a Gamma integral (`integral_F0`). Hence, for `N ≥ 3`, `m, n ≥ 1`, `2 < Re s' < Re s`,
`⟨P_m(s), P_n(s')⟩ = N (δ_{mn} (N/4πm)^{s+\bar s'-1} Γ(s+\bar s'-1) + Σ_c ∫_0^∞ Fc_c)` (`petersson_split`).
-/

namespace GaloisForLFunctions.RHTower.SelbergPeterssonSplit
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergPeterssonKloosterman
  GaloisForLFunctions.RHTower.KloostermanUniform

theorem conj_cpow_pos {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (starRingEnd ℂ) ((y : ℂ) ^ s) = (y : ℂ) ^ ((starRingEnd ℂ) s) := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [cpow_def_of_ne_zero hy0, cpow_def_of_ne_zero hy0, ← exp_conj, map_mul, ← ofReal_log hy.le,
    conj_ofReal]

variable (N : ℕ) [NeZero N]

/-- `n`-uniform bound: `|B_{c,k}(y)| ≤ c^{-2σ} (y/N)^{1-σ} C_σ kmaxU`. -/
theorem norm_kcoef_le' (n : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) (c k : ℤ) :
    ‖kcoef N n s y c k‖ ≤ ((c : ℝ) ^ 2) ^ (-s.re) *
      ((y / N) ^ (1 - s.re) * cst s.re * kmaxU (c.sign * n) (c.natAbs * N)) := by
  unfold kcoef
  by_cases hc : c = 0
  · simp only [if_pos hc, norm_zero]
    have := cst_nonneg s.re
    have := kmaxU_nonneg (c.sign * n) (c.natAbs * N)
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have : 0 < y / N := div_pos hy hN
    positivity
  rw [if_neg hc]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (0 : ℝ) < N := by linarith
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by nlinarith [Int.one_le_abs hc, sq_abs c]
    exact_mod_cast this
  have hE := norm_exp_neg_mul_log (s := s) hc2 le_rfl
  have hEN := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
  rw [neg_zero, Real.rpow_zero] at hEN
  have hF := norm_fourier_ker_le (β := n / ((c : ℝ) ^ 2 * N) / N) (by positivity) (div_pos hy hN) hs (k : ℝ)
  have hK := GaloisForLFunctions.RHTower.SelbergKloostermanCongruence.norm_ksum_le N n hc k
  rw [norm_mul, norm_mul, norm_mul]
  have h1 := cst_nonneg s.re
  calc ‖cexp (-s * (Real.log ((c : ℝ) ^ 2) : ℂ))‖ * ‖cexp (-s * (Real.log N : ℂ))‖ *
        (‖𝓕 (ker (n / ((c : ℝ) ^ 2 * N) / N) (y / N) s) k‖ * ‖ksum N n c k‖)
      ≤ ((c : ℝ) ^ 2) ^ (-s.re) * 1 * ((y / N) ^ (1 - s.re) * cst s.re * kmaxU (c.sign * n) (c.natAbs * N)) := by
        apply mul_le_mul (mul_le_mul hE hEN (norm_nonneg _) (by positivity)) (mul_le_mul hF hK (norm_nonneg _)
          (by have : 0 < y / N := div_pos hy hN; positivity)) (by positivity) (by positivity)
    _ = _ := by ring

/-- The `c`-th Kloosterman integrand of the Petersson pairing. -/
noncomputable def Fc (m n : ℕ) (s s' : ℂ) (c : ℤ) (y : ℝ) : ℂ :=
  ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) * (starRingEnd ℂ) (kcoef N n s' y c m)

omit [NeZero N] in
theorem measurable_kcoef (n : ℕ) (s : ℂ) (c k : ℤ) : Measurable (fun y : ℝ => kcoef N n s y c k) := by
  unfold kcoef
  by_cases hc : c = 0
  · simp only [if_pos hc]; exact measurable_const
  simp only [if_neg hc]
  exact measurable_const.mul
    (((GaloisForLFunctions.RHTower.SelbergPoincarePole.measurable_fourier_ker _ s k).comp
      (measurable_id.div_const _)).mul measurable_const)

theorem norm_Fc_le (m n : ℕ) {s s' : ℂ} (hs' : 1 / 2 < s'.re) (c : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖Fc N m n s s' c y‖ ≤ cw N n s'.re c * (cst s'.re * (N : ℝ) ^ (s'.re - 1)) *
      (y ^ (s.re - 1 - s'.re) * Real.exp (-(2 * Real.pi * m / N) * y)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold Fc
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hy, ← Complex.ofReal_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hk := norm_kcoef_le' N n hs' hy c (m : ℤ)
  have hcw : ((c : ℝ) ^ 2) ^ (-s'.re) * kmaxU (c.sign * n) (c.natAbs * N) ≤ cw N n s'.re c ∨ c = 0 := by
    by_cases hc : c = 0
    · right; exact hc
    · left; simp [cw, hc]
  have hsub : (s - 2).re = s.re - 2 := by simp
  rw [hsub]
  have hyN : (y / N) ^ (1 - s'.re) = y ^ (1 - s'.re) * (N : ℝ) ^ (s'.re - 1) := by
    rw [Real.div_rpow hy.le hN.le, div_eq_mul_inv, ← Real.rpow_neg hN.le]; congr 2; ring
  have hexp : Real.exp (-(2 * Real.pi * m * y / N)) = Real.exp (-(2 * Real.pi * m / N) * y) := by
    congr 1; ring
  rw [hexp]
  have hpow : y ^ (s.re - 2) * y ^ (1 - s'.re) = y ^ (s.re - 1 - s'.re) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  rcases hcw with hcw | hc0
  · rw [hyN] at hk
    have hc := cst_nonneg s'.re
    calc y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y) * ‖kcoef N n s' y c m‖
        ≤ y ^ (s.re - 2) * Real.exp (-(2 * Real.pi * m / N) * y) *
          (((c : ℝ) ^ 2) ^ (-s'.re) * (y ^ (1 - s'.re) * (N : ℝ) ^ (s'.re - 1) * cst s'.re *
            kmaxU (c.sign * n) (c.natAbs * N))) := by gcongr
      _ = (((c : ℝ) ^ 2) ^ (-s'.re) * kmaxU (c.sign * n) (c.natAbs * N)) * (cst s'.re * (N : ℝ) ^ (s'.re - 1)) *
          ((y ^ (s.re - 2) * y ^ (1 - s'.re)) * Real.exp (-(2 * Real.pi * m / N) * y)) := by ring
      _ ≤ _ := by
          rw [hpow]
          gcongr
  · subst hc0
    simp [kcoef, cw]

theorem integrableOn_Fc (m n : ℕ) (hm : 1 ≤ m) {s s' : ℂ} (hs' : 1 / 2 < s'.re) (hss : s'.re < s.re) (c : ℤ) :
    IntegrableOn (Fc N m n s s' c) (Ioi 0) := by
  have hκ : 0 < 2 * Real.pi * m / N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1 - s'.re) (by linarith) le_rfl hκ
  simp only [Real.rpow_one] at hg
  refine (hg.const_mul (cw N n s'.re c * (cst s'.re * (N : ℝ) ^ (s'.re - 1)))).mono' ?_
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => norm_Fc_le N m n hs' c hy))
  refine Measurable.aestronglyMeasurable ?_
  unfold Fc
  refine ((Measurable.pow_const Complex.measurable_ofReal _).mul (Complex.measurable_exp.comp
    (Complex.measurable_ofReal.comp (by fun_prop)))).mul (Complex.continuous_conj.measurable.comp
    (measurable_kcoef N n s' c m))

/-- The diagonal integrand `y^{s-2} e^{-2πmy/N} \overline{y^{s'} e^{-2πmy/N}}`. -/
noncomputable def F0 (m : ℕ) (s s' : ℂ) (y : ℝ) : ℂ :=
  ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
    (starRingEnd ℂ) ((y : ℂ) ^ s' * cexp (-(2 * Real.pi * m * y / N : ℝ)))

/-- **Diagonal term in closed form**: `∫_0^∞ F0 = (N/(4πm))^{s+\bar s'-1} Γ(s + \bar s' - 1)`. -/
theorem integral_F0 (m : ℕ) (hm : 1 ≤ m) {s s' : ℂ} (hre : 1 < s.re + s'.re) :
    ∫ y in Ioi (0 : ℝ), F0 N m s s' y =
      (1 / (4 * Real.pi * m / N) : ℂ) ^ (s + (starRingEnd ℂ) s' - 1) * Complex.Gamma (s + (starRingEnd ℂ) s' - 1) := by
  have hκ : 0 < 4 * Real.pi * m / N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have ha : 0 < (s + (starRingEnd ℂ) s' - 1).re := by simp; linarith
  have h := integral_cpow_mul_exp_neg_mul_Ioi ha hκ
  push_cast at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := hy
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  unfold F0
  rw [map_mul, conj_cpow_pos hy0, ← Complex.exp_conj, map_neg, Complex.conj_ofReal]
  simp only
  rw [show s + (starRingEnd ℂ) s' - 1 - 1 = (s - 2) + (starRingEnd ℂ) s' by ring, cpow_add _ _ hyc,
    mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

theorem integrableOn_F0 (m : ℕ) (hm : 1 ≤ m) {s s' : ℂ} (hre : 1 < s.re + s'.re) :
    IntegrableOn (F0 N m s s') (Ioi 0) := by
  have hκ : 0 < 4 * Real.pi * m / N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re + s'.re - 2) (by linarith) le_rfl hκ
  simp only [Real.rpow_one] at hg
  refine hg.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => le_of_eq ?_))
  · refine Measurable.aestronglyMeasurable ?_
    unfold F0
    have h1 : Measurable (fun y : ℝ => Complex.exp (-(2 * Real.pi * m * y / N) : ℝ)) :=
      Complex.measurable_exp.comp (Complex.measurable_ofReal.comp (by fun_prop))
    have h3 : Measurable (fun y : ℝ => cexp (-(((2 * Real.pi * m * y / N : ℝ)) : ℂ))) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (by fun_prop)).neg)
    exact ((Measurable.pow_const Complex.measurable_ofReal _).mul h1).mul (Complex.continuous_conj.measurable.comp
      ((Measurable.pow_const Complex.measurable_ofReal _).mul h3))
  · have hy0 : 0 < y := hy
    unfold F0
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, ← Complex.ofReal_exp, Complex.norm_real, Complex.norm_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Complex.sub_re, Complex.re_ofNat, Complex.neg_re, Complex.ofReal_re]
    rw [show s.re + s'.re - 2 = (s.re - 2) + s'.re by ring, Real.rpow_add hy0]
    have : Real.exp (-(2 * Real.pi * m * y / N)) * Real.exp (-(2 * Real.pi * m * y / N)) =
        Real.exp (-(4 * Real.pi * m / N) * y) := by rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring

open GaloisForLFunctions.RHTower.SarnakXuePretrace GaloisForLFunctions.RHTower.SelbergPoincare in
/-- **Petersson formula, split**: for `N ≥ 3`, `m, n ≥ 1`, `2 < Re s' < Re s`,
`⟨P_m(s), P_n(s')⟩ = N δ_{mn} (N/4πm)^{s+\bar s'-1} Γ(s+\bar s'-1) + N Σ_{c≠0} ∫_0^∞ Fc_c(y) dy`. -/
theorem petersson_split (hN : 3 ≤ N) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {s s' : ℂ}
    (hs' : 2 < s'.re) (hss : s'.re < s.re) :
    ∫ z in cellP N, poincare N m s z * (starRingEnd ℂ) (poincare N n s' z) =
      N * ((if (m : ℤ) = n then (1 / (4 * Real.pi * m / N) : ℂ) ^ (s + (starRingEnd ℂ) s' - 1) *
          Complex.Gamma (s + (starRingEnd ℂ) s' - 1) else 0) +
        ∑' c, ∫ y in Ioi (0 : ℝ), Fc N m n s s' c y) := by
  have hs : 1 < s.re := by linarith
  rw [petersson_kloosterman N hN hm hn hs hs']
  congr 1
  have hsum_int : Summable (fun c => ∫ y in Ioi (0 : ℝ), ‖Fc N m n s s' c y‖) := by
    have hκ : 0 < 2 * Real.pi * m / N := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      positivity
    set g : ℝ → ℝ := fun y => y ^ (s.re - 1 - s'.re) * Real.exp (-(2 * Real.pi * m / N) * y)
    have hg : IntegrableOn g (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1 - s'.re) (by linarith) le_rfl hκ
      refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
      simp only [g, Real.rpow_one]
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) (fun c => ?_)
      ((summable_cw N n (Nat.pos_of_ne_zero (NeZero.ne N)) (by omega) (σ := s'.re) (by linarith)).mul_right
        ((cst s'.re * (N : ℝ) ^ (s'.re - 1)) * ∫ y in Ioi (0 : ℝ), g y))
    rw [← mul_assoc, ← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_Fc N m n hm (by linarith) hss c).norm
      (hg.const_mul _) measurableSet_Ioi (fun y hy =>
        (norm_Fc_le N m n (s := s) (by linarith) c hy).trans (le_of_eq (by simp only [g])))
  have hpt : ∀ y ∈ Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * Complex.exp (-(2 * Real.pi * m * y / N) : ℝ) *
      (starRingEnd ℂ) ((if (m : ℤ) = n then (y : ℂ) ^ s' * cexp (-(2 * Real.pi * n * y / N : ℝ)) else 0) +
        ∑' c, kcoef N n s' y c m) =
      (if (m : ℤ) = n then F0 N m s s' y else 0) + ∑' c, Fc N m n s s' c y := by
    intro y _
    rw [map_add, mul_add, Complex.conj_tsum, ← tsum_mul_left]
    congr 1
    · split_ifs with h
      · have hmn : m = n := by exact_mod_cast h
        subst hmn; rfl
      · simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hT : IntegrableOn (fun y => ∑' c, Fc N m n s s' c y) (Ioi 0) := by
    exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm (fun c => integrableOn_Fc N m n hm (by linarith) hss c) hsum_int
  rw [integral_add (by split_ifs; exacts [integrableOn_F0 N m hm (by linarith), integrableOn_zero]) hT,
    ← integral_tsum_of_summable_integral_norm (fun c => integrableOn_Fc N m n hm (by linarith) hss c) hsum_int]
  congr 1
  split_ifs
  · exact integral_F0 N m hm (by linarith)
  · simp

end GaloisForLFunctions.RHTower.SelbergPeterssonSplit
