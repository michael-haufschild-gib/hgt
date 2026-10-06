import GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
import GaloisForLFunctions.RHTower.DirichletLLogDerivativeStrip
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Bounds for the unit-class inverse `L`-series to the right of `Re w = 1`

`L_u(w) = φ(N)⁻¹ Σ_χ χ(u⁻¹) L(w, χ)⁻¹` satisfies, for `1 < Re w ≤ A`:

* `|L_u(w)| ≤ 1 + 1/(Re w − 1)` (its Dirichlet series has coefficients of modulus `≤ 1`);
* `|L_u(w)|` is bounded on every rectangle `|Im w| ≤ B`: each `L(w, χ)⁻¹` extends continuously to
  `Re w ≥ 1` — for the trivial character as `(w − 1)/((w − 1)L(w, χ₀))`, the regularized function being
  entire and nonzero at `1` — and is bounded on the compact closure;
* `|L_u(w)| ≤ C log⁹|Im w|` for `|Im w| ≥ 9`, from the character 3-4-1 floor in the logarithmic strip
  `|Re w − 1| ≤ a/log⁹|Im w|` and the first bound outside it.
-/

open Complex LSeries Filter Topology
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
open GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering GaloisForLFunctions.RHTower.TotientMulLSeries

noncomputable section

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem norm_muChiU_le (u : (ZMod N)ˣ) (n : ℕ) : ‖muChiU N u n‖ ≤ 1 := by
  unfold muChiU
  rw [norm_mul]
  split_ifs
  · rw [norm_one, mul_one]; exact norm_muChi_le N n
  · rw [norm_zero, mul_zero]; exact zero_le_one

/-- **The Dirichlet-series bound** `|L_u(w)| ≤ 1 + 1/(Re w − 1)`. -/
theorem norm_LU_le_of_one_lt (u : (ZMod N)ˣ) {w : ℂ} (hw : 1 < w.re) :
    ‖LU N u w‖ ≤ 1 + 1 / (w.re - 1) := by
  rw [← LSeries_muChiU_eq N hw]
  have hterm : ∀ n : ℕ, ‖term (muChiU N u) w n‖ ≤ (n : ℝ) ^ (-w.re) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [term_zero, norm_zero, Nat.cast_zero]
      exact Real.rpow_nonneg le_rfl _
    rw [term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    exact mul_le_of_le_one_left (by positivity) (norm_muChiU_le N u n)
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc ‖LSeries (muChiU N u) w‖ ≤ ∑' n : ℕ, ‖term (muChiU N u) w n‖ :=
        norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-w.re) :=
        (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm).tsum_le_tsum hterm hsum
    _ ≤ 1 + 1 / (w.re - 1) := RHTower.Sieve.tsum_nat_rpow_neg_le hw

/-! ## The regularized inverse on `Re w ≥ 1` -/

/-- `L(w, χ)⁻¹`, written for the trivial character as `(w − 1)/((w − 1)L(w, χ₀))`. -/
def invLreg (χ : DirichletCharacter ℂ N) (w : ℂ) : ℂ :=
  if χ = 1 then (w - 1) / DirichletCharacter.LFunctionTrivChar₁ N w
  else (DirichletCharacter.LFunction χ w)⁻¹

theorem invLreg_eq {χ : DirichletCharacter ℂ N} {w : ℂ} (hw1 : w ≠ 1) :
    invLreg N χ w = (DirichletCharacter.LFunction χ w)⁻¹ := by
  unfold invLreg
  split_ifs with hχ
  · subst hχ
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr hw1), one_div]
  · rfl

theorem continuousOn_invLreg (χ : DirichletCharacter ℂ N) :
    ContinuousOn (invLreg N χ) {w : ℂ | 1 ≤ w.re} := by
  unfold invLreg
  split_ifs with hχ
  · subst hχ
    refine ((continuous_id.sub continuous_const).continuousOn).div
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous.continuousOn
      fun w hw => ?_
    rcases eq_or_ne w 1 with rfl | hw1
    · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
    · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re 1 (Or.inr hw1) hw)
  · refine ((DirichletCharacter.differentiable_LFunction hχ).continuous.continuousOn).inv₀
      fun w hw => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hw

theorem LU_eq_sum_invLreg (u : (ZMod N)ˣ) {w : ℂ} (hw1 : w ≠ 1) :
    LU N u w = (N.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ N,
      χ ((u : ZMod N)⁻¹) * invLreg N χ w := by
  rw [LU]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [invLreg_eq N hw1]

theorem norm_LU_le_sum_invLreg (u : (ZMod N)ˣ) {w : ℂ} (hw1 : w ≠ 1) :
    ‖LU N u w‖ ≤ ∑ χ : DirichletCharacter ℂ N, ‖invLreg N χ w‖ := by
  rw [LU_eq_sum_invLreg N u hw1, norm_mul]
  have hφ : (1 : ℝ) ≤ (N.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hinv : ‖((N.totient : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ hφ
  refine (mul_le_of_le_one_left (norm_nonneg _) hinv).trans ((norm_sum_le _ _).trans
    (Finset.sum_le_sum fun χ _ => ?_))
  rw [norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact DirichletCharacter.norm_le_one χ _

/-- **`L_u` is bounded on rectangles** `1 < Re w ≤ A`, `|Im w| ≤ B`. -/
theorem exists_bound_LU_rect (A B : ℝ) :
    ∃ C, ∀ (u : (ZMod N)ˣ) (w : ℂ), 1 < w.re → w.re ≤ A → |w.im| ≤ B → ‖LU N u w‖ ≤ C := by
  set K : Set ℂ := Set.Icc 1 A ×ℂ Set.Icc (-B) B
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : K ⊆ {w : ℂ | 1 ≤ w.re} := fun w hw => hw.1.1
  have hb : ∀ χ : DirichletCharacter ℂ N, ∃ C, ∀ w ∈ K, ‖invLreg N χ w‖ ≤ C := fun χ => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((continuousOn_invLreg N χ).mono hKsub)
    exact ⟨C, hC⟩
  choose C hC using hb
  refine ⟨∑ χ : DirichletCharacter ℂ N, C χ, fun u w hw1 hwA hwB => ?_⟩
  have hw1' : w ≠ 1 := fun h => by rw [h] at hw1; simp at hw1
  have hwK : w ∈ K := ⟨⟨hw1.le, hwA⟩, abs_le.mp hwB⟩
  exact (norm_LU_le_sum_invLreg N u hw1').trans (Finset.sum_le_sum fun χ _ => hC χ w hwK)

/-- **`L_u` grows at most like `log⁹|Im w|`** to the right of `Re w = 1`. -/
theorem exists_bound_LU_high :
    ∃ C, 0 ≤ C ∧ ∀ (u : (ZMod N)ˣ) (w : ℂ), 1 < w.re → 9 ≤ |w.im| →
      ‖LU N u w‖ ≤ C * Real.log |w.im| ^ 9 := by
  set a := RHTower.characterPerronWidth N
  set K := RHTower.characterLogStripConstant N
  have ha : 0 < a := RHTower.characterPerronWidth_pos N
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (RHTower.one_le_characterLogStripConstant N)
  set c : ℝ := (Fintype.card (DirichletCharacter ℂ N) : ℝ)
  refine ⟨c / (16 * K * a) + (1 + 1 / a), by positivity, fun u w hw1 ht => ?_⟩
  set t := w.im
  set lg := Real.log |t|
  have hL2 : 2 < lg := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le RHTower.exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |t|))
    rwa [Real.log_exp] at h
  have hL1 : 1 ≤ lg ^ 9 := one_le_pow₀ (by linarith)
  have hL79 : lg ^ 7 ≤ lg ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hw1' : w ≠ 1 := fun h => by rw [h] at hw1; simp at hw1
  by_cases hstrip : w.re ≤ 1 + a / lg ^ 9
  · have hχ : ∀ χ : DirichletCharacter ℂ N, ‖invLreg N χ w‖ ≤ lg ^ 9 / (16 * K * a) := fun χ => by
      have hlow := RHTower.norm_LFunction_lower_log_strip χ (σ := w.re) (t := t) ht
        (by have : 0 ≤ a / lg ^ 9 := by positivity
            linarith) hstrip
      rw [show ((w.re : ℂ) + (t : ℂ) * Complex.I) = w from Complex.re_add_im w] at hlow
      have hpos : 0 < 16 * K * a / lg ^ 7 := by positivity
      rw [invLreg_eq N hw1', norm_inv]
      calc ‖DirichletCharacter.LFunction χ w‖⁻¹ ≤ (16 * K * a / lg ^ 7)⁻¹ :=
            inv_anti₀ hpos hlow.le
        _ = lg ^ 7 / (16 * K * a) := by rw [inv_div]
        _ ≤ lg ^ 9 / (16 * K * a) := div_le_div_of_nonneg_right hL79 (by positivity)
    calc ‖LU N u w‖ ≤ ∑ χ : DirichletCharacter ℂ N, ‖invLreg N χ w‖ :=
          norm_LU_le_sum_invLreg N u hw1'
      _ ≤ ∑ _χ : DirichletCharacter ℂ N, lg ^ 9 / (16 * K * a) := Finset.sum_le_sum fun χ _ => hχ χ
      _ = c * (lg ^ 9 / (16 * K * a)) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ (c / (16 * K * a) + (1 + 1 / a)) * lg ^ 9 := by
          rw [mul_div_assoc']
          have : 0 ≤ (1 + 1 / a) * lg ^ 9 := by positivity
          rw [add_mul]
          linarith [le_of_eq (show c * lg ^ 9 / (16 * K * a) = c / (16 * K * a) * lg ^ 9 by ring)]
  · push Not at hstrip
    have hη : 0 < a / lg ^ 9 := by positivity
    calc ‖LU N u w‖ ≤ 1 + 1 / (w.re - 1) := norm_LU_le_of_one_lt N u hw1
      _ ≤ 1 + 1 / (a / lg ^ 9) := by
          gcongr
          linarith
      _ = 1 + lg ^ 9 / a := by rw [one_div_div]
      _ ≤ (c / (16 * K * a) + (1 + 1 / a)) * lg ^ 9 := by
          have hc0 : 0 ≤ c / (16 * K * a) * lg ^ 9 := by positivity
          have : lg ^ 9 / a = 1 / a * lg ^ 9 := by ring
          nlinarith

end

end GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
