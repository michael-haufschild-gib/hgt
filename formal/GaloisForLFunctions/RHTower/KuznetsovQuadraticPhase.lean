import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Non-stationary phase for the quadratic phase `Ξ(s² − τs)`

For a smooth amplitude `a` whose derivatives all vanish at the ends of `[α, β]`, and `x = 2s − τ > 0` on
`[α, β]`, write `e(Ξ(s² − τs))' = 2πiΞ x e(Ξ(s² − τs))` and integrate by parts:

`∫_α^β G_k e(Ξ(s² − τs)) ds = −(2πiΞ)⁻¹ ∫_α^β G_{k+1} e(Ξ(s² − τs)) ds`,  `G_{k+1} = (G_k / x)'`,

with `G_0 = a`.  By induction `G_k = Σ_{i ≤ k} b_{k,i} a^{(i)} x^{−(2k−i)}` with coefficients independent of
`τ` (`hasDerivAt_phaseForm_div`), so on `τ ∈ [−κ, κ]`, `2α − κ > 0`, all `G_k` are bounded uniformly, and

`|∫_α^β a(s) e(Ξ(s² − τs)) ds| ≤ C_p |Ξ|^{−p}`

(`exists_quadratic_phase_bound`).
-/

open MeasureTheory Set Filter Complex intervalIntegral

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

noncomputable section

variable (a : ℝ → ℂ)

/-- The closed form `Σ_{i ≤ k} b_i a^{(i)}(s) (2s − τ)^{−(2k−i)}`. -/
def phaseForm (b : ℕ → ℝ) (k : ℕ) (τ s : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1), (b i : ℂ) * iteratedDeriv i a s *
    (((2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ)) : ℝ) : ℂ)

theorem hasDerivAt_zpow_lin (m : ℤ) {τ s : ℝ} (hx : τ < 2 * s) :
    HasDerivAt (fun s : ℝ => (((2 * s - τ) ^ m : ℝ) : ℂ))
      (((m * (2 * s - τ) ^ (m - 1) * 2 : ℝ)) : ℂ) s := by
  have hlin : HasDerivAt (fun s : ℝ => 2 * s - τ) 2 s := by
    simpa using ((hasDerivAt_id s).const_mul 2).sub_const τ
  have h := ((hasDerivAt_zpow m (2 * s - τ) (Or.inl (by linarith))).comp s hlin).ofReal_comp
  exact h

/-- The coefficients of `G_{k+1}` from those of `G_k`. -/
def shiftCoeff (b : ℕ → ℝ) (k j : ℕ) : ℝ :=
  (if j = 0 then 0 else b (j - 1)) +
    (if j ≤ k then 2 * (-((2 * k - j : ℕ) : ℝ) - 1) * b j else 0)

variable {a}

theorem exp_shift_one {i k : ℕ} (hik : i ≤ k) :
    (-((2 * (k + 1) - (i + 1) : ℕ) : ℤ)) = -((2 * k - i : ℕ) : ℤ) - 1 := by omega

theorem exp_shift_two {i k : ℕ} (hik : i ≤ k) :
    (-((2 * (k + 1) - i : ℕ) : ℤ)) = -((2 * k - i : ℕ) : ℤ) - 1 - 1 := by omega

theorem hasDerivAt_phaseForm_div (ha : ContDiff ℝ (⊤ : ℕ∞) a) (b : ℕ → ℝ) (k : ℕ) {τ s : ℝ}
    (hx : τ < 2 * s) :
    HasDerivAt (fun s => phaseForm a b k τ s / (((2 * s - τ : ℝ)) : ℂ))
      (phaseForm a (shiftCoeff b k) (k + 1) τ s) s := by
  -- rewrite the quotient as a sum with shifted exponents near `s`
  have heq : (fun s => phaseForm a b k τ s / (((2 * s - τ : ℝ)) : ℂ)) =ᶠ[nhds s]
      fun s => ∑ i ∈ Finset.range (k + 1), (b i : ℂ) * (iteratedDeriv i a s *
        (((2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1) : ℝ) : ℂ)) := by
    filter_upwards [lt_mem_nhds (show τ / 2 < s by linarith)] with y hy
    have hy0 : (2 * y - τ) ≠ 0 := by linarith
    rw [phaseForm, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_sub₀ hy0, zpow_one, Complex.ofReal_div, mul_div_assoc, mul_assoc]
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hterm : ∀ i ∈ Finset.range (k + 1), HasDerivAt (fun s => (b i : ℂ) * (iteratedDeriv i a s *
      (((2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1) : ℝ) : ℂ)))
      ((b i : ℂ) * (iteratedDeriv (i + 1) a s *
        (((2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1) : ℝ) : ℂ) +
        iteratedDeriv i a s * (((((-((2 * k - i : ℕ) : ℤ) - 1 : ℤ) : ℝ) *
          (2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1 - 1) * 2 : ℝ)) : ℂ))) s := fun i _ => by
    have hd : HasDerivAt (fun s => iteratedDeriv i a s) (iteratedDeriv (i + 1) a s) s := by
      rw [iteratedDeriv_succ]
      exact ((ha.differentiable_iteratedDeriv i (by exact_mod_cast WithTop.coe_lt_top _)) s).hasDerivAt
    exact (hd.mul (hasDerivAt_zpow_lin (-((2 * k - i : ℕ) : ℤ) - 1) hx)).const_mul (b i : ℂ)
  refine (HasDerivAt.fun_sum hterm).congr_deriv ?_
  -- regroup into the closed form for `k + 1`
  rw [phaseForm]
  have hA : ∑ j ∈ Finset.range (k + 1 + 1), (((if j = 0 then 0 else b (j - 1) : ℝ)) : ℂ) *
      iteratedDeriv j a s * (((2 * s - τ) ^ (-((2 * (k + 1) - j : ℕ) : ℤ)) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (k + 1), (b i : ℂ) * (iteratedDeriv (i + 1) a s *
        (((2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1) : ℝ) : ℂ)) := by
    rw [Finset.sum_range_succ', if_pos rfl, Complex.ofReal_zero, zero_mul, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, exp_shift_one hik]
    ring
  have hB : ∑ j ∈ Finset.range (k + 1 + 1),
      (((if j ≤ k then 2 * (-((2 * k - j : ℕ) : ℝ) - 1) * b j else 0 : ℝ)) : ℂ) *
      iteratedDeriv j a s * (((2 * s - τ) ^ (-((2 * (k + 1) - j : ℕ) : ℤ)) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (k + 1), (b i : ℂ) * (iteratedDeriv i a s *
        (((((-((2 * k - i : ℕ) : ℤ) - 1 : ℤ) : ℝ) *
          (2 * s - τ) ^ (-((2 * k - i : ℕ) : ℤ) - 1 - 1) * 2 : ℝ)) : ℂ)) := by
    rw [Finset.sum_range_succ, if_neg (by omega), Complex.ofReal_zero, zero_mul, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [if_pos hik, exp_shift_two hik]
    push_cast
    ring
  simp only [shiftCoeff, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
  rw [hA, hB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The coefficients `b_{k,i}` of `G_k`. -/
def phaseCoeff : ℕ → ℕ → ℝ
  | 0 => fun i => if i = 0 then 1 else 0
  | k + 1 => shiftCoeff (phaseCoeff k) k

theorem phaseForm_zero (τ s : ℝ) : phaseForm a (phaseCoeff 0) 0 τ s = a s := by
  simp [phaseForm, phaseCoeff]

theorem phaseForm_eq_zero_of_iteratedDeriv (b : ℕ → ℝ) (k : ℕ) {τ s : ℝ}
    (h : ∀ i, iteratedDeriv i a s = 0) : phaseForm a b k τ s = 0 := by
  simp [phaseForm, h]

theorem continuousAt_phaseForm (ha : ContDiff ℝ (⊤ : ℕ∞) a) (b : ℕ → ℝ) (k : ℕ) {τ s : ℝ}
    (hx : τ < 2 * s) : ContinuousAt (phaseForm a b k τ) s := by
  unfold phaseForm ContinuousAt
  refine tendsto_finsetSum _ fun i _ => ?_
  refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_)
    (hasDerivAt_zpow_lin _ hx).continuousAt
  exact (ha.continuous_iteratedDeriv i (by exact_mod_cast le_top)).continuousAt

/-- The quadratic phase `e(Ξ(s² − τs))`. -/
def quadPhase (Ξ τ s : ℝ) : ℂ := cexp (((2 * Real.pi * Ξ * (s ^ 2 - τ * s) : ℝ)) * I)

theorem norm_quadPhase (Ξ τ s : ℝ) : ‖quadPhase Ξ τ s‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_quadPhase (Ξ τ s : ℝ) :
    HasDerivAt (quadPhase Ξ τ) ((((2 * Real.pi * Ξ * (2 * s - τ) : ℝ)) : ℂ) * I * quadPhase Ξ τ s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Ξ * (s ^ 2 - τ * s))
      (2 * Real.pi * Ξ * (2 * s - τ)) s := by
    have := (((hasDerivAt_pow 2 s).sub ((hasDerivAt_id s).const_mul τ)).const_mul (2 * Real.pi * Ξ))
    refine this.congr_deriv ?_
    simp
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  refine h2.congr_deriv ?_
  rw [quadPhase]; ring

theorem continuous_quadPhase (Ξ τ : ℝ) : Continuous (quadPhase Ξ τ) := by
  unfold quadPhase; fun_prop

/-- **One integration by parts** against `e(Ξ(s² − τs))`. -/
theorem integral_phaseForm_mul_quadPhase (ha : ContDiff ℝ (⊤ : ℕ∞) a) (b : ℕ → ℝ) (k : ℕ)
    {α β τ Ξ : ℝ} (hαβ : α ≤ β) (hτ : τ < 2 * α) (hΞ : Ξ ≠ 0)
    (hα : phaseForm a b k τ α = 0) (hβ : phaseForm a b k τ β = 0) :
    ∫ s in α..β, phaseForm a b k τ s * quadPhase Ξ τ s =
      -((((2 * Real.pi * Ξ : ℝ)) : ℂ) * I)⁻¹ *
        ∫ s in α..β, phaseForm a (shiftCoeff b k) (k + 1) τ s * quadPhase Ξ τ s := by
  set L : ℂ := (((2 * Real.pi * Ξ : ℝ)) : ℂ) * I
  have hL : L ≠ 0 := mul_ne_zero (by exact_mod_cast mul_ne_zero (by positivity) hΞ) I_ne_zero
  have hpos : ∀ s ∈ uIcc α β, τ < 2 * s := fun s hs => by
    rw [uIcc_of_le hαβ] at hs; linarith [hs.1]
  have hu : ∀ s ∈ uIcc α β, HasDerivAt (fun s => phaseForm a b k τ s / (((2 * s - τ : ℝ)) : ℂ))
      (phaseForm a (shiftCoeff b k) (k + 1) τ s) s := fun s hs =>
    hasDerivAt_phaseForm_div ha b k (hpos s hs)
  have hv : ∀ s ∈ uIcc α β, HasDerivAt (fun s => L⁻¹ * quadPhase Ξ τ s)
      ((((2 * s - τ : ℝ)) : ℂ) * quadPhase Ξ τ s) s := fun s _ => by
    refine ((hasDerivAt_quadPhase Ξ τ s).const_mul L⁻¹).congr_deriv ?_
    rw [show (((2 * Real.pi * Ξ * (2 * s - τ) : ℝ)) : ℂ) * I * quadPhase Ξ τ s =
      L * ((((2 * s - τ : ℝ)) : ℂ) * quadPhase Ξ τ s) by simp only [L]; push_cast; ring,
      ← mul_assoc, inv_mul_cancel₀ hL, one_mul]
  have hcu : ContinuousOn (phaseForm a (shiftCoeff b k) (k + 1) τ) (uIcc α β) := fun s hs =>
    (continuousAt_phaseForm ha _ _ (hpos s hs)).continuousWithinAt
  have hcv : Continuous fun s : ℝ => (((2 * s - τ : ℝ)) : ℂ) * quadPhase Ξ τ s := by
    have := continuous_quadPhase Ξ τ; fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (hcu.intervalIntegrable) (hcv.intervalIntegrable _ _)
  have hlhs : ∫ s in α..β, phaseForm a b k τ s / (((2 * s - τ : ℝ)) : ℂ) *
      ((((2 * s - τ : ℝ)) : ℂ) * quadPhase Ξ τ s) =
      ∫ s in α..β, phaseForm a b k τ s * quadPhase Ξ τ s := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have : (((2 * s - τ : ℝ)) : ℂ) ≠ 0 := by
      have := hpos s hs; exact_mod_cast (by linarith : (2 * s - τ) ≠ 0)
    field_simp
  rw [hlhs, hα, hβ, zero_div, zero_div, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  rw [hibp, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ => ?_
  ring

/-- **Iterated integration by parts.** -/
theorem integral_mul_quadPhase_eq_iterate (ha : ContDiff ℝ (⊤ : ℕ∞) a) {α β τ Ξ : ℝ} (hαβ : α ≤ β)
    (hτ : τ < 2 * α) (hΞ : Ξ ≠ 0) (hα : ∀ i, iteratedDeriv i a α = 0)
    (hβ : ∀ i, iteratedDeriv i a β = 0) (k : ℕ) :
    ∫ s in α..β, a s * quadPhase Ξ τ s =
      (-((((2 * Real.pi * Ξ : ℝ)) : ℂ) * I)⁻¹) ^ k *
        ∫ s in α..β, phaseForm a (phaseCoeff k) k τ s * quadPhase Ξ τ s := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    exact intervalIntegral.integral_congr fun s _ => by rw [phaseForm_zero]
  | succ k ih =>
    rw [ih, integral_phaseForm_mul_quadPhase ha _ k hαβ hτ hΞ
      (phaseForm_eq_zero_of_iteratedDeriv _ _ hα) (phaseForm_eq_zero_of_iteratedDeriv _ _ hβ),
      pow_succ, mul_assoc ((-((((2 * Real.pi * Ξ : ℝ)) : ℂ) * I)⁻¹) ^ k)]
    rfl

theorem zpow_neg_natCast_le {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) (n : ℕ) :
    x ^ (-(n : ℤ)) ≤ δ ^ (-(n : ℤ)) := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos hδ n) (pow_le_pow_left₀ hδ.le hx n)

/-- **Non-stationary phase.** For a smooth amplitude all of whose derivatives vanish at `α` and `β`,
uniformly in `|τ| ≤ κ < 2α`: `|∫_α^β a(s) e(Ξ(s² − τs)) ds| ≤ C_p |Ξ|^{−p}`. -/
theorem exists_quadratic_phase_bound (ha : ContDiff ℝ (⊤ : ℕ∞) a) {α β κ : ℝ} (hαβ : α ≤ β)
    (hκ : κ < 2 * α) (hα : ∀ i, iteratedDeriv i a α = 0) (hβ : ∀ i, iteratedDeriv i a β = 0)
    (p : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ τ : ℝ, Ξ ≠ 0 → |τ| ≤ κ →
      ‖∫ s in α..β, a s * quadPhase Ξ τ s‖ ≤ C / |Ξ| ^ p := by
  have hM : ∀ i, ∃ M, 0 ≤ M ∧ ∀ s ∈ Icc α β, ‖iteratedDeriv i a s‖ ≤ M := fun i => by
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (ha.continuous_iteratedDeriv i (by exact_mod_cast le_top)).continuousOn
    exact ⟨max M 0, le_max_right _ _, fun s hs => (hM s hs).trans (le_max_left _ _)⟩
  choose M hM0 hMb using hM
  set δ := 2 * α - κ
  have hδ : 0 < δ := by simp only [δ]; linarith
  set G := ∑ i ∈ Finset.range (p + 1), |phaseCoeff p i| * M i * δ ^ (-((2 * p - i : ℕ) : ℤ))
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => by
    have := hM0 i; have := zpow_pos hδ (-((2 * p - i : ℕ) : ℤ)); positivity
  refine ⟨G * (β - α) / (2 * Real.pi) ^ p, by have := sub_nonneg.2 hαβ; positivity,
    fun Ξ τ hΞ hτ => ?_⟩
  have hτ' : τ < 2 * α := by linarith [le_abs_self τ, (abs_nonneg τ).trans hτ]
  rw [integral_mul_quadPhase_eq_iterate ha hαβ hτ' hΞ hα hβ p, norm_mul, norm_pow, norm_neg,
    norm_inv, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hbound : ∀ s ∈ uIoc α β, ‖phaseForm a (phaseCoeff p) p τ s * quadPhase Ξ τ s‖ ≤ G := by
    intro s hs
    rw [uIoc_of_le hαβ] at hs
    have hsI : s ∈ Icc α β := ⟨hs.1.le, hs.2⟩
    have hx : δ ≤ 2 * s - τ := by
      simp only [δ]; linarith [hs.1, le_abs_self τ, hτ]
    rw [norm_mul, norm_quadPhase, mul_one, phaseForm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (zpow_pos (hδ.trans_le hx) _)]
    have h1 := hMb i s hsI
    have h2 := zpow_neg_natCast_le hδ hx (2 * p - i)
    have := hM0 i
    have := (zpow_pos (hδ.trans_le hx) (-((2 * p - i : ℕ) : ℤ))).le
    gcongr
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (sub_nonneg.2 hαβ)] at hint
  have hΞp : 0 < |Ξ| ^ p := pow_pos (abs_pos.2 hΞ) p
  calc ((2 * Real.pi) * |Ξ|)⁻¹ ^ p * ‖∫ s in α..β, phaseForm a (phaseCoeff p) p τ s * quadPhase Ξ τ s‖
      ≤ ((2 * Real.pi) * |Ξ|)⁻¹ ^ p * (G * (β - α)) := by gcongr
    _ = G * (β - α) / (2 * Real.pi) ^ p / |Ξ| ^ p := by
        rw [inv_pow, mul_pow]; field_simp

end


end GaloisForLFunctions.RHTower.KuznetsovSeparation
