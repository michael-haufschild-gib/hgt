import GaloisForLFunctions.HTGeometry.CosineLaplaceTransform
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaShiftKappa

/-!
# The Suzuki Gamma jump frequency symbol

`r(eta) = 2 ∫_0^∞ (1 − cos(eta s))/(e^s − 1) ds` is the frequency symbol of the literal Gamma jump.
It is the unshifted case of the integrand already carried by the shifted-kappa layer, so its
integrability is inherited.  Expanding `1/(e^s − 1)` as a geometric series and integrating termwise
against the cosine Laplace transform gives the closed series `r(eta) = 2 ∑_{n≥1} eta²/(n(n²+eta²))`,
from which evenness, vanishing to second order at zero, and strict monotonicity on the positive ray
all follow.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The Suzuki Gamma jump frequency symbol. -/
noncomputable def suzukiGammaSymbol (η : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), suzukiGammaShiftRealIntegrand 0 η s

theorem gammaSymbolIntegrand_apply (η s : ℝ) :
    suzukiGammaShiftRealIntegrand 0 η s = 2 * (1 - Real.cos (η * s)) / (Real.exp s - 1) := by
  rw [suzukiGammaShiftRealIntegrand]
  simp

theorem integrableOn_gammaSymbolIntegrand (η : ℝ) :
    IntegrableOn (suzukiGammaShiftRealIntegrand 0 η) (Ioi 0) :=
  integrableOn_suzukiGammaShiftRealIntegrand le_rfl (by norm_num) η

theorem gammaSymbolIntegrand_nonneg {η s : ℝ} (hs : 0 < s) :
    0 ≤ suzukiGammaShiftRealIntegrand 0 η s := by
  rw [gammaSymbolIntegrand_apply]
  have hden : 0 < Real.exp s - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)
  have hcos : Real.cos (η * s) ≤ 1 := Real.cos_le_one _
  positivity

/-- **The symbol is nonnegative.** -/
theorem suzukiGammaSymbol_nonneg (η : ℝ) : 0 ≤ suzukiGammaSymbol η :=
  setIntegral_nonneg measurableSet_Ioi fun _ hs => gammaSymbolIntegrand_nonneg hs

/-- **The symbol is even.** -/
theorem suzukiGammaSymbol_neg (η : ℝ) : suzukiGammaSymbol (-η) = suzukiGammaSymbol η := by
  unfold suzukiGammaSymbol
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [gammaSymbolIntegrand_apply, gammaSymbolIntegrand_apply, neg_mul, Real.cos_neg]

/-- **The symbol vanishes at zero.** -/
theorem suzukiGammaSymbol_zero : suzukiGammaSymbol 0 = 0 := by
  unfold suzukiGammaSymbol
  rw [show (fun s : ℝ => suzukiGammaShiftRealIntegrand 0 0 s) = fun _ : ℝ => (0 : ℝ) by
    funext s
    rw [gammaSymbolIntegrand_apply]
    simp]
  simp

/-! ## The geometric expansion of the Bose kernel -/

/-- **The Bose kernel is the geometric series of exponentials.** -/
theorem inv_exp_sub_one_eq_tsum {s : ℝ} (hs : 0 < s) :
    (Real.exp s - 1)⁻¹ = ∑' n : ℕ, Real.exp (-(((n : ℝ) + 1) * s)) := by
  have hr0 : 0 < Real.exp (-s) := Real.exp_pos _
  have hr1 : Real.exp (-s) < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hterm : ∀ n : ℕ, Real.exp (-(((n : ℝ) + 1) * s)) = Real.exp (-s) ^ (n + 1) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsum : ∑' n : ℕ, Real.exp (-s) ^ (n + 1)
      = Real.exp (-s) * (1 - Real.exp (-s))⁻¹ := by
    have hg := tsum_geometric_of_lt_one hr0.le hr1
    calc ∑' n : ℕ, Real.exp (-s) ^ (n + 1)
        = ∑' n : ℕ, Real.exp (-s) * Real.exp (-s) ^ n := by
          refine tsum_congr fun n => ?_
          rw [pow_succ]
          ring
      _ = Real.exp (-s) * ∑' n : ℕ, Real.exp (-s) ^ n := tsum_mul_left
      _ = Real.exp (-s) * (1 - Real.exp (-s))⁻¹ := by rw [hg]
  simp only [hterm]
  rw [hsum]
  have hexp : Real.exp (-s) = (Real.exp s)⁻¹ := by rw [Real.exp_neg]
  have hpos : 0 < Real.exp s := Real.exp_pos _
  have hne : Real.exp s - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)).ne'
  rw [hexp]
  field_simp

/-! ## The termwise integral -/

/-- **Each grade of the expansion integrates in closed form.** -/
theorem integral_gammaSymbolTerm (η : ℝ) (n : ℕ) :
    (∫ s in Ioi (0 : ℝ), 2 * (1 - Real.cos (η * s)) * Real.exp (-(((n : ℝ) + 1) * s)))
      = 2 * η ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ))) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h0 := integral_cosLaplace (a := (n : ℝ) + 1) (b := 0) ha
  have h1 := integral_cosLaplace (a := (n : ℝ) + 1) (b := η) ha
  simp only [zero_mul, Real.cos_zero, mul_one] at h0
  have hint0 : IntegrableOn (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s))) (Ioi 0) := by
    have := integrableOn_cosLaplace (a := (n : ℝ) + 1) (b := 0) ha
    simpa using this
  have hint1 : IntegrableOn
      (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) (Ioi 0) :=
    integrableOn_cosLaplace (a := (n : ℝ) + 1) (b := η) ha
  have hrw : (fun s : ℝ => 2 * (1 - Real.cos (η * s)) * Real.exp (-(((n : ℝ) + 1) * s)))
      = fun s : ℝ => 2 * Real.exp (-(((n : ℝ) + 1) * s))
        - 2 * (Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) := by
    funext s
    ring
  rw [hrw, integral_sub ((hint0.const_mul 2)) ((hint1.const_mul 2)),
    integral_const_mul, integral_const_mul, h0, h1]
  have hden : (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ)) ≠ 0 := by positivity
  field_simp
  ring


/-! ## The closed series -/

/-- The grade of the expansion, as a function on the ray. -/
noncomputable def gammaSymbolGrade (η : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  2 * (1 - Real.cos (η * s)) * Real.exp (-(((n : ℝ) + 1) * s))

theorem gammaSymbolGrade_nonneg (η : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ gammaSymbolGrade η n s := by
  have hcos : Real.cos (η * s) ≤ 1 := Real.cos_le_one _
  have hexp : 0 < Real.exp (-(((n : ℝ) + 1) * s)) := Real.exp_pos _
  rw [gammaSymbolGrade]
  positivity

theorem integrableOn_gammaSymbolGrade (η : ℝ) (n : ℕ) :
    IntegrableOn (gammaSymbolGrade η n) (Ioi 0) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hint0 : IntegrableOn (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s))) (Ioi 0) := by
    have := integrableOn_cosLaplace (a := (n : ℝ) + 1) (b := 0) ha
    simpa using this
  have hint1 : IntegrableOn
      (fun s : ℝ => Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) (Ioi 0) :=
    integrableOn_cosLaplace (a := (n : ℝ) + 1) (b := η) ha
  have hrw : gammaSymbolGrade η n = fun s : ℝ => 2 * Real.exp (-(((n : ℝ) + 1) * s))
      - 2 * (Real.exp (-(((n : ℝ) + 1) * s)) * Real.cos (η * s)) := by
    funext s
    rw [gammaSymbolGrade]
    ring
  rw [hrw]
  exact (hint0.const_mul 2).sub (hint1.const_mul 2)

theorem integral_gammaSymbolGrade_norm (η : ℝ) (n : ℕ) :
    (∫ s in Ioi (0 : ℝ), ‖gammaSymbolGrade η n s‖)
      = 2 * η ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ))) := by
  rw [← integral_gammaSymbolTerm η n]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (gammaSymbolGrade_nonneg η n s), gammaSymbolGrade]

theorem summable_gammaSymbolTerm (η : ℝ) :
    Summable (fun n : ℕ => 2 * η ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ)))) := by
  have hcube : Summable (fun n : ℕ => 2 * η ^ (2 : ℕ) / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
      have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 : ℕ)) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h2 := (summable_nat_add_iff 1).mpr h1
      refine h2.congr fun n => ?_
      push_cast
      ring_nf
    have := h0.mul_left (2 * η ^ (2 : ℕ))
    refine this.congr fun n => ?_
    ring
  refine hcube.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : ((n : ℝ) + 1) ^ (3 : ℕ) ≤ ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ)) := by nlinarith [sq_nonneg η]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) hd

/-- **The closed series of the Gamma symbol.** -/
theorem hasSum_suzukiGammaSymbol (η : ℝ) :
    HasSum (fun n : ℕ => 2 * η ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η ^ (2 : ℕ))))
      (suzukiGammaSymbol η) := by
  have hsum : Summable (fun n : ℕ => ∫ s in Ioi (0 : ℝ), ‖gammaSymbolGrade η n s‖) := by
    refine (summable_gammaSymbolTerm η).congr fun n => ?_
    exact (integral_gammaSymbolGrade_norm η n).symm
  have h := hasSum_integral_of_summable_integral_norm
    (μ := (volume.restrict (Ioi (0 : ℝ)))) (fun n => integrableOn_gammaSymbolGrade η n) hsum
  have hval : (∫ s in Ioi (0 : ℝ), ∑' n : ℕ, gammaSymbolGrade η n s) = suzukiGammaSymbol η := by
    unfold suzukiGammaSymbol
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    rw [gammaSymbolIntegrand_apply]
    have hexpand : ∑' n : ℕ, gammaSymbolGrade η n s
        = 2 * (1 - Real.cos (η * s)) * ∑' n : ℕ, Real.exp (-(((n : ℝ) + 1) * s)) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => rfl
    rw [hexpand, ← inv_exp_sub_one_eq_tsum hs0, div_eq_mul_inv]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  exact (integral_gammaSymbolTerm η n).symm


/-- **The symbol is strictly increasing on the positive ray.** -/
theorem suzukiGammaSymbol_lt_of_lt {η₁ η₂ : ℝ} (h0 : 0 ≤ η₁) (h : η₁ < η₂) :
    suzukiGammaSymbol η₁ < suzukiGammaSymbol η₂ := by
  have hsq : η₁ ^ (2 : ℕ) < η₂ ^ (2 : ℕ) := by nlinarith
  have hterm : ∀ n : ℕ,
      2 * η₁ ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η₁ ^ (2 : ℕ)))
        ≤ 2 * η₂ ^ (2 : ℕ) / (((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η₂ ^ (2 : ℕ))) := by
    intro n
    have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hd1 : (0 : ℝ) < ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η₁ ^ (2 : ℕ)) := by positivity
    have hd2 : (0 : ℝ) < ((n : ℝ) + 1) * (((n : ℝ) + 1) ^ (2 : ℕ) + η₂ ^ (2 : ℕ)) := by positivity
    rw [div_le_div_iff₀ hd1 hd2]
    have key : η₁ ^ (2 : ℕ) * ((n : ℝ) + 1) ^ (3 : ℕ) ≤ η₂ ^ (2 : ℕ) * ((n : ℝ) + 1) ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right hsq.le (by positivity)
    nlinarith [key, ha.le, sq_nonneg η₁, sq_nonneg η₂]
  have hstrict :
      2 * η₁ ^ (2 : ℕ) / ((((0 : ℕ) : ℝ) + 1) * ((((0 : ℕ) : ℝ) + 1) ^ (2 : ℕ) + η₁ ^ (2 : ℕ)))
        < 2 * η₂ ^ (2 : ℕ) / ((((0 : ℕ) : ℝ) + 1) * ((((0 : ℕ) : ℝ) + 1) ^ (2 : ℕ) + η₂ ^ (2 : ℕ))) := by
    have hd1 : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) * ((((0 : ℕ) : ℝ) + 1) ^ (2 : ℕ) + η₁ ^ (2 : ℕ)) := by positivity
    have hd2 : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) * ((((0 : ℕ) : ℝ) + 1) ^ (2 : ℕ) + η₂ ^ (2 : ℕ)) := by positivity
    rw [div_lt_div_iff₀ hd1 hd2]
    push_cast
    nlinarith
  have h1 := hasSum_suzukiGammaSymbol η₁
  have h2 := hasSum_suzukiGammaSymbol η₂
  rw [← h1.tsum_eq, ← h2.tsum_eq]
  exact h1.summable.tsum_lt_tsum (i := 0) hterm hstrict h2.summable


end GaloisForLFunctions.RHTower
