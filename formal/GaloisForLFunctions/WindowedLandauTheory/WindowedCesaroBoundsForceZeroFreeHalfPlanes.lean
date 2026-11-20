import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.LandauOnWindows
import GaloisForLFunctions.WindowedLandauTheory.LogarithmicPoleData
import GaloisForLFunctions.WindowedLandauTheory.TheCesaroRamp
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.MatomakiRadziwill.LFunctionConj
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Windowed Cesàro bounds force zero-free half-planes

Let `G_ζ(y) = Σ_{n ≤ y} Λ(n)(y/n - 1) - y log y + (1 + γ) y` and, for a nonprincipal Dirichlet
character `χ`, `G_χ(y) = Σ_{n ≤ y} χ(n)Λ(n)(y/n - 1) + y·L'/L(1, χ)`. For nonprincipal characters
`χ_i` with weights `w_i > 0` put `G = G_ζ + Σ w_i Re G_{χ_i}`.

**Theorem** (`zeroFree_of_windowed_cesaro_bound`). If `G(y) ≤ C y^θ` for all `y` in windows
`[Y, Y^{1+δ}]` with arbitrarily large `Y` (`θ ≥ 0`, `δ > 0`), then `ζ(s) ≠ 0` and `L(s, χ_i) ≠ 0`
for `Re s > θ`.

In the variable `u = log y`, the Laplace transform of `G(e^u)` is the positive combination
`Φ_{(s-1)ζ, 1} + Σ (w_i/2)(Φ_{L(χ_i), 0} + Φ_{L(χ_i⁻¹), 0})` of normalized logarithmic derivatives
(`Re G_χ = (G_χ + G_{χ⁻¹})/2`). Its poles in `Re s > θ` are the zeros, with residue
`(Σ w m)/(ρ(1 - ρ))`, positive at real zeros `β ∈ (0, 1)`, and Landau's theorem on windows
(`re_le_of_window_bound`) leaves none.
-/

open MeasureTheory Set Complex Filter Topology ArithmeticFunction

namespace WindowedLandauTheory

noncomputable section

/-! ## The Cesàro functionals -/

/-- `G_ζ(y) = Σ_{n ≤ y} Λ(n)(y/n - 1) - y log y + (1 + γ) y`. -/
def zetaCesaroFunctional (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1) - y * Real.log y +
    (1 + Real.eulerMascheroniConstant) * y

/-- The von Mangoldt coefficients twisted by `χ`. -/
def twistedVonMangoldt {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  χ n * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

/-- `G_χ(y) = Σ_{n ≤ y} χ(n)Λ(n)(y/n - 1) + y·L'/L(1, χ)`. -/
def charCesaroFunctional {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  cesaroRamp (twistedVonMangoldt χ) y + y * logDeriv (DirichletCharacter.LFunction χ) 1

/-- The functional of a family: `G_ζ + Σ w_i Re G_{χ_i}`. -/
def familyCesaroFunctional {ι : Type*} [Fintype ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ) (y : ℝ) : ℝ :=
  zetaCesaroFunctional y + ∑ i, w i * (charCesaroFunctional (χ i) y).re

theorem ofReal_vonMangoldtRamp (y : ℝ) :
    ((∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1) : ℝ) : ℂ) =
      cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) y := by
  unfold cesaroRamp
  push_cast
  rfl

theorem ofReal_zetaCesaroFunctional (y : ℝ) :
    (zetaCesaroFunctional y : ℂ) = cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) y -
      ((y * Real.log y : ℝ) : ℂ) + (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ) := by
  rw [← ofReal_vonMangoldtRamp, zetaCesaroFunctional, Complex.ofReal_add, Complex.ofReal_sub]

theorem measurable_zetaCesaroFunctional : Measurable zetaCesaroFunctional := by
  have h : Measurable fun y : ℝ => (cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) y -
      ((y * Real.log y : ℝ) : ℂ) + (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)).re :=
    Complex.measurable_re.comp (((measurable_cesaroRamp _).sub
      (Complex.measurable_ofReal.comp Real.continuous_mul_log.measurable)).add
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)))
  have e : zetaCesaroFunctional = fun y : ℝ => (cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) y -
      ((y * Real.log y : ℝ) : ℂ) + (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)).re :=
    funext fun y => by rw [← ofReal_zetaCesaroFunctional, Complex.ofReal_re]
  rw [e]
  exact h

theorem measurable_charCesaroFunctional {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Measurable (charCesaroFunctional χ) :=
  (measurable_cesaroRamp _).add (Complex.measurable_ofReal.mul measurable_const)

theorem measurable_familyCesaroFunctional {ι : Type*} [Fintype ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ) :
    Measurable (familyCesaroFunctional χ w) :=
  measurable_zetaCesaroFunctional.add (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul (Complex.measurable_re.comp (measurable_charCesaroFunctional (χ i))))

/-! ## Growth -/

theorem norm_cesaroRamp_vonMangoldt_le {y : ℝ} (hy : 0 ≤ y) :
    ‖cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) y‖ ≤ y ^ 2 := by
  have h : ∀ n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ ≤ 1 * n := fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, one_mul]
    exact vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
  simpa using norm_cesaroRamp_le h hy

theorem norm_cesaroRamp_twisted_le {N : ℕ} (χ : DirichletCharacter ℂ N) {y : ℝ} (hy : 0 ≤ y) :
    ‖cesaroRamp (twistedVonMangoldt χ) y‖ ≤ y ^ 2 := by
  have h : ∀ n : ℕ, ‖twistedVonMangoldt χ n‖ ≤ 1 * n := fun n => by
    rw [twistedVonMangoldt, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    calc ‖χ n‖ * ArithmeticFunction.vonMangoldt n ≤ 1 * ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ n) vonMangoldt_nonneg
      _ ≤ 1 * n := by
          rw [one_mul, one_mul]
          exact vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
  simpa using norm_cesaroRamp_le h hy

theorem abs_zetaCesaroFunctional_le {y : ℝ} (hy : 1 ≤ y) :
    |zetaCesaroFunctional y| ≤ (2 + |1 + Real.eulerMascheroniConstant|) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hS : |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)| ≤ y ^ 2 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_vonMangoldtRamp]
    exact norm_cesaroRamp_vonMangoldt_le hy0
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlog : Real.log y ≤ y := Real.log_le_self hy0
  have h2 : 0 ≤ y * Real.log y := mul_nonneg hy0 hlog0
  have h3 : y * Real.log y ≤ y ^ 2 := by nlinarith
  have h4 : |(1 + Real.eulerMascheroniConstant) * y| ≤
      |1 + Real.eulerMascheroniConstant| * y ^ 2 := by
    rw [abs_mul, abs_of_nonneg hy0]
    exact mul_le_mul_of_nonneg_left hyy (abs_nonneg _)
  have hS' := abs_le.mp hS
  have h4' := abs_le.mp h4
  have e : (2 + |1 + Real.eulerMascheroniConstant|) * y ^ 2 =
      2 * y ^ 2 + |1 + Real.eulerMascheroniConstant| * y ^ 2 := by ring
  unfold zetaCesaroFunctional
  rw [e, abs_le]
  constructor <;> linarith [hS'.1, hS'.2, h4'.1, h4'.2]

theorem norm_charCesaroFunctional_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {y : ℝ} (hy : 1 ≤ y) :
    ‖charCesaroFunctional χ y‖ ≤ (1 + ‖logDeriv (DirichletCharacter.LFunction χ) 1‖) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hyy : y ≤ y ^ 2 := by nlinarith
  have h1 := norm_cesaroRamp_twisted_le χ hy0
  have h2 : ‖(y : ℂ) * logDeriv (DirichletCharacter.LFunction χ) 1‖ ≤
      ‖logDeriv (DirichletCharacter.LFunction χ) 1‖ * y ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0, mul_comm]
    exact mul_le_mul_of_nonneg_left hyy (norm_nonneg _)
  calc ‖charCesaroFunctional χ y‖
      ≤ ‖cesaroRamp (twistedVonMangoldt χ) y‖ +
          ‖(y : ℂ) * logDeriv (DirichletCharacter.LFunction χ) 1‖ := norm_add_le _ _
    _ ≤ y ^ 2 + ‖logDeriv (DirichletCharacter.LFunction χ) 1‖ * y ^ 2 := add_le_add h1 h2
    _ = (1 + ‖logDeriv (DirichletCharacter.LFunction χ) 1‖) * y ^ 2 := by ring

/-- The growth constant of the family functional. -/
def familyGrowth {ι : Type*} [Fintype ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ) : ℝ :=
  2 + |1 + Real.eulerMascheroniConstant| +
    ∑ i, |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖)

theorem abs_familyCesaroFunctional_le {ι : Type*} [Fintype ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
    (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ) {y : ℝ} (hy : 1 ≤ y) :
    |familyCesaroFunctional χ w y| ≤ familyGrowth χ w * y ^ 2 := by
  have h1 := abs_zetaCesaroFunctional_le hy
  have h2 : |∑ i, w i * (charCesaroFunctional (χ i) y).re| ≤
      (∑ i, |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖)) * y ^ 2 := by
    calc |∑ i, w i * (charCesaroFunctional (χ i) y).re|
        ≤ ∑ i, |w i * (charCesaroFunctional (χ i) y).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖) * y ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [abs_mul]
            calc |w i| * |(charCesaroFunctional (χ i) y).re|
                ≤ |w i| * ‖charCesaroFunctional (χ i) y‖ :=
                  mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
              _ ≤ |w i| * ((1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖) * y ^ 2) :=
                  mul_le_mul_of_nonneg_left (norm_charCesaroFunctional_le _ hy) (abs_nonneg _)
              _ = |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖) * y ^ 2 := by
                  ring
      _ = (∑ i, |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖)) * y ^ 2 := by
          rw [Finset.sum_mul]
  calc |familyCesaroFunctional χ w y|
      ≤ |zetaCesaroFunctional y| + |∑ i, w i * (charCesaroFunctional (χ i) y).re| :=
        abs_add_le _ _
    _ ≤ (2 + |1 + Real.eulerMascheroniConstant|) * y ^ 2 +
          (∑ i, |w i| * (1 + ‖logDeriv (DirichletCharacter.LFunction (χ i)) 1‖)) * y ^ 2 :=
        add_le_add h1 h2
    _ = familyGrowth χ w * y ^ 2 := by
        unfold familyGrowth
        ring

/-! ## Laplace transforms -/

theorem exp_sq_eq (u : ℝ) : Real.exp u ^ 2 = Real.exp (2 * u) := by
  rw [sq, ← Real.exp_add, two_mul]

/-- Exponential growth of order `e^{2u}` makes `f(u) e^{-su}` integrable for `Re s > 2`. -/
theorem integrableOn_mul_cexp_of_le {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) {K : ℝ}
    (hK : ∀ u, 0 < u → ‖f u‖ ≤ K * Real.exp (2 * u)) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => f u * cexp (-s * u)) (Ioi 0) := by
  refine Integrable.mono'
    ((integrableOn_exp_mul_Ioi (a := 2 - s.re) (by linarith) 0).const_mul K)
    (hf.mul (by fun_prop : Continuous fun u : ℝ => cexp (-s * u)).aestronglyMeasurable) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [norm_mul, Complex.norm_exp, show (-s * (u : ℂ)).re = -s.re * u by simp]
  calc ‖f u‖ * Real.exp (-s.re * u) ≤ K * Real.exp (2 * u) * Real.exp (-s.re * u) :=
        mul_le_mul_of_nonneg_right (hK u hu) (Real.exp_pos _).le
    _ = K * Real.exp ((2 - s.re) * u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_exp_mul_cexp {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => cexp u * cexp (-s * u)) (Ioi 0) :=
  integrableOn_mul_cexp_of_le (K := 1)
    (by fun_prop : Continuous fun u : ℝ => cexp u).aestronglyMeasurable (fun u hu => by
      rw [Complex.norm_exp, Complex.ofReal_re, one_mul]
      exact Real.exp_le_exp.mpr (by linarith)) hs

theorem integrableOn_mul_exp_mul_cexp {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) * cexp u * cexp (-s * u)) (Ioi 0) :=
  integrableOn_mul_cexp_of_le (K := 1)
    (by fun_prop : Continuous fun u : ℝ => (u : ℂ) * cexp u).aestronglyMeasurable (fun u hu => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le, Complex.norm_exp,
        Complex.ofReal_re, one_mul, ← exp_sq_eq, sq]
      have := Real.add_one_le_exp u
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos u).le) hs

theorem integrableOn_zetaCesaroFunctional_mul {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => (zetaCesaroFunctional (Real.exp u) : ℂ) * cexp (-s * u)) (Ioi 0) :=
  integrableOn_mul_cexp_of_le (f := fun u => (zetaCesaroFunctional (Real.exp u) : ℂ))
    (K := 2 + |1 + Real.eulerMascheroniConstant|)
    ((Complex.measurable_ofReal.comp
      (measurable_zetaCesaroFunctional.comp Real.measurable_exp)).aestronglyMeasurable)
    (fun u hu => by
      rw [Complex.norm_real, Real.norm_eq_abs, ← exp_sq_eq]
      exact abs_zetaCesaroFunctional_le (Real.one_le_exp hu.le)) hs

theorem integrableOn_charCesaroFunctional_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => charCesaroFunctional χ (Real.exp u) * cexp (-s * u)) (Ioi 0) :=
  integrableOn_mul_cexp_of_le (f := fun u => charCesaroFunctional χ (Real.exp u))
    (K := 1 + ‖logDeriv (DirichletCharacter.LFunction χ) 1‖)
    (((measurable_charCesaroFunctional χ).comp Real.measurable_exp).aestronglyMeasurable)
    (fun u hu => by
      rw [← exp_sq_eq]
      exact norm_charCesaroFunctional_le χ (Real.one_le_exp hu.le)) hs

/-- The transform of `G_ζ(e^u)` is `Φ_{(s-1)ζ, 1}`. -/
theorem integral_zetaCesaroFunctional_exp_mul {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (zetaCesaroFunctional (Real.exp u) : ℂ) * cexp (-s * u) =
      logPoleFun RHTower.zetaResidueUnit 1 s := by
  have hs1 : 1 < s.re := by linarith
  have hsne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsne1
  have hpt : ∀ u : ℝ, (zetaCesaroFunctional (Real.exp u) : ℂ) * cexp (-s * u) =
      cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (Real.exp u) * cexp (-s * u) -
        (u : ℂ) * cexp u * cexp (-s * u) +
        (1 + Real.eulerMascheroniConstant) * (cexp u * cexp (-s * u)) := fun u => by
    rw [ofReal_zetaCesaroFunctional, Real.log_exp]
    push_cast
    ring
  have hA : IntegrableOn (fun u : ℝ =>
      cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (Real.exp u) * cexp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (K := 1)
      (((measurable_cesaroRamp _).comp Real.measurable_exp).aestronglyMeasurable)
      (fun u hu => by
        rw [one_mul, ← exp_sq_eq]
        exact norm_cesaroRamp_vonMangoldt_le (Real.exp_pos u).le) hs
  have hB := integrableOn_mul_exp_mul_cexp hs
  have hAB : IntegrableOn (fun u : ℝ =>
      cesaroRamp (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) (Real.exp u) * cexp (-s * u) -
        (u : ℂ) * cexp u * cexp (-s * u)) (Ioi 0) := hA.sub hB
  have hD : IntegrableOn (fun u : ℝ =>
      (1 + Real.eulerMascheroniConstant : ℂ) * (cexp u * cexp (-s * u))) (Ioi 0) :=
    (integrableOn_exp_mul_cexp hs).const_mul _
  have hGz : RHTower.zetaResidueUnit s ≠ 0 := by
    rw [RHTower.zetaResidueUnit, Function.update_of_ne hsne1]
    exact mul_ne_zero hsub (riemannZeta_ne_zero_of_one_le_re hs1.le)
  have hlog := RHTower.logDeriv_zeta_eq hsne1 hGz
  have hL : LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s = -logDeriv riemannZeta s := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1, logDeriv_apply, neg_div]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_add hAB hD,
    integral_sub hA hB, integral_const_mul,
    integral_cesaroRamp_exp_mul hs1 (LSeriesSummable_vonMangoldt hs1),
    integral_mul_exp_mul_exp hs1, integral_exp_mul_exp hs1, logPoleFun_eq _ _ hsne1, logPoleNum,
    RHTower.logDeriv_zetaResidueUnit_one, hL,
    show logDeriv RHTower.zetaResidueUnit s = logDeriv riemannZeta s + (s - 1)⁻¹ by
      rw [hlog]
      ring]
  field_simp
  ring

/-- The transform of `G_χ(e^u)` is `Φ_{L(χ), 0}`. -/
theorem integral_charCesaroFunctional_exp_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), charCesaroFunctional χ (Real.exp u) * cexp (-s * u) =
      logPoleFun (DirichletCharacter.LFunction χ) 0 s := by
  have hs1 : 1 < s.re := by linarith
  have hsne1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsne1
  have hpt : ∀ u : ℝ, charCesaroFunctional χ (Real.exp u) * cexp (-s * u) =
      cesaroRamp (twistedVonMangoldt χ) (Real.exp u) * cexp (-s * u) +
        logDeriv (DirichletCharacter.LFunction χ) 1 * (cexp u * cexp (-s * u)) := fun u => by
    rw [charCesaroFunctional, Complex.ofReal_exp]
    ring
  have hA : IntegrableOn (fun u : ℝ =>
      cesaroRamp (twistedVonMangoldt χ) (Real.exp u) * cexp (-s * u)) (Ioi 0) :=
    integrableOn_mul_cexp_of_le (K := 1)
      (((measurable_cesaroRamp _).comp Real.measurable_exp).aestronglyMeasurable)
      (fun u hu => by
        rw [one_mul, ← exp_sq_eq]
        exact norm_cesaroRamp_twisted_le χ (Real.exp_pos u).le) hs
  have hD : IntegrableOn (fun u : ℝ =>
      logDeriv (DirichletCharacter.LFunction χ) 1 * (cexp u * cexp (-s * u))) (Ioi 0) :=
    (integrableOn_exp_mul_cexp hs).const_mul _
  have hsum : LSeriesSummable (twistedVonMangoldt χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have hL : LSeries (twistedVonMangoldt χ) s = -logDeriv (DirichletCharacter.LFunction χ) s :=
    (RHTower.neg_logDeriv_LFunction_eq_LSeries χ hs1).symm
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u), integral_add hA hD,
    integral_const_mul, integral_cesaroRamp_exp_mul hs1 hsum, integral_exp_mul_exp hs1,
    logPoleFun_eq _ _ hsne1, logPoleNum, hL]
  field_simp
  ring

/-! ## Real parts through the inverse character -/

theorem conj_charCesaroFunctional {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (y : ℝ) : starRingEnd ℂ (charCesaroFunctional χ y) = charCesaroFunctional χ⁻¹ y := by
  have hc : starRingEnd ℂ (logDeriv (DirichletCharacter.LFunction χ) 1) =
      logDeriv (DirichletCharacter.LFunction χ⁻¹) 1 := by
    rw [GaloisForLFunctions.MatomakiRadziwill.logDeriv_LFunction_eq_conj_inv χ hχ 1, map_one,
      Complex.conj_conj]
  unfold charCesaroFunctional cesaroRamp twistedVonMangoldt
  rw [map_add, map_sum, map_mul, Complex.conj_ofReal, hc]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ), RHTower.conj_dirichletCharacter_apply,
    Complex.conj_ofReal, map_sub (starRingEnd ℂ), map_div₀ (starRingEnd ℂ), Complex.conj_ofReal,
    map_natCast (starRingEnd ℂ) n, map_one (starRingEnd ℂ)]

theorem re_charCesaroFunctional {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (y : ℝ) : ((charCesaroFunctional χ y).re : ℂ) =
      (charCesaroFunctional χ y + charCesaroFunctional χ⁻¹ y) / 2 := by
  rw [Complex.re_eq_add_conj, conj_charCesaroFunctional hχ]

/-! ## The family -/

section Family

variable {ι : Type*} {N : ι → ℕ}

/-- The shifts `κ`: `1` for `(s-1)ζ(s)`, `0` for the `L`-functions. -/
def familyShift : Option (ι ⊕ ι) → ℂ
  | none => 1
  | some _ => 0

/-- The weights: `1` for `ζ`, `w_i/2` for `χ_i` and for `χ_i⁻¹`. -/
def familyWeight (w : ι → ℝ) : Option (ι ⊕ ι) → ℝ
  | none => 1
  | some (Sum.inl i) => w i / 2
  | some (Sum.inr i) => w i / 2

theorem familyWeight_pos {w : ι → ℝ} (hw : ∀ i, 0 < w i) (j : Option (ι ⊕ ι)) :
    0 < familyWeight w j := by
  rcases j with _ | i | i
  · simp [familyWeight]
  · simpa [familyWeight] using hw i
  · simpa [familyWeight] using hw i

variable [∀ i, NeZero (N i)]

/-- The entire functions of the family: `(s-1)ζ(s)`, `L(s, χ_i)` and `L(s, χ_i⁻¹)`. -/
def familyFactor (χ : (i : ι) → DirichletCharacter ℂ (N i)) : Option (ι ⊕ ι) → ℂ → ℂ
  | none => RHTower.zetaResidueUnit
  | some (Sum.inl i) => DirichletCharacter.LFunction (χ i)
  | some (Sum.inr i) => DirichletCharacter.LFunction (χ i)⁻¹

variable {χ : (i : ι) → DirichletCharacter ℂ (N i)}

theorem differentiable_familyFactor (hχ : ∀ i, χ i ≠ 1) (j : Option (ι ⊕ ι)) :
    Differentiable ℂ (familyFactor χ j) := by
  rcases j with _ | i | i
  · exact fun s => (RHTower.analyticAt_zetaResidueUnit s).differentiableAt
  · exact DirichletCharacter.differentiable_LFunction (hχ i)
  · exact DirichletCharacter.differentiable_LFunction (inv_ne_one.mpr (hχ i))

theorem familyFactor_one_ne_zero (hχ : ∀ i, χ i ≠ 1) (j : Option (ι ⊕ ι)) :
    familyFactor χ j 1 ≠ 0 := by
  rcases j with _ | i | i
  · simp [familyFactor]
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ i) (Or.inl (hχ i)) (by simp)
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ i)⁻¹
      (Or.inl (inv_ne_one.mpr (hχ i))) (by simp)

/-- Zeros of the family lie left of `Re s = 1`. -/
theorem re_lt_one_of_familyFactor_eq_zero (hχ : ∀ i, χ i ≠ 1) (j : Option (ι ⊕ ι)) {s : ℂ}
    (h : familyFactor χ j s = 0) : s.re < 1 := by
  by_contra hge
  have hge' : 1 ≤ s.re := not_lt.mp hge
  rcases j with _ | i | i
  · have hs1 : s ≠ 1 := fun h1 => by
      rw [h1] at h
      exact familyFactor_one_ne_zero hχ none h
    have hz : (s - 1) * riemannZeta s = 0 := by
      have e : familyFactor χ none s = (s - 1) * riemannZeta s := by
        show RHTower.zetaResidueUnit s = _
        rw [RHTower.zetaResidueUnit, Function.update_of_ne hs1]
      rw [← e]
      exact h
    exact riemannZeta_ne_zero_of_one_le_re hge'
      ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs1))
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ i) (Or.inl (hχ i)) hge' h
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ i)⁻¹
      (Or.inl (inv_ne_one.mpr (hχ i))) hge' h

theorem not_eventually_familyFactor_eq_zero (hχ : ∀ i, χ i ≠ 1) (j : Option (ι ⊕ ι)) (z : ℂ) :
    ¬∀ᶠ w in 𝓝 z, familyFactor χ j w = 0 := by
  intro h
  have han : AnalyticOnNhd ℂ (familyFactor χ j) univ :=
    (differentiable_familyFactor hχ j).differentiableOn.analyticOnNhd isOpen_univ
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h
  exact familyFactor_one_ne_zero hχ j (h0 (mem_univ 1))

variable [Fintype ι]

theorem sum_familyWeight_mul_logPoleFun (w : ι → ℝ) (s : ℂ) :
    ∑ j, (familyWeight w j : ℂ) * logPoleFun (familyFactor χ j) (familyShift j) s =
      logPoleFun RHTower.zetaResidueUnit 1 s + ∑ i, ((w i / 2 : ℝ) : ℂ) *
        (logPoleFun (DirichletCharacter.LFunction (χ i)) 0 s +
          logPoleFun (DirichletCharacter.LFunction (χ i)⁻¹) 0 s) := by
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [familyWeight, familyFactor, familyShift, Complex.ofReal_one, one_mul, mul_add,
    Finset.sum_add_distrib]

theorem ofReal_familyCesaroFunctional (hχ : ∀ i, χ i ≠ 1) (w : ι → ℝ) (y : ℝ) :
    (familyCesaroFunctional χ w y : ℂ) = (zetaCesaroFunctional y : ℂ) +
      ∑ i, ((w i / 2 : ℝ) : ℂ) * (charCesaroFunctional (χ i) y + charCesaroFunctional (χ i)⁻¹ y) := by
  rw [familyCesaroFunctional, Complex.ofReal_add, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_mul, re_charCesaroFunctional (hχ i), Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The Laplace transform of the family functional is a positive combination of normalized
logarithmic derivatives. -/
theorem integral_familyCesaroFunctional_exp_mul (hχ : ∀ i, χ i ≠ 1) (w : ι → ℝ) {s : ℂ}
    (hs : 2 < s.re) :
    ∫ u in Ioi (0 : ℝ), (familyCesaroFunctional χ w (Real.exp u) : ℂ) * cexp (-s * u) =
      ∑ j, (familyWeight w j : ℂ) * logPoleFun (familyFactor χ j) (familyShift j) s := by
  have hpt : ∀ u : ℝ, (familyCesaroFunctional χ w (Real.exp u) : ℂ) * cexp (-s * u) =
      (zetaCesaroFunctional (Real.exp u) : ℂ) * cexp (-s * u) +
        ∑ i, ((w i / 2 : ℝ) : ℂ) * (charCesaroFunctional (χ i) (Real.exp u) * cexp (-s * u) +
          charCesaroFunctional (χ i)⁻¹ (Real.exp u) * cexp (-s * u)) := fun u => by
    rw [ofReal_familyCesaroFunctional hχ, add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hI : ∀ i, Integrable (fun u : ℝ => ((w i / 2 : ℝ) : ℂ) *
      (charCesaroFunctional (χ i) (Real.exp u) * cexp (-s * u) +
        charCesaroFunctional (χ i)⁻¹ (Real.exp u) * cexp (-s * u))) (volume.restrict (Ioi 0)) :=
    fun i => ((integrableOn_charCesaroFunctional_mul (χ i) hs).add
      (integrableOn_charCesaroFunctional_mul (χ i)⁻¹ hs)).const_mul _
  have hsumI : Integrable (fun u : ℝ => ∑ i, ((w i / 2 : ℝ) : ℂ) *
      (charCesaroFunctional (χ i) (Real.exp u) * cexp (-s * u) +
        charCesaroFunctional (χ i)⁻¹ (Real.exp u) * cexp (-s * u))) (volume.restrict (Ioi 0)) :=
    integrable_finsetSum _ fun i _ => hI i
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hpt u),
    integral_add (integrableOn_zetaCesaroFunctional_mul hs) hsumI,
    integral_finsetSum _ fun i _ => hI i, integral_zetaCesaroFunctional_exp_mul hs,
    sum_familyWeight_mul_logPoleFun]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_add (integrableOn_charCesaroFunctional_mul (χ i) hs)
      (integrableOn_charCesaroFunctional_mul (χ i)⁻¹ hs),
    integral_charCesaroFunctional_exp_mul _ hs, integral_charCesaroFunctional_exp_mul _ hs]

/-- **Windowed Cesàro bounds force zero-free half-planes.** If the family functional
`G = G_ζ + Σ w_i Re G_{χ_i}` (nonprincipal `χ_i`, `w_i > 0`) satisfies `G(y) ≤ C y^θ` on windows
`[Y, Y^{1+δ}]` for arbitrarily large `Y`, with `θ ≥ 0` and `δ > 0`, then `ζ(s) ≠ 0` and
`L(s, χ_i) ≠ 0` for `Re s > θ`. -/
theorem zeroFree_of_windowed_cesaro_bound (hχ : ∀ i, χ i ≠ 1) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {θ δ C : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ)
    (hwin : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), familyCesaroFunctional χ w y ≤ C * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧ ∀ i, DirichletCharacter.LFunction (χ i) s ≠ 0 := by
  classical
  have hP := differentiable_familyFactor hχ
  have hP1 := familyFactor_one_ne_zero hχ
  have hg : AEStronglyMeasurable (fun u => familyCesaroFunctional χ w (Real.exp u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_familyCesaroFunctional χ w).comp Real.measurable_exp).aestronglyMeasurable
  have hgC : ∀ u, 0 < u →
      |familyCesaroFunctional χ w (Real.exp u)| ≤ familyGrowth χ w * Real.exp (2 * u) :=
    fun u hu => by
      rw [← exp_sq_eq]
      exact abs_familyCesaroFunctional_le χ w (Real.one_le_exp hu.le)
  have hΦ : ∀ z : ℂ, 2 < z.re →
      ∑ j, (familyWeight w j : ℂ) * logPoleFun (familyFactor χ j) (familyShift j) z =
        ∫ u in Ioi (0 : ℝ), (familyCesaroFunctional χ w (Real.exp u) : ℂ) * cexp (-z * u) :=
    fun z hz => (integral_familyCesaroFunctional_exp_mul hχ w hz).symm
  have hwin' : ∀ U₀ : ℝ, ∃ U ≥ U₀, ∀ u ∈ Icc U ((1 + δ) * U),
      familyCesaroFunctional χ w (Real.exp u) ≤ C * Real.exp (θ * u) := by
    intro U₀
    obtain ⟨Y, hY, hYw⟩ := hwin (Real.exp U₀)
    have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos U₀) hY
    refine ⟨Real.log Y, ?_, fun u hu => ?_⟩
    · rw [ge_iff_le, Real.le_log_iff_exp_le hY0]
      exact hY
    · have h1 : Y ≤ Real.exp u := by
        rw [← Real.exp_log hY0]
        exact Real.exp_le_exp.mpr hu.1
      have h2 : Real.exp u ≤ Y ^ (1 + δ) := by
        rw [Real.rpow_def_of_pos hY0]
        exact Real.exp_le_exp.mpr (by linarith [hu.2])
      have := hYw (Real.exp u) ⟨h1, h2⟩
      rwa [← Real.exp_mul, mul_comm u θ] at this
  have hZfin : ∀ K : Set ℂ, IsCompact K → K ⊆ {s | θ < s.re} →
      ({ρ | ∃ j, familyFactor χ j ρ = 0} ∩ K).Finite := by
    intro K hK _
    refine (Set.finite_iUnion fun j =>
      GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_univ (hP j).differentiableOn
        (fun z _ => not_eventually_familyFactor_eq_zero hχ j z) hK (subset_univ K)).subset ?_
    rintro ρ ⟨⟨j, hj⟩, hρK⟩
    exact mem_iUnion.mpr ⟨j, hρK, hj⟩
  have hdiff : DifferentiableOn ℂ
      (fun s => ∑ j, (familyWeight w j : ℂ) * logPoleFun (familyFactor χ j) (familyShift j) s)
      ({s | θ < s.re} \ {ρ | ∃ j, familyFactor χ j ρ = 0}) := by
    intro s hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      have h := hs.1
      simp only [mem_setOf_eq, Complex.zero_re] at h
      linarith
    refine (DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_).differentiableWithinAt
    have hPs : familyFactor χ j s ≠ 0 := fun h => hs.2 ⟨j, h⟩
    have hopen : IsOpen ({z : ℂ | familyFactor χ j z ≠ 0} \ {0}) :=
      (isOpen_ne_fun (hP j).continuous continuous_const).sdiff isClosed_singleton
    exact (differentiableOn_logPoleFun (hP j) (hP1 j) (familyShift j)).differentiableAt
      (hopen.mem_nhds ⟨hPs, hs0⟩)
  have hpole : ∀ ρ ∈ {ρ | ∃ j, familyFactor χ j ρ = 0}, θ < ρ.re → ∃ c : ℂ, c ≠ 0 ∧
      (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, ∑ j, (familyWeight w j : ℂ) *
          logPoleFun (familyFactor χ j) (familyShift j) s = c / (s - ρ) + h s := by
    rintro ρ ⟨j₀, hj₀⟩ hρθ
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [Complex.zero_re] at hρθ
      linarith
    have hρ1 : ρ ≠ 1 := by
      rintro rfl
      exact hP1 j₀ hj₀
    have hρlt : ρ.re < 1 := re_lt_one_of_familyFactor_eq_zero hχ j₀ hj₀
    obtain ⟨m, hm, h, hh, hev⟩ := exists_sum_logPoleFun_principal Finset.univ hP hP1 familyShift
      (familyWeight w) hρ0 hρ1
    have hS : 0 < ∑ j ∈ Finset.univ, familyWeight w j * (m j : ℝ) :=
      Finset.sum_pos' (fun j _ => mul_nonneg (familyWeight_pos hw j).le (Nat.cast_nonneg _))
        ⟨j₀, Finset.mem_univ _, mul_pos (familyWeight_pos hw j₀)
          (by exact_mod_cast (hm j₀).mp hj₀)⟩
    refine ⟨((∑ j ∈ Finset.univ, familyWeight w j * (m j : ℝ) : ℝ) : ℂ) / (ρ * (1 - ρ)),
      div_ne_zero (Complex.ofReal_ne_zero.mpr hS.ne')
        (mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))), fun him => ?_, h, hh, hev⟩
    generalize (∑ j ∈ Finset.univ, familyWeight w j * (m j : ℝ)) = S at hS ⊢
    obtain ⟨x, rfl⟩ : ∃ x : ℝ, ρ = x := ⟨ρ.re, Complex.ext (by simp) (by simp [him])⟩
    rw [Complex.ofReal_re] at hρθ hρlt
    have hx0 : 0 < x := lt_of_le_of_lt hθ hρθ
    have e : (S : ℂ) / ((x : ℂ) * (1 - (x : ℂ))) = ((S / (x * (1 - x)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨div_pos hS (mul_pos hx0 (by linarith)), rfl⟩
  have hmain := re_le_of_window_bound hg hgC hΦ hδ hwin' hZfin hdiff hpole
  intro s hs
  refine ⟨fun hζ => ?_, fun i hL => absurd (hmain s ⟨some (Sum.inl i), hL⟩) (not_le.mpr hs)⟩
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero hζ
  · have h0 : familyFactor χ none s = 0 := by
      show RHTower.zetaResidueUnit s = 0
      rw [RHTower.zetaResidueUnit, Function.update_of_ne hs1, hζ, mul_zero]
    exact absurd (hmain s ⟨none, h0⟩) (not_le.mpr hs)

end Family

end

end WindowedLandauTheory
