import GaloisForLFunctions.RHTower.ThetaTiltFluxCarrier
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The full prime action on a rapidly decaying theta source

Absolute summability, continuity, and the literal von Mangoldt Laplace multiplier.
No positivity claim is made for the prime–archimedean difference.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform
noncomputable section
namespace RHTower.ThetaSourceWard

def laplaceIntegrand (S : ThetaSource) (w : ℂ) (x : ℝ) : ℂ :=
  (S.k x : ℂ) * Complex.exp (w*x)

lemma integrable_laplaceIntegrand (S : ThetaSource) (w : ℂ) :
    Integrable (laplaceIntegrand S w) := integrable_bilateralLaplace S w

def primeCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (-(Real.log n : ℂ)/2)

def primeSourceTerm (S : ThetaSource) (n : ℕ) (x : ℝ) : ℂ :=
  primeCoefficient n * (S.k (x+Real.log n) : ℂ)

lemma primeCoefficient_laplace (w : ℂ) (n : ℕ) :
    primeCoefficient n * Complex.exp (-w*(Real.log n : ℂ)) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeCoefficient, LSeries.term]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero hnC,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log hnR.le]]
  unfold primeCoefficient
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma primeSourceTerm_laplace_point (S : ThetaSource) (w : ℂ) (n : ℕ) (x : ℝ) :
    primeSourceTerm S n x * Complex.exp (w*x) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) n *
        laplaceIntegrand S w (x+Real.log n) := by
  rw [← primeCoefficient_laplace]
  unfold primeSourceTerm laplaceIntegrand
  have he : Complex.exp (-w*(Real.log n : ℂ)) *
      Complex.exp (w*((x+Real.log n : ℝ):ℂ)) = Complex.exp (w*x) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = primeCoefficient n * (S.k (x+Real.log n) : ℂ) *
      (Complex.exp (-w*(Real.log n : ℂ)) *
        Complex.exp (w*((x+Real.log n : ℝ):ℂ))) := by rw [he]
    _ = _ := by ring

lemma integrable_primeSourceTerm_laplace (S : ThetaSource) (w : ℂ) (n : ℕ) :
    Integrable (fun x : ℝ => primeSourceTerm S n x * Complex.exp (w*x)) := by
  have h := ((integrable_bilateralLaplace S w).comp_add_right (Real.log n)).const_mul
    (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) n)
  exact h.congr (Filter.Eventually.of_forall fun x =>
    (primeSourceTerm_laplace_point S w n x).symm)

lemma integral_primeSourceTerm_laplace (S : ThetaSource) (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, primeSourceTerm S n x * Complex.exp (w*x)) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) n *
        bilateralLaplace S w := by
  simp_rw [primeSourceTerm_laplace_point]
  rw [integral_const_mul, integral_add_right_eq_self]
  rfl

lemma integral_norm_primeSourceTerm_laplace (S : ThetaSource) (w : ℂ) (n : ℕ) :
    (∫ x : ℝ, ‖primeSourceTerm S n x * Complex.exp (w*x)‖) =
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) n‖ *
        ∫ x : ℝ, ‖laplaceIntegrand S w x‖ := by
  simp_rw [primeSourceTerm_laplace_point, norm_mul]
  rw [integral_const_mul, integral_add_right_eq_self
    (fun x : ℝ => ‖laplaceIntegrand S w x‖) (Real.log n)]

lemma summable_integral_norm_primeSourceTerm_laplace
    (S : ThetaSource) {w : ℂ} (hw : 1/2 < w.re) :
    Summable (fun n : ℕ => ∫ x : ℝ, ‖primeSourceTerm S n x * Complex.exp (w*x)‖) := by
  have hs : 1 < (1/2+w).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  simpa only [integral_norm_primeSourceTerm_laplace] using
    hsum.mul_right (∫ x : ℝ, ‖laplaceIntegrand S w x‖)

lemma integral_full_prime_source_laplace
    (S : ThetaSource) {w : ℂ} (hw : 1/2 < w.re) :
    (∫ x : ℝ, (∑' n : ℕ, primeSourceTerm S n x) * Complex.exp (w*x)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+w) *
        bilateralLaplace S w := by
  have hf := integral_tsum_of_summable_integral_norm
    (integrable_primeSourceTerm_laplace S w)
    (summable_integral_norm_primeSourceTerm_laplace S hw)
  calc
    _ = ∫ x : ℝ, ∑' n : ℕ, primeSourceTerm S n x * Complex.exp (w*x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact tsum_mul_right.symm
    _ = ∑' n : ℕ, ∫ x : ℝ, primeSourceTerm S n x * Complex.exp (w*x) := hf.symm
    _ = _ := by
      simp_rw [integral_primeSourceTerm_laplace]
      rw [tsum_mul_right]
      rfl
def fullPrimeSource (S : ThetaSource) (x : ℝ) : ℂ :=
  ∑' n : ℕ, primeSourceTerm S n x

lemma exists_bound_laplaceIntegrand_one (S : ThetaSource) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖laplaceIntegrand S 1 x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := S.norm_le (M := 1)
  refine ⟨C, hC, fun x => ?_⟩
  have he : Real.exp (-|x|) * Real.exp x ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    linarith [le_abs_self x]
  calc
    _ = ‖(S.k x : ℂ)‖ * Real.exp x := by
      simp [laplaceIntegrand, Complex.norm_exp]
    _ ≤ C * Real.exp (-|x|) * Real.exp x := by
      exact mul_le_mul_of_nonneg_right (by simpa using hb x) (Real.exp_pos x).le
    _ ≤ C := by nlinarith [mul_le_mul_of_nonneg_left he hC.le]

lemma fullPrimeSource_continuous (S : ThetaSource) : Continuous (fullPrimeSource S) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_laplaceIntegrand_one S
  have hs : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+1) n‖ * C) :=
    ((ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := 1/2+1) (by norm_num)).norm).mul_right C
  have hc (n : ℕ) : Continuous (fun x : ℝ =>
      primeSourceTerm S n x * Complex.exp ((1 : ℂ)*x)) := by
    have hk := S.cont
    unfold primeSourceTerm
    fun_prop
  have hbound (n : ℕ) (x : ℝ) :
      ‖primeSourceTerm S n x * Complex.exp ((1 : ℂ)*x)‖ ≤
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1/2+1) n‖ * C := by
    rw [primeSourceTerm_laplace_point, norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have ht := continuous_tsum hc hs hbound
  have heq : fullPrimeSource S = fun x : ℝ =>
      (∑' n : ℕ, primeSourceTerm S n x * Complex.exp ((1 : ℂ)*x)) *
        Complex.exp (-(x : ℂ)) := by
    funext x
    rw [tsum_mul_right, mul_assoc, ← Complex.exp_add]
    simp [fullPrimeSource]
  rw [heq]
  exact ht.mul (by fun_prop)

lemma summable_primeSourceTerm (S : ThetaSource) (x : ℝ) :
    Summable (fun n : ℕ => primeSourceTerm S n x) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_laplaceIntegrand_one S
  have hs := ((ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := 1/2+1) (by norm_num)).norm).mul_right C
  have hs' : Summable (fun n : ℕ => primeSourceTerm S n x*Complex.exp ((1:ℂ)*x)) := by
    apply Summable.of_norm_bounded hs
    intro n
    rw [primeSourceTerm_laplace_point,norm_mul]
    exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  have h := hs'.mul_right (Complex.exp (-(x:ℂ)))
  apply h.congr
  intro n
  rw [mul_assoc,← Complex.exp_add]
  simp

lemma fullPrimeSource_laplace_integrable (S : ThetaSource) {w : ℂ} (hw : 1/2 < w.re) :
    Integrable (fun x : ℝ => fullPrimeSource S x*Complex.exp (w*x)) := by
  have hcoef : Continuous primeCoefficient := continuous_of_discreteTopology
  have hlog : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
  have hkc := S.cont
  have hc : Continuous (fun p : ℕ × ℝ => primeSourceTerm S p.1 p.2*Complex.exp (w*p.2)) := by
    unfold primeSourceTerm
    exact ((hcoef.comp continuous_fst).mul
      (Complex.continuous_ofReal.comp (hkc.comp
        (continuous_snd.add (hlog.comp continuous_fst))))).mul (by fun_prop)
  have hp : Integrable (fun p : ℕ × ℝ => primeSourceTerm S p.1 p.2*Complex.exp (w*p.2))
      (Measure.count.prod volume) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall (integrable_primeSourceTerm_laplace S w)
    · rw [integrable_count_iff]
      simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using
        summable_integral_norm_primeSourceTerm_laplace S hw
  apply hp.integral_prod_right.congr
  filter_upwards [hp.prod_left_ae] with x hx
  rw [integral_countable hx]
  simp [measureReal_def,tsum_mul_right,fullPrimeSource]

end RHTower.ThetaSourceWard
