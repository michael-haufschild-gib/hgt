import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite
import GaloisForLFunctions.HTGeometry.ConvolutionAtomBounds
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic functions are positive definite

This module supplies the measure-theoretic Bochner direction for the finite-matrix
`PositiveDefiniteOnReal` interface.  Every probability characteristic function has a nonnegative
Gram form: the form is the integral of the squared norm of its finite Fourier packet.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ComplexConjugate
open MeasureTheory

noncomputable section

/-- **Universal Bochner Gram law.**  The characteristic function of every probability measure on
the real line is positive definite in the corpus's finite-matrix sense. -/
theorem positiveDefiniteOnReal_charFun
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    PositiveDefiniteOnReal (charFun μ) := by
  intro N t c
  let V : ℝ → ℂ := fun x =>
    ∑ i, c i * realFourierCharacter x (t i)
  have hCharCont (a : ℝ) :
      Continuous (fun x : ℝ => realFourierCharacter x a) := by
    rw [show (fun x : ℝ => realFourierCharacter x a) =
      fun x : ℝ => Complex.exp (Complex.I * (((x * a : ℝ) : ℝ) : ℂ)) by rfl]
    fun_prop
  have hcharInt (i j : Fin N) :
      Integrable (fun x : ℝ =>
        star (c i) * realFourierCharacter x (t j - t i) * c j) μ := by
    have hexp : Integrable (fun x : ℝ =>
        realFourierCharacter x (t j - t i)) μ := by
      refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
      · exact (hCharCont _).aestronglyMeasurable
      · filter_upwards with x
        rw [norm_realFourierCharacter]
    exact (hexp.const_mul (star (c i))).mul_const (c j)
  have hVInt : Integrable (fun x : ℝ => Complex.normSq (V x)) μ := by
    have hVcont : Continuous V := by
      dsimp only [V]
      exact continuous_finsetSum _ fun i _ =>
        continuous_const.mul (hCharCont (t i))
    have hbound : ∀ x, Complex.normSq (V x) ≤ (∑ i, ‖c i‖) ^ 2 := by
      intro x
      rw [← Complex.sq_norm]
      gcongr
      calc
        ‖V x‖ ≤ ∑ i, ‖c i * realFourierCharacter x (t i)‖ :=
          norm_sum_le _ _
        _ = ∑ i, ‖c i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_realFourierCharacter, mul_one]
    exact (integrable_const (μ := μ) ((∑ i, ‖c i‖) ^ 2)).mono'
      (Complex.continuous_normSq.comp hVcont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]
        exact hbound x)
  refine ⟨∫ x, Complex.normSq (V x) ∂μ,
    integral_nonneg fun x => Complex.normSq_nonneg (V x), ?_⟩
  calc
    ∑ i, ∑ j, star (c i) * charFun μ (t j - t i) * c j =
        ∑ i, ∑ j, ∫ x : ℝ,
          star (c i) * realFourierCharacter x (t j - t i) * c j ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [charFun_apply_real, ← integral_const_mul, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      rw [realFourierCharacter]
      congr 1
      push_cast
      ring_nf
    _ = ∫ x : ℝ, ∑ i, ∑ j,
          star (c i) * realFourierCharacter x (t j - t i) * c j ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        intro j _
        exact hcharInt i j
      · intro i _
        exact integrable_finsetSum _ fun j _ => hcharInt i j
    _ = ∫ x : ℝ, (Complex.normSq (V x) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.normSq_eq_conj_mul_self]
      dsimp only [V]
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, realFourierCharacter_sub]
      ac_rfl
    _ = ((∫ x : ℝ, Complex.normSq (V x) ∂μ : ℝ) : ℂ) := by
      exact Complex.ofRealCLM.integral_comp_comm hVInt

/-- Characteristic function of a convolution power of a probability measure. -/
theorem charFun_convPow_probability
    (Q : Measure ℝ) [IsProbabilityMeasure Q] (n : ℕ) (t : ℝ) :
    charFun (convPow Q n) t = charFun Q t ^ n := by
  induction n with
  | zero =>
      rw [convPow, charFun_dirac]
      simp
  | succ n ih =>
      haveI : IsProbabilityMeasure (convPow Q n) :=
        isProbabilityMeasure_convPow Q n
      rw [convPow, charFun_conv, ih, pow_succ']

/-- **Compound-Poisson characteristic law.**  A jump law with characteristic function `φ`
produces the characteristic function `exp (λ (φ - 1))` at intensity `λ`. -/
theorem charFun_compoundPoisson
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    [IsProbabilityMeasure Q] (t : ℝ) :
    charFun (compoundPoisson lam Q) t =
      Complex.exp ((lam : ℂ) * (charFun Q t - 1)) := by
  let μ := compoundPoisson lam Q
  let f : ℝ → ℂ := fun x => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  haveI hμprob : IsProbabilityMeasure μ :=
    isProbabilityMeasure_compoundPoisson lam hlam Q
  have hf : Integrable f μ := by
    refine (integrable_const (μ := μ) (1 : ℝ)).mono' ?_ ?_
    · dsimp only [f]
      fun_prop
    · filter_upwards with x
      dsimp only [f]
      rw [Complex.norm_exp_ofReal_mul_I]
  have hcoeff (n : ℕ) :
      (ENNReal.ofReal (Real.exp (-lam) * lam ^ n / n.factorial)).toReal =
        Real.exp (-lam) * lam ^ n / n.factorial := by
    rw [ENNReal.toReal_ofReal]
    positivity
  have hterm (n : ℕ) :
      ∫ x, f x ∂(ENNReal.ofReal (Real.exp (-lam) * lam ^ n / n.factorial) •
          convPow Q n) =
        ((Real.exp (-lam) * lam ^ n / n.factorial : ℝ) : ℂ) *
          charFun Q t ^ n := by
    rw [integral_smul_measure, hcoeff]
    · have hfchar :
          (∫ x, f x ∂convPow Q n) = charFun (convPow Q n) t := by
          rw [charFun_apply_real]
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [f]
          congr 1
          push_cast
          ring_nf
      rw [hfchar, charFun_convPow_probability]
      rfl
  have hseries :
      (∑' n : ℕ,
        ((Real.exp (-lam) * lam ^ n / n.factorial : ℝ) : ℂ) *
          charFun Q t ^ n) =
        Complex.exp ((lam : ℂ) * (charFun Q t - 1)) := by
    calc
      _ = (Real.exp (-lam) : ℂ) *
          ∑' n : ℕ, ((lam : ℂ) * charFun Q t) ^ n / n.factorial := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        push_cast
        ring
      _ = (Real.exp (-lam) : ℂ) *
          Complex.exp ((lam : ℂ) * charFun Q t) := by
        rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
      _ = _ := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        push_cast
        ring
  rw [charFun_apply_real]
  have hfun :
      (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) = f := by
    funext x
    dsimp only [f]
    congr 1
    push_cast
    ring
  rw [hfun]
  change (∫ x, f x ∂μ) = _
  rw [show μ = Measure.sum (fun n =>
      ENNReal.ofReal (Real.exp (-lam) * lam ^ n / n.factorial) • convPow Q n) by
    rfl]
  rw [integral_sum_measure hf]
  rw [show (∑' n, ∫ x, f x ∂
      (ENNReal.ofReal (Real.exp (-lam) * lam ^ n / n.factorial) • convPow Q n)) =
      ∑' n, ((Real.exp (-lam) * lam ^ n / n.factorial : ℝ) : ℂ) *
        charFun Q t ^ n by
    apply tsum_congr
    exact hterm]
  exact hseries

/-- Every compound-Poisson law supplies an unconditional positive-definite Gram kernel. -/
theorem positiveDefiniteOnReal_charFun_compoundPoisson
    (lam : ℝ) (hlam : 0 ≤ lam) (Q : Measure ℝ)
    [IsProbabilityMeasure Q] :
    PositiveDefiniteOnReal (charFun (compoundPoisson lam Q)) := by
  letI : IsProbabilityMeasure (compoundPoisson lam Q) :=
    isProbabilityMeasure_compoundPoisson lam hlam Q
  exact positiveDefiniteOnReal_charFun (compoundPoisson lam Q)

end

end GaloisForLFunctions.HTGeometry
