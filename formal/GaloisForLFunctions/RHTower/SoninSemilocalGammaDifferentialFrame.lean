import GaloisForLFunctions.RHTower.SoninSemilocalGammaShiftedKernel
import GaloisForLFunctions.RHTower.SoninSemilocalGammaAutocorrelation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Differential frame of the quarter-Gamma log kernel

Differentiation of the quarter-Gamma log kernel closes on a polynomial frame in `exp (-x)`.
Expanding that polynomial expresses every derivative as a finite linear combination of the shifted
kernels from `SoninSemilocalGammaShiftedKernel`.  Consequently every derivative is integrable and
uniformly bounded.  This is the Sobolev input needed to prove all polynomial moments of the
archimedean Gamma measure without invoking a vertical Gamma asymptotic.
-/

noncomputable section

open Complex MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace RHTower

theorem hasDerivAt_semilocalGammaLogKernel (a x : ℝ) :
    HasDerivAt (semilocalGammaLogKernel a)
      (((-a + Real.exp (-x) : ℝ) : ℂ) * semilocalGammaLogKernel a x) x := by
  have hlinear : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
    exact ((hasDerivAt_id x).const_mul (-a)).congr_deriv (by ring)
  have hfirst : HasDerivAt (fun y : ℝ => Real.exp (-a * y))
      (-a * Real.exp (-a * x)) x := by
    exact hlinear.exp.congr_deriv (by ring)
  have hnegRaw := (hasDerivAt_id x).neg
  have hnegFun : (-id : ℝ → ℝ) = fun y : ℝ => -y := by
    funext y
    rfl
  rw [hnegFun] at hnegRaw
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := hnegRaw
  have hexpNeg : HasDerivAt (fun y : ℝ => Real.exp (-y))
      (-Real.exp (-x)) x := by
    exact hneg.exp.congr_deriv (by ring)
  have hnegexpRaw := hexpNeg.neg
  have hnegexpFun :
      -(fun y : ℝ => Real.exp (-y)) = fun y : ℝ => -Real.exp (-y) := by
    funext y
    rfl
  rw [hnegexpFun] at hnegexpRaw
  have hnegexp : HasDerivAt (fun y : ℝ => -Real.exp (-y))
      (Real.exp (-x)) x := by
    exact hnegexpRaw.congr_deriv (by ring)
  have hsecond : HasDerivAt (fun y : ℝ => Real.exp (-Real.exp (-y)))
      (Real.exp (-x) * Real.exp (-Real.exp (-x))) x := by
    exact hnegexp.exp.congr_deriv (by ring)
  have hreal := hfirst.mul hsecond
  have hrealFun :
      (fun y : ℝ => Real.exp (-a * y)) *
          (fun y : ℝ => Real.exp (-Real.exp (-y))) =
        fun y : ℝ => Real.exp (-a * y) * Real.exp (-Real.exp (-y)) := by
    funext y
    rfl
  rw [hrealFun] at hreal
  have hcomplex := hreal.ofReal_comp
  have hkernelFun :
      (fun y : ℝ => ((Real.exp (-a * y) * Real.exp (-Real.exp (-y)) : ℝ) : ℂ)) =
        semilocalGammaLogKernel a := by
    funext y
    rfl
  rw [hkernelFun] at hcomplex
  apply hcomplex.congr_deriv
  unfold semilocalGammaLogKernel
  push_cast
  ring

/-- The polynomial update induced by one derivative of the quarter-Gamma log kernel. -/
def semilocalGammaDifferentialStep (p : ℝ[X]) : ℝ[X] :=
  X * p - X * p.derivative - C (1 / 4) * p

/-- The polynomial multiplying the quarter-Gamma log kernel after `n` derivatives. -/
def semilocalGammaDifferentialPolynomial : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => semilocalGammaDifferentialStep
      (semilocalGammaDifferentialPolynomial n)

def semilocalGammaDifferentialFrame (p : ℝ[X]) (x : ℝ) : ℂ :=
  ((p.eval (Real.exp (-x)) : ℝ) : ℂ) * semilocalGammaQuarterKernel x

theorem hasDerivAt_semilocalGammaDifferentialFrame (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (semilocalGammaDifferentialFrame p)
      (semilocalGammaDifferentialFrame (semilocalGammaDifferentialStep p) x) x := by
  have hnegRaw := (hasDerivAt_id x).neg
  have hnegFun : (-id : ℝ → ℝ) = fun y : ℝ => -y := by
    funext y
    rfl
  rw [hnegFun] at hnegRaw
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := hnegRaw
  have hexpNeg : HasDerivAt (fun y : ℝ => Real.exp (-y))
      (-Real.exp (-x)) x := by
    exact hneg.exp.congr_deriv (by ring)
  have hpolyBase : HasDerivAt (fun y : ℝ => p.eval y)
      (p.derivative.eval (Real.exp (-x))) (Real.exp (-x)) :=
    Polynomial.hasDerivAt p (Real.exp (-x))
  have hpolyRaw := hpolyBase.comp x hexpNeg
  have hpolyFun :
      (fun y : ℝ => p.eval y) ∘ (fun y : ℝ => Real.exp (-y)) =
        fun y : ℝ => p.eval (Real.exp (-y)) := by
    funext y
    rfl
  rw [hpolyFun] at hpolyRaw
  have hpolyReal : HasDerivAt (fun y : ℝ => p.eval (Real.exp (-y)))
      (p.derivative.eval (Real.exp (-x)) * (-Real.exp (-x))) x :=
    hpolyRaw
  have hproduct := hpolyReal.ofReal_comp.mul
    (hasDerivAt_semilocalGammaLogKernel (1 / 4) x)
  have hproductFun :
      (fun y : ℝ => ((p.eval (Real.exp (-y)) : ℝ) : ℂ)) *
          semilocalGammaLogKernel (1 / 4) =
        semilocalGammaDifferentialFrame p := by
    funext y
    rfl
  rw [hproductFun] at hproduct
  apply hproduct.congr_deriv
  unfold semilocalGammaDifferentialFrame semilocalGammaDifferentialStep
    semilocalGammaQuarterKernel semilocalGammaLogKernel
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  push_cast
  ring_nf

theorem iteratedDeriv_semilocalGammaQuarterKernel (n : ℕ) :
    iteratedDeriv n semilocalGammaQuarterKernel =
      semilocalGammaDifferentialFrame (semilocalGammaDifferentialPolynomial n) := by
  induction n with
  | zero =>
      funext x
      simp [semilocalGammaQuarterKernel, semilocalGammaDifferentialFrame,
        semilocalGammaDifferentialPolynomial]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_semilocalGammaDifferentialFrame
        (semilocalGammaDifferentialPolynomial n) x).deriv

theorem semilocalGammaDifferentialFrame_eq_sum (p : ℝ[X]) (x : ℝ) :
    semilocalGammaDifferentialFrame p x =
      ∑ j ∈ Finset.range (p.natDegree + 1),
        (p.coeff j : ℂ) *
          semilocalGammaLogKernel ((j : ℝ) + 1 / 4) x := by
  unfold semilocalGammaDifferentialFrame semilocalGammaQuarterKernel
  rw [Polynomial.eval_eq_sum_range]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold semilocalGammaLogKernel
  push_cast
  calc
    (p.coeff j : ℂ) * Complex.exp (-x) ^ j *
          (Complex.exp (-(1 / 4) * x) * Complex.exp (-Complex.exp (-x))) =
        (p.coeff j : ℂ) *
          ((Complex.exp (-x) ^ j * Complex.exp (-(1 / 4) * x)) *
            Complex.exp (-Complex.exp (-x))) := by ring
    _ = _ := by
      congr 3
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring

theorem integrable_semilocalGammaDifferentialFrame (p : ℝ[X]) :
    Integrable (semilocalGammaDifferentialFrame p) := by
  rw [show semilocalGammaDifferentialFrame p = fun x : ℝ =>
      ∑ j ∈ Finset.range (p.natDegree + 1),
        (p.coeff j : ℂ) *
          semilocalGammaLogKernel ((j : ℝ) + 1 / 4) x by
    funext x
    exact semilocalGammaDifferentialFrame_eq_sum p x]
  exact MeasureTheory.integrable_finsetSum _ fun j _hj =>
    (integrable_semilocalGammaShiftedKernel j).const_mul (p.coeff j : ℂ)

def semilocalGammaDifferentialFrameBound (p : ℝ[X]) : ℝ :=
  ∑ j ∈ Finset.range (p.natDegree + 1),
    |p.coeff j| * ((Nat.factorial (j + 1) : ℝ) + 1)

theorem norm_semilocalGammaDifferentialFrame_le (p : ℝ[X]) (x : ℝ) :
    ‖semilocalGammaDifferentialFrame p x‖ ≤
      semilocalGammaDifferentialFrameBound p := by
  rw [semilocalGammaDifferentialFrame_eq_sum]
  refine (norm_sum_le _ _).trans ?_
  unfold semilocalGammaDifferentialFrameBound
  apply Finset.sum_le_sum
  intro j _hj
  rw [norm_mul, norm_real, Real.norm_eq_abs]
  gcongr
  exact norm_semilocalGammaShiftedKernel_le j x

theorem integrable_iteratedDeriv_semilocalGammaQuarterKernel (n : ℕ) :
    Integrable (iteratedDeriv n semilocalGammaQuarterKernel) := by
  rw [iteratedDeriv_semilocalGammaQuarterKernel]
  exact integrable_semilocalGammaDifferentialFrame _

theorem contDiff_semilocalGammaQuarterKernel :
    ContDiff ℝ ⊤ semilocalGammaQuarterKernel := by
  have hreal : ContDiff ℝ ⊤
      (fun x : ℝ => Real.exp (-(1 / 4) * x) * Real.exp (-Real.exp (-x))) := by
    fun_prop
  have hcomplex := Complex.ofRealCLM.contDiff.comp hreal
  have hfun :
      Complex.ofRealCLM ∘
          (fun x : ℝ => Real.exp (-(1 / 4) * x) * Real.exp (-Real.exp (-x))) =
        semilocalGammaQuarterKernel := by
    funext x
    rfl
  rw [hfun] at hcomplex
  exact hcomplex

end RHTower
