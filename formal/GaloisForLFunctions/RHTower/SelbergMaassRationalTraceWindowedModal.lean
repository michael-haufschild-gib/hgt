import GaloisForLFunctions.RHTower.SelbergMaassPositiveRationalTrace
import GaloisForLFunctions.RHTower.SelbergMaassPrincipalPositiveRationalLifts
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.SelbergMaassRationalTraceFourierAggregation

/-!
# Windowed Maass equations for individual rational-trace summands

Every individual coset summand in a rational principal trace remains a local
Maass eigenfunction at the original eigenvalue.  Its Fourier coefficient over
the target's common horizontal window therefore satisfies the exact modal
identity with the two endpoint seams retained.  This is the local analytic
input needed to sum the rational trace without silently imposing periodicity
on its individual terms.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex Set Filter Topology UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassFourier
open scoped BigOperators MatrixGroups

noncomputable section

/-- One literal coset summand of the rational principal trace. -/
def rationalPrincipalTraceSummand (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) : ℍ → ℂ :=
  maassTraceQuotientFunc
    (rationalMaassPullback N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1 q

/-- The literal common-window Fourier coefficient of one rational-trace summand. -/
def rationalPrincipalTraceSummandCoefficient (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (n : ℤ) : ℝ → ℂ :=
  coefficient w n (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex)

/-- The explicit endpoint defect in the windowed modal equation of one raw summand. -/
def rationalPrincipalTraceSummandSeam (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (n : ℤ) (y : ℝ) : ℂ :=
  (directional 1 (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point w y) -
    directional 1 (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point 0 y)) / w +
  ((2 * Real.pi * Complex.I * n) / w) *
    ((rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point w y) -
      (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point 0 y)) / w

/-- Each literal rational-trace summand has the original Maass eigenvalue. -/
theorem rationalPrincipalTraceSummand_isMaassEigenfunction (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) :
    IsMaassEigenfunction lam (rationalPrincipalTraceSummand N f g hg q) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  exact positiveRationalTrace_component_eigen
    (principalCongruenceGL_hasPositiveRationalLifts N) lam
    (rationalMaassPullback N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1
    (rationalMaassPullback N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).2.2.1 q

/-- The exact modal equation of one raw rational trace summand over any positive
common target window.  The displayed seams are the only failure of the
homogeneous periodic equation. -/
theorem rationalPrincipalTraceSummand_windowed_modal_equation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (hw : 0 < w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 *
      (deriv (deriv (coefficient w n (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex))) y -
        ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
          coefficient w n (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) y +
        (directional 1 (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point w y) -
          directional 1 (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point 0 y)) / w +
        ((2 * Real.pi * Complex.I * n) / w) *
          ((rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point w y) -
            (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point 0 y)) / w) =
      (lam : ℂ) * coefficient w n (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) y :=
  windowedCoefficient_modal_equation (rationalPrincipalTraceSummand N f g hg q)
    (rationalPrincipalTraceSummand_isMaassEigenfunction N f g hg q) w hw n hy

/-- Every raw summand coefficient has its first height derivative. -/
theorem rationalPrincipalTraceSummandCoefficient_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (hw : 0 ≤ w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (rationalPrincipalTraceSummandCoefficient N f g hg q w n)
      (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n) y) y :=
  have hsmooth : ContDiffOn ℝ 2
      (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    rationalPrincipalTraceSummand_isMaassEigenfunction N f g hg q |>.1
  (coefficient_hasDerivAt w hw n
    (hsmooth.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)) hy).differentiableAt.hasDerivAt

/-- Every raw summand coefficient has its second height derivative. -/
theorem rationalPrincipalTraceSummandCoefficient_second_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (hw : 0 ≤ w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n))
      (deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y) y :=
  have hsmooth : ContDiffOn ℝ 2
      (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    rationalPrincipalTraceSummand_isMaassEigenfunction N f g hg q |>.1
  (coefficient_second_hasDerivAt w hw n hsmooth hy).differentiableAt.hasDerivAt

/-- The individual windowed equation expressed through the named raw coefficient and seam. -/
theorem rationalPrincipalTraceSummandCoefficient_windowed_modal_equation (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (w : ℝ) (hw : 0 < w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    -(y : ℂ) ^ 2 *
      (deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y -
        ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
          rationalPrincipalTraceSummandCoefficient N f g hg q w n y +
        rationalPrincipalTraceSummandSeam N f g hg q w n y) =
      (lam : ℂ) * rationalPrincipalTraceSummandCoefficient N f g hg q w n y := by
  simpa only [rationalPrincipalTraceSummandCoefficient, rationalPrincipalTraceSummandSeam, add_assoc] using
    rationalPrincipalTraceSummand_windowed_modal_equation N f g hg q w hw n hy

/-- Summing the literal local Maass equations leaves one finite, explicit
seam functional.  All rational trace summands retain the same physical
frequency because they are measured in the common target window. -/
theorem rationalPrincipalTraceSummandCoefficient_sum_windowed_modal_equation
    (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (w : ℝ) (hw : 0 < w) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    (-(y : ℂ) ^ 2 *
      (deriv (deriv (fun t : ℝ => ∑ q,
          rationalPrincipalTraceSummandCoefficient N f g hg q w n t)) y -
        ((signedFrequency w n : ℝ) : ℂ) ^ 2 * (∑ q,
          rationalPrincipalTraceSummandCoefficient N f g hg q w n y) +
        (∑ q, rationalPrincipalTraceSummandSeam N f g hg q w n y)) =
      (lam : ℂ) * (∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n y)) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite (principalCongruenceGL N ⧸
    ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  have hsumFirst : HasDerivAt (fun t : ℝ => ∑ q,
      rationalPrincipalTraceSummandCoefficient N f g hg q w n t)
      (∑ q, deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n) y) y := by
    apply (HasDerivAt.sum (u := Finset.univ)
      (fun q _ => rationalPrincipalTraceSummandCoefficient_hasDerivAt N f g hg q w hw.le n hy)).congr_of_eventuallyEq
    filter_upwards with t
    simp only [Finset.sum_apply]
  have hsumSecondRaw : HasDerivAt (fun t : ℝ => ∑ q,
      deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n) t)
      (∑ q, deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y) y := by
    apply (HasDerivAt.sum (u := Finset.univ)
      (fun q _ => rationalPrincipalTraceSummandCoefficient_second_hasDerivAt
        N f g hg q w hw.le n hy)).congr_of_eventuallyEq
    filter_upwards with t
    simp only [Finset.sum_apply]
  have hderivSum : (deriv (fun t : ℝ => ∑ q,
      rationalPrincipalTraceSummandCoefficient N f g hg q w n t)) =ᶠ[𝓝 y]
      (fun t : ℝ => ∑ q, deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n) t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have h := (HasDerivAt.sum (u := Finset.univ)
      (fun q _ => rationalPrincipalTraceSummandCoefficient_hasDerivAt N f g hg q w hw.le n ht)).deriv
    have hfun : (fun u : ℝ => ∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n u) =
        ∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n := by
      funext u
      simp only [Finset.sum_apply]
    rw [hfun]
    exact h
  have hsumSecond : HasDerivAt (deriv (fun t : ℝ => ∑ q,
      rationalPrincipalTraceSummandCoefficient N f g hg q w n t))
      (∑ q, deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y) y := by
    apply hsumSecondRaw.congr_of_eventuallyEq
    exact hderivSum
  have hsumModal : ∑ q, -(y : ℂ) ^ 2 *
      (deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y -
        ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
          rationalPrincipalTraceSummandCoefficient N f g hg q w n y +
        rationalPrincipalTraceSummandSeam N f g hg q w n y) =
      ∑ q, (lam : ℂ) * rationalPrincipalTraceSummandCoefficient N f g hg q w n y := by
    exact Finset.sum_congr rfl (fun q _ =>
      rationalPrincipalTraceSummandCoefficient_windowed_modal_equation N f g hg q w hw n hy)
  rw [hsumSecond.deriv]
  symm
  calc
    (lam : ℂ) * (∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n y) =
        ∑ q, (lam : ℂ) * rationalPrincipalTraceSummandCoefficient N f g hg q w n y :=
      by rw [Finset.mul_sum]
    _ = ∑ q, -(y : ℂ) ^ 2 *
        (deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y -
          ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
            rationalPrincipalTraceSummandCoefficient N f g hg q w n y +
          rationalPrincipalTraceSummandSeam N f g hg q w n y) := hsumModal.symm
    _ =
        -(y : ℂ) ^ 2 * ∑ q,
          (deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y -
            ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
              rationalPrincipalTraceSummandCoefficient N f g hg q w n y +
            rationalPrincipalTraceSummandSeam N f g hg q w n y) :=
      by rw [Finset.mul_sum]
    _ = -(y : ℂ) ^ 2 *
        ((∑ q, deriv (deriv (rationalPrincipalTraceSummandCoefficient N f g hg q w n)) y) -
          ((signedFrequency w n : ℝ) : ℂ) ^ 2 *
            (∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n y) +
          (∑ q, rationalPrincipalTraceSummandSeam N f g hg q w n y)) := by
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- At a common target window, the rational trace coefficient is literally the
finite sum of its raw coset coefficients.  This is the bridge from the local
summand equations to the periodic trace coefficient. -/
theorem rationalPrincipalTrace_coefficient_eq_summandCoefficient_sum
    (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (w : ℝ) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    coefficient w n
      (rationalPrincipalTraceFunction N g hg lam
        (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f) ∘ ofComplex) y =
      ∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q w n y := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite (principalCongruenceGL N ⧸
    ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  have hcontinuous (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) :
      Continuous (fun x : ℝ =>
        (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) (point x y)) := by
    have hsmooth : ContDiffOn ℝ 2
        (rationalPrincipalTraceSummand N f g hg q ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      rationalPrincipalTraceSummand_isMaassEigenfunction N f g hg q |>.1
    apply hsmooth.continuousOn.comp_continuous
      (show Continuous (fun x : ℝ => point x y) by unfold point; fun_prop)
    intro x
    simpa [point] using hy
  change deningerFourierCoeff w
      (fun x => ∑ q, rationalPrincipalTraceSummand N f g hg q
        (UpperHalfPlane.ofComplex (point x y))) n =
    ∑ q, deningerFourierCoeff w
      (fun x => rationalPrincipalTraceSummand N f g hg q
        (UpperHalfPlane.ofComplex (point x y))) n
  apply deningerFourierCoeff_fintype_sum w n
  intro q
  simpa only [Function.comp_apply] using hcontinuous q

/-- A nonzero rational trace is periodic at the common principal width, so its
homogeneous modal equation cancels the finite sum of local window seams. -/
theorem rationalPrincipalTrace_summandSeam_sum_eq_zero
    (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (F : GLMaassCuspEigenform (principalCongruenceGL N) lam)
    (hF : F.1.1 = rationalPrincipalTraceFunction N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    ∑ q, rationalPrincipalTraceSummandSeam N f g hg q (N + 1 : ℕ) n y = 0 := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite (principalCongruenceGL N ⧸
    ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  let M := glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam F
  have hcoefficient (t : ℝ) (ht : 0 < t) :
      maassCoefficient N M n t = ∑ q,
        rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n t := by
    change coefficient (N + 1 : ℕ) n (F.1.1 ∘ ofComplex) t = _
    rw [hF]
    exact rationalPrincipalTrace_coefficient_eq_summandCoefficient_sum N f g hg
      (N + 1 : ℕ) n ht
  have hderivNear : deriv (maassCoefficient N M n) =ᶠ[𝓝 y]
      (fun t => deriv (fun u => ∑ q,
        rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n u) t) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    have hlocal : maassCoefficient N M n =ᶠ[𝓝 t]
        (fun u => ∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n u) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact hcoefficient u hu
    exact hlocal.deriv_eq
  have hsecond := hderivNear.deriv_eq
  have hperiodic := maassCoefficient_modal_equation N M n hy
  rw [hcoefficient y hy, hsecond] at hperiodic
  have hwindowed := rationalPrincipalTraceSummandCoefficient_sum_windowed_modal_equation
    N f g hg (N + 1 : ℕ) (by positivity) n hy
  have hseam : -(y : ℂ) ^ 2 *
      (∑ q, rationalPrincipalTraceSummandSeam N f g hg q (N + 1 : ℕ) n y) = 0 := by
    calc
      -(y : ℂ) ^ 2 * (∑ q, rationalPrincipalTraceSummandSeam N f g hg q (N + 1 : ℕ) n y) =
          -(y : ℂ) ^ 2 *
            (deriv (deriv (fun t => ∑ q,
              rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n t)) y -
              ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) ^ 2 *
                (∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n y) +
              (∑ q, rationalPrincipalTraceSummandSeam N f g hg q (N + 1 : ℕ) n y)) -
            -(y : ℂ) ^ 2 *
              (deriv (deriv (fun t => ∑ q,
                rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n t)) y -
                ((signedFrequency (N + 1 : ℕ) n : ℝ) : ℂ) ^ 2 *
                  (∑ q, rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n y)) := by
            ring
      _ = (lam : ℂ) * (∑ q,
            rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n y) -
          (lam : ℂ) * (∑ q,
            rationalPrincipalTraceSummandCoefficient N f g hg q (N + 1 : ℕ) n y) := by
            rw [hwindowed, hperiodic]
      _ = 0 := sub_self _
  exact (mul_eq_zero.mp hseam).resolve_left
    (neg_ne_zero.mpr (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))))

end

end GaloisForLFunctions.RHTower
