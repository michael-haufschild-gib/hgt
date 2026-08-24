import GaloisForLFunctions.RHTower.C5JensenKernelAlgebra
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# Simple-root perturbation for the C5 Jensen kernel

A simple root of a polynomial has a local analytic branch under a linear
polynomial perturbation.  Differentiating its exact root identity gives the
classical displacement quotient

`root'(0) = - perturbation(root) / original'(root)`.

The C5 specialization turns its finite Leibniz section into a literal
polynomial and proves that a single logarithmic frequency moves a simple
Jensen root by exactly the pinned finite C5 kernel.
-/

open Complex Filter Topology Polynomial

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exact analytic branch and first velocity of a simple root under a linear
polynomial perturbation. -/
theorem exists_analyticAt_rootBranch_linearPolynomialPerturbation
    (J K : Polynomial ℂ) {r0 : ℂ}
    (hroot : J.eval r0 = 0) (hsimple : J.derivative.eval r0 ≠ 0) :
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r 0 ∧ r 0 = r0 ∧
      (∀ᶠ epsilon in 𝓝 0,
        J.eval (r epsilon) + epsilon * K.eval (r epsilon) = 0) ∧
      HasDerivAt r (-K.eval r0 / J.derivative.eval r0) 0 := by
  let f : ℂ × ℂ → ℂ := fun p => J.eval p.2 + p.1 * K.eval p.2
  have hJ : AnalyticAt ℂ (fun z : ℂ => J.eval z) r0 := by
    simpa using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) r0).aeval_polynomial J
  have hK : AnalyticAt ℂ (fun z : ℂ => K.eval z) r0 := by
    simpa using
      (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) r0).aeval_polynomial K
  have hsnd : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (0, r0) := analyticAt_snd
  have hfst : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (0, r0) := analyticAt_fst
  have hf : AnalyticAt ℂ f (0, r0) := by
    have hJs : AnalyticAt ℂ (fun p : ℂ × ℂ => J.eval p.2) (0, r0) := by
      simpa only [Function.comp_def] using hJ.comp hsnd
    have hKs : AnalyticAt ℂ (fun p : ℂ × ℂ => K.eval p.2) (0, r0) := by
      simpa only [Function.comp_def] using hK.comp hsnd
    exact hJs.add (hfst.mul hKs)
  have hfroot : f (0, r0) = 0 := by simp [f, hroot]
  have hpartial : (fderiv ℂ f (0, r0)) (0, 1) = J.derivative.eval r0 := by
    have hfdiff : HasFDerivAt f (fderiv ℂ f (0, r0)) (0, r0) :=
      hf.differentiableAt.hasFDerivAt
    have hline : HasFDerivAt (fun z : ℂ => ((0 : ℂ), z))
        ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) r0 :=
      (hasFDerivAt_const (0 : ℂ) r0).prodMk (hasFDerivAt_id r0)
    have hcomp := hfdiff.comp r0 hline
    have hpoly : HasDerivAt (fun z : ℂ => f (0, z))
        (J.derivative.eval r0) r0 := by
      simpa [f] using J.hasDerivAt r0
    have huniq := hcomp.unique hpoly.hasFDerivAt
    have hev := ContinuousLinearMap.ext_iff.mp huniq 1
    simpa [f] using hev
  obtain ⟨r, hrAnalytic, hr0, hrroot⟩ :=
    HTGeometry.parametric_holo_implicit hf hfroot (by rwa [hpartial])
  let rdot := deriv r 0
  have hrDeriv : HasDerivAt r rdot 0 :=
    hrAnalytic.differentiableAt.hasDerivAt
  have hJcomp := (J.hasDerivAt (r 0)).comp 0 hrDeriv
  have hKcomp := (K.hasDerivAt (r 0)).comp 0 hrDeriv
  have hleft := hJcomp.add ((hasDerivAt_id 0).mul hKcomp)
  have hrroot' :
      (((fun x : ℂ => J.eval x) ∘ r) +
          id * ((fun x : ℂ => K.eval x) ∘ r)) =ᶠ[𝓝 0]
        (fun _ : ℂ => 0) := by
    filter_upwards [hrroot] with epsilon hepsilon
    simpa [f, Function.comp_def] using hepsilon
  have htransport := hrroot'.hasDerivAt_iff.mp hleft
  have hzeroRaw :=
    htransport.unique (hasDerivAt_const (x := (0 : ℂ)) (c := (0 : ℂ)))
  have hzero : J.derivative.eval r0 * rdot + K.eval r0 = 0 := by
    simpa [hr0] using hzeroRaw
  have hrdot : rdot = -K.eval r0 / J.derivative.eval r0 := by
    apply (eq_div_iff hsimple).2
    linear_combination hzero
  refine ⟨r, hrAnalytic, hr0, hrroot, ?_⟩
  rwa [← hrdot]

/-- Degree-`d` unperturbed Jensen section as a literal polynomial. -/
def c5JensenSectionPolynomial (d : ℕ) (arch : ℕ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.monomial j ((d.choose j : ℂ) * arch j / (j.factorial : ℂ))

/-- First-order C5 Jensen section as a literal polynomial. -/
def c5JensenFirstOrderPolynomial
    (d : ℕ) (arch perturb : ℕ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.monomial j
      ((d.choose j : ℂ) / (j.factorial : ℂ) *
        ∑ i ∈ Finset.range (d + 1),
          if i ≤ j then (j.choose i : ℂ) * arch (j - i) * perturb i else 0)

/-- Evaluation of the literal unperturbed section gives its standard finite
Jensen sum. -/
theorem eval_c5JensenSectionPolynomial
    (d : ℕ) (arch : ℕ → ℂ) (X : ℂ) :
    (c5JensenSectionPolynomial d arch).eval X =
      ∑ j ∈ Finset.range (d + 1),
        (d.choose j : ℂ) * arch j * X ^ j / (j.factorial : ℂ) := by
  simp only [c5JensenSectionPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Evaluation of the literal first-order polynomial is the previously pinned
finite Leibniz section. -/
theorem eval_c5JensenFirstOrderPolynomial
    (d : ℕ) (arch perturb : ℕ → ℂ) (X : ℂ) :
    (c5JensenFirstOrderPolynomial d arch perturb).eval X =
      c5JensenFirstOrderSection d arch perturb X := by
  simp only [c5JensenFirstOrderPolynomial, c5JensenFirstOrderSection,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A simple root of the unperturbed C5 section has an analytic branch whose
first velocity is the exact first-order Jensen quotient. -/
theorem exists_c5JensenRootBranch
    (d : ℕ) (arch perturb : ℕ → ℂ) {r0 : ℂ}
    (hroot : (c5JensenSectionPolynomial d arch).eval r0 = 0)
    (hsimple : (c5JensenSectionPolynomial d arch).derivative.eval r0 ≠ 0) :
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r 0 ∧ r 0 = r0 ∧
      (∀ᶠ epsilon in 𝓝 0,
        (c5JensenSectionPolynomial d arch).eval (r epsilon) +
          epsilon * c5JensenFirstOrderSection d arch perturb (r epsilon) = 0) ∧
      HasDerivAt r
        (-c5JensenFirstOrderSection d arch perturb r0 /
          (c5JensenSectionPolynomial d arch).derivative.eval r0) 0 := by
  obtain ⟨r, hra, hr0, hrroot, hrderiv⟩ :=
    exists_analyticAt_rootBranch_linearPolynomialPerturbation
      (c5JensenSectionPolynomial d arch)
      (c5JensenFirstOrderPolynomial d arch perturb) hroot hsimple
  refine ⟨r, hra, hr0, ?_, ?_⟩
  · filter_upwards [hrroot] with epsilon hepsilon
    simpa [eval_c5JensenFirstOrderPolynomial] using hepsilon
  · simpa [eval_c5JensenFirstOrderPolynomial] using hrderiv

/-- One logarithmic frequency moves a simple Jensen root with the exact C5
kernel velocity. The zero-order perturbation is absent, so the numerator is
the positive-order finite Leibniz kernel. -/
theorem exists_c5JensenLogFrequencyRootBranch
    (d : ℕ) (arch : ℕ → ℂ) (amplitude frequency : ℂ) {r0 : ℂ}
    (hroot : (c5JensenSectionPolynomial d arch).eval r0 = 0)
    (hsimple : (c5JensenSectionPolynomial d arch).derivative.eval r0 ≠ 0) :
    ∃ r : ℂ → ℂ,
      AnalyticAt ℂ r 0 ∧ r 0 = r0 ∧
      (∀ᶠ epsilon in 𝓝 0,
        (c5JensenSectionPolynomial d arch).eval (r epsilon) +
          epsilon * (amplitude * ∑ i ∈ Finset.range (d + 1),
            if i = 0 then 0 else
              (-Complex.I * frequency) ^ i *
                c5JensenLeibnizCoefficient d arch i (r epsilon)) = 0) ∧
      HasDerivAt r
        (-(amplitude * ∑ i ∈ Finset.range (d + 1),
            if i = 0 then 0 else
              (-Complex.I * frequency) ^ i *
                c5JensenLeibnizCoefficient d arch i r0) /
          (c5JensenSectionPolynomial d arch).derivative.eval r0) 0 := by
  obtain ⟨r, hra, hr0, hrroot, hrderiv⟩ :=
    exists_c5JensenRootBranch d arch
      (fun i => if i = 0 then 0 else
        amplitude * (-Complex.I * frequency) ^ i)
      hroot hsimple
  refine ⟨r, hra, hr0, ?_, ?_⟩
  · filter_upwards [hrroot] with epsilon hepsilon
    rw [c5JensenFirstOrderSection_singleFrequency_noConstant] at hepsilon
    exact hepsilon
  · rw [c5JensenFirstOrderSection_singleFrequency_noConstant] at hrderiv
    exact hrderiv

end

end GaloisForLFunctions.RHTower
