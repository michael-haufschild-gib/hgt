import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedClassicalTwoHeadTruncation

/-!
# Height derivatives of the classical displaced AFE heads

Both finite Dirichlet heads in the displaced classical AFE differentiate
exactly term by term.  These identities isolate the logarithmic coefficients
needed by Levinson's `zeta + lambda zeta'` detector.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaDisplacedDirectTerm
    (d x τ : ℝ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) ^ (-displacedLinePt d τ) *
    smoothAFECutoff ((n + 1 : ℝ) / x)

def smoothAFEZetaDisplacedDirectHeightDerivativeTerm
    (d x τ : ℝ) (n : ℕ) : ℂ :=
  ((n + 1 : ℂ) ^ (-displacedLinePt d τ) *
      Complex.log (n + 1 : ℂ) * (-I)) *
    smoothAFECutoff ((n + 1 : ℝ) / x)

theorem hasDerivAt_smoothAFEZetaDisplacedDirectTerm
    (d x τ : ℝ) (n : ℕ) :
    HasDerivAt (fun u : ℝ => smoothAFEZetaDisplacedDirectTerm d x u n)
      (smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n) τ := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hpC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ)) (y := -displacedLinePt d τ) (Or.inl hn)).hasDerivAt
  have hp := hpC.comp τ (hasDerivAt_displacedLinePt d τ).neg
  have h := hp.mul_const (smoothAFECutoff ((n + 1 : ℝ) / x))
  simpa only [Function.comp_apply, Pi.neg_apply,
    smoothAFEZetaDisplacedDirectTerm,
    smoothAFEZetaDisplacedDirectHeightDerivativeTerm] using h

def smoothAFEZetaDisplacedReflectedMainTerm
    (d τ : ℝ) (n : ℕ) : ℂ :=
  zetaChi (displacedLinePt d τ) *
    (n + 1 : ℂ) ^ (displacedLinePt d τ - 1)

def smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm
    (d τ : ℝ) (n : ℕ) : ℂ :=
  (deriv zetaChi (displacedLinePt d τ) * I) *
      (n + 1 : ℂ) ^ (displacedLinePt d τ - 1) +
    zetaChi (displacedLinePt d τ) *
      ((n + 1 : ℂ) ^ (displacedLinePt d τ - 1) *
        Complex.log (n + 1 : ℂ) * I)

theorem hasDerivAt_smoothAFEZetaDisplacedReflectedMainTerm
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) (n : ℕ) :
    HasDerivAt
      (fun u : ℝ => smoothAFEZetaDisplacedReflectedMainTerm d u n)
      (smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d τ n) τ := by
  have hn : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast (show n + 1 ≠ 0 by omega)
  have hgamma : Gammaℝ (1 - displacedLinePt d τ) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp [displacedLinePt]
    linarith
  have hchi :=
    ((zetaChi_analyticAt hgamma).differentiableAt.hasDerivAt.comp τ
      (hasDerivAt_displacedLinePt d τ))
  have hpC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (n + 1 : ℂ))
      (y := displacedLinePt d τ - 1) (Or.inl hn)).hasDerivAt
  have hp := hpC.comp τ ((hasDerivAt_displacedLinePt d τ).sub_const 1)
  have h := hchi.mul hp
  change HasDerivAt
    (fun u : ℝ => zetaChi (displacedLinePt d u) *
      (n + 1 : ℂ) ^ (displacedLinePt d u - 1))
    ((deriv zetaChi (displacedLinePt d τ) * I) *
        (n + 1 : ℂ) ^ (displacedLinePt d τ - 1) +
      zetaChi (displacedLinePt d τ) *
        ((n + 1 : ℂ) ^ (displacedLinePt d τ - 1) *
          Complex.log (n + 1 : ℂ) * I)) τ
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => rfl)

theorem hasDerivAt_sum_smoothAFEZetaDisplacedDirectTerm
    (d x τ : ℝ) (L : ℕ) :
    HasDerivAt
      (fun u : ℝ => ∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedDirectTerm d x u n)
      (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedDirectHeightDerivativeTerm d x τ n) τ := by
  have h := HasDerivAt.sum (u := Finset.range L)
    (fun n hn => hasDerivAt_smoothAFEZetaDisplacedDirectTerm d x τ n)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by simp [Finset.sum_apply])

theorem hasDerivAt_sum_smoothAFEZetaDisplacedReflectedMainTerm
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) (L : ℕ) :
    HasDerivAt
      (fun u : ℝ => ∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedMainTerm d u n)
      (∑ n ∈ Finset.range L,
        smoothAFEZetaDisplacedReflectedMainHeightDerivativeTerm d τ n) τ := by
  have h := HasDerivAt.sum (u := Finset.range L)
    (fun n hn =>
      hasDerivAt_smoothAFEZetaDisplacedReflectedMainTerm hd hdhalf τ n)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u => by simp [Finset.sum_apply])

end RHTower
