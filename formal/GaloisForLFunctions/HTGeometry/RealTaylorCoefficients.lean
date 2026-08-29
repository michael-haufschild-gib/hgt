import GaloisForLFunctions.HTGeometry.LaguerrePolyaJensenConverse
import GaloisForLFunctions.HTGeometry.MovingEvenCanonicalFiniteJetSubmersion

/-!
# Real Taylor coefficients of a Schwarz-real entire function

A Schwarz-real entire function has real derivative jets at the origin, so its Taylor expansion has
real coefficients and both directions of Jensen's theorem apply to it: a nonreal zero forces some
Jensen polynomial to fail to split.
-/

open Polynomial Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real Taylor coefficient sequence of a Schwarz-real entire function at the origin. -/
def realTaylorCoeff (F : ℂ → ℂ) (j : ℕ) : ℝ :=
  (((j.factorial : ℂ))⁻¹ * iteratedDeriv j F 0).re

theorem iteratedDeriv_conj_of_schwarzReal {f : ℂ → ℂ}
    (hs : ∀ z, f (conj z) = conj (f z)) (n : ℕ) (z : ℂ) :
    iteratedDeriv n f (conj z) = conj (iteratedDeriv n f z) := by
  have hfun : (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = f := by
    funext w
    simpa [Function.comp_apply] using (hs (conj w)).symm
  have hder := iteratedDeriv_star_comp_star f n
  rw [hfun] at hder
  simpa [Function.comp_apply] using congrFun hder (conj z)

theorem ofReal_realTaylorCoeff {F : ℂ → ℂ}
    (hs : ∀ z, F (conj z) = conj (F z)) (j : ℕ) :
    ((realTaylorCoeff F j : ℝ) : ℂ) = ((j.factorial : ℂ))⁻¹ * iteratedDeriv j F 0 := by
  have h : conj (iteratedDeriv j F 0) = iteratedDeriv j F 0 := by
    have := iteratedDeriv_conj_of_schwarzReal hs j 0
    simpa using this.symm
  have hw : (((iteratedDeriv j F 0).re : ℝ) : ℂ) = iteratedDeriv j F 0 :=
    Complex.conj_eq_iff_re.1 h
  have hfac : ((j.factorial : ℂ))⁻¹ = ((((j.factorial : ℝ))⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [realTaylorCoeff, hfac, ← hw, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.ofReal_mul]

theorem hasSum_realTaylorCoeff {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hs : ∀ z, F (conj z) = conj (F z)) (z : ℂ) :
    HasSum (fun i => ((realTaylorCoeff F i : ℝ) : ℂ) * z ^ i) (F z) := by
  have hfun : (fun i : ℕ => ((realTaylorCoeff F i : ℝ) : ℂ) * z ^ i)
      = fun i : ℕ => ((i.factorial : ℂ))⁻¹ • (z - 0) ^ i • iteratedDeriv i F 0 := by
    funext i
    rw [ofReal_realTaylorCoeff hs i]
    simp only [smul_eq_mul, sub_zero]
    ring
  rw [hfun]
  exact Complex.hasSum_taylorSeries_of_entire hF 0 z

theorem ofReal_realTaylorCoeff_deriv {F : ℂ → ℂ}
    (hs : ∀ z, F (conj z) = conj (F z)) (j : ℕ) :
    ((realTaylorCoeff F j : ℝ) : ℂ) = deriv^[j] F 0 / (j.factorial : ℂ) := by
  rw [ofReal_realTaylorCoeff hs j, ← iteratedDeriv_eq_iterate]
  field_simp

/-- **A nonreal zero of a Schwarz-real entire function breaks Jensen hyperbolicity.** -/
theorem exists_jensenPoly_not_splits_of_nonreal_zero {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hs : ∀ z, F (conj z) = conj (F z))
    {a z : ℂ} (ha : F a ≠ 0) (hz : F z = 0) (him : z.im ≠ 0) :
    ∃ d, ¬ (jensenPoly (realTaylorCoeff F) d).Splits := by
  by_contra h
  push Not at h
  have hLP : LaguerrePolya F :=
    laguerrePolya_of_splits_jensenPoly (hasSum_realTaylorCoeff hF hs) h
  exact him (im_eq_zero_of_laguerrePolya hLP ha hz)

/-- **All Jensen polynomials of a Laguerre–Pólya Schwarz-real entire function split.** -/
theorem splits_jensenPoly_realTaylorCoeff {F : ℂ → ℂ}
    (hLP : LaguerrePolya F) (hs : ∀ z, F (conj z) = conj (F z)) (d : ℕ) :
    (jensenPoly (realTaylorCoeff F) d).Splits :=
  splits_jensenPoly_of_laguerrePolya hLP (fun j => ofReal_realTaylorCoeff_deriv hs j) d

end

end GaloisForLFunctions.HTGeometry
