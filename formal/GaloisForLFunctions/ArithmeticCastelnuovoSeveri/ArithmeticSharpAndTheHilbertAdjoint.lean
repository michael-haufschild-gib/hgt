import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FaithfulPositiveMeyerDegrees

/-!
# Arithmetic sharp and the actual Hilbert adjoint

The faithful full-Hasse convolution representation respects arithmetic sharp as
Hilbert adjoint exactly when every Xi zero is simple and critical. Faithfulness
turns the Hilbert Gram identity into sharp-square-root closure of the genuine
Poisson ideal; conversely simple critical blocks are scalar conjugate pairs.
-/

noncomputable section
open Complex Zeta23 RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Simplicity reduces the actual triangular Hasse action to its value multiplier. -/
theorem meyerHilbertConvolution_apply_of_simple
    (hs : ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1)
    (g : DeningerMeyerStrongLogTarget) (x : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertConvolution g x q =
      deningerMeyerStrongLogMellin g (q.1 : ℂ) * x q := by
  have hq : q.2.val = 0 := by
    have hlt := q.2.isLt
    have hm := hs q.1
    omega
  rw [deningerMeyerHilbertConvolution_jets, hq]
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
    deningerMeyerHasseMoment, Nat.factorial_zero, Nat.cast_one, div_one,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero]
  congr 1

/-- Adjoint compatibility forces sharp-square-root closure of the genuine Poisson ideal. -/
theorem meyerHilbertConvolution_adjoint_forces_sharp_roots
    (hadj : ∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
        ContinuousLinearMap.adjoint (deningerMeyerHilbertConvolution g)) :
    ∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g) ∈
        LinearMap.range deningerMeyerStrongLogSumLM →
      g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  intro g hg
  have hz := (deningerMeyerHilbertConvolution_eq_zero_iff _).mpr hg
  rw [deningerMeyerSourceConvolution_comm g (deningerMeyerSourceSharp g),
    deningerMeyerHilbertConvolution_mul, hadj g] at hz
  have hn := ContinuousLinearMap.norm_adjoint_comp_self (deningerMeyerHilbertConvolution g)
  rw [hz, norm_zero] at hn
  apply (deningerMeyerHilbertConvolution_eq_zero_iff g).mp
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa only [pow_two] using hn.symm))

/-- At simple critical zeros arithmetic sharp is the actual Hilbert adjoint. -/
theorem meyerHilbertConvolution_sharp_eq_adjoint_of_simple_critical
    (hRH : RiemannHypothesis)
    (hs : ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
      ContinuousLinearMap.adjoint (deningerMeyerHilbertConvolution g) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro q
  rw [meyerHilbertConvolution_apply_of_simple hs,
    meyerHilbertConvolution_apply_of_simple hs]
  have href : star (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by
    apply Complex.ext
    · change 1 - (q.1 : ℂ).re = (q.1 : ℂ).re
      rw [xi_divisor_support_re_eq_half_of_rh hRH q.1]
      norm_num
    · change -(0 - (q.1 : ℂ).im) = (q.1 : ℂ).im
      ring
  have hsharp : deningerMeyerStrongLogMellin (deningerMeyerSourceSharp g) (q.1 : ℂ) =
      star (deningerMeyerStrongLogMellin g (q.1 : ℂ)) := by
    rw [deningerMeyerSourceSharp_mellin, href]
  simp only [RCLike.inner_apply, hsharp]
  change y q * star (star (deningerMeyerStrongLogMellin g (q.1 : ℂ)) * x q) =
    (deningerMeyerStrongLogMellin g (q.1 : ℂ) * y q) * star (x q)
  rw [star_mul, star_star]
  ring

/-- The exact adjoint criterion includes simplicity in addition to ordinary trace positivity. -/
theorem meyerHilbertConvolution_sharp_eq_adjoint_iff :
    (∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
        ContinuousLinearMap.adjoint (deningerMeyerHilbertConvolution g)) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro hadj
    exact meyerSource_sharp_square_root_boundary_iff.mp
      (meyerHilbertConvolution_adjoint_forces_sharp_roots hadj)
  · rintro ⟨hRH, hs⟩
    exact meyerHilbertConvolution_sharp_eq_adjoint_of_simple_critical hRH hs

/-- Adjoint compatibility and existence of any faithful positive linear degree are equivalent. -/
theorem meyerHilbertConvolution_adjoint_iff_faithful_positive_degree :
    (∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerHilbertConvolution (deningerMeyerSourceSharp g) =
        ContinuousLinearMap.adjoint (deningerMeyerHilbertConvolution g)) ↔
    (∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      ∀ g : DeningerMeyerStrongLogTarget,
        g ∉ LinearMap.range deningerMeyerStrongLogSumLM →
        0 < (d (Submodule.Quotient.mk
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) :=
  meyerHilbertConvolution_sharp_eq_adjoint_iff.trans
    exists_faithful_positive_meyer_degree_iff.symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
