import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerSourceIntersectionSurface
import GaloisForLFunctions.RHTower.XiRealCriticalPointSignLaw

/-!
# Positive linear cohomological degrees can forget nonprincipal sources

Evaluation at a critical Xi point is a genuine linear degree nonnegative on every
arithmetic sharp square. Hardy's theorem supplies such a point unconditionally. Its
conjugate point supplies a nonprincipal source of square degree zero, so this degree
cannot replace faithful ordinary intersection data.
-/

noncomputable section
open Complex Zeta23 RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Zeroth Mellin evaluation is a linear degree on the actual Poisson quotient. -/
def meyerPointDegree (rho : XiDivisorSupport) : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerMeyerXiSupportJetEvaluationLM rho ⟨0, xiSupportMultiplicity_pos rho⟩

@[simp] theorem meyerPointDegree_mk (rho : XiDivisorSupport) (g : DeningerMeyerStrongLogTarget) :
    meyerPointDegree rho (Submodule.Quotient.mk g) = deningerMeyerStrongLogMellin g (rho : ℂ) := rfl

/-- Value evaluation is multiplicative on the genuine Poisson quotient. -/
theorem meyerPointDegree_product (rho : XiDivisorSupport)
    (u v : DeningerMeyerStrongLogCohomology) :
    meyerPointDegree rho (deningerMeyerCohomologyConvolution u v) =
      meyerPointDegree rho u * meyerPointDegree rho v := by
  induction u using Submodule.Quotient.induction_on with
  | H g =>
    induction v using Submodule.Quotient.induction_on with
    | H h =>
      rw [deningerMeyerCohomologyConvolution_mk, meyerPointDegree_mk,
        meyerPointDegree_mk, meyerPointDegree_mk, deningerMeyerSourceConvolution_mellin]

/-- A critical point reads an exact Mellin square, without requiring all zeros to be critical. -/
theorem meyerPointDegree_sharp_square (rho : XiDivisorSupport) (hr : (rho : ℂ).re = 1 / 2)
    (g : DeningerMeyerStrongLogTarget) :
    meyerPointDegree rho (Submodule.Quotient.mk
      (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))) =
        (Complex.normSq (deningerMeyerStrongLogMellin g (rho : ℂ)) : ℂ) := by
  have href : star (1 - (rho : ℂ)) = (rho : ℂ) := by
    apply Complex.ext
    · change 1 - (rho : ℂ).re = (rho : ℂ).re
      rw [hr]
      norm_num
    · change -(0 - (rho : ℂ).im) = (rho : ℂ).im
      ring
  rw [meyerPointDegree_mk, deningerMeyerSourceConvolution_mellin,
    deningerMeyerSourceSharp_mellin, href]
  exact Complex.mul_conj _

/-- Hardy's critical point gives a positive linear degree with an explicit nonprincipal null source. -/
theorem exists_positive_meyer_degree_with_nonprincipal_null_source :
    ∃ d : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ,
      (∀ g : DeningerMeyerStrongLogTarget,
        0 ≤ (d (Submodule.Quotient.mk
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ∧
      (∃ g : DeningerMeyerStrongLogTarget,
        d (Submodule.Quotient.mk
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))) = 1) ∧
      (∃ g : DeningerMeyerStrongLogTarget,
        g ∉ LinearMap.range deningerMeyerStrongLogSumLM ∧
        d (Submodule.Quotient.mk
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))) = 0) := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_eq_half
  let rho : XiDivisorSupport := q.1
  have hr : (rho : ℂ).re = 1 / 2 := hq
  let sigma : XiDivisorSupport := xiZeroConjEquiv rho
  have hne : rho ≠ sigma := by
    intro he
    have him := congrArg (fun z : XiDivisorSupport => (z : ℂ).im) he
    change (rho : ℂ).im = -(rho : ℂ).im at him
    have hrho : (rho : ℂ) = 1 / 2 := by
      apply Complex.ext
      · simpa using hr
      · change (rho : ℂ).im = 0
        linarith only [him]
    exact xi_divisor_support_ne_half rho hrho
  refine ⟨meyerPointDegree rho, ?_, ?_, ?_⟩
  · intro g
    rw [meyerPointDegree_sharp_square rho hr, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · refine ⟨meyerPointSource rho, ?_⟩
    rw [meyerPointDegree_sharp_square rho hr, meyerPointSource_values, if_pos rfl]
    norm_num
  · refine ⟨meyerPointSource sigma, ?_, ?_⟩
    · intro hg
      have hz := (meyerSource_boundary_iff_jets_zero _).mp hg sigma
        ⟨0, xiSupportMultiplicity_pos sigma⟩
      change deningerMeyerStrongLogMellin (meyerPointSource sigma) (sigma : ℂ) = 0 at hz
      rw [meyerPointSource_values, if_pos rfl] at hz
      exact one_ne_zero hz
    · rw [meyerPointDegree_sharp_square rho hr, meyerPointSource_values, if_neg hne]
      simp only [Complex.normSq_zero, Complex.ofReal_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPointDegree_mk
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPointDegree_sharp_square
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_positive_meyer_degree_with_nonprincipal_null_source

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerPointDegree_product
