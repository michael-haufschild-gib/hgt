import GaloisForLFunctions.HTGeometry.QKrawtchoukJacobiRealization
import GaloisForLFunctions.HTGeometry.QKrawtchoukPolynomialResolventLimit

/-!
# The actual selected Jacobi resolvent

For every upper-half-plane parameter, the selected inverse-q Hermite Jacobi
operator has a concrete bounded two-sided resolvent. Its coordinate matrix
elements are the polynomial Cauchy integrals appearing in arXiv:2609.24149,
Theorem 6.1. This identifies the limits of the pinned quadrature integrals
with entries of the actual operator resolvent.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators LinearPMap Topology
open GaloisForLFunctions.HTGeometry
  (maximalMul maximalMulDomain mulResolvent mulResolvent_mem_domain
   maximalMul_mulResolvent mulResolvent_maximalMul mulResolvent_coeFn
   norm_resolventSymbol_le resolventSymbol unitaryConjugateDomainMap)

namespace HTGeometry

private theorem spectral_gap (a b y : ℝ) :
    Real.exp b ≤ ‖(y : ℂ) - Complex.mk a (Real.exp b)‖ := by
  have h := Complex.abs_im_le_norm ((y : ℂ) - Complex.mk a (Real.exp b))
  simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
    abs_of_pos (Real.exp_pos b)] using h

/-- The actual bounded resolvent, transported from the selected measure space. -/
def inverseQHermiteResolvent (t u x a b : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (inverseQHermiteSpectralBasis t u x).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((mulResolvent (μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ)) measurable_id
      (Complex.mk a (Real.exp b)) (Real.exp_pos b)).comp
      (inverseQHermiteSpectralBasis t u x).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem resolvent_apply (t u x a b : ℝ) (f : lp (fun _ : ℕ => ℂ) 2) :
    inverseQHermiteResolvent t u x a b f = (inverseQHermiteSpectralBasis t u x).repr
      (mulResolvent measurable_id (Complex.mk a (Real.exp b)) (Real.exp_pos b)
        ((inverseQHermiteSpectralBasis t u x).repr.symm f)) := rfl

/-- The resolvent sends every sequence into the exact self-adjoint domain. -/
theorem inverseQHermiteResolvent_mem_domain (t u x a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    inverseQHermiteResolvent t u x a b f ∈ (inverseQHermiteJacobi t u x).domain := by
  change (inverseQHermiteSpectralBasis t u x).repr.symm
    (inverseQHermiteResolvent t u x a b f) ∈
      (maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id).domain
  rw [resolvent_apply, LinearIsometryEquiv.symm_apply_apply]
  exact mulResolvent_mem_domain measurable_id _ (Real.exp_pos b) _

/-- `(J-z)R(z)` is identity on the whole sequence space. -/
theorem inverseQHermiteJacobi_resolvent (t u x a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    inverseQHermiteJacobi t u x
      ⟨inverseQHermiteResolvent t u x a b f, inverseQHermiteResolvent_mem_domain t u x a b f⟩ -
        Complex.mk a (Real.exp b) • inverseQHermiteResolvent t u x a b f = f := by
  let B := inverseQHermiteSpectralBasis t u x
  let μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ)
  let w : (maximalMul μ id).domain :=
    ⟨mulResolvent measurable_id (Complex.mk a (Real.exp b)) (Real.exp_pos b) (B.repr.symm f),
      mulResolvent_mem_domain measurable_id _ (Real.exp_pos b) _⟩
  have harg : unitaryConjugateDomainMap B.repr.symm (maximalMul μ id)
      ⟨inverseQHermiteResolvent t u x a b f, inverseQHermiteResolvent_mem_domain t u x a b f⟩ = w := by
    apply Subtype.ext
    exact B.repr.symm_apply_apply _
  change B.repr (maximalMul μ id _) - _ = _
  erw [harg]
  have h := congrArg B.repr (maximalMul_mulResolvent (μ := μ) measurable_id
    (Real.exp_pos b) (ae_of_all μ (spectral_gap a b)) (B.repr.symm f))
  simpa only [w, resolvent_apply, map_sub, map_smul,
    LinearIsometryEquiv.apply_symm_apply, B, μ] using h

/-- `R(z)(J-z)` is identity on the full self-adjoint domain. -/
theorem inverseQHermiteResolvent_jacobi (t u x a b : ℝ)
    (f : (inverseQHermiteJacobi t u x).domain) :
    inverseQHermiteResolvent t u x a b
      (inverseQHermiteJacobi t u x f - Complex.mk a (Real.exp b) •
        (f : lp (fun _ : ℕ => ℂ) 2)) = f := by
  let B := inverseQHermiteSpectralBasis t u x
  let μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ)
  let g := unitaryConjugateDomainMap B.repr.symm (maximalMul μ id) f
  have h := mulResolvent_maximalMul (μ := μ) measurable_id (Real.exp_pos b)
    (ae_of_all μ (spectral_gap a b)) g
  rw [resolvent_apply]
  change B.repr (mulResolvent measurable_id _ (Real.exp_pos b)
    (B.repr.symm (B.repr (maximalMul μ id g) - _))) = _
  rw [map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]
  change B.repr (mulResolvent measurable_id _ (Real.exp_pos b)
    (maximalMul μ id g - Complex.mk a (Real.exp b) • (g : Lp ℂ 2 μ))) = _
  rw [h]
  exact B.repr.apply_symm_apply _

/-- The resolvent bound is the reciprocal distance from the real axis. -/
theorem inverseQHermiteResolvent_norm_le (t u x a b : ℝ) :
    ‖inverseQHermiteResolvent t u x a b‖ ≤ Real.exp (-b) := by
  let B := inverseQHermiteSpectralBasis t u x
  let μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ)
  let R := mulResolvent (μ := μ) measurable_id (Complex.mk a (Real.exp b)) (Real.exp_pos b)
  have hn : ‖R‖ ≤ (Real.exp b)⁻¹ :=
    norm_le_of_ae_mul (by positivity)
      (norm_resolventSymbol_le id _ (Real.exp_pos b))
      (mulResolvent_coeFn measurable_id _ (Real.exp_pos b))
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos (-b)).le
  intro f
  calc
    ‖inverseQHermiteResolvent t u x a b f‖ = ‖R (B.repr.symm f)‖ := by
      rw [resolvent_apply, LinearIsometryEquiv.norm_map]
    _ ≤ ‖R‖ * ‖B.repr.symm f‖ := R.le_opNorm _
    _ ≤ (Real.exp b)⁻¹ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right hn (norm_nonneg f)
    _ = Real.exp (-b) * ‖f‖ := by rw [Real.exp_neg]

private theorem basis_ae (t u x : ℝ) (n : ℕ) :
    (fun y => inverseQHermiteSpectralBasis t u x n y)
      =ᵐ[(inverseQHermiteAtomMeasure t u x : Measure ℝ)]
        fun y => (((orthonormalPoly (inverseQHermiteMoment t u) n).eval y : ℝ) : ℂ) := by
  rw [inverseQHermiteSpectralBasis_apply]
  unfold inverseQHermiteOrthonormalLp inverseQHermitePolynomialLp
  exact MemLp.coeFn_toLp _

/-- Every resolvent matrix element is the actual polynomial Cauchy integral. -/
theorem inverseQHermiteResolvent_matrixElement (t u x a b : ℝ) (i j : ℕ) :
    inner ℂ (lp.single 2 i (1 : ℂ))
      (inverseQHermiteResolvent t u x a b (lp.single 2 j (1 : ℂ))) =
      ∫ y, (((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
        (orthonormalPoly (inverseQHermiteMoment t u) j).eval y : ℝ) : ℂ) *
          ((y : ℂ) - Complex.mk a (Real.exp b))⁻¹
        ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ) := by
  let B := inverseQHermiteSpectralBasis t u x
  rw [resolvent_apply, HilbertBasis.repr_symm_single]
  rw [← B.repr_self i, B.repr.inner_map_map, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [basis_ae t u x i, basis_ae t u x j,
    mulResolvent_coeFn (μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ))
      measurable_id (Complex.mk a (Real.exp b)) (Real.exp_pos b) (B j)] with y hi hj hr
  rw [hr, hi, hj, resolventSymbol]
  simp only [id_eq, if_pos (spectral_gap a b y), RCLike.inner_apply,
    Complex.conj_ofReal, Complex.ofReal_mul]
  ring

/-- Pinned finite quadrature entries converge to the selected Jacobi resolvent. -/
theorem inverseQHermitePinnedQuadrature_resolventEntry_tendsto
    (t u x r a b : ℝ) (i j : ℕ) :
    Tendsto (fun n : ℕ =>
      ∫ y, (((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
        (orthonormalPoly (inverseQHermiteMoment t u) j).eval y : ℝ) : ℂ) *
          ((y : ℂ) - Complex.mk a (Real.exp b))⁻¹
        ∂(inverseQHermitePinnedQuadrature t u (x + r / ((n : ℝ) + 1)) n : Measure ℝ))
      atTop (𝓝 (inner ℂ (lp.single 2 i (1 : ℂ))
        (inverseQHermiteResolvent t u x a b (lp.single 2 j (1 : ℂ))))) := by
  rw [inverseQHermiteResolvent_matrixElement]
  let P := (orthonormalPoly (inverseQHermiteMoment t u) i) *
    (orthonormalPoly (inverseQHermiteMoment t u) j)
  have heval (y : ℝ) : (P.map Complex.ofRealHom).eval (y : ℂ) =
      (((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
        (orthonormalPoly (inverseQHermiteMoment t u) j).eval y : ℝ) : ℂ) := by
    simpa only [P, Polynomial.eval_mul, Complex.ofRealHom_eq_coe] using
      (Polynomial.eval_map_apply Complex.ofRealHom (p := P) y)
  have h := inverseQHermitePinnedQuadrature_polynomialCauchy_tendsto t u x r a b
    (P.map Complex.ofRealHom)
  simpa only [heval] using h

end HTGeometry
