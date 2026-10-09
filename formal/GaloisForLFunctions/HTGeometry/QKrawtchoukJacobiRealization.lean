import GaloisForLFunctions.HTGeometry.QKrawtchoukSpectralBasis
import GaloisForLFunctions.HTGeometry.MaximalMultiplicationSelfAdjoint
import GaloisForLFunctions.HTGeometry.LinearPMapBoundedUnitaryTransport

/-!
# The selected inverse-q Hermite Jacobi operator

The maximal multiplication operator of the selected measure is transported
to ℓ² using the actual polynomial Hilbert basis. The resulting operator is
self-adjoint on its exact transported domain and acts on the coordinate
vectors by the Jacobi coefficients of arXiv:2609.24149, Proposition 3.1.
All positivity, measure existence, and polynomial completeness inputs have
already been discharged for this concrete family.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap
open GaloisForLFunctions.HTGeometry
  (maximalMul maximalMulDomain maximalMul_coeFn maximalMul_isSelfAdjoint
   unitaryConjugateLinearPMap unitaryConjugateLinearPMap_apply)

namespace HTGeometry

/-- The positive Jacobi off-diagonal, with the degree-zero endpoint equal to zero. -/
def inverseQHermiteOffDiagonal (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.exp (Real.exp t * n) - 1)

private theorem norm_ratio (t u : ℝ) (n : ℕ) :
    monicOrthoNorm (inverseQHermiteMoment t u) (n + 1) /
      monicOrthoNorm (inverseQHermiteMoment t u) n =
      inverseQHermiteOffDiagonal t (n + 1) := by
  rw [inverseQHermiteOffDiagonal, Nat.cast_add, Nat.cast_one, ← inverseQHermiteMoment_beta t u n,
    monicOrthoBeta, Real.sqrt_div (monicOrthoNormSq_pos
      (inverseQHermiteMoment_positive t u) (n + 1)).le]
  rfl

private theorem lower_norm_ratio (t u : ℝ) (n : ℕ) :
    monicOrthoBeta (inverseQHermiteMoment t u) n *
        monicOrthoNorm (inverseQHermiteMoment t u) (n - 1) /
        monicOrthoNorm (inverseQHermiteMoment t u) n = inverseQHermiteOffDiagonal t n := by
  cases n with
  | zero => simp [monicOrthoBeta, inverseQHermiteOffDiagonal]
  | succ n =>
      rw [← norm_ratio t u n]
      simp only [Nat.add_sub_cancel, monicOrthoBeta,
        monicOrthoNormSq, ← monicOrthoNorm_sq (inverseQHermiteMoment_positive t u)]
      field_simp [monicOrthoNorm_ne_zero (inverseQHermiteMoment_positive t u)]

private theorem normalized_recurrence {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    Polynomial.X * orthonormalPoly s n =
      (monicOrthoNorm s (n + 1) / monicOrthoNorm s n) • orthonormalPoly s (n + 1) +
      monicOrthoAlpha s n • orthonormalPoly s n +
      (monicOrthoBeta s n * monicOrthoNorm s (n - 1) / monicOrthoNorm s n) •
        orthonormalPoly s (n - 1) := by
  have hu : (monicOrthoNorm s (n + 1) / monicOrthoNorm s n) *
      (monicOrthoNorm s (n + 1))⁻¹ = (monicOrthoNorm s n)⁻¹ := by
    field_simp [monicOrthoNorm_ne_zero h]
  have hl : (monicOrthoBeta s n * monicOrthoNorm s (n - 1) / monicOrthoNorm s n) *
      (monicOrthoNorm s (n - 1))⁻¹ = (monicOrthoNorm s n)⁻¹ * monicOrthoBeta s n := by
    field_simp [monicOrthoNorm_ne_zero h]
  simp only [orthonormalPoly, mul_smul_comm, X_mul_monicOrtho h, smul_add,
    smul_smul, hu, hl]
  rw [mul_comm (monicOrthoAlpha s n)]

/-- The normalized family has precisely the limiting Jacobi recurrence. -/
theorem inverseQHermiteOrthonormalPoly_recurrence (t u : ℝ) (n : ℕ) :
    Polynomial.X * orthonormalPoly (inverseQHermiteMoment t u) n =
      inverseQHermiteOffDiagonal t (n + 1) •
        orthonormalPoly (inverseQHermiteMoment t u) (n + 1) +
      (Real.exp (-u) - Real.exp u) • orthonormalPoly (inverseQHermiteMoment t u) n +
      inverseQHermiteOffDiagonal t n • orthonormalPoly (inverseQHermiteMoment t u) (n - 1) := by
  simpa only [norm_ratio, lower_norm_ratio, inverseQHermiteMoment_alpha] using
    normalized_recurrence (inverseQHermiteMoment_positive t u) n

/-- The selected self-adjoint extension on the common sequence space. -/
def inverseQHermiteJacobi (t u x : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  unitaryConjugateLinearPMap (inverseQHermiteSpectralBasis t u x).repr.symm
    (maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id)

/-- Self-adjointness holds for every actual selected leaf. -/
theorem inverseQHermiteJacobi_isSelfAdjoint (t u x : ℝ) :
    IsSelfAdjoint (inverseQHermiteJacobi t u x) :=
  GaloisForLFunctions.HTGeometry.IsSelfAdjoint.unitaryConjugate _
    (maximalMul_isSelfAdjoint measurable_id)

private theorem polynomialLp_ae (t u x : ℝ) (p : Polynomial ℝ) :
    (fun y => inverseQHermitePolynomialLp t u x p y)
      =ᵐ[(inverseQHermiteAtomMeasure t u x : Measure ℝ)]
        fun y => ((p.eval y : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

private theorem polynomialLp_add (t u x : ℝ) (p q : Polynomial ℝ) :
    inverseQHermitePolynomialLp t u x (p + q) =
      inverseQHermitePolynomialLp t u x p + inverseQHermitePolynomialLp t u x q := by
  apply Lp.ext
  filter_upwards [polynomialLp_ae t u x (p + q), polynomialLp_ae t u x p,
    polynomialLp_ae t u x q, Lp.coeFn_add (inverseQHermitePolynomialLp t u x p)
      (inverseQHermitePolynomialLp t u x q)] with y hpq hp hq hadd
  simp only [hpq, hadd, Pi.add_apply, hp, hq, Polynomial.eval_add, Complex.ofReal_add]

private theorem polynomialLp_smul (t u x c : ℝ) (p : Polynomial ℝ) :
    inverseQHermitePolynomialLp t u x (c • p) =
      (c : ℂ) • inverseQHermitePolynomialLp t u x p := by
  apply Lp.ext
  filter_upwards [polynomialLp_ae t u x (c • p), polynomialLp_ae t u x p,
    Lp.coeFn_smul (c : ℂ) (inverseQHermitePolynomialLp t u x p)] with y hcp hp hsmul
  simp only [hcp, hsmul, Pi.smul_apply, hp, Polynomial.eval_smul,
    smul_eq_mul, Complex.ofReal_mul]

private theorem polynomialLp_mem_domain (t u x : ℝ) (p : Polynomial ℝ) :
    inverseQHermitePolynomialLp t u x p ∈
      (maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id).domain := by
  change MemLp _ 2 _
  refine (Lp.memLp (inverseQHermitePolynomialLp t u x (Polynomial.X * p))).ae_eq ?_
  filter_upwards [polynomialLp_ae t u x (Polynomial.X * p), polynomialLp_ae t u x p]
    with y hxp hp
  simp only [hxp, hp, Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul, id_eq]

private theorem maximalMul_polynomialLp (t u x : ℝ) (p : Polynomial ℝ) :
    maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id
      ⟨inverseQHermitePolynomialLp t u x p, polynomialLp_mem_domain t u x p⟩ =
      inverseQHermitePolynomialLp t u x (Polynomial.X * p) := by
  apply Lp.ext
  filter_upwards [maximalMul_coeFn id
      ⟨inverseQHermitePolynomialLp t u x p, polynomialLp_mem_domain t u x p⟩,
    polynomialLp_ae t u x p, polynomialLp_ae t u x (Polynomial.X * p)] with y hm hp hxp
  simp only [hm, hp, hxp, Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_mul, id_eq]

/-- Every standard coordinate vector belongs to the selected operator domain. -/
theorem inverseQHermiteJacobi_single_mem_domain (t u x : ℝ) (n : ℕ) :
    lp.single 2 n (1 : ℂ) ∈ (inverseQHermiteJacobi t u x).domain := by
  change (inverseQHermiteSpectralBasis t u x).repr.symm (lp.single 2 n (1 : ℂ)) ∈
    (maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id).domain
  rw [HilbertBasis.repr_symm_single, inverseQHermiteSpectralBasis_apply]
  exact polynomialLp_mem_domain t u x _

/-- The transported self-adjoint operator realizes the paper's tridiagonal
matrix on every coordinate vector, including the zero endpoint. -/
theorem inverseQHermiteJacobi_single (t u x : ℝ) (n : ℕ) :
    inverseQHermiteJacobi t u x
      ⟨lp.single 2 n (1 : ℂ), inverseQHermiteJacobi_single_mem_domain t u x n⟩ =
      (inverseQHermiteOffDiagonal t (n + 1) : ℂ) • lp.single 2 (n + 1) (1 : ℂ) +
      ((Real.exp (-u) - Real.exp u : ℝ) : ℂ) • lp.single 2 n (1 : ℂ) +
      (inverseQHermiteOffDiagonal t n : ℂ) • lp.single 2 (n - 1) (1 : ℂ) := by
  let B := inverseQHermiteSpectralBasis t u x
  have harg : GaloisForLFunctions.HTGeometry.unitaryConjugateDomainMap B.repr.symm
      (maximalMul (inverseQHermiteAtomMeasure t u x : Measure ℝ) id)
      ⟨lp.single 2 n (1 : ℂ), inverseQHermiteJacobi_single_mem_domain t u x n⟩ =
      ⟨inverseQHermitePolynomialLp t u x (orthonormalPoly (inverseQHermiteMoment t u) n),
        polynomialLp_mem_domain t u x _⟩ := by
    apply Subtype.ext
    exact (B.repr_symm_single n).trans (inverseQHermiteSpectralBasis_apply t u x n)
  change B.repr (maximalMul _ id _) = _
  erw [harg, maximalMul_polynomialLp]
  rw [inverseQHermiteOrthonormalPoly_recurrence,
    polynomialLp_add, polynomialLp_add, polynomialLp_smul, polynomialLp_smul, polynomialLp_smul]
  simp only [map_add, map_smul]
  have hb (k : ℕ) : B.repr (inverseQHermitePolynomialLp t u x
      (orthonormalPoly (inverseQHermiteMoment t u) k)) = lp.single 2 k (1 : ℂ) := by
    change B.repr (inverseQHermiteOrthonormalLp t u x k) = _
    rw [← inverseQHermiteSpectralBasis_apply t u x k]
    exact B.repr_self k
  rw [hb, hb, hb]

end HTGeometry
