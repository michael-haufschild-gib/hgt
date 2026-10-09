import GaloisForLFunctions.HTGeometry.QKrawtchoukPolynomialCompleteness
import GaloisForLFunctions.HTGeometry.OrthonormalMomentPolynomials
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The actual inverse-q Hermite spectral basis

The selected measure is now identified with the common sequence space used
in arXiv:2609.24149. Its normalized orthogonal polynomials form a complex
Hilbert basis, with no completeness premise. The basis's `repr` field is
the resulting unitary map to ℓ². This supplies the coordinate identification
needed to turn multiplication by the spectral variable into a Jacobi operator.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

namespace HTGeometry

private theorem polynomial_memLp (t u x : ℝ) (p : Polynomial ℝ) :
    MemLp (fun y : ℝ => ((p.eval y : ℝ) : ℂ)) 2
      (inverseQHermiteAtomMeasure t u x : Measure ℝ) := by
  have hm := inverseQHermiteAtomMeasure_moments t u x
  have hsq : Integrable (fun y => (p.eval y) ^ 2)
      (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
    (integrable_eval (fun k => (hm k).1) (p ^ (2 : ℕ))).congr
      (ae_of_all _ fun _ => Polynomial.eval_pow 2)
  exact ((memLp_two_iff_integrable_sq (by fun_prop)).mpr hsq).ofReal

/-- Evaluate a real polynomial in the selected complex L² space. -/
def inverseQHermitePolynomialLp (t u x : ℝ) (p : Polynomial ℝ) :
    Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
  (polynomial_memLp t u x p).toLp (fun y : ℝ => ((p.eval y : ℝ) : ℂ))

private theorem polynomialLp_ae (t u x : ℝ) (p : Polynomial ℝ) :
    (fun y => inverseQHermitePolynomialLp t u x p y)
      =ᵐ[(inverseQHermiteAtomMeasure t u x : Measure ℝ)] fun y => ((p.eval y : ℝ) : ℂ) :=
  MemLp.coeFn_toLp (polynomial_memLp t u x p)

private theorem polynomial_mul_integrable (t u x : ℝ)
    (g : Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) (p : Polynomial ℝ) :
    Integrable (fun y => ((p.eval y : ℝ) : ℂ) * g y)
      (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
  memLp_one_iff_integrable.mp ((Lp.memLp g).mul' (polynomial_memLp t u x p))

private def polynomialMomentMap (t u x : ℝ)
    (g : Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :
    Polynomial ℝ →ₗ[ℝ] ℂ where
  toFun p := ∫ y, ((p.eval y : ℝ) : ℂ) * g y ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ)
  map_add' p q := by
    change (∫ y, (((p + q).eval y : ℝ) : ℂ) * g y ∂_) = _
    rw [← integral_add (polynomial_mul_integrable t u x g p)
      (polynomial_mul_integrable t u x g q)]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by simp only [Polynomial.eval_add, Complex.ofReal_add, add_mul]
  map_smul' c p := by
    change (∫ y, (((c • p).eval y : ℝ) : ℂ) * g y ∂_) =
      c • (∫ y, ((p.eval y : ℝ) : ℂ) * g y ∂_)
    rw [← integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      simp only [Polynomial.eval_smul, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
      ring

private theorem inner_polynomialLp_left (t u x : ℝ) (p : Polynomial ℝ)
    (g : Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :
    inner ℂ (inverseQHermitePolynomialLp t u x p) g = polynomialMomentMap t u x g p := by
  rw [L2.inner_def]
  change (∫ y, inner ℂ (inverseQHermitePolynomialLp t u x p y) (g y) ∂_) = _
  apply integral_congr_ae
  filter_upwards [polynomialLp_ae t u x p] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

/-- The L² realization preserves the actual Hankel inner product. -/
theorem inverseQHermitePolynomialLp_inner (t u x : ℝ) (p q : Polynomial ℝ) :
    inner ℂ (inverseQHermitePolynomialLp t u x p) (inverseQHermitePolynomialLp t u x q) =
      (momentInner (inverseQHermiteMoment t u) p q : ℂ) := by
  rw [inner_polynomialLp_left]
  change (∫ y, ((p.eval y : ℝ) : ℂ) * inverseQHermitePolynomialLp t u x q y ∂_) = _
  have heq : (fun y => ((p.eval y : ℝ) : ℂ) * inverseQHermitePolynomialLp t u x q y)
      =ᵐ[(inverseQHermiteAtomMeasure t u x : Measure ℝ)] fun y => ((p.eval y * q.eval y : ℝ) : ℂ) := by
    filter_upwards [polynomialLp_ae t u x q] with y hy
    rw [hy, Complex.ofReal_mul]
  rw [integral_congr_ae heq, integral_complex_ofReal]
  congr 1
  have hm := inverseQHermiteAtomMeasure_moments t u x
  simpa only [momentInner_def] using
    (momentFunctional_mul_eq_integral (inverseQHermiteMoment t u)
      (fun k => (hm k).2.symm) (fun k => (hm k).1) p q).symm

/-- Complex polynomial moments also separate every L² vector. -/
theorem inverseQHermiteAtomMeasure_complexL2_moments_zero_iff (t u x : ℝ)
    (g : Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :
    (∀ n : ℕ, ∫ y, ((y ^ n : ℝ) : ℂ) * g y
      ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ) = 0) ↔ g = 0 := by
  constructor
  · intro hz
    let μ := (inverseQHermiteAtomMeasure t u x : Measure ℝ)
    have hR : MemLp (fun y => (g y).re) 2 μ := (Lp.memLp g).re
    have hI : MemLp (fun y => (g y).im) 2 μ := (Lp.memLp g).im
    let gR := hR.toLp (fun y => (g y).re)
    let gI := hI.toLp (fun y => (g y).im)
    have hint (n : ℕ) : Integrable (fun y => ((y ^ n : ℝ) : ℂ) * g y) μ := by
      simpa using polynomial_mul_integrable t u x g (Polynomial.X ^ n)
    have hRzero : gR = 0 := by
      apply (inverseQHermiteAtomMeasure_L2_moments_zero_iff t u x gR).mp
      intro n
      have heq : (fun y => y ^ n * gR y) =ᵐ[μ] fun y => y ^ n * (g y).re := by
        filter_upwards [MemLp.coeFn_toLp hR] with y hy
        exact congrArg (fun z => y ^ n * z) hy
      rw [integral_congr_ae heq]
      have hc := Complex.reCLM.integral_comp_comm (hint n)
      simp only [Complex.reCLM_apply, Complex.re_ofReal_mul] at hc
      rw [show (∫ y, ((y ^ n : ℝ) : ℂ) * g y ∂μ) = 0 from hz n] at hc
      exact hc
    have hIzero : gI = 0 := by
      apply (inverseQHermiteAtomMeasure_L2_moments_zero_iff t u x gI).mp
      intro n
      have heq : (fun y => y ^ n * gI y) =ᵐ[μ] fun y => y ^ n * (g y).im := by
        filter_upwards [MemLp.coeFn_toLp hI] with y hy
        exact congrArg (fun z => y ^ n * z) hy
      rw [integral_congr_ae heq]
      have hc := Complex.imCLM.integral_comp_comm (hint n)
      simp only [Complex.imCLM_apply, Complex.im_ofReal_mul] at hc
      rw [show (∫ y, ((y ^ n : ℝ) : ℂ) * g y ∂μ) = 0 from hz n] at hc
      exact hc
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp hR, MemLp.coeFn_toLp hI,
      Lp.coeFn_zero ℝ 2 μ, Lp.coeFn_zero ℂ 2 μ] with y hyR hyI h0R h0C
    change gR y = (g y).re at hyR
    change gI y = (g y).im at hyI
    rw [hRzero, h0R] at hyR
    rw [hIzero, h0R] at hyI
    rw [h0C]
    apply Complex.ext
    · exact hyR.symm
    · exact hyI.symm
  · rintro rfl n
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2
      (inverseQHermiteAtomMeasure t u x : Measure ℝ)] with y hy
    change ((y ^ n : ℝ) : ℂ) * (0 : Lp ℂ 2 _) y = 0
    simp only [hy, Pi.zero_apply, mul_zero]

/-- The normalized recurrence polynomials, realized as L² vectors. -/
def inverseQHermiteOrthonormalLp (t u x : ℝ) (n : ℕ) :
    Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
  inverseQHermitePolynomialLp t u x (orthonormalPoly (inverseQHermiteMoment t u) n)

theorem inverseQHermiteOrthonormalLp_orthonormal (t u x : ℝ) :
    Orthonormal ℂ (inverseQHermiteOrthonormalLp t u x) := by
  rw [orthonormal_iff_ite]
  intro m n
  change inner ℂ (inverseQHermitePolynomialLp t u x _) (inverseQHermitePolynomialLp t u x _) = _
  rw [inverseQHermitePolynomialLp_inner,
    orthonormalPoly_inner (inverseQHermiteMoment_positive t u)]
  split_ifs <;> rfl

private theorem orthonormalLp_orthogonal_eq_bot (t u x : ℝ) :
    (Submodule.span ℂ (Set.range (inverseQHermiteOrthonormalLp t u x)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  let h := inverseQHermiteMoment_positive t u
  let Φ := polynomialMomentMap t u x g
  have hp (n : ℕ) : Φ (orthonormalPoly (inverseQHermiteMoment t u) n) = 0 := by
    have hn := hg (inverseQHermiteOrthonormalLp t u x n)
      (Submodule.subset_span (Set.mem_range_self n))
    exact (inner_polynomialLp_left t u x _ g).symm.trans hn
  have hq (n : ℕ) : Φ (monicOrtho (inverseQHermiteMoment t u) n) = 0 := by
    have heq : monicOrtho (inverseQHermiteMoment t u) n =
        monicOrthoNorm (inverseQHermiteMoment t u) n •
          orthonormalPoly (inverseQHermiteMoment t u) n := by
      rw [orthonormalPoly, smul_smul, mul_inv_cancel₀ (monicOrthoNorm_ne_zero h n), one_smul]
    rw [heq, map_smul, hp, smul_zero]
  have hall (p : Polynomial ℝ) : Φ p = 0 := by
    have hdeg : p.degree < ((p.natDegree + 1 : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self _)
    rw [monicOrtho_expansion h (p.natDegree + 1) p hdeg, map_sum]
    simp only [map_smul, hq, smul_zero, Finset.sum_const_zero]
  apply (inverseQHermiteAtomMeasure_complexL2_moments_zero_iff t u x g).mp
  intro n
  simpa [Φ, polynomialMomentMap] using hall (Polynomial.X ^ n)

/-- The actual complex spectral Hilbert basis. Its `repr` is a unitary
identification of the selected measure space with ℓ²(ℕ,ℂ). -/
def inverseQHermiteSpectralBasis (t u x : ℝ) :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :=
  HilbertBasis.mkOfOrthogonalEqBot (inverseQHermiteOrthonormalLp_orthonormal t u x)
    (orthonormalLp_orthogonal_eq_bot t u x)

/-- The constructed basis consists exactly of the recurrence polynomials. -/
theorem inverseQHermiteSpectralBasis_apply (t u x : ℝ) (n : ℕ) :
    inverseQHermiteSpectralBasis t u x n = inverseQHermiteOrthonormalLp t u x n := by
  rw [inverseQHermiteSpectralBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]

end HTGeometry
