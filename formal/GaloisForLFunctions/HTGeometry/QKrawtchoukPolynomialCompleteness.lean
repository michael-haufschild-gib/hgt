import GaloisForLFunctions.HTGeometry.QKrawtchoukKernelApproximation
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Polynomial completeness for the selected inverse-q Hermite measure

The maximal-atom selection in arXiv:2609.24149 produces an actual spectral
realization only when polynomials are complete in the selected measure's
L² space. Here that conclusion follows from the proved atom approximations,
without assuming an N-extremality or polynomial-density theorem.

The denominator label is constant almost everywhere on each selected leaf.
Thus almost every point selects the same measure. At each such point the
normalized kernels approximate its atom indicator. Cauchy–Schwarz then
forces every polynomial annihilator to vanish almost everywhere.
-/

noncomputable section
open MeasureTheory Filter
open GaloisForLFunctions.HTGeometry (integrable_mul_of_sq_integrable sq_integral_mul_le)
open scoped BigOperators Topology

namespace HTGeometry

/-- Almost every atom on a selected leaf selects that same leaf again. -/
theorem inverseQHermiteAtomMeasure_ae_reselect (t u x : ℝ) :
    ∀ᵐ y ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ),
      inverseQHermiteAtomMeasure t u y = inverseQHermiteAtomMeasure t u x := by
  let F := inverseQHermiteNevanlinnaFamily t u
  have hc := F.matrix.toCarrierMatrix.continuous_projectiveLabel
    F.continuous_B F.continuous_D.neg
  rw [funext F.matrix.toCarrierMatrix_projectiveLabel] at hc
  have hpush := F.map_projectiveLabel_leaf (F.matrix.projectiveLabel x)
  have hae : ∀ᵐ y ∂(F.leaf (F.matrix.projectiveLabel x) : Measure ℝ),
      F.matrix.projectiveLabel y = F.matrix.projectiveLabel x := by
    apply ae_of_ae_map (μ := (F.leaf (F.matrix.projectiveLabel x) : Measure ℝ))
      (p := fun z => z = F.matrix.projectiveLabel x) hc.measurable.aemeasurable
    rw [hpush]
    simp
  filter_upwards [hae] with y hy
  change F.leaf (F.matrix.projectiveLabel y) = F.leaf (F.matrix.projectiveLabel x)
  rw [hy]

private theorem polynomial_sq_integrable {s : ℕ → ℝ} (μ : Measure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ) (p : Polynomial ℝ) :
    Integrable (fun y => (p.eval y) ^ 2) μ :=
  (integrable_eval (fun k => (hm k).1) (p ^ (2 : ℕ))).congr
    (ae_of_all _ fun _ => Polynomial.eval_pow 2)

private theorem polynomial_mul_integrable {s : ℕ → ℝ} (μ : Measure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ)
    (hf2 : Integrable (fun y => f y ^ 2) μ) (p : Polynomial ℝ) :
    Integrable (fun y => p.eval y * f y) μ :=
  integrable_mul_of_sq_integrable (by fun_prop) hf (polynomial_sq_integrable μ hm p) hf2

private theorem polynomial_annihilated {s : ℕ → ℝ} (μ : Measure ℝ)
    (hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments s μ)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f μ)
    (hf2 : Integrable (fun y => f y ^ 2) μ)
    (hz : ∀ k : ℕ, ∫ y, y ^ k * f y ∂μ = 0) (p : Polynomial ℝ) :
    ∫ y, p.eval y * f y ∂μ = 0 := by
  have hpow (k : ℕ) : Integrable (fun y => y ^ k * f y) μ := by
    simpa using polynomial_mul_integrable μ hm hf hf2 (Polynomial.X ^ k)
  have heq (y : ℝ) : p.eval y * f y =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (y ^ k * f y) := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  simp_rw [heq]
  rw [integral_finsetSum _ (fun k _ => (hpow k).const_mul _)]
  simp_rw [integral_const_mul, hz, mul_zero, Finset.sum_const_zero]

private theorem annihilator_at_selected_atom (t u x : ℝ) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (inverseQHermiteAtomMeasure t u x : Measure ℝ))
    (hf2 : Integrable (fun y => f y ^ 2) (inverseQHermiteAtomMeasure t u x : Measure ℝ))
    (hz : ∀ p : Polynomial ℝ,
      ∫ y, p.eval y * f y ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ) = 0) :
    f x = 0 := by
  let μ := inverseQHermiteAtomMeasure t u x
  let p := inverseQHermiteAtomProbe t u x
  let e := fun n y => ({x} : Set ℝ).indicator (fun _ => (1 : ℝ)) y - (p n).eval y
  have hm := inverseQHermiteAtomMeasure_moments t u x
  have hif : Integrable f (μ : Measure ℝ) := by
    have hi := integrable_mul_of_sq_integrable hf
      (f := f) (g := fun _ => (1 : ℝ)) (by fun_prop) hf2 (by simp)
    simpa only [mul_one] using hi
  have herr (n : ℕ) : AEStronglyMeasurable (e n) (μ : Measure ℝ) := by
    exact ((measurable_const.indicator (measurableSet_singleton x)).sub
      (p n).continuous.measurable).aestronglyMeasurable
  have heint (n : ℕ) : (∫ y, f y * e n y ∂(μ : Measure ℝ)) =
      (μ : Measure ℝ).real {x} * f x := by
    have hprod := polynomial_mul_integrable (μ : Measure ℝ) hm hf hf2 (p n)
    have heq : (fun y => f y * e n y) =
        (fun y => ({x} : Set ℝ).indicator f y - (p n).eval y * f y) := by
      funext y
      dsimp [e]
      by_cases hy : y ∈ ({x} : Set ℝ)
      · simp only [Set.indicator_of_mem hy]
        ring
      · simp only [Set.indicator_of_notMem hy]
        ring
    rw [heq, integral_sub (hif.indicator (measurableSet_singleton x)) hprod,
      integral_indicator (measurableSet_singleton x), integral_singleton, smul_eq_mul,
      hz, sub_zero]
  have hcs (n : ℕ) : ((μ : Measure ℝ).real {x} * f x) ^ 2 ≤
      (∫ y, f y ^ 2 ∂(μ : Measure ℝ)) * (∫ y, e n y ^ 2 ∂(μ : Measure ℝ)) := by
    have hs := sq_integral_mul_le hf (herr n) hf2 (inverseQHermiteAtomProbe_error t u x n).1
    rwa [heint n] at hs
  have hlim : Tendsto (fun n => (∫ y, f y ^ 2 ∂(μ : Measure ℝ)) *
      (∫ y, e n y ^ 2 ∂(μ : Measure ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (inverseQHermiteAtomProbe_error_tendsto t u x).const_mul
      (∫ y, f y ^ 2 ∂(μ : Measure ℝ))
  have hsq : ((μ : Measure ℝ).real {x} * f x) ^ 2 ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hcs)
  have hmass : 0 < (μ : Measure ℝ).real {x} := by
    rw [inverseQHermiteAtomMeasure_atom_real]
    exact inverseQHermiteMoment_christoffel_pos t u x
  have hzero : (μ : Measure ℝ).real {x} * f x = 0 := by
    nlinarith [sq_nonneg ((μ : Measure ℝ).real {x} * f x)]
  exact (mul_eq_zero.mp hzero).resolve_left hmass.ne'

/-- Polynomial moments separate all vectors in the selected real L² space. -/
theorem inverseQHermiteAtomMeasure_L2_moments_zero_iff (t u x : ℝ)
    (g : Lp ℝ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :
    (∀ n : ℕ, ∫ y, y ^ n * g y ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ) = 0) ↔
      g = 0 := by
  constructor
  · intro hz
    have hf : AEStronglyMeasurable (fun y => g y)
        (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
      (Lp.stronglyMeasurable g).aestronglyMeasurable
    have hf2 := (Lp.memLp g).integrable_sq
    have hp := polynomial_annihilated (inverseQHermiteAtomMeasure t u x : Measure ℝ)
      (inverseQHermiteAtomMeasure_moments t u x) hf hf2 hz
    have hzero : ∀ᵐ y ∂(inverseQHermiteAtomMeasure t u x : Measure ℝ), g y = 0 := by
      filter_upwards [inverseQHermiteAtomMeasure_ae_reselect t u x] with y hy
      apply annihilator_at_selected_atom t u y (fun z => g z)
      · rw [hy]
        exact hf
      · rw [hy]
        exact hf2
      · rw [hy]
        exact hp
    apply Lp.ext
    filter_upwards [hzero, Lp.coeFn_zero ℝ 2
      (inverseQHermiteAtomMeasure t u x : Measure ℝ)] with y hy h0
    exact hy.trans h0.symm
  · rintro rfl n
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2
      (inverseQHermiteAtomMeasure t u x : Measure ℝ)] with y hy
    change y ^ n * (0 : Lp ℝ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) y = 0
    simp only [hy, Pi.zero_apply, mul_zero]

private theorem monomial_memLp (t u x : ℝ) (n : ℕ) :
    MemLp (fun y : ℝ => y ^ n) 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa using polynomial_sq_integrable (inverseQHermiteAtomMeasure t u x : Measure ℝ)
    (inverseQHermiteAtomMeasure_moments t u x) (Polynomial.X ^ n)

/-- A monomial in the actual L² space of the selected measure. -/
def inverseQHermiteMonomialLp (t u x : ℝ) (n : ℕ) :
    Lp ℝ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ) :=
  (monomial_memLp t u x n).toLp (fun y : ℝ => y ^ n)

/-- The algebraic polynomial subspace of that L² space. -/
def inverseQHermitePolynomialSpan (t u x : ℝ) :
    Submodule ℝ (Lp ℝ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)) :=
  Submodule.span ℝ (Set.range (inverseQHermiteMonomialLp t u x))

/-- Polynomials are dense in every constructed maximal-atom realization. -/
theorem inverseQHermitePolynomialSpan_dense (t u x : ℝ) :
    (inverseQHermitePolynomialSpan t u x).topologicalClosure = ⊤ := by
  have horth : (inverseQHermitePolynomialSpan t u x)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    apply (inverseQHermiteAtomMeasure_L2_moments_zero_iff t u x g).mp
    intro n
    have hn := hg (inverseQHermiteMonomialLp t u x n)
      (Submodule.subset_span (Set.mem_range_self n))
    rw [L2.inner_def] at hn
    have hpoint :
        (fun y => inner ℝ (inverseQHermiteMonomialLp t u x n y) (g y))
          =ᵐ[(inverseQHermiteAtomMeasure t u x : Measure ℝ)] fun y => y ^ n * g y := by
      filter_upwards [MemLp.coeFn_toLp (monomial_memLp t u x n)] with y hy
      change inner ℝ (((monomial_memLp t u x n).toLp (fun y : ℝ => y ^ n)) y) (g y) = _
      rw [hy, RCLike.inner_apply]
      change g y * y ^ n = y ^ n * g y
      ring
    rw [integral_congr_ae hpoint] at hn
    exact hn
  calc
    (inverseQHermitePolynomialSpan t u x).topologicalClosure =
        (inverseQHermitePolynomialSpan t u x)ᗮᗮ :=
      (Submodule.orthogonal_orthogonal_eq_closure _).symm
    _ = (⊥ : Submodule ℝ (Lp ℝ 2 (inverseQHermiteAtomMeasure t u x : Measure ℝ)))ᗮ := by
      rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

end HTGeometry
