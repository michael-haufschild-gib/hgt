import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerNuclearExpansion
import GaloisForLFunctions.HTGeometry.GeometricDecayFredholmDeterminant
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# A global Fredholm determinant for the actual Gauss–Mayer operator

Rescaling the Cauchy expansion factors the regularized disc-algebra operator as
`JQ` through `ℓ²`. The reverse product `QJ` has a geometrically decaying matrix.
Its finite determinants converge with an explicit error to an entire function
of the spectral variable. Identifying that limit with the global Hilbert–Carleman
determinant transfers its zero criterion to the original Banach operator.

The construction uses fixed radii `9/8`, `6/5`, `32/25`. It applies on `Re w > 0`;
the analytic interpretation excludes the scalar pole at `w = 1`.
-/

open Complex Metric Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm

/-- Radius used in the local operator estimate. -/
def innerRadius : ℝ := 9 / 8
/-- Rescaling radius, between the local and coefficient radii. -/
def balanceRadius : ℝ := 6 / 5
/-- Radius of the actual Cauchy coefficient integrals. -/
def coefficientRadius : ℝ := 32 / 25
/-- Common geometric rate `15/16` for both rescaled factors. -/
def rate : ℝ := 15 / 16

theorem radii : 1 < innerRadius ∧ innerRadius < coefficientRadius ∧
    coefficientRadius < 3 / 2 := by norm_num [innerRadius, coefficientRadius]

theorem coefficientRadius_pos : 0 < coefficientRadius := by
  norm_num [coefficientRadius]

theorem balanceRadius_pos : 0 < balanceRadius := by norm_num [balanceRadius]

theorem rate_bounds : 0 ≤ rate ∧ rate < 1 := by norm_num [rate]

/-- The `k`th Cauchy functional rescaled by `(6/5)^k`. -/
def functional (k : ℕ) : DiscSpace →L[ℂ] ℂ :=
  ((balanceRadius : ℂ) ^ k) •
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 k

/-- The image of the `k`th monomial rescaled by `(6/5)⁻ᵏ`. -/
def vector (w : ℂ) (hw : 0 < w.re) (k : ℕ) : DiscSpace :=
  ((balanceRadius : ℂ) ^ k)⁻¹ • regularized w hw (monomial k)

/-- The explicit smaller-disc bound for the regularized Mayer operator. -/
def constantBound (w : ℂ) : ℝ := localBound w innerRadius

theorem constantBound_nonneg {w : ℂ} (hw : 0 < w.re) : 0 ≤ constantBound w := by
  have h := (norm_nonneg (regularized w hw (monomial 0))).trans
    (regularized_monomial_bound hw radii.1 (radii.2.1.trans radii.2.2) 0)
  change 0 ≤ localBound w innerRadius
  simpa only [pow_zero, mul_one] using h

/-- The rescaled coefficient functionals decay geometrically. -/
theorem norm_functional_le (k : ℕ) : ‖functional k‖ ≤ rate ^ k := by
  rw [functional, norm_smul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg balanceRadius_pos.le]
  calc
    _ ≤ balanceRadius ^ k * (coefficientRadius⁻¹ ^ k) :=
      mul_le_mul_of_nonneg_left
        (norm_coefficient_le coefficientRadius coefficientRadius_pos radii.2.2 k)
        (pow_nonneg balanceRadius_pos.le _)
    _ = rate ^ k := by rw [← mul_pow]; norm_num [balanceRadius, coefficientRadius, rate]

/-- The rescaled monomial images decay at the same geometric rate. -/
theorem norm_vector_le {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    ‖vector w hw k‖ ≤ constantBound w * rate ^ k := by
  rw [vector, norm_smul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg balanceRadius_pos.le]
  calc
    _ ≤ (balanceRadius ^ k)⁻¹ * (constantBound w * innerRadius ^ k) :=
      mul_le_mul_of_nonneg_left
        (regularized_monomial_bound hw radii.1 (radii.2.1.trans radii.2.2) k)
        (inv_nonneg.mpr (pow_nonneg balanceRadius_pos.le _))
    _ = constantBound w * rate ^ k := by
      rw [show (balanceRadius ^ k)⁻¹ * (constantBound w * innerRadius ^ k) =
        constantBound w * (innerRadius / balanceRadius) ^ k by rw [div_pow]; ring]
      norm_num [innerRadius, balanceRadius, rate]

/-- Rescaling cancels exactly in each source rank-one operator. -/
theorem scaled_rankTerm {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    (functional k).smulRight (vector w hw k) =
      rankTerm w hw coefficientRadius coefficientRadius_pos radii.2.2 k := by
  have hs : (balanceRadius : ℂ) ^ k ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr balanceRadius_pos.ne')
  ext f
  change (((balanceRadius : ℂ) ^ k) *
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 k f) •
      (((balanceRadius : ℂ) ^ k)⁻¹ • regularized w hw (monomial k)) =
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 k f •
      regularized w hw (monomial k)
  rw [smul_smul]
  congr 1
  field_simp

private theorem functional_norm_summable : Summable (fun k => ‖functional k‖) :=
  (summable_geometric_of_lt_one rate_bounds.1 rate_bounds.2).of_nonneg_of_le
    (fun _ => norm_nonneg _) norm_functional_le

private theorem vector_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun k => ‖vector w hw k‖) :=
  ((summable_geometric_of_lt_one rate_bounds.1 rate_bounds.2).mul_left (constantBound w)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_vector_le hw)

private theorem hasSum_scaled_rankTerm {w : ℂ} (hw : 0 < w.re) :
    HasSum (fun k => (functional k).smulRight (vector w hw k)) (regularized w hw) := by
  simp only [scaled_rankTerm]
  exact hasSum_rankTerm hw radii.1 radii.2.1 radii.2.2

/-- The Hilbert sequence space used to factor the Banach operator. -/
abbrev SequenceSpace := lp (fun _ : ℕ => ℂ) 2

private def mode (k : ℕ) : SequenceSpace := lp.single 2 k 1

private theorem norm_mode (k : ℕ) : ‖mode k‖ = 1 := by
  rw [mode, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one]

private def coordinate (k : ℕ) : SequenceSpace →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 k

private theorem norm_coordinate_le (k : ℕ) : ‖coordinate k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(x : ℕ → ℂ) k‖ ≤ 1 * ‖x‖
  rw [one_mul]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x k

private def analysisTerm (k : ℕ) : DiscSpace →L[ℂ] SequenceSpace :=
  (functional k).smulRight (mode k)

private theorem analysisTerm_norm_summable : Summable (fun k => ‖analysisTerm k‖) := by
  simpa only [analysisTerm, ContinuousLinearMap.norm_smulRight_apply, norm_mode, mul_one]
    using functional_norm_summable

/-- The bounded map from disc-algebra functions to their rescaled Cauchy coefficients. -/
def analysisMap : DiscSpace →L[ℂ] SequenceSpace := ∑' k, analysisTerm k

private theorem hasSum_analysis : HasSum analysisTerm analysisMap :=
  analysisTerm_norm_summable.of_norm.hasSum

/-- Every coordinate of the analysis map is the actual Cauchy functional. -/
theorem analysis_coordinate (f : DiscSpace) (i : ℕ) :
    (analysisMap f : ℕ → ℂ) i = functional i f := by
  have h := (coordinate i).hasSum
    ((ContinuousLinearMap.apply ℂ SequenceSpace f).hasSum hasSum_analysis)
  change HasSum (fun j => functional j f * (mode j : ℕ → ℂ) i)
    ((analysisMap f : ℕ → ℂ) i) at h
  rw [← h.tsum_eq, tsum_eq_single i]
  · rw [mode, lp.single_apply_self, mul_one]
  · intro j hj
    rw [mode, lp.single_apply_ne _ _ _ hj.symm, mul_zero]

private def synthesisTerm (w : ℂ) (hw : 0 < w.re) (k : ℕ) :
    SequenceSpace →L[ℂ] DiscSpace := (coordinate k).smulRight (vector w hw k)

private theorem synthesisTerm_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun k => ‖synthesisTerm w hw k‖) := by
  apply (vector_norm_summable hw).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  rw [synthesisTerm, ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_coordinate_le k)

/-- The bounded synthesis map formed from rescaled images of monomials. -/
def synthesisMap (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] DiscSpace :=
  ∑' k, synthesisTerm w hw k

private theorem hasSum_synthesis {w : ℂ} (hw : 0 < w.re) :
    HasSum (synthesisTerm w hw) (synthesisMap w hw) :=
  (synthesisTerm_norm_summable hw).of_norm.hasSum

/-- Synthesis is the absolutely convergent vector series with the given coordinates. -/
theorem synthesis_apply {w : ℂ} (hw : 0 < w.re) (x : SequenceSpace) :
    synthesisMap w hw x = ∑' k, (x : ℕ → ℂ) k • vector w hw k :=
  ((ContinuousLinearMap.apply ℂ DiscSpace x).hasSum (hasSum_synthesis hw)).tsum_eq.symm

/-- A coordinate vector synthesizes to the corresponding rescaled monomial image. -/
theorem synthesis_mode {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    synthesisMap w hw (mode j) = vector w hw j := by
  rw [synthesis_apply, tsum_eq_single j]
  · rw [mode, lp.single_apply_self, one_smul]
  · intro k hk
    rw [mode, lp.single_apply_ne _ _ _ hk, zero_smul]

/-- The factorization recovers the actual regularized Gauss–Mayer operator. -/
theorem synthesis_comp_analysis {w : ℂ} (hw : 0 < w.re) :
    (synthesisMap w hw).comp analysisMap = regularized w hw := by
  ext f
  change synthesisMap w hw (analysisMap f) = regularized w hw f
  rw [synthesis_apply]
  simp only [analysis_coordinate]
  exact ((ContinuousLinearMap.apply ℂ DiscSpace f).hasSum
    (hasSum_scaled_rankTerm hw)).tsum_eq

/-- The reverse product of analysis and synthesis on the Hilbert sequence space. -/
def hilbertOperator (w : ℂ) (hw : 0 < w.re) : SequenceSpace →L[ℂ] SequenceSpace :=
  analysisMap.comp (synthesisMap w hw)

/-- The actual coefficient matrix of the Hilbert realization. -/
def matrix (w : ℂ) (hw : 0 < w.re) (i j : ℕ) : ℂ :=
  functional i (vector w hw j)

/-- The coefficient matrix is the matrix of the constructed Hilbert operator. -/
theorem matrixOf_hilbertOperator {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.matrixOf (hilbertOperator w hw) = fun p => matrix w hw p.1 p.2 := by
  funext p
  change (analysisMap (synthesisMap w hw (mode p.2)) : ℕ → ℂ) p.1 = _
  rw [analysis_coordinate, synthesis_mode]
  rfl

/-- Both matrix indices have the explicit geometric decay `15/16`. -/
theorem geomDecay_matrix {w : ℂ} (hw : 0 < w.re) :
    GeomFredholm.GeomDecay (matrix w hw) (constantBound w) rate := by
  refine ⟨constantBound_nonneg hw, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  calc
    ‖functional i (vector w hw j)‖ ≤ ‖functional i‖ * ‖vector w hw j‖ :=
      (functional i).le_opNorm _
    _ ≤ rate ^ i * (constantBound w * rate ^ j) :=
      mul_le_mul (norm_functional_le i) (norm_vector_le hw j)
        (norm_nonneg _) (pow_nonneg rate_bounds.1 _)
    _ = _ := by ring

/-- The synthesis map has an explicit absolutely summable rank-one decomposition. -/
theorem nuclear_synthesis {w : ℂ} (hw : 0 < w.re) :
    RHTower.DeningerIsNuclear (synthesisMap w hw) := by
  refine ⟨ℕ, coordinate, vector w hw, ?_, ?_⟩
  · simpa only [synthesisTerm, ContinuousLinearMap.norm_smulRight_apply]
      using synthesisTerm_norm_summable hw
  · intro x
    have h := (ContinuousLinearMap.apply ℂ DiscSpace x).hasSum (hasSum_synthesis hw)
    change HasSum (fun k => synthesisTerm w hw k x) (synthesisMap w hw x) at h
    simpa only [synthesisTerm, ContinuousLinearMap.smulRight_apply] using h

/-- The Hilbert realization is nuclear, by bounded composition with the synthesis map. -/
theorem nuclear_hilbertOperator {w : ℂ} (hw : 0 < w.re) :
    RHTower.DeningerIsNuclear (hilbertOperator w hw) :=
  (nuclear_synthesis hw).compL analysisMap

/-- The finite rank-one operators are exactly the certified Taylor approximations. -/
theorem finite_factor_eq_approximation {w : ℂ} (hw : 0 < w.re) (N : ℕ) :
    (∑ k ∈ Finset.range N, (functional k).smulRight (vector w hw k)) =
      approximation w hw coefficientRadius coefficientRadius_pos radii.2.2 N := by
  simp only [scaled_rankTerm, approximation]

/-- The same coefficient matrix in the kernel convention for Hilbert–Schmidt theory. -/
def kernel (w : ℂ) (hw : 0 < w.re) : ℕ × ℕ → ℂ :=
  fun p => matrix w hw p.1 p.2

/-- Geometric decay makes the actual coefficient kernel square-summable. -/
theorem kernel_isHS {w : ℂ} (hw : 0 < w.re) : HilbertSchmidt.IsHS (kernel w hw) := by
  have hs : Summable (fun k : ℕ => (rate ^ 2) ^ k) :=
    summable_geometric_of_lt_one (sq_nonneg rate)
      (GeomFredholm.sq_lt_one rate_bounds.1 rate_bounds.2)
  have hp : Summable (fun p : ℕ × ℕ => (rate ^ 2) ^ p.1 * (rate ^ 2) ^ p.2) :=
    summable_mul_of_summable_norm hs.norm hs.norm
  apply (hp.mul_left (constantBound w ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
  intro p
  calc
    ‖kernel w hw p‖ ^ 2 ≤ (constantBound w * rate ^ p.1 * rate ^ p.2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((geomDecay_matrix hw).bound p.1 p.2) 2
    _ = _ := by simp only [mul_pow, ← pow_mul, Nat.mul_comm]; ring

/-- The Hilbert–Schmidt kernel reconstructs precisely the reverse product `QJ`. -/
theorem toOperator_kernel {w : ℂ} (hw : 0 < w.re) :
    HilbertSchmidt.toOperator (kernel_isHS hw) = hilbertOperator w hw := by
  -- Equality on coordinate vectors determines the bounded Hilbert operator.
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
  rintro x ⟨j, rfl⟩
  rw [HilbertSchmidt.lpBasis_apply]
  apply lp.ext
  funext i
  rw [HilbertSchmidt.toOperator_single]
  exact (congrFun (matrixOf_hilbertOperator hw) (i, j)).symm

/-- Analysis and synthesis transfer every nonzero eigenvalue between `JQ` and `QJ`. -/
theorem eigenvector_transfer {w μ : ℂ} (hw : 0 < w.re) (hμ : μ ≠ 0) :
    (∃ x : SequenceSpace, x ≠ 0 ∧ hilbertOperator w hw x = μ • x) ↔
      ∃ f : DiscSpace, f ≠ 0 ∧ regularized w hw f = μ • f := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨synthesisMap w hw x, ?_, ?_⟩
    · intro hzero
      have h : μ • x = 0 := by
        rw [← hx]
        change analysisMap (synthesisMap w hw x) = 0
        rw [hzero, map_zero]
      exact hx0 ((smul_eq_zero.mp h).resolve_left hμ)
    · calc
        regularized w hw (synthesisMap w hw x) =
            synthesisMap w hw (analysisMap (synthesisMap w hw x)) :=
          congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T (synthesisMap w hw x))
            (synthesis_comp_analysis hw).symm
        _ = synthesisMap w hw (hilbertOperator w hw x) := rfl
        _ = μ • synthesisMap w hw x := by rw [hx, map_smul]
  · rintro ⟨f, hf0, hf⟩
    refine ⟨analysisMap f, ?_, ?_⟩
    · intro hzero
      have h : μ • f = 0 := by
        rw [← hf, ← synthesis_comp_analysis hw]
        change synthesisMap w hw (analysisMap f) = 0
        rw [hzero, map_zero]
      exact hf0 ((smul_eq_zero.mp h).resolve_left hμ)
    · change analysisMap (synthesisMap w hw (analysisMap f)) = _
      have h := congrArg (fun T : DiscSpace →L[ℂ] DiscSpace => T f)
        (synthesis_comp_analysis hw)
      change synthesisMap w hw (analysisMap f) = regularized w hw f at h
      rw [h, hf, map_smul]

private theorem tendsto_ranges : Tendsto Finset.range atTop (atTop : Filter (Finset ℕ)) := by
  apply tendsto_atTop_finset_of_monotone
  · exact fun a b hab => Finset.range_mono hab
  · exact fun k => ⟨k + 1, Finset.mem_range.mpr (Nat.lt_succ_self k)⟩

private theorem finiteDet2_trunc {w : ℂ} (hw : 0 < w.re) (N : ℕ) (lam : ℂ) :
    finiteDet2 (-(GeomFredholm.trunc (matrix w hw) N)) lam =
      finiteDet2 (-(HilbertSchmidt.blockMatrix (kernel w hw) (Finset.range N))) lam := by
  let e : Fin N ≃ Finset.range N :=
    { toFun := fun i => ⟨i, Finset.mem_range.mpr i.isLt⟩
      invFun := fun i => ⟨i, Finset.mem_range.mp i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he : -(GeomFredholm.trunc (matrix w hw) N) =
      (-(HilbertSchmidt.blockMatrix (kernel w hw) (Finset.range N))).submatrix e e := by
    ext i j
    rfl
  rw [he, finiteDet2_submatrix]

theorem diagonal_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun k => ‖matrix w hw k k‖) := by
  apply ((GeomFredholm.hasSum_pow_two_mul rate_bounds.1 rate_bounds.2).summable.mul_left
    (constantBound w)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  exact ((geomDecay_matrix hw).bound k k).trans_eq (mul_assoc _ _ _)

/-- The absolutely convergent sum of the actual coefficient diagonal. -/
def diagonalTrace (w : ℂ) (hw : 0 < w.re) : ℂ := ∑' k, matrix w hw k k

private theorem tendsto_trace_trunc {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun N => (GeomFredholm.trunc (matrix w hw) N).trace) atTop
      (𝓝 (diagonalTrace w hw)) := by
  have he : ∀ N, (GeomFredholm.trunc (matrix w hw) N).trace =
      ∑ k ∈ Finset.range N, matrix w hw k k := by
    intro N
    simp only [Matrix.trace, Matrix.diag_apply, GeomFredholm.trunc, Matrix.of_apply]
    exact Fin.sum_univ_eq_sum_range (fun k => matrix w hw k k) N
  simp only [he]
  exact (diagonal_norm_summable hw).of_norm.hasSum.tendsto_sum_nat

private theorem truncDet_eq_finiteDet2 {w : ℂ} (hw : 0 < w.re) (lam : ℂ) (N : ℕ) :
    GeomFredholm.truncDet (matrix w hw) lam N =
      finiteDet2 (-(GeomFredholm.trunc (matrix w hw) N)) lam *
        Complex.exp (-(lam * (GeomFredholm.trunc (matrix w hw) N).trace)) := by
  unfold finiteDet2 GeomFredholm.truncDet
  rw [smul_neg, ← sub_eq_add_neg, Matrix.trace_neg, mul_neg, neg_neg,
    mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

/-- The entire limit of finite determinants of the actual Mayer coefficient matrix. -/
def determinant (w : ℂ) (hw : 0 < w.re) : ℂ → ℂ :=
  GeomFredholm.fdet (matrix w hw)

/-- The finite-determinant limit equals the global regularized determinant with its diagonal correction. -/
theorem determinant_eq_entireDet2 {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    determinant w hw lam = entireDet2 (kernel w hw) lam * Complex.exp (-(lam * diagonalTrace w hw)) := by
  -- Separate the finite diagonal correction before taking the global determinant limit.
  have hreg : Tendsto (fun N => finiteDet2 (-(GeomFredholm.trunc (matrix w hw) N)) lam)
      atTop (𝓝 (entireDet2 (kernel w hw) lam)) := by
    simp only [finiteDet2_trunc hw]
    exact (tendsto_finiteDet2_entireDet2 (kernel_isHS hw) lam).comp tendsto_ranges
  have hdiag := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_trace_trunc hw).const_mul lam).neg
  have hprod := hreg.mul hdiag
  have ht : Tendsto (GeomFredholm.truncDet (matrix w hw) lam) atTop
      (𝓝 (entireDet2 (kernel w hw) lam * Complex.exp (-(lam * diagonalTrace w hw)))) := by
    simpa only [Function.comp_apply, ← truncDet_eq_finiteDet2 hw] using hprod
  exact tendsto_nhds_unique (GeomFredholm.tendsto_truncDet (geomDecay_matrix hw) lam) ht

/-- The actual-source determinant is entire in the spectral variable. -/
theorem differentiable_determinant {w : ℂ} (hw : 0 < w.re) :
    Differentiable ℂ (determinant w hw) :=
  GeomFredholm.differentiable_fdet (geomDecay_matrix hw)

/-- The determinant is normalized to one at the zero spectral parameter. -/
theorem determinant_zero {w : ℂ} (hw : 0 < w.re) : determinant w hw 0 = 1 := by
  rw [determinant_eq_entireDet2 hw,
    (isRegularizedDet_entireDet2 (kernel_isHS hw)).eq_one_at_zero]
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]

/-- At a nonzero spectral parameter, determinant zeros are exactly actual disc-algebra eigenfunctions. -/
theorem determinant_eq_zero_iff_eigenvector {w lam : ℂ} (hw : 0 < w.re) (hlam : lam ≠ 0) :
    determinant w hw lam = 0 ↔ ∃ f : DiscSpace, f ≠ 0 ∧ regularized w hw f = lam⁻¹ • f := by
  rw [determinant_eq_entireDet2 hw, mul_eq_zero,
    or_iff_left (Complex.exp_ne_zero _),
    entireDet2_eq_zero_iff_exists_eigenvector (kernel_isHS hw) hlam,
    toOperator_kernel hw, eigenvector_transfer hw (inv_ne_zero hlam)]

/-- The determinant vanishes exactly when the original Banach operator fails the Fredholm invertibility test. -/
theorem determinant_eq_zero_iff_not_isUnit {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    determinant w hw lam = 0 ↔ ¬ IsUnit (1 - lam • regularized w hw) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp only [determinant_zero hw, one_ne_zero, zero_smul, sub_zero, isUnit_one, not_true_eq_false]
  rw [determinant_eq_zero_iff_eigenvector hw hlam]
  constructor
  · rintro ⟨f, hf0, hf⟩ hunit
    apply hf0
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    rw [map_zero]
    change f - lam • regularized w hw f = 0
    rw [hf, smul_smul, mul_inv_cancel₀ hlam, one_smul, sub_self]
  · intro hnotunit
    have hcpt : IsCompactOperator (lam • regularized w hw) := (compact_regularized hw).smul lam
    rcases hcpt.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℂ)) one_ne_zero with heig | hres
    · obtain ⟨f, hf⟩ := heig.exists_hasUnifEigenvector
      refine ⟨f, hf.2, ?_⟩
      have h := hf.apply_eq_smul
      change lam • regularized w hw f = (1 : ℂ) • f at h
      have hi := congrArg (fun x : DiscSpace => lam⁻¹ • x) h
      simpa only [smul_smul, inv_mul_cancel₀ hlam, one_smul, mul_one] using hi
    · rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
      exact False.elim (hnotunit (by simpa only [one_smul] using hres))

/-- Finite source determinants converge with an explicit geometric error. -/
theorem determinant_approximation_error {w : ℂ} (hw : 0 < w.re) (lam : ℂ) (N : ℕ) :
    dist (GeomFredholm.truncDet (matrix w hw) lam N) (determinant w hw lam) ≤
      GeomFredholm.incConst lam (constantBound w) rate * rate ^ N / (1 - rate) :=
  GeomFredholm.dist_truncDet_fdet_le (geomDecay_matrix hw) lam N

#print axioms synthesis_comp_analysis
#print axioms geomDecay_matrix
#print axioms eigenvector_transfer
#print axioms determinant_eq_entireDet2
#print axioms differentiable_determinant
#print axioms determinant_eq_zero_iff_not_isUnit
#print axioms determinant_approximation_error
#print axioms nuclear_hilbertOperator
#print axioms finite_factor_eq_approximation

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
