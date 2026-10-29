import GaloisForLFunctions.HTGeometry.NumberFieldIdealTraceDuality
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# Covolume of trace-normalized ideal lattices

Splitting complex places into two real coordinates and weighting both by `√2` changes
mixed-space volume by `2^r₂`. Comparing the actual ideal basis with the standard mixed
basis cancels the `2^(-r₂)` factor in the mixed-lattice covolume formula. The resulting
covolume is the ideal's absolute norm times the square root of the absolute discriminant.
-/

noncomputable section
open NumberField NumberField.InfinitePlace Module MeasureTheory
open scoped Classical NumberField

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [NumberField K]
local notation "ι" => numberFieldMixedRealCoordinateIndex K
local notation "X" => ι → ℝ
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- Split real coordinates are the coordinates in the standard mixed basis. -/
theorem numberFieldMixedRealCoordinates_eq_stdBasis_repr
    (z : mixedEmbedding.mixedSpace K) (i : ι) :
    numberFieldMixedRealCoordinates z i = (mixedEmbedding.stdBasis K).repr z i := by
  rcases i with w | ⟨w, j⟩
  · rfl
  · fin_cases j <;> rfl

theorem numberFieldTraceRealCoordinates_apply (z : mixedEmbedding.mixedSpace K) :
    numberFieldTraceRealCoordinates z =
      fun i => numberFieldMixedTraceWeight i * numberFieldMixedRealCoordinates z i := by
  exact congrArg (fun x : EuclideanSpace ℝ ι => x.ofLp)
    (numberFieldTraceCoordinates_apply z)

/-- Each complex place contributes the product `√2 · √2 = 2`. -/
theorem prod_numberFieldMixedTraceWeight :
    ∏ i : ι, numberFieldMixedTraceWeight i = (2 : ℝ) ^ nrComplexPlaces K := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [numberFieldMixedTraceWeight, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The two weighted coordinates at each complex place contribute a factor of `2`. -/
theorem volume_real_fundamentalDomain_traceCoordinates
    (b : Basis ι ℝ (mixedEmbedding.mixedSpace K)) :
    volume.real (ZSpan.fundamentalDomain (b.map numberFieldTraceRealCoordinates)) =
      (2 : ℝ) ^ nrComplexPlaces K * volume.real (ZSpan.fundamentalDomain b) := by
  -- Weighted coordinates multiply each column of the basis matrix by its place weight.
  have hmatrix : Matrix.of ⇑(b.map numberFieldTraceRealCoordinates) =
      ((mixedEmbedding.stdBasis K).toMatrix b).transpose *
        Matrix.diagonal numberFieldMixedTraceWeight := by
    ext i j
    rw [Matrix.mul_diagonal]
    change numberFieldTraceRealCoordinates (b i) j =
      (mixedEmbedding.stdBasis K).repr (b i) j * numberFieldMixedTraceWeight j
    rw [numberFieldTraceRealCoordinates_apply]
    dsimp only
    rw [numberFieldMixedRealCoordinates_eq_stdBasis_repr, mul_comm]
  have hvolume : volume.real (ZSpan.fundamentalDomain b) =
      |((mixedEmbedding.stdBasis K).toMatrix b).det| := by
    rw [ZSpan.measureReal_fundamentalDomain b volume (mixedEmbedding.stdBasis K), Basis.det_apply]
    simp only [measureReal_def, mixedEmbedding.volume_fundamentalDomain_stdBasis,
      ENNReal.toReal_one, mul_one]
  rw [ZSpan.volume_real_fundamentalDomain, hmatrix, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, prod_numberFieldMixedTraceWeight, abs_mul,
    abs_of_pos (pow_pos (show (0 : ℝ) < 2 by norm_num) _), hvolume, mul_comm]

private theorem covolume_trace_of_indexEquiv (I : FIˣ)
    (e : Free.ChooseBasisIndex ℤ I ≃ ι) :
    ZLattice.covolume (numberFieldTraceLattice I) =
      (FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| := by
  let b₀ := mixedEmbedding.fractionalIdealLatticeBasis K I
  let b := b₀.reindex e
  have hrange : Set.range (b.map numberFieldTraceRealCoordinates) =
      Set.range (numberFieldTraceLatticeBasis I) := by
    change Set.range ((b₀.reindex e).map numberFieldTraceRealCoordinates) =
      Set.range (b₀.map numberFieldTraceRealCoordinates)
    ext x
    simp only [Basis.coe_map, Basis.coe_reindex, Function.comp_apply, Set.mem_range]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩
  have hspan : Submodule.span ℤ (Set.range (b.map numberFieldTraceRealCoordinates)) =
      numberFieldTraceLattice I := by
    rw [hrange, span_numberFieldTraceLatticeBasis]
  have hvolume : volume.real (ZSpan.fundamentalDomain b) =
      ZLattice.covolume (mixedEmbedding.idealLattice K I) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (mixedEmbedding.fundamentalDomain_idealLattice K I)]
    exact congrArg volume.real (ZSpan.fundamentalDomain_reindex b₀ e)
  rw [← hspan, ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (b.map numberFieldTraceRealCoordinates) volume),
    volume_real_fundamentalDomain_traceCoordinates, hvolume, mixedEmbedding.covolume_idealLattice]
  have hpow : (2 : ℝ) ^ nrComplexPlaces K * (2⁻¹ : ℝ) ^ nrComplexPlaces K = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (FractionalIdeal.absNorm (I : FI) : ℝ) *
        ((2 : ℝ) ^ nrComplexPlaces K * (2⁻¹ : ℝ) ^ nrComplexPlaces K) *
          Real.sqrt |(NumberField.discr K : ℝ)| := by ring
    _ = _ := by rw [hpow, mul_one]

/-- The covolume of the trace-normalized ideal lattice. -/
theorem covolume_numberFieldTraceLattice (I : FIˣ) :
    ZLattice.covolume (numberFieldTraceLattice I) =
      (FractionalIdeal.absNorm (I : FI) : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)| :=
  covolume_trace_of_indexEquiv I
    ((mixedEmbedding.fractionalIdealLatticeBasis K I).indexEquiv (mixedEmbedding.stdBasis K))

end GaloisForLFunctions.HTGeometry
