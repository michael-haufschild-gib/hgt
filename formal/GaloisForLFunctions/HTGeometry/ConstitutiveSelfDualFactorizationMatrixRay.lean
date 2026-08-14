import GaloisForLFunctions.HTGeometry.CartanWorkProperness
import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationGeometry
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Instances.Matrix

open scoped BigOperators ComplexOrder
open scoped Matrix.Norms.L2Operator
open NormedSpace Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

def factorizationMatrixRay (X Y : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  exp ((t : ℂ) • Y) * exp ((t : ℂ) • X)

def factorizationMatrixReversal (S : Matrix n n ℂ) : Matrix n n ℂ :=
  (Sᴴ)⁻¹

theorem trace_exp_smul_hermitian
    {X : Matrix n n ℂ} (hX : X.IsHermitian) (t : ℝ) :
    (exp ((t : ℂ) • X)).trace.re = ∑ i, Real.exp (t * hX.eigenvalues i) := by
  let U : Matrix n n ℂ := hX.eigenvectorUnitary
  let D : Matrix n n ℂ := diagonal (fun i ↦ (hX.eigenvalues i : ℂ))
  have hUU : Uᴴ * U = 1 := by
    dsimp only [U]
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hUinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv (by
    dsimp only [U]
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.coe_mul_star_self _)
  have hU : IsUnit U := by
    dsimp only [U]
    exact Unitary.isUnit_coe
  have hspec : X = U * D * Uᴴ := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hX.spectral_theorem
  have hscaled : (t : ℂ) • X = U * ((t : ℂ) • D) * U⁻¹ := by
    rw [hspec, hUinv]
    simp
  rw [hscaled, Matrix.exp_conj U _ hU, hUinv, Matrix.trace_mul_cycle, hUU,
    Matrix.one_mul]
  have hdiag : ((t : ℂ) • D) = diagonal (fun i ↦ ((t * hX.eigenvalues i : ℝ) : ℂ)) := by
    dsimp only [D]
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  rw [hdiag, Matrix.exp_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Pi.coe_exp]
  change (exp (((fun i => ((t * hX.eigenvalues i : ℝ) : ℂ)) i))).re = _
  rw [Real.exp_eq_exp_ℝ]
  exact (congrArg Complex.re (NormedSpace.ofReal_exp_ℝ_ℝ
    (t * hX.eigenvalues i))).symm

/-- Adjoint reversal in matrix Cartan-ray coordinates, paper formula CT.22. -/
theorem factorizationMatrixReversal_ray
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Yᴴ = -Y) (t : ℝ) :
    factorizationMatrixReversal (factorizationMatrixRay X Y t) =
      exp ((t : ℂ) • Y) * exp (-((t : ℂ) • X)) := by
  have hXt : (((t : ℂ) • X)ᴴ) = (t : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hX]
    simp
  have hYt : (((t : ℂ) • Y)ᴴ) = -((t : ℂ) • Y) := by
    rw [Matrix.conjTranspose_smul, hY]
    simp
  unfold factorizationMatrixReversal factorizationMatrixRay
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose,
    ← Matrix.exp_conjTranspose, hXt, hYt, Matrix.mul_inv_rev]
  rw [← Matrix.exp_neg, ← Matrix.exp_neg]
  simp

/-- The compact phase cancels from the positive Gram of a matrix Cartan ray. -/
theorem factorizationMatrixRay_gram
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Yᴴ = -Y) (t : ℝ) :
    (factorizationMatrixRay X Y t)ᴴ * factorizationMatrixRay X Y t =
      exp (((2 * t : ℝ) : ℂ) • X) := by
  have hXt : (((t : ℂ) • X)ᴴ) = (t : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hX]
    simp
  have hYt : (((t : ℂ) • Y)ᴴ) = -((t : ℂ) • Y) := by
    rw [Matrix.conjTranspose_smul, hY]
    simp
  have hunit := Matrix.isUnit_exp ((t : ℂ) • Y)
  letI := hunit.invertible
  unfold factorizationMatrixRay
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose,
    ← Matrix.exp_conjTranspose, hXt, hYt, Matrix.exp_neg]
  calc
    (exp ((t : ℂ) • X) * (exp ((t : ℂ) • Y))⁻¹) *
          (exp ((t : ℂ) • Y) * exp ((t : ℂ) • X)) =
        exp ((t : ℂ) • X) * exp ((t : ℂ) • X) := by
      rw [Matrix.mul_assoc,
        ← Matrix.mul_assoc (exp ((t : ℂ) • Y))⁻¹ (exp ((t : ℂ) • Y)),
        Matrix.inv_mul_of_invertible, Matrix.one_mul]
    _ = exp (((2 * t : ℝ) : ℂ) • X) := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _)]
      congr 1
      ext i j
      simp
      ring

theorem factorizationMatrixRay_isUnit (X Y : Matrix n n ℂ) (t : ℝ) :
    IsUnit (factorizationMatrixRay X Y t) := by
  exact (Matrix.isUnit_exp ((t : ℂ) • Y)).mul
    (Matrix.isUnit_exp ((t : ℂ) • X))

/-- Exact matrix Cartan-ray work formula, paper formula CT.23. -/
theorem cartanWork_factorizationMatrixRay
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Yᴴ = -Y) (t : ℝ) :
    cartanWork (factorizationMatrixRay X Y t) =
      ∑ i, cartanModeWork (t * hX.eigenvalues i) := by
  have hgram := factorizationMatrixRay_gram hX hY t
  have hinv : (exp (((2 * t : ℝ) : ℂ) • X))⁻¹ =
      exp (((-2 * t : ℝ) : ℂ) • X) := by
    rw [← Matrix.exp_neg]
    congr 1
    ext i j
    simp
  rw [cartanWork, hgram, hinv,
    trace_exp_smul_hermitian hX (2 * t),
    trace_exp_smul_hermitian hX (-2 * t)]
  rw [show (2 : ℝ) * Fintype.card n = ∑ _i : n, (2 : ℝ) by
    rw [Finset.sum_const, Finset.card_univ]
    ring]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show 2 * t * hX.eigenvalues i = 2 * (t * hX.eigenvalues i) by ring,
    show -2 * t * hX.eigenvalues i = -2 * (t * hX.eigenvalues i) by ring]
  rw [← cartanModeWork_add_two]
  ring

section NonemptyPhase

variable [Nonempty n]

/-- Finite-dimensional unitary matrices form a compact group in the entrywise topology. -/
theorem isCompact_matrixUnitaryGroup :
    IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, fun U hU ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary hU).le

/-- Every finite-dimensional unitary has powers returning arbitrarily close to identity at
unbounded natural times. -/
theorem matrixUnitary_pow_recurrent (U : Matrix.unitaryGroup n ℂ) :
    MapClusterPt 1 Filter.atTop (fun k : ℕ ↦ U ^ k) := by
  letI : CompactSpace (Matrix.unitaryGroup n ℂ) :=
    isCompact_iff_compactSpace.mp isCompact_matrixUnitaryGroup
  exact mapClusterPt_one_atTop_pow U

def skewHermitianPhaseUnitary (Y : Matrix n n ℂ) (hY : Yᴴ = -Y) :
    Matrix.unitaryGroup n ℂ := by
  refine ⟨exp Y, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← Matrix.exp_conjTranspose, hY, Matrix.exp_neg]
  letI := (Matrix.isUnit_exp Y).invertible
  exact Matrix.mul_inv_of_invertible _

omit [Nonempty n] in theorem skewHermitianPhaseUnitary_pow_coe
    (Y : Matrix n n ℂ) (hY : Yᴴ = -Y) (k : ℕ) :
    ((skewHermitianPhaseUnitary Y hY) ^ k : Matrix.unitaryGroup n ℂ) =
      skewHermitianPhaseUnitary (k • Y) (by
        rw [Matrix.conjTranspose_nsmul, hY]
        simp) := by
  apply Subtype.ext
  change exp Y ^ k = exp (k • Y)
  exact (Matrix.exp_nsmul k Y).symm

/-- Exact recurrent-phase statement at unbounded integer times. -/
theorem skewHermitianPhase_recurrent (Y : Matrix n n ℂ) (hY : Yᴴ = -Y) :
    MapClusterPt 1 Filter.atTop
      (fun k : ℕ ↦ skewHermitianPhaseUnitary (k • Y) (by
        rw [Matrix.conjTranspose_nsmul, hY]
        simp)) := by
  simpa only [skewHermitianPhaseUnitary_pow_coe] using
    matrixUnitary_pow_recurrent (skewHermitianPhaseUnitary Y hY)

/-- The whole real unitary phase orbit has compact closure. -/
theorem isCompact_closure_range_skewHermitianPhase
    (Y : Matrix n n ℂ) (hY : Yᴴ = -Y) :
    IsCompact (closure (Set.range (fun t : ℝ ↦ exp ((t : ℂ) • Y)))) := by
  apply isCompact_matrixUnitaryGroup.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_unitary
  rintro U ⟨t, rfl⟩
  have hYt : (((t : ℂ) • Y)ᴴ) = -((t : ℂ) • Y) := by
    rw [Matrix.conjTranspose_smul, hY]
    simp
  exact (skewHermitianPhaseUnitary ((t : ℂ) • Y) hYt).property

end NonemptyPhase

/-- Operator-level bounded-work selection, paper formula CT.24. -/
theorem bounded_cartanWork_factorizationMatrixRay_iff
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Yᴴ = -Y) :
    (∃ C : ℝ, ∀ t : ℝ, cartanWork (factorizationMatrixRay X Y t) ≤ C) ↔ X = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    apply hX.eigenvalues_eq_zero_iff.mp
    funext i
    exact (bounded_sinh_sq_sum_iff hX.eigenvalues).mp ⟨C, fun t ↦ by
      simpa [cartanWork_factorizationMatrixRay hX hY t, cartanModeWork,
        Finset.mul_sum] using hC t⟩ i
  · intro hzero
    subst X
    refine ⟨0, fun t ↦ ?_⟩
    have heig : hX.eigenvalues = 0 := hX.eigenvalues_eq_zero_iff.mpr rfl
    rw [cartanWork_factorizationMatrixRay hX hY]
    simp [heig, cartanModeWork]

/-- Strong cofinal form: bounded work along any times escaping in absolute value forces the
Hermitian radial generator to vanish. -/
theorem eq_zero_of_bounded_cartanWork_along_cobounded
    {X Y : Matrix n n ℂ} (hX : X.IsHermitian) (hY : Yᴴ = -Y)
    (time : ℕ → ℝ)
    (htime : Filter.Tendsto (fun k ↦ |time k|) Filter.atTop Filter.atTop)
    (hwork : ∃ C : ℝ, ∀ k,
      cartanWork (factorizationMatrixRay X Y (time k)) ≤ C) :
    X = 0 := by
  apply hX.eigenvalues_eq_zero_iff.mp
  funext i
  change hX.eigenvalues i = 0
  by_contra hne
  obtain ⟨C, hC⟩ := hwork
  have hlambda : 0 < |hX.eigenvalues i| := abs_pos.mpr hne
  have harg : Filter.Tendsto
      (fun k ↦ |time k * hX.eigenvalues i|) Filter.atTop Filter.atTop := by
    simpa [abs_mul] using htime.atTop_mul_const' hlambda
  have hexp : Filter.Tendsto
      (fun k ↦ Real.exp (2 * |time k * hX.eigenvalues i|))
      Filter.atTop Filter.atTop := by
    exact Real.tendsto_exp_atTop.comp (harg.const_mul_atTop' zero_lt_two)
  have hevent : ∀ᶠ k in Filter.atTop,
      C + 2 < Real.exp (2 * |time k * hX.eigenvalues i|) :=
    by
      filter_upwards [(Filter.tendsto_atTop.1 hexp) (C + 3)] with k hk
      linarith
  obtain ⟨k, hk⟩ := hevent.exists
  have hsingle : cartanModeWork (time k * hX.eigenvalues i) ≤
      ∑ j, cartanModeWork (time k * hX.eigenvalues j) :=
    Finset.single_le_sum (f := fun j ↦ cartanModeWork (time k * hX.eigenvalues j))
      (fun j _ ↦ cartanModeWork_nonneg _)
      (Finset.mem_univ i)
  have hterm : cartanModeWork (time k * hX.eigenvalues i) ≤ C := by
    calc
      cartanModeWork (time k * hX.eigenvalues i) ≤
          ∑ j, cartanModeWork (time k * hX.eigenvalues j) := hsingle
      _ = cartanWork (factorizationMatrixRay X Y (time k)) :=
        (cartanWork_factorizationMatrixRay hX hY (time k)).symm
      _ ≤ C := hC k
  have habs : cartanModeWork |time k * hX.eigenvalues i| =
      cartanModeWork (time k * hX.eigenvalues i) := by
    rcases le_total 0 (time k * hX.eigenvalues i) with hnonneg | hnonpos
    · rw [abs_of_nonneg hnonneg]
    · rw [abs_of_nonpos hnonpos, cartanModeWork_neg]
  have hid := cartanModeWork_add_two |time k * hX.eigenvalues i|
  rw [habs] at hid
  nlinarith [Real.exp_pos (-2 * |time k * hX.eigenvalues i|)]

end

end GaloisForLFunctions.HTGeometry
