import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.HTGeometry.LidskiiSelfAdjoint

/-!
# Vanishing negative spectral mass for the arithmetic dilation limit

The signed greedy spectrum is complete for compact self-adjoint operators.  Its total negative
mass is controlled by trace-norm distance to any positive operator: on each negative eigenvector,
positivity of the comparator bounds the negative eigenvalue by the corresponding diagonal matrix
coefficient of the difference, and the Horn trace-norm inequality sums those coefficients.

Applied to the symmetrized arithmetic dilation matrices, this proves the card's spectral
consequence: trace-norm convergence to the positive arithmetic diagonal forces total negative
spectral mass to vanish.
-/

noncomputable section

open Filter ContinuousLinearMap
open scoped InnerProductSpace

namespace RHTower

/-! ## Hermitian absolutely-projective matrices -/

/-- Matrix coefficient of the canonical nuclear matrix-unit realization. -/
theorem inner_basis_absoluteMatrixOperator_basis
    {M : ℕ × ℕ → ℂ} (hterms : Summable (absoluteMatrixRankOneTerm M))
    (i j : ℕ) :
    inner ℂ (HilbertSchmidt.lpBasis ℕ i)
      (absoluteMatrixOperator M (HilbertSchmidt.lpBasis ℕ j)) = M (i, j) := by
  let φ : (ArithmeticDilationHilbert →L[ℂ] ArithmeticDilationHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ (HilbertSchmidt.lpBasis ℕ i)).comp
      (ContinuousLinearMap.apply ℂ ArithmeticDilationHilbert
        (HilbertSchmidt.lpBasis ℕ j))
  change φ (absoluteMatrixOperator M) = M (i, j)
  rw [absoluteMatrixOperator, φ.map_tsum hterms, tsum_eq_single (i, j)]
  · simp [φ, absoluteMatrixRankOneTerm,
      (HilbertSchmidt.lpBasis ℕ).orthonormal.norm_eq_one]
  · intro p hp
    change φ (absoluteMatrixRankOneTerm M p) = 0
    simp only [φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, absoluteMatrixRankOneTerm, smul_apply,
      InnerProductSpace.rankOne_apply, inner_smul_right]
    have hi := (orthonormal_iff_ite.mp
      (HilbertSchmidt.lpBasis ℕ).orthonormal) i p.1
    have hj := (orthonormal_iff_ite.mp
      (HilbertSchmidt.lpBasis ℕ).orthonormal) p.2 j
    rw [hj, hi]
    by_cases hpi : p.1 = i
    · have hpj : p.2 ≠ j := fun hpj => hp (Prod.ext hpi hpj)
      simp [hpi, hpj]
    · simp [Ne.symm hpi]

/-- A Hermitian matrix-unit expansion is self-adjoint.  This statement is total: if the matrix
unit family is not summable, Lean's total `tsum` is zero; in the summable case its basis matrix is
the given Hermitian matrix. -/
theorem absoluteMatrixOperator_isSelfAdjoint_of_isHermitian
    (M : ℕ × ℕ → ℂ) (hherm : ∀ i j, M (i, j) = star (M (j, i))) :
    IsSelfAdjoint (absoluteMatrixOperator M) := by
  by_cases hterms : Summable (absoluteMatrixRankOneTerm M)
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr
        (HilbertSchmidt.lpBasis ℕ).dense_span) ?_
    rintro x ⟨j, rfl⟩
    apply (HilbertSchmidt.lpBasis ℕ).repr.injective
    apply lp.ext
    funext i
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.adjoint_inner_right,
      inner_basis_absoluteMatrixOperator_basis hterms,
      ← inner_conj_symm,
      inner_basis_absoluteMatrixOperator_basis hterms, hherm]
    simp
  · rw [absoluteMatrixOperator, tsum_eq_zero_of_not_summable hterms]
    exact IsSelfAdjoint.zero _

theorem arithmeticDilationComplexMatrix_isHermitian
    {a : α → ℕ → ℝ} {E : α → ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    (hEsym : ∀ x i j, E x i j = E x j i) (x : α) (i j : ℕ) :
    arithmeticDilationComplexMatrix a E w x (i, j) =
      star (arithmeticDilationComplexMatrix a E w x (j, i)) := by
  by_cases hij : i = j
  · subst j
    simp [arithmeticDilationComplexMatrix, diagMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp [arithmeticDilationComplexMatrix, diagMatrix, hij, hji, hEsym]
    exact Or.inl (add_comm _ _)

theorem arithmeticDilationComplexOperator_isSelfAdjoint
    {a : α → ℕ → ℝ} {E : α → ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    (hEsym : ∀ x i j, E x i j = E x j i) (x : α) :
    IsSelfAdjoint
      (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x)) :=
  absoluteMatrixOperator_isSelfAdjoint_of_isHermitian _
    (arithmeticDilationComplexMatrix_isHermitian hEsym x)

/-! ## Trace-norm control of negative spectral mass -/

/-- Total negative mass of the signed greedy spectrum.  For compact self-adjoint operators this
is the complete negative spectrum with multiplicity, by `exists_sgVal_eq_of_eigenvalue` and the
signed Lidskii exhaustion. -/
def signedGreedyNegativeMass {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : H →L[ℂ] H) : ℝ :=
  ∑' n : ℕ, (ContinuousLinearMap.sgVal S n)⁻

theorem sgVal_negPart_le_norm_inner_sub_of_positive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S T : H →L[ℂ] H) (hT : T.IsPositive) (n : ℕ) :
    (ContinuousLinearMap.sgVal S n)⁻ ≤
      ‖inner ℂ (ContinuousLinearMap.sgVec S n)
        ((S - T) (ContinuousLinearMap.sgVec S n))‖ := by
  by_cases hnonneg : 0 ≤ ContinuousLinearMap.sgVal S n
  · rw [negPart_eq_zero.mpr hnonneg]
    exact norm_nonneg _
  · have hneg : ContinuousLinearMap.sgVal S n < 0 := lt_of_not_ge hnonneg
    rw [negPart_of_nonpos hneg.le]
    let v := ContinuousLinearMap.sgVec S n
    have hq : 0 ≤ (inner ℂ v (T v)).re := hT.re_inner_nonneg_right v
    have hre : (inner ℂ v ((S - T) v)).re =
        ContinuousLinearMap.sgVal S n - (inner ℂ v (T v)).re := by
      simp only [sub_apply, inner_sub_right, ContinuousLinearMap.sgVal, v]
      rfl
    have hrle : (inner ℂ v ((S - T) v)).re ≤ ContinuousLinearMap.sgVal S n := by
      rw [hre]
      linarith
    have hrnonpos : (inner ℂ v ((S - T) v)).re ≤ 0 := hrle.trans hneg.le
    calc
      -ContinuousLinearMap.sgVal S n ≤ -(inner ℂ v ((S - T) v)).re :=
        neg_le_neg hrle
      _ = |(inner ℂ v ((S - T) v)).re| := (abs_of_nonpos hrnonpos).symm
      _ ≤ ‖inner ℂ v ((S - T) v)‖ := Complex.abs_re_le_norm _

/-- Negative spectral mass is 1-Lipschitz at the positive cone in trace norm. -/
theorem signedGreedyNegativeMass_le_traceNorm_sub_of_positive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S T : H →L[ℂ] H} (hT : T.IsPositive)
    (hdiff : MemSchattenClass 1 (S - T)) :
    signedGreedyNegativeMass S ≤ traceNorm H (S - T) := by
  rw [signedGreedyNegativeMass]
  apply Real.tsum_le_of_sum_le (fun n => negPart_nonneg _)
  intro s
  calc
    ∑ n ∈ s, (ContinuousLinearMap.sgVal S n)⁻ ≤
        ∑ n ∈ s, ‖inner ℂ (ContinuousLinearMap.sgVec S n)
          ((S - T) (ContinuousLinearMap.sgVec S n))‖ := by
      exact Finset.sum_le_sum fun n _ =>
        sgVal_negPart_le_norm_inner_sub_of_positive S T hT n
    _ ≤ traceNorm H (S - T) := by
      exact sum_norm_inner_le_traceNorm
        (hdiff.isCompactOperator one_pos) hdiff.one_summable
        (ContinuousLinearMap.norm_sgVec_zero_or_one S)
        (fun _ _ h => ContinuousLinearMap.inner_sgVec_sgVec_of_ne S h)
        (ContinuousLinearMap.norm_sgVec_zero_or_one S)
        (fun _ _ h => ContinuousLinearMap.inner_sgVec_sgVec_of_ne S h) s

/-! ## Arithmetic dilation specialization -/

theorem arithmeticDilationLimitComplexMatrix_eq_diagMul
    (L w : ℕ → ℝ) :
    arithmeticDilationLimitComplexMatrix L w =
      HilbertSchmidt.diagMul (fun k => ((2 * L k * w k : ℝ) : ℂ)) := by
  funext p
  by_cases h : p.1 = p.2 <;>
    simp [arithmeticDilationLimitComplexMatrix, diagMatrix,
      HilbertSchmidt.diagMul, h]

theorem arithmeticDilationLimitComplexOperator_isPositive
    {L w : ℕ → ℝ} (hL0 : ∀ k, 0 ≤ L k) (hw : ∀ k, 0 ≤ w k)
    (hLw : Summable fun k => L k * w k) :
    (absoluteMatrixOperator (arithmeticDilationLimitComplexMatrix L w)).IsPositive := by
  have hnorm : Summable fun k => ‖(((2 * L k * w k : ℝ) : ℂ))‖ := by
    refine (hLw.mul_left 2).congr fun k => ?_
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hL0 k)) (hw k))]
    ring
  rw [arithmeticDilationLimitComplexMatrix_eq_diagMul]
  exact absoluteMatrixOperator_diagMul_isPositive_ofReal _ hnorm
    (fun k => mul_nonneg (mul_nonneg (by norm_num) (hL0 k)) (hw k))

/-- **Vanishing negative spectral mass.**  Under the card's weighted projective hypothesis,
divisor trap, and Gram symmetry, the arithmetic stages are self-adjoint trace-class operators,
the limit is positive trace class, and the full negative eigenvalue mass tends to zero. -/
theorem arithmeticDilation_negativeSpectralMass_tendsto_zero
    {α : Type*} {l : Filter α} {E : α → ℕ → ℕ → ℝ}
    {w L Ω : ℕ → ℝ} {a : α → ℕ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hL0 : ∀ k, 0 ≤ L k) (hΩ : ∀ k, L k ≤ Ω k)
    (ha0 : ∀ x k, 0 ≤ a x k) (haL : ∀ x k, a x k ≤ L k)
    (haev : ∀ k, ∀ᶠ x in l, a x k = L k)
    (hLw : Summable fun k => L k * w k)
    (hEsum : ∀ x, Summable fun p : ℕ × ℕ =>
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|)
    (hEtend : Tendsto (fun x => ∑' p : ℕ × ℕ,
      (Ω p.1 + Ω p.2) * |E x p.1 p.2|) l (nhds 0))
    (hEsym : ∀ x i j, E x i j = E x j i) :
    (∀ x, IsSelfAdjoint
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x))) ∧
      (absoluteMatrixOperator
        (arithmeticDilationLimitComplexMatrix L w)).IsPositive ∧
      Tendsto (fun x => signedGreedyNegativeMass
        (absoluteMatrixOperator (arithmeticDilationComplexMatrix a E w x)))
        l (nhds 0) := by
  obtain ⟨hstage, hlimit, htend⟩ := arithmeticDilation_traceClass_traceNorm_limit
    hw hΩ ha0 haL haev hLw hEsum hEtend
  have hpos := arithmeticDilationLimitComplexOperator_isPositive hL0 hw hLw
  refine ⟨arithmeticDilationComplexOperator_isSelfAdjoint hEsym, hpos, ?_⟩
  refine squeeze_zero (fun _ => tsum_nonneg fun n => negPart_nonneg _)
    (fun x => signedGreedyNegativeMass_le_traceNorm_sub_of_positive hpos
      ((hstage x).one_sub hlimit)) htend

end RHTower

end
