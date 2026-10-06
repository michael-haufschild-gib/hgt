import GaloisForLFunctions.HTGeometry.FramePurificationPartialTrace
import GaloisForLFunctions.HTGeometry.GradedRowSynthesis
import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearDefect
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift
import GaloisForLFunctions.RHTower.TraceNormBound

/-!
# Purity of a unit-mass frame operator

For a square-summable family `α` in a Hilbert space with `∑ ‖α_i‖² = 1`, the frame operator
`T = ∑ |α_i⟩⟨α_i|` is positive and trace class with `Tr T = ‖T‖₁ = 1`, and

* `Tr T² = ∑_k ∑_i |⟨α_i, α_k⟩|²`;
* `1 - Tr T² = ∑_k ∑_i (‖α_i‖² ‖α_k‖² - |⟨α_i, α_k⟩|²)`, a sum of nonnegative Gram determinants
  `det [[⟨a,a⟩, ⟨a,b⟩], [⟨b,a⟩, ⟨b,b⟩]]`;
* `‖T‖² ≤ Tr T²`.

The trace of `T²` is the squared Hilbert–Schmidt norm of the right Gram `W*W` of the synthesis
`W`, whose matrix entries are the inner products `⟨α_i, α_k⟩`.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {ι : Type*} {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- The Gram determinant `‖a‖²‖b‖² - |⟨a,b⟩|²`. -/
def frameGramDeterminant (a b : K) : ℝ := ‖a‖ ^ 2 * ‖b‖ ^ 2 - ‖⟪a, b⟫_ℂ‖ ^ 2

omit [CompleteSpace K] in
theorem frameGramDeterminant_nonneg (a b : K) : 0 ≤ frameGramDeterminant a b := by
  rw [frameGramDeterminant, sub_nonneg, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a b) 2

omit [CompleteSpace K] in
/-- The Gram determinant is the determinant of the `2 × 2` Gram matrix. -/
theorem frameGramDeterminant_eq_det (a b : K) :
    ((frameGramDeterminant a b : ℝ) : ℂ) =
      Matrix.det !![⟪a, a⟫_ℂ, ⟪a, b⟫_ℂ; ⟪b, a⟫_ℂ, ⟪b, b⟫_ℂ] := by
  have hab : ⟪a, b⟫_ℂ * ⟪b, a⟫_ℂ = ((‖⟪a, b⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [show ⟪b, a⟫_ℂ = (starRingEnd ℂ) ⟪a, b⟫_ℂ from (inner_conj_symm b a).symm,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have ha : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hb : ⟪b, b⟫_ℂ = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [Matrix.det_fin_two_of, ha, hb, hab, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    frameGramDeterminant]

section Frame

variable {α : ι → K}

omit [CompleteSpace K] in
theorem norm_inner_frame_sq_le (i k : ι) :
    ‖⟪α i, α k⟫_ℂ‖ ^ 2 ≤ ‖α i‖ ^ 2 * ‖α k‖ ^ 2 := by
  have h := frameGramDeterminant_nonneg (α i) (α k)
  rw [frameGramDeterminant] at h
  linarith

variable (hα : Summable fun i => ‖α i‖ ^ 2)
include hα

theorem frameOperator_isPositive [DecidableEq ι] : (frameOperator α).IsPositive := by
  rw [frameOperator_eq_leftGram hα]
  exact isPositive_self_comp_adjoint _

theorem opTrace_frameOperator : opTrace (frameOperator α) = ((∑' i, ‖α i‖ ^ 2 : ℝ) : ℂ) := by
  have h := opTrace_frameOperator_comp hα (ContinuousLinearMap.id ℂ K)
  rw [comp_id] at h
  rw [h, Complex.ofReal_tsum]
  refine tsum_congr fun i => ?_
  rw [id_apply, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem traceNorm_frameOperator [DecidableEq ι] :
    traceNorm K (frameOperator α) = ∑' i, ‖α i‖ ^ 2 := by
  rw [traceNorm_eq_re_opTrace_of_isPositive (frameOperator_memSchattenClass_one hα)
    (frameOperator_isPositive hα), opTrace_frameOperator hα, Complex.ofReal_re]

omit [CompleteSpace K] in
theorem summable_inner_frame_sq (k : ι) :
    Summable fun i => ‖⟪α i, α k⟫_ℂ‖ ^ 2 :=
  (hα.mul_right (‖α k‖ ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _)
    fun i => norm_inner_frame_sq_le i k

/-- `Tr T² = ∑_k ∑_i |⟨α_i, α_k⟩|²`. -/
theorem opTrace_frameOperator_sq [DecidableEq ι] :
    opTrace (frameOperator α ∘L frameOperator α) =
      ((∑' k, ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  set W := squareSummableSynthesis α hα
  have hW : IsHilbertSchmidt W := squareSummableSynthesis_isHilbertSchmidt hα
  set G := adjoint W ∘L W
  have hG : IsHilbertSchmidt G := hW.comp_left (adjoint W)
  have hB : IsHilbertSchmidt (adjoint W ∘L (W ∘L adjoint W)) :=
    (hW.adjoint.comp_left W).comp_left (adjoint W)
  rw [frameOperator_eq_leftGram hα]
  have hcyc : opTrace ((W ∘L adjoint W) ∘L (W ∘L adjoint W)) = opTrace (G ∘L G) := by
    rw [show (W ∘L adjoint W) ∘L (W ∘L adjoint W) = W ∘L (adjoint W ∘L (W ∘L adjoint W)) by
      simp only [comp_assoc], opTrace_comp_comm hW hB]
    simp only [G, comp_assoc]
  rw [hcyc]
  have hGsa : adjoint G = G := by simp [G, adjoint_comp]
  rw [show G ∘L G = adjoint G ∘L G by rw [hGsa], opTrace_adjoint_comp_self,
    hsInner_self_eq_ofReal_hsNormSq', hsNormSq_eq hG (HilbertSchmidt.lpBasis ι)]
  congr 1
  refine tsum_congr fun k => ?_
  rw [HilbertSchmidt.lpBasis_apply]
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (G (lp.single 2 k 1))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [h]
  refine tsum_congr fun i => ?_
  have he := inner_single_rightGram_single hα i k
  rw [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at he
  simp only [G]
  rw [he]

omit [CompleteSpace K] in
theorem tsum_inner_frame_sq_le (hα1 : ∑' i, ‖α i‖ ^ 2 = 1) (k : ι) :
    ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 ≤ ‖α k‖ ^ 2 := by
  calc ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 ≤ ∑' i, ‖α i‖ ^ 2 * ‖α k‖ ^ 2 :=
        (summable_inner_frame_sq hα k).tsum_le_tsum (fun i => norm_inner_frame_sq_le i k)
          (hα.mul_right _)
    _ = ‖α k‖ ^ 2 := by rw [tsum_mul_right, hα1, one_mul]

omit [CompleteSpace K] in
theorem summable_tsum_inner_frame_sq (hα1 : ∑' i, ‖α i‖ ^ 2 = 1) :
    Summable fun k => ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 :=
  hα.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => sq_nonneg _)
    (tsum_inner_frame_sq_le hα hα1)

omit [CompleteSpace K] in
theorem summable_frameGramDeterminant (k : ι) :
    Summable fun i => frameGramDeterminant (α i) (α k) :=
  (hα.mul_right _).sub (summable_inner_frame_sq hα k)

omit [CompleteSpace K] in
theorem tsum_frameGramDeterminant_eq (hα1 : ∑' i, ‖α i‖ ^ 2 = 1) (k : ι) :
    ∑' i, frameGramDeterminant (α i) (α k) = ‖α k‖ ^ 2 - ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 := by
  simp only [frameGramDeterminant]
  rw [(hα.mul_right _).tsum_sub (summable_inner_frame_sq hα k), tsum_mul_right, hα1, one_mul]

omit [CompleteSpace K] in
theorem summable_tsum_frameGramDeterminant (hα1 : ∑' i, ‖α i‖ ^ 2 = 1) :
    Summable fun k => ∑' i, frameGramDeterminant (α i) (α k) := by
  refine hα.of_nonneg_of_le (fun k => tsum_nonneg fun i => frameGramDeterminant_nonneg _ _)
    fun k => ?_
  rw [tsum_frameGramDeterminant_eq hα hα1]
  exact sub_le_self _ (tsum_nonneg fun _ => sq_nonneg _)

omit [CompleteSpace K] in
/-- `1 - ∑_k ∑_i |⟨α_i, α_k⟩|² = ∑_k ∑_i (‖α_i‖² ‖α_k‖² - |⟨α_i, α_k⟩|²)`. -/
theorem one_sub_framePurity (hα1 : ∑' i, ‖α i‖ ^ 2 = 1) :
    1 - ∑' k, ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 =
      ∑' k, ∑' i, frameGramDeterminant (α i) (α k) := by
  simp_rw [tsum_frameGramDeterminant_eq hα hα1]
  rw [hα.tsum_sub (summable_tsum_inner_frame_sq hα hα1), hα1]

/-- `‖T‖² ≤ Tr T²`. -/
theorem norm_frameOperator_sq_le [DecidableEq ι] :
    ‖frameOperator α‖ ^ 2 ≤ ∑' k, ∑' i, ‖⟪α i, α k⟫_ℂ‖ ^ 2 := by
  have hT := frameOperator_isPositive hα
  have hsa : adjoint (frameOperator α) = frameOperator α := hT.isSelfAdjoint.adjoint_eq
  have hsq : ‖frameOperator α‖ ^ 2 = ‖frameOperator α ∘L frameOperator α‖ := by
    rw [sq, ← ContinuousLinearMap.norm_adjoint_comp_self (frameOperator α), hsa]
  set W := squareSummableSynthesis α hα
  have hW : IsHilbertSchmidt W := squareSummableSynthesis_isHilbertSchmidt hα
  have hmem : MemSchattenClass 1 (frameOperator α ∘L frameOperator α) := by
    rw [frameOperator_eq_leftGram hα, comp_assoc]
    exact memSchattenClass_one_comp hW
      ((hW.adjoint.comp_left W).comp_left (adjoint W) |> fun h => by
        simpa only [comp_assoc] using h)
  have hpos : (frameOperator α ∘L frameOperator α).IsPositive := by
    rw [show frameOperator α ∘L frameOperator α = adjoint (frameOperator α) ∘L frameOperator α by
      rw [hsa]]
    exact isPositive_adjoint_comp_self _
  have htr := traceNorm_eq_re_opTrace_of_isPositive hmem hpos
  rw [opTrace_frameOperator_sq hα, Complex.ofReal_re] at htr
  rw [hsq, ← htr]
  exact norm_le_traceNorm_of_memSchattenClass_one hmem

end Frame

/-! ### The positive square root -/

/-- The positive square root `√A` of an operator (continuous functional calculus). -/
def positiveSqrt (A : K →L[ℂ] K) : K →L[ℂ] K := CFC.sqrt A

theorem positiveSqrt_isPositive (A : K →L[ℂ] K) : (positiveSqrt A).IsPositive :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).1 (CFC.sqrt_nonneg A)

theorem positiveSqrt_comp_self {A : K →L[ℂ] K} (hA : A.IsPositive) :
    positiveSqrt A ∘L positiveSqrt A = A :=
  CFC.sqrt_mul_sqrt_self A ((ContinuousLinearMap.nonneg_iff_isPositive A).2 hA)

end GaloisForLFunctions.HTGeometry
