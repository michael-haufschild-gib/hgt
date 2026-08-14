import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHermitianGram
import GaloisForLFunctions.RHTower.SoninCofinalComplexPhaseOddFisherSplice

/-!
# Critical Hardy saturation of the complex Möbius Fisher Gram

The precritical complex-damped Möbius columns together with their completed
Fisher tangent form an actual Hilbert Gram matrix.  Along the canonical
critical schedule, its three blocks converge respectively to the
right-half-plane Cauchy kernel, the full holomorphic Fisher score, and the
exact four-unit Fisher energy.  Entrywise closure of finite positive
semidefinite matrices therefore produces an unconditional boundary Gram.

This is stronger than a diagonal budget: it retains every non-diagonal
complex phase and proves that arithmetic criticality lands on a genuine
Hardy positive kernel with no lost source energy.
-/

open Complex Filter Set Topology
open scoped BigOperators ComplexOrder

noncomputable section

namespace RHTower

/-- Entrywise limits of finite complex positive semidefinite matrices remain
positive semidefinite. -/
theorem posSemidef_of_entrywise_tendsto
    {ι : Type*} [Fintype ι]
    (A : ℕ → Matrix ι ι ℂ) (M : Matrix ι ι ℂ)
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j,
      Tendsto (fun n => A n i j) atTop (nhds (M i j))) :
    M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hstar : Tendsto (fun n => star (A n j i)) atTop
        (nhds (star (M j i))) :=
      (continuous_star.tendsto _).comp (hlim j i)
    apply tendsto_nhds_unique hstar
    apply (hlim i j).congr'
    filter_upwards with n
    exact ((hA n).isHermitian.apply i j).symm
  · intro x
    have hquad : Tendsto
        (fun n => dotProduct (star x) (Matrix.mulVec (A n) x)) atTop
        (nhds (dotProduct (star x) (Matrix.mulVec M x))) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply tendsto_finsetSum
      intro i hi
      apply tendsto_finsetSum
      intro j hj
      exact tendsto_const_nhds.mul ((hlim i j).mul_const (x j))
    exact ge_of_tendsto hquad (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg x)

/-- Universal critical Cauchy kernel selected by the squarefree Möbius
complex clock. -/
def mobiusCriticalUniversalHardyKernel (u v : ℂ) : ℂ :=
  (1 + v + star u)⁻¹

/-- Universal completed Fisher boundary column. -/
def mobiusCriticalUniversalFisherScore (u : ℂ) : ℂ :=
  2 * u / (1 + u) ^ 2

/-- Precritical arithmetic vector packet: complex-damped features followed
by the completed Fisher tangent. -/
def mobiusCriticalComplexPhaseFisherVector
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    Fin n ⊕ Unit → lp (fun _ : ℕ => ℂ) 2
  | Sum.inl i =>
      infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u i) hsigma (hu i)
  | Sum.inr _ => infiniteMobiusCriticalFisherTangentLp sigma hsigma

/-- Actual precritical arithmetic Gram of the phase packet and Fisher
tangent. -/
def mobiusCriticalComplexPhaseFisherGram
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.gram ℂ
    (mobiusCriticalComplexPhaseFisherVector sigma hsigma u hu)

/-- The precritical augmented arithmetic matrix is positive because it is
an actual Hilbert Gram, not a postulated kernel. -/
theorem mobiusCriticalComplexPhaseFisherGram_posSemidef
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    (mobiusCriticalComplexPhaseFisherGram sigma hsigma u hu).PosSemidef :=
  Matrix.posSemidef_gram ℂ
    (mobiusCriticalComplexPhaseFisherVector sigma hsigma u hu)

/-- Exact non-diagonal arithmetic top-left block. -/
theorem mobiusCriticalComplexPhaseFisherGram_topLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (i j : Fin n) :
    mobiusCriticalComplexPhaseFisherGram sigma hsigma u hu
        (Sum.inl i) (Sum.inl j) =
      mobiusCriticalComplexPhaseKernel sigma (u i) (u j) := by
  exact inner_complexDamped_complexDamped_eq_squarefreeBoundaryOverlap
    hsigma (hu i) (hu j)

/-- Exact Fisher boundary row. -/
theorem mobiusCriticalComplexPhaseFisherGram_bottomLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (i : Fin n) :
    mobiusCriticalComplexPhaseFisherGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inl i) =
      GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u i) := by
  change inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u i) hsigma (hu i)) = _
  have hshift : 1 < ((sigma : ℂ) +
      u i * ((sigma - 1 : ℝ) : ℂ)).re := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im]
    have hmul : 0 ≤ (u i).re * (sigma - 1) :=
      mul_nonneg (hu i) (sub_nonneg.mpr hsigma.le)
    nlinarith
  exact inner_fisherTangent_complexDamped_eq_squarefreeFisherScore
    hsigma (hu i) hshift

/-- Exact conjugate Fisher boundary column. -/
theorem mobiusCriticalComplexPhaseFisherGram_topRight
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (i : Fin n) :
    mobiusCriticalComplexPhaseFisherGram sigma hsigma u hu
        (Sum.inl i) (Sum.inr ()) =
      star (GaloisForLFunctions.squarefreeFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u i)) := by
  change inner ℂ
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u i) hsigma (hu i))
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma) = _
  rw [← mobiusCriticalComplexPhaseFisherGram_bottomLeft hsigma u hu i]
  change inner ℂ
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u i) hsigma (hu i))
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma) =
    star (inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (infiniteMobiusCriticalComplexDampedSignedWeightLp
        sigma (u i) hsigma (hu i)))
  exact (inner_conj_symm (𝕜 := ℂ)
    (infiniteMobiusCriticalComplexDampedSignedWeightLp
      sigma (u i) hsigma (hu i))
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).symm

/-- Exact Fisher energy on the final diagonal. -/
theorem mobiusCriticalComplexPhaseFisherGram_bottomRight
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    mobiusCriticalComplexPhaseFisherGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inr ()) =
      (‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 : ℂ) := by
  change inner ℂ (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma) = _
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
    (infiniteMobiusCriticalFisherTangentLp sigma hsigma)

/-- Universal boundary block: Cauchy kernel, conjugate Fisher column, Fisher
row, and exact diagonal energy four. -/
def mobiusCriticalUniversalHardyFisherGram
    {n : ℕ} (u : Fin n → ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.fromBlocks
    (fun i j => mobiusCriticalUniversalHardyKernel (u i) (u j))
    (fun i _ => star (mobiusCriticalUniversalFisherScore (u i)))
    (fun _ j => mobiusCriticalUniversalFisherScore (u j))
    (Matrix.of fun _ _ : Unit => (4 : ℂ))

/-- Every entry of the actual arithmetic Gram converges to the universal
Hardy/Fisher boundary block. -/
theorem tendsto_mobiusCriticalComplexPhaseFisherGram_entry
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re)
    (a b : Fin n ⊕ Unit) :
    Tendsto (fun j =>
      mobiusCriticalComplexPhaseFisherGram
        (soninMobiusCriticalSigmaSequence j)
        (soninMobiusCriticalSigmaSequence_gt_one j) u hu a b)
      atTop (nhds (mobiusCriticalUniversalHardyFisherGram u a b)) := by
  rcases a with i | z <;> rcases b with k | w
  · have hq : 0 ≤ (u k + star (u i)).re := by
      simpa using add_nonneg (hu k) (hu i)
    have h := (tendsto_squarefreeBoundaryOverlap_complexCritical hq).comp
      tendsto_soninMobiusCriticalSigmaSequence
    convert h using 1
    · funext j
      rw [mobiusCriticalComplexPhaseFisherGram_topLeft
        (soninMobiusCriticalSigmaSequence_gt_one j) u hu]
      rfl
    · simp [mobiusCriticalUniversalHardyFisherGram,
        mobiusCriticalUniversalHardyKernel]
      ring
  · have hscore := tendsto_inner_fisherTangent_complexDamped_criticalSequence
      (hu i)
    have hstar := (continuous_star.tendsto _).comp hscore
    convert hstar using 1
    · funext j
      rw [mobiusCriticalComplexPhaseFisherGram_topRight
        (soninMobiusCriticalSigmaSequence_gt_one j) u hu]
      rw [← mobiusCriticalComplexPhaseFisherGram_bottomLeft
        (soninMobiusCriticalSigmaSequence_gt_one j) u hu]
      rfl
    · simp [mobiusCriticalUniversalHardyFisherGram,
        mobiusCriticalUniversalFisherScore]
  · simpa [mobiusCriticalComplexPhaseFisherGram,
      mobiusCriticalComplexPhaseFisherVector,
      mobiusCriticalUniversalHardyFisherGram,
      mobiusCriticalUniversalFisherScore] using
      (tendsto_inner_fisherTangent_complexDamped_criticalSequence (hu k))
  · have hreal := tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq.comp
      tendsto_soninMobiusCriticalSigmaSequence
    have hcomplex := (Complex.continuous_ofReal.tendsto 4).comp hreal
    convert hcomplex using 1
    · funext j
      rw [mobiusCriticalComplexPhaseFisherGram_bottomRight
        (soninMobiusCriticalSigmaSequence_gt_one j) u hu]
      simp only [Function.comp_apply,
        dif_pos (soninMobiusCriticalSigmaSequence_gt_one j)]
      push_cast
      congr
    · simp [mobiusCriticalUniversalHardyFisherGram]

/-- **Critical four-unit Hardy saturation.**  Every finite packet of inward
complex Möbius nodes has an unconditional positive universal boundary Gram.
The bottom diagonal is exactly four, while the entire non-diagonal source
geometry survives. -/
theorem mobiusCriticalUniversalHardyFisherGram_posSemidef
    {n : ℕ} (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    (mobiusCriticalUniversalHardyFisherGram u).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (fun j => mobiusCriticalComplexPhaseFisherGram
      (soninMobiusCriticalSigmaSequence j)
      (soninMobiusCriticalSigmaSequence_gt_one j) u hu)
  · intro j
    exact mobiusCriticalComplexPhaseFisherGram_posSemidef
      (soninMobiusCriticalSigmaSequence j)
      (soninMobiusCriticalSigmaSequence_gt_one j) u hu
  · exact tendsto_mobiusCriticalComplexPhaseFisherGram_entry u hu

/-- Two critical Hardy nodes at separation `t`. -/
def mobiusCriticalHardySaturationNodes (t : ℝ) : Fin 2 → ℂ :=
  ![(0 : ℂ), (t : ℂ)]

/-- Difference-quotient coefficients approximating the completed Fisher
source from the two Hardy nodes `0,t`; the last coefficient subtracts the
boundary source itself. -/
def mobiusCriticalHardySaturationCoefficients
    (t : ℝ) : Fin 2 ⊕ Unit → ℂ
  | Sum.inl i =>
      ![((2 - 2 / t : ℝ) : ℂ), ((2 / t : ℝ) : ℂ)] i
  | Sum.inr _ => -1

/-- Exact two-node residual.  It is a quadratic form of the universal
boundary Gram, so the formula measures the squared Hardy distance from the
Fisher source to its difference-quotient approximant. -/
theorem mobiusCriticalHardySaturation_quadratic_eq
    {t : ℝ} (ht : 0 < t) :
    dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGram
            (mobiusCriticalHardySaturationNodes t))
          (mobiusCriticalHardySaturationCoefficients t)) =
      ((8 * t ^ 2 * (2 * t + 3) /
        ((1 + t) ^ 2 * (1 + 2 * t)) : ℝ) : ℂ) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : (1 + t : ℝ) ≠ 0 := by positivity
  have ht2 : (1 + 2 * t : ℝ) ≠ 0 := by positivity
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    mobiusCriticalHardySaturationCoefficients,
    mobiusCriticalHardySaturationNodes,
    mobiusCriticalUniversalHardyFisherGram,
    mobiusCriticalUniversalHardyKernel,
    mobiusCriticalUniversalFisherScore]
  simp only [map_ofNat]
  field_simp [ht0, ht1, ht2]
  ring

/-- The two-node residual tends to zero at the critical Hardy node.  Thus
the four-unit source lies in the closure of the Cauchy-feature span; the
bottom diagonal has no positive orthogonal slack. -/
theorem tendsto_mobiusCriticalHardySaturation_quadratic_zero :
    Tendsto (fun t : ℝ =>
      dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGram
            (mobiusCriticalHardySaturationNodes t))
          (mobiusCriticalHardySaturationCoefficients t)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hformula : Tendsto (fun t : ℝ =>
      ((8 * t ^ 2 * (2 * t + 3) /
        ((1 + t) ^ 2 * (1 + 2 * t)) : ℝ) : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hn : ContinuousAt (fun t : ℝ =>
        8 * t ^ 2 * (2 * t + 3)) 0 := by fun_prop
    have hd : ContinuousAt (fun t : ℝ =>
        (1 + t) ^ 2 * (1 + 2 * t)) 0 := by fun_prop
    have hr : ContinuousAt (fun t : ℝ =>
        8 * t ^ 2 * (2 * t + 3) /
          ((1 + t) ^ 2 * (1 + 2 * t))) 0 :=
      hn.div hd (by norm_num)
    have hc : ContinuousAt (fun t : ℝ =>
        ((8 * t ^ 2 * (2 * t + 3) /
          ((1 + t) ^ 2 * (1 + 2 * t)) : ℝ) : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt.comp hr
    change Tendsto (fun t : ℝ =>
      ((8 * t ^ 2 * (2 * t + 3) /
        ((1 + t) ^ 2 * (1 + 2 * t)) : ℝ) : ℂ))
      (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
    simpa using hc.tendsto.mono_left inf_le_left
  apply hformula.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (mobiusCriticalHardySaturation_quadratic_eq ht).symm

/-- Universal Hardy/Fisher block with a variable real bottom budget. -/
def mobiusCriticalUniversalHardyFisherGramWithBudget
    {n : ℕ} (u : Fin n → ℂ) (budget : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherGram u +
    Matrix.single (Sum.inr ()) (Sum.inr ()) ((budget : ℂ) - 4)

theorem mobiusCriticalUniversalHardyFisherGramWithBudget_four
    {n : ℕ} (u : Fin n → ℂ) :
    mobiusCriticalUniversalHardyFisherGramWithBudget u 4 =
      mobiusCriticalUniversalHardyFisherGram u := by
  simp [mobiusCriticalUniversalHardyFisherGramWithBudget]

/-- Exact rank-one effect of changing only the final diagonal budget. -/
theorem mobiusCriticalHardySaturation_budget_quadratic_eq_four_add
    (t budget : ℝ) :
    dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes t) budget)
          (mobiusCriticalHardySaturationCoefficients t)) =
      dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGram
            (mobiusCriticalHardySaturationNodes t))
          (mobiusCriticalHardySaturationCoefficients t)) +
        ((budget : ℂ) - 4) := by
  rw [mobiusCriticalUniversalHardyFisherGramWithBudget,
    Matrix.add_mulVec, dotProduct_add]
  simp [Matrix.single_mulVec_eq,
    mobiusCriticalHardySaturationCoefficients]

/-- Lowering the bottom budget changes the saturation quadratic by exactly
`budget - 4`. -/
theorem mobiusCriticalHardySaturation_budget_quadratic_eq
    {t budget : ℝ} (ht : 0 < t) :
    dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes t) budget)
          (mobiusCriticalHardySaturationCoefficients t)) =
      ((8 * t ^ 2 * (2 * t + 3) /
          ((1 + t) ^ 2 * (1 + 2 * t)) + budget - 4 : ℝ) : ℂ) := by
  rw [mobiusCriticalHardySaturation_budget_quadratic_eq_four_add,
    mobiusCriticalHardySaturation_quadratic_eq ht]
  push_cast
  ring

/-- Positive two-node scales tending to the critical node. -/
def mobiusCriticalHardySaturationScale (j : ℕ) : ℝ :=
  1 / ((j : ℝ) + 1)

theorem mobiusCriticalHardySaturationScale_pos (j : ℕ) :
    0 < mobiusCriticalHardySaturationScale j := by
  rw [mobiusCriticalHardySaturationScale]
  positivity

theorem tendsto_mobiusCriticalHardySaturationScale :
    Tendsto mobiusCriticalHardySaturationScale atTop
      (nhdsWithin 0 (Ioi 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [mobiusCriticalHardySaturationScale] using
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall
      mobiusCriticalHardySaturationScale_pos

/-- Every strict reduction below four is detected by a finite two-node
packet: its augmented quadratic form becomes negative. -/
theorem exists_mobiusCriticalHardyFisherGramWithBudget_quadratic_neg
    {budget : ℝ} (hbudget : budget < 4) :
    ∃ t : ℝ, 0 < t ∧
      (dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes t) budget)
          (mobiusCriticalHardySaturationCoefficients t))).re < 0 := by
  have hzero := tendsto_mobiusCriticalHardySaturation_quadratic_zero.comp
    tendsto_mobiusCriticalHardySaturationScale
  have hshift := hzero.add_const ((budget - 4 : ℝ) : ℂ)
  have hshift' : Tendsto (fun j =>
      ((fun t =>
        dotProduct (star (mobiusCriticalHardySaturationCoefficients t))
          (Matrix.mulVec
            (mobiusCriticalUniversalHardyFisherGram
              (mobiusCriticalHardySaturationNodes t))
            (mobiusCriticalHardySaturationCoefficients t)))
        (mobiusCriticalHardySaturationScale j) +
          ((budget - 4 : ℝ) : ℂ)))
      atTop (nhds ((budget - 4 : ℝ) : ℂ)) := by
    simpa using hshift
  have hbudgetC : (((budget - 4 : ℝ) : ℂ)).re < 0 := by
    simpa using sub_neg.mpr hbudget
  have hbudgetTend : Tendsto (fun j =>
      dotProduct (star
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j)))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) budget)
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j))))
      atTop (nhds ((budget - 4 : ℝ) : ℂ)) := by
    apply hshift'.congr'
    filter_upwards with j
    exact (mobiusCriticalHardySaturation_budget_quadratic_eq_four_add
      (mobiusCriticalHardySaturationScale j) budget).symm
  have hre : Tendsto (fun j =>
      (dotProduct (star
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j)))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) budget)
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j)))).re)
      atTop (nhds (((budget - 4 : ℝ) : ℂ).re)) := by
    exact (Complex.continuous_re.tendsto _).comp hbudgetTend
  have hevent : ∀ᶠ j : ℕ in atTop,
      (dotProduct (star
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j)))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) budget)
          (mobiusCriticalHardySaturationCoefficients
            (mobiusCriticalHardySaturationScale j)))).re < 0 :=
    hre.eventually (Iio_mem_nhds hbudgetC)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨mobiusCriticalHardySaturationScale N,
    mobiusCriticalHardySaturationScale_pos N, hN N le_rfl⟩

/-- **Sharp four-unit minimality.**  If every inward finite packet remains
positive for one common bottom budget, that budget is at least four. -/
theorem four_le_of_all_mobiusCriticalHardyFisherGramWithBudget_posSemidef
    {budget : ℝ}
    (hpos : ∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusCriticalUniversalHardyFisherGramWithBudget u budget).PosSemidef) :
    4 ≤ budget := by
  by_contra hnot
  have hbudget : budget < 4 := lt_of_not_ge hnot
  obtain ⟨t, ht, hneg⟩ :=
    exists_mobiusCriticalHardyFisherGramWithBudget_quadratic_neg hbudget
  have hnodes : ∀ i, 0 ≤ (mobiusCriticalHardySaturationNodes t i).re := by
    intro i
    fin_cases i <;> simp [mobiusCriticalHardySaturationNodes, ht.le]
  have hnonneg :=
    (hpos (mobiusCriticalHardySaturationNodes t) hnodes).dotProduct_mulVec_nonneg
      (mobiusCriticalHardySaturationCoefficients t)
  rw [RCLike.le_iff_re_im] at hnonneg
  exact (not_lt_of_ge hnonneg.1) hneg

/-- The escaped-mass Hardy profile based at the critical source node. -/
def mobiusCriticalUniversalHardyMassProfile (u : ℂ) : ℂ :=
  (1 + u)⁻¹

/-- The mass profile is exactly the Cauchy feature at node zero. -/
theorem mobiusCriticalUniversalHardyMassProfile_eq_kernel_zero (u : ℂ) :
    mobiusCriticalUniversalHardyMassProfile u =
      mobiusCriticalUniversalHardyKernel 0 u := by
  simp [mobiusCriticalUniversalHardyMassProfile,
    mobiusCriticalUniversalHardyKernel]

/-- Universal boundary block after adding an escaped-mass component `d` to
the Fisher cross term while keeping the bottom budget fixed at four. -/
def mobiusCriticalUniversalHardyFisherMassPerturbedGram
    {n : ℕ} (u : Fin n → ℂ) (d : ℂ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.fromBlocks
    (fun i j => mobiusCriticalUniversalHardyKernel (u i) (u j))
    (fun i _ => star (mobiusCriticalUniversalFisherScore (u i) +
      d * mobiusCriticalUniversalHardyMassProfile (u i)))
    (fun _ j => mobiusCriticalUniversalFisherScore (u j) +
      d * mobiusCriticalUniversalHardyMassProfile (u j))
    (Matrix.of fun _ _ : Unit => (4 : ℂ))

/-- The two-node Fisher approximant translated by the exact source feature
which realizes the mass cross term. -/
def mobiusCriticalHardyMassSaturationCoefficients
    (t : ℝ) (d : ℂ) : Fin 2 ⊕ Unit → ℂ
  | Sum.inl i =>
      ![((2 - 2 / t : ℝ) : ℂ) + star d, ((2 / t : ℝ) : ℂ)] i
  | Sum.inr _ => -1

/-- Exact escaped-mass deficit.  Translating the Fisher column by the mass
feature costs `|d|²`, but the saturated four-unit diagonal supplies no such
energy. -/
theorem mobiusCriticalHardyMassSaturation_quadratic_eq
    {t : ℝ} (ht : 0 < t) (d : ℂ) :
    dotProduct (star (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes t) d)
          (mobiusCriticalHardyMassSaturationCoefficients t d)) =
      ((8 * t ^ 2 * (2 * t + 3) /
        ((1 + t) ^ 2 * (1 + 2 * t)) : ℝ) : ℂ) -
        (Complex.normSq d : ℂ) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have ht1 : (1 + t : ℝ) ≠ 0 := by positivity
  have ht2 : (1 + 2 * t : ℝ) ≠ 0 := by positivity
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_two,
    mobiusCriticalHardyMassSaturationCoefficients,
    mobiusCriticalHardySaturationNodes,
    mobiusCriticalUniversalHardyFisherMassPerturbedGram,
    mobiusCriticalUniversalHardyKernel,
    mobiusCriticalUniversalFisherScore,
    mobiusCriticalUniversalHardyMassProfile]
  simp only [map_ofNat]
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [ht0, ht1, ht2]
  ring

/-- Every nonzero mass perturbation has asymptotic quadratic form
`-|d|²` along the two-node saturation packet. -/
theorem tendsto_mobiusCriticalHardyMassSaturation_quadratic
    (d : ℂ) :
    Tendsto (fun t : ℝ =>
      dotProduct (star (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes t) d)
          (mobiusCriticalHardyMassSaturationCoefficients t d)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (-((Complex.normSq d : ℝ) : ℂ))) := by
  have hbase :=
    tendsto_mobiusCriticalHardySaturation_quadratic_zero.sub_const
      (Complex.normSq d : ℂ)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [mobiusCriticalHardyMassSaturation_quadratic_eq ht d,
    mobiusCriticalHardySaturation_quadratic_eq ht]

/-- A nonzero escaped-mass component is detected by a finite inward packet:
the fixed four-unit boundary block is not positive semidefinite. -/
theorem exists_mobiusCriticalHardyFisherMassPerturbed_quadratic_neg
    {d : ℂ} (hd : d ≠ 0) :
    ∃ t : ℝ, 0 < t ∧
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes t) d)
          (mobiusCriticalHardyMassSaturationCoefficients t d))).re < 0 := by
  have hcomplex :=
    tendsto_mobiusCriticalHardyMassSaturation_quadratic d |>.comp
      tendsto_mobiusCriticalHardySaturationScale
  have hre : Tendsto (fun j =>
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) d)
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))).re)
      atTop (nhds (-Complex.normSq d)) := by
    simpa using (Complex.continuous_re.tendsto _).comp hcomplex
  have hlim : -Complex.normSq d < 0 :=
    neg_neg_of_pos (Complex.normSq_pos.mpr hd)
  have hevent : ∀ᶠ j : ℕ in atTop,
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) d)
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))).re < 0 :=
    hre.eventually (Iio_mem_nhds hlim)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨mobiusCriticalHardySaturationScale N,
    mobiusCriticalHardySaturationScale_pos N, hN N le_rfl⟩

/-- Two-node rigidity already suffices: positivity need not be postulated on
the whole right half-plane packet category. -/
theorem eq_zero_of_all_twoNode_mobiusCriticalHardyFisherMassPerturbed_posSemidef
    {d : ℂ}
    (hpos : ∀ t : ℝ, 0 < t →
      (mobiusCriticalUniversalHardyFisherMassPerturbedGram
        (mobiusCriticalHardySaturationNodes t) d).PosSemidef) :
    d = 0 := by
  by_contra hd
  obtain ⟨t, ht, hneg⟩ :=
    exists_mobiusCriticalHardyFisherMassPerturbed_quadratic_neg hd
  have hnonneg := (hpos t ht).dotProduct_mulVec_nonneg
    (mobiusCriticalHardyMassSaturationCoefficients t d)
  rw [RCLike.le_iff_re_im] at hnonneg
  exact (not_lt_of_ge hnonneg.1) hneg

/-- Mass-perturbed boundary block with an arbitrary real bottom budget. -/
def mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
    {n : ℕ} (u : Fin n → ℂ) (d : ℂ) (budget : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  mobiusCriticalUniversalHardyFisherMassPerturbedGram u d +
    Matrix.single (Sum.inr ()) (Sum.inr ()) ((budget : ℂ) - 4)

/-- Changing only the bottom budget contributes exactly `budget - 4` to
the translated mass-saturation quadratic. -/
theorem mobiusCriticalHardyMassSaturation_budget_quadratic_eq_four_add
    (t budget : ℝ) (d : ℂ) :
    dotProduct (star (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes t) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients t d)) =
      dotProduct (star (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGram
            (mobiusCriticalHardySaturationNodes t) d)
          (mobiusCriticalHardyMassSaturationCoefficients t d)) +
        ((budget : ℂ) - 4) := by
  rw [mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget,
    Matrix.add_mulVec, dotProduct_add]
  simp [Matrix.single_mulVec_eq,
    mobiusCriticalHardyMassSaturationCoefficients]

/-- Exact quadratic with both escaped-mass coefficient and variable bottom
budget. -/
theorem mobiusCriticalHardyMassSaturation_budget_quadratic_eq
    {t : ℝ} (ht : 0 < t) (d : ℂ) (budget : ℝ) :
    dotProduct (star (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes t) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients t d)) =
      ((8 * t ^ 2 * (2 * t + 3) /
        ((1 + t) ^ 2 * (1 + 2 * t)) + budget - 4 : ℝ) : ℂ) -
        (Complex.normSq d : ℂ) := by
  rw [mobiusCriticalHardyMassSaturation_budget_quadratic_eq_four_add,
    mobiusCriticalHardyMassSaturation_quadratic_eq ht d]
  push_cast
  ring

/-- If the budget is smaller than `4 + |d|²`, a finite two-node packet
detects a negative quadratic form. -/
theorem exists_mobiusCriticalHardyFisherMassPerturbedWithBudget_quadratic_neg
    {d : ℂ} {budget : ℝ}
    (hbudget : budget < 4 + Complex.normSq d) :
    ∃ t : ℝ, 0 < t ∧
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients t d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes t) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients t d))).re < 0 := by
  have hmass :=
    tendsto_mobiusCriticalHardyMassSaturation_quadratic d |>.comp
      tendsto_mobiusCriticalHardySaturationScale
  have hshift := hmass.add_const ((budget - 4 : ℝ) : ℂ)
  have htotal : Tendsto (fun j =>
      dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d)))
      atTop
      (nhds (((budget - 4 - Complex.normSq d : ℝ) : ℂ))) := by
    have hshift' : Tendsto (fun j =>
        dotProduct (star
            (mobiusCriticalHardyMassSaturationCoefficients
              (mobiusCriticalHardySaturationScale j) d))
          (Matrix.mulVec
            (mobiusCriticalUniversalHardyFisherMassPerturbedGram
              (mobiusCriticalHardySaturationNodes
                (mobiusCriticalHardySaturationScale j)) d)
            (mobiusCriticalHardyMassSaturationCoefficients
              (mobiusCriticalHardySaturationScale j) d)) +
          ((budget - 4 : ℝ) : ℂ))
        atTop
        (nhds (-((Complex.normSq d : ℝ) : ℂ) +
          ((budget - 4 : ℝ) : ℂ))) := by
      simpa using hshift
    apply hshift'.congr'
    · filter_upwards with j
      exact
        (mobiusCriticalHardyMassSaturation_budget_quadratic_eq_four_add
          (mobiusCriticalHardySaturationScale j) budget d).symm
    · push_cast
      ring
  have hre : Tendsto (fun j =>
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))).re)
      atTop (nhds (budget - 4 - Complex.normSq d)) := by
    simpa using (Complex.continuous_re.tendsto _).comp htotal
  have hlim : budget - 4 - Complex.normSq d < 0 := by
    linarith
  have hevent : ∀ᶠ j : ℕ in atTop,
      (dotProduct (star
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))
        (Matrix.mulVec
          (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
            (mobiusCriticalHardySaturationNodes
              (mobiusCriticalHardySaturationScale j)) d budget)
          (mobiusCriticalHardyMassSaturationCoefficients
            (mobiusCriticalHardySaturationScale j) d))).re < 0 :=
    hre.eventually (Iio_mem_nhds hlim)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨mobiusCriticalHardySaturationScale N,
    mobiusCriticalHardySaturationScale_pos N, hN N le_rfl⟩

/-- **Exact curvature toll.**  Positivity on only canonical two-node
packets forces bottom budget at least `4 + |d|²`. -/
theorem four_add_normSq_le_of_all_twoNode_massPerturbedWithBudget_posSemidef
    {d : ℂ} {budget : ℝ}
    (hpos : ∀ t : ℝ, 0 < t →
      (mobiusCriticalUniversalHardyFisherMassPerturbedGramWithBudget
        (mobiusCriticalHardySaturationNodes t) d budget).PosSemidef) :
    4 + Complex.normSq d ≤ budget := by
  by_contra hnot
  have hbudget : budget < 4 + Complex.normSq d := lt_of_not_ge hnot
  obtain ⟨t, ht, hneg⟩ :=
    exists_mobiusCriticalHardyFisherMassPerturbedWithBudget_quadratic_neg
      hbudget
  have hnonneg := (hpos t ht).dotProduct_mulVec_nonneg
    (mobiusCriticalHardyMassSaturationCoefficients t d)
  rw [RCLike.le_iff_re_im] at hnonneg
  exact (not_lt_of_ge hnonneg.1) hneg

/-- **Mass-mode rigidity at the saturated boundary.**  If every finite
inward packet with a common escaped-mass coefficient remains positive at
the fixed four-unit budget, that coefficient is zero. -/
theorem eq_zero_of_all_mobiusCriticalHardyFisherMassPerturbed_posSemidef
    {d : ℂ}
    (hpos : ∀ {n : ℕ} (u : Fin n → ℂ),
      (∀ i, 0 ≤ (u i).re) →
      (mobiusCriticalUniversalHardyFisherMassPerturbedGram u d).PosSemidef) :
    d = 0 := by
  by_contra hd
  obtain ⟨t, ht, hneg⟩ :=
    exists_mobiusCriticalHardyFisherMassPerturbed_quadratic_neg hd
  have hnodes : ∀ i, 0 ≤ (mobiusCriticalHardySaturationNodes t i).re := by
    intro i
    fin_cases i <;> simp [mobiusCriticalHardySaturationNodes, ht.le]
  have hnonneg :=
    (hpos (mobiusCriticalHardySaturationNodes t) hnodes).dotProduct_mulVec_nonneg
      (mobiusCriticalHardyMassSaturationCoefficients t d)
  rw [RCLike.le_iff_re_im] at hnonneg
  exact (not_lt_of_ge hnonneg.1) hneg

end RHTower
