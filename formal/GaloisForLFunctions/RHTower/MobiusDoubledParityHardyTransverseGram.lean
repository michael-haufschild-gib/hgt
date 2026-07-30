import GaloisForLFunctions.RHTower.MobiusParityLikelihoodHardyGram
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentHilbertLift
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Doubled Möbius parity separates the Hardy father space from the four-unit detail

The critical Möbius likelihood family is total in its one-carrier Hardy limit, so a bounded
transport preserving every father vector cannot assign an independent Ward column to its tangent.
The parity-doubled carrier removes that rigidity.

We construct the doubled father vector from a damped signed likelihood and its parity transform.
The doubled detail vector uses the Fisher tangent with the opposite parity sign.  Möbius parity is
an isometry on squarefree support, hence:

* father/father inner products are exactly the original likelihood Gram;
* the detail is exactly orthogonal to every father vector, before taking a limit;
* the detail squared norm is exactly the Fisher energy and tends to four.

Thus the critical source Gram is the direct sum of the Hardy Cauchy Gram and a transverse
four-unit channel.  This is the source space on which a genuinely non-diagonal Gamma/Julia defect
transport must act.
-/

open Complex Filter Set
open scoped BigOperators ComplexOrder ENNReal NNReal Topology lp

namespace RHTower

noncomputable section

/-- Möbius parity applied to the completed critical Fisher tangent. -/
def infiniteMobiusCriticalParityFisherTangentWeight
    (sigma : ℝ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    infiniteMobiusCriticalFisherTangentWeight sigma n

private theorem summable_norm_sq_infiniteMobiusCriticalParityFisherTangentWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalParityFisherTangentWeight sigma n‖ ^ 2) := by
  have hbase : Summable (fun n : ℕ =>
      ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2) := by
    have h := (lp.memℓp
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma)).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat] at h
    simp only [infiniteMobiusCriticalFisherTangentLp] at h
    apply h.congr
    intro n
    rw [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hbase
  intro n
  rw [infiniteMobiusCriticalParityFisherTangentWeight, norm_mul, mul_pow]
  have hmu : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmu0 := norm_nonneg (((ArithmeticFunction.moebius n : ℤ) : ℂ))
  have hsq : ‖(((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ^ 2 ≤ 1 := by
    nlinarith
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

/-- The parity transform of the completed critical Fisher tangent as an `ℓ²` vector. -/
def infiniteMobiusCriticalParityFisherTangentLp
  (sigma : ℝ) (hsigma : 1 < sigma) : lp (fun _ : ℕ => ℂ) 2 :=
  ⟨infiniteMobiusCriticalParityFisherTangentWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_infiniteMobiusCriticalParityFisherTangentWeight hsigma)⟩

private theorem parityFisher_inner_term_eq_fisher
    {sigma u : ℝ} (n : ℕ) :
    infiniteMobiusCriticalParityDampedWeight sigma u n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalParityFisherTangentWeight sigma n) =
      infiniteMobiusCriticalDampedSignedWeight sigma u n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalFisherTangentWeight sigma n) := by
  by_cases hsq : Squarefree n
  · have hmu :
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    have hstar :
        (starRingEnd ℂ) (((ArithmeticFunction.moebius n : ℤ) : ℂ)) =
          (((ArithmeticFunction.moebius n : ℤ) : ℂ)) := by
      simp
    unfold infiniteMobiusCriticalParityDampedWeight
      infiniteMobiusCriticalParityFisherTangentWeight
    rw [map_mul, hstar]
    rw [show
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            infiniteMobiusCriticalDampedSignedWeight sigma u n *
          (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            (starRingEnd ℂ)
              (infiniteMobiusCriticalFisherTangentWeight sigma n)) =
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 2) *
          (infiniteMobiusCriticalDampedSignedWeight sigma u n *
            (starRingEnd ℂ)
              (infiniteMobiusCriticalFisherTangentWeight sigma n)) by ring,
      hmu, one_mul]
  · rw [infiniteMobiusCriticalParityDampedWeight,
      infiniteMobiusCriticalParityFisherTangentWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp [infiniteMobiusCriticalDampedSignedWeight, infiniteMobiusSignedWeight,
      infiniteMobiusCriticalFisherTangentWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- Parity preserves the Fisher-tangent/damped-likelihood coefficient exactly. -/
theorem inner_infiniteMobiusCriticalParityFisherTangentLp_parityDamped_eq
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (infiniteMobiusCriticalParityFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu) =
      inner ℂ
        (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalParityFisherTangentLp,
    infiniteMobiusCriticalParityDampedWeightLp,
    infiniteMobiusCriticalFisherTangentLp,
    infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  apply tsum_congr
  exact parityFisher_inner_term_eq_fisher

private theorem parityFisher_norm_term_eq_fisher
    {sigma : ℝ} (n : ℕ) :
    ‖infiniteMobiusCriticalParityFisherTangentWeight sigma n‖ ^ 2 =
      ‖infiniteMobiusCriticalFisherTangentWeight sigma n‖ ^ 2 := by
  by_cases hsq : Squarefree n
  · have hmu :
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [infiniteMobiusCriticalParityFisherTangentWeight, norm_mul, mul_pow,
      ← norm_pow, hmu, norm_one, one_mul]
  · rw [infiniteMobiusCriticalParityFisherTangentWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp [infiniteMobiusCriticalFisherTangentWeight, infiniteMobiusSignedWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- Möbius parity preserves the completed Fisher-tangent norm. -/
theorem norm_infiniteMobiusCriticalParityFisherTangentLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusCriticalParityFisherTangentLp sigma hsigma‖ ^ 2 =
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  exact parityFisher_norm_term_eq_fisher

/-- Infinite doubled Hilbert carrier for the parity father/detail splitting. -/
abbrev infiniteMobiusDoubledHilbert :=
  WithLp 2
    (lp (fun _ : ℕ => ℂ) 2 × lp (fun _ : ℕ => ℂ) 2)

/-- Normalized doubled father likelihood at aperture `u`. -/
def infiniteMobiusDoubledParityFather
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    infiniteMobiusDoubledHilbert :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    WithLp.toLp 2
      (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu,
        infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu)

/-- Normalized clock-odd Fisher detail, with the parity sector carrying the opposite sign. -/
def infiniteMobiusDoubledParityFisherDetail
    (sigma : ℝ) (hsigma : 1 < sigma) :
    infiniteMobiusDoubledHilbert :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    WithLp.toLp 2
      (infiniteMobiusCriticalFisherTangentLp sigma hsigma,
        -infiniteMobiusCriticalParityFisherTangentLp sigma hsigma)

/-- The doubled father family has exactly the undoubled likelihood Gram. -/
theorem inner_infiniteMobiusDoubledParityFather
    {sigma u v : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    inner ℂ
        (infiniteMobiusDoubledParityFather sigma u hsigma hu)
        (infiniteMobiusDoubledParityFather sigma v hsigma hv) =
      inner ℂ
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma v hsigma hv) := by
  rw [infiniteMobiusDoubledParityFather, infiniteMobiusDoubledParityFather,
    inner_smul_left, inner_smul_right]
  change
    (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (inner ℂ
            (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu)
            (infiniteMobiusCriticalDampedSignedWeightLp sigma v hsigma hv) +
          inner ℂ
            (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu)
            (infiniteMobiusCriticalParityDampedWeightLp sigma v hsigma hv))) =
      inner ℂ
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma v hsigma hv)
  rw [inner_infiniteMobiusCriticalParityDampedWeightLp_eq_damped
    hsigma hu hv]
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtSq : (((Real.sqrt 2 : ℝ) : ℂ) ^ 2) = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [map_inv₀, Complex.conj_ofReal]
  field_simp
  rw [hsqrtSq]
  ring

/-- The clock-odd Fisher detail is exactly orthogonal to every doubled father likelihood. -/
theorem inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (infiniteMobiusDoubledParityFisherDetail sigma hsigma)
        (infiniteMobiusDoubledParityFather sigma u hsigma hu) = 0 := by
  rw [infiniteMobiusDoubledParityFisherDetail,
    infiniteMobiusDoubledParityFather, inner_smul_left, inner_smul_right]
  change
    (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (inner ℂ
            (infiniteMobiusCriticalFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu) +
          inner ℂ
            (-infiniteMobiusCriticalParityFisherTangentLp sigma hsigma)
            (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu))) = 0
  rw [inner_neg_left,
    inner_infiniteMobiusCriticalParityFisherTangentLp_parityDamped_eq
      hsigma hu]
  ring

/-- The doubled clock-odd detail has exactly the undoubled Fisher-tangent energy. -/
theorem norm_infiniteMobiusDoubledParityFisherDetail_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖infiniteMobiusDoubledParityFisherDetail sigma hsigma‖ ^ 2 =
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 := by
  rw [infiniteMobiusDoubledParityFisherDetail, norm_smul, mul_pow,
    WithLp.prod_norm_sq_eq_of_L2]
  change
    ‖(((Real.sqrt 2 : ℝ) : ℂ)⁻¹)‖ ^ 2 *
      (‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 +
        ‖-infiniteMobiusCriticalParityFisherTangentLp sigma hsigma‖ ^ 2) =
      ‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2
  rw [norm_neg, norm_infiniteMobiusCriticalParityFisherTangentLp_sq hsigma,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)),
    inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

/-- The transverse doubled detail carries exactly four units at the critical boundary. -/
theorem tendsto_norm_infiniteMobiusDoubledParityFisherDetail_sq :
    Tendsto (fun sigma : ℝ =>
      if hsigma : 1 < sigma then
        ‖infiniteMobiusDoubledParityFisherDetail sigma hsigma‖ ^ 2
      else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 4) := by
  apply tendsto_norm_infiniteMobiusCriticalFisherTangentLp_sq.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rw [norm_infiniteMobiusDoubledParityFisherDetail_sq hsigma]

/-- The father Gram converges to the right-half-plane Hardy Cauchy kernel. -/
theorem tendsto_inner_infiniteMobiusDoubledParityFather
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          inner ℂ
            (infiniteMobiusDoubledParityFather sigma u hsigma hu)
            (infiniteMobiusDoubledParityFather sigma v hsigma hv)
        else 0)
      (𝓝[>] (1 : ℝ))
      (𝓝 (((1 + u + v : ℝ) : ℂ)⁻¹)) := by
  apply tendsto_inner_infiniteMobiusCriticalParityDampedWeightLp hu hv |>.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [dif_pos hsigma, dif_pos hsigma,
    inner_infiniteMobiusDoubledParityFather hsigma hu hv,
    ← inner_infiniteMobiusCriticalParityDampedWeightLp_eq_damped
      hsigma hu hv]

/-! ## Exact augmented source Gram -/

/-- Finite source packet consisting of all father apertures and one common clock-odd detail. -/
def infiniteMobiusDoubledParityAugmentedPacket
    {n : ℕ} (sigma : ℝ) (u : Fin n → ℝ) (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) :
    Fin n ⊕ Unit → infiniteMobiusDoubledHilbert
  | Sum.inl i => infiniteMobiusDoubledParityFather sigma (u i) hsigma (hu i)
  | Sum.inr _ => infiniteMobiusDoubledParityFisherDetail sigma hsigma

/-- Actual finite augmented source Gram before the critical limit. -/
def infiniteMobiusDoubledParityAugmentedGram
    {n : ℕ} (sigma : ℝ) (u : Fin n → ℝ) (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.gram ℂ
    (infiniteMobiusDoubledParityAugmentedPacket sigma u hsigma hu)

/-- Source-side positivity is unconditional at every finite Euler parameter. -/
theorem infiniteMobiusDoubledParityAugmentedGram_posSemidef
    {n : ℕ} (sigma : ℝ) (u : Fin n → ℝ) (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) :
    (infiniteMobiusDoubledParityAugmentedGram
      sigma u hsigma hu).PosSemidef :=
  Matrix.posSemidef_gram ℂ
    (infiniteMobiusDoubledParityAugmentedPacket sigma u hsigma hu)

/-- Exact father block of the finite augmented source Gram. -/
theorem infiniteMobiusDoubledParityAugmentedGram_father
    {n : ℕ} {sigma : ℝ} {u : Fin n → ℝ} (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) (i j : Fin n) :
    infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
        (Sum.inl i) (Sum.inl j) =
      squarefreeMobiusBoundaryLayerLaplace sigma (u i + u j) := by
  rw [infiniteMobiusDoubledParityAugmentedGram, Matrix.gram_apply]
  change
    inner ℂ
        (infiniteMobiusDoubledParityFather sigma (u i) hsigma (hu i))
        (infiniteMobiusDoubledParityFather sigma (u j) hsigma (hu j)) =
      _
  rw [inner_infiniteMobiusDoubledParityFather hsigma (hu i) (hu j),
    inner_infiniteMobiusCriticalDampedSignedWeightLp_eq_boundaryLayerLaplace
      hsigma (hu i) (hu j)]

/-- Exact zero detail column of the finite augmented source Gram. -/
theorem infiniteMobiusDoubledParityAugmentedGram_detail_father
    {n : ℕ} {sigma : ℝ} {u : Fin n → ℝ} (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) (i : Fin n) :
    infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
        (Sum.inr ()) (Sum.inl i) = 0 := by
  rw [infiniteMobiusDoubledParityAugmentedGram, Matrix.gram_apply]
  exact inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
    hsigma (hu i)

/-- Exact zero detail row of the finite augmented source Gram. -/
theorem infiniteMobiusDoubledParityAugmentedGram_father_detail
    {n : ℕ} {sigma : ℝ} {u : Fin n → ℝ} (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) (i : Fin n) :
    infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
        (Sum.inl i) (Sum.inr ()) = 0 := by
  rw [infiniteMobiusDoubledParityAugmentedGram, Matrix.gram_apply]
  change
    inner ℂ
        (infiniteMobiusDoubledParityFather sigma (u i) hsigma (hu i))
        (infiniteMobiusDoubledParityFisherDetail sigma hsigma) = 0
  rw [← inner_conj_symm,
    inner_infiniteMobiusDoubledParityFisherDetail_father_eq_zero
      hsigma (hu i), map_zero]

/-- Exact detail diagonal of the finite augmented source Gram. -/
theorem infiniteMobiusDoubledParityAugmentedGram_detail
    {n : ℕ} {sigma : ℝ} {u : Fin n → ℝ} (hsigma : 1 < sigma)
    (hu : ∀ i, 0 ≤ u i) :
    infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
        (Sum.inr ()) (Sum.inr ()) =
      (‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 : ℂ) := by
  rw [infiniteMobiusDoubledParityAugmentedGram, Matrix.gram_apply]
  change
    inner ℂ
        (infiniteMobiusDoubledParityFisherDetail sigma hsigma)
        (infiniteMobiusDoubledParityFisherDetail sigma hsigma) =
      (‖infiniteMobiusCriticalFisherTangentLp sigma hsigma‖ ^ 2 : ℂ)
  rw [inner_self_eq_norm_sq_to_K]
  simpa only [Complex.ofReal_pow] using!
    congrArg (fun x : ℝ => (x : ℂ))
      (norm_infiniteMobiusDoubledParityFisherDetail_sq hsigma)

/-- Critical father entry of the augmented source Gram is the Hardy Cauchy entry. -/
theorem tendsto_infiniteMobiusDoubledParityAugmentedGram_father
    {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ u i) (i j : Fin n) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
            (Sum.inl i) (Sum.inl j)
        else 0)
      (𝓝[>] (1 : ℝ))
      (𝓝 (rightHalfPlaneHardyCauchyGram
        (mobiusParityHardyNode u) i j)) := by
  rw [rightHalfPlaneHardyCauchyGram_mobiusParityHardyNode]
  apply tendsto_inner_infiniteMobiusDoubledParityFather (hu i) (hu j) |>.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [dif_pos hsigma]
  rfl

/-- Critical detail diagonal of the augmented source Gram is exactly four. -/
theorem tendsto_infiniteMobiusDoubledParityAugmentedGram_detail
    {n : ℕ} {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ u i) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          infiniteMobiusDoubledParityAugmentedGram sigma u hsigma hu
            (Sum.inr ()) (Sum.inr ())
        else 0)
      (𝓝[>] (1 : ℝ)) (𝓝 (4 : ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_norm_infiniteMobiusDoubledParityFisherDetail_sq
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  simp only [Function.comp_apply, dif_pos hsigma]
  rw [infiniteMobiusDoubledParityAugmentedGram_detail hsigma hu]
  simpa only [Complex.ofReal_pow] using
    congrArg (fun x : ℝ => (x : ℂ))
      (norm_infiniteMobiusDoubledParityFisherDetail_sq hsigma)

end

end RHTower
