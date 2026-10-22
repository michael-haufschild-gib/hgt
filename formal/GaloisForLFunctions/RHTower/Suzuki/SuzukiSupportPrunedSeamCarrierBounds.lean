import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedSelfAdjointSeamCarrier

/-!
# Norm bound and explicit action of the support-pruned prime seam carrier

The seam shift is unitary with adjoint the opposite translation, so each symmetric valuation step
has norm at most two and the finite prime adjacency has norm at most twice the total weight.  The
support-pruned carrier acts by the explicit pruned formula: a coordinate outside the strict
aperture is annihilated, and inside the aperture each neighbour contributes only through its own
aperture indicator, so no path is restored after leaving the interval.
-/

open Complex Set ContinuousLinearMap
open scoped BigOperators InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

private theorem lp_finset_sum_apply {ι : Type*} (s : Finset ι)
    (g : ι → SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    (∑ i ∈ s, g i) q = ∑ i ∈ s, (g i) q := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- The adjoint of a seam translation is the opposite translation. -/
theorem suzukiSeamShift_adjoint (δ : SuzukiSeamValuation) :
    ContinuousLinearMap.adjoint
        (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) =
      (suzukiSeamShift (-δ) : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) := by
  have hstep : ∀ (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex),
      suzukiSymmetricSeamStep δ f q = f (q.1, q.2 - δ) + f (q.1, q.2 + δ) :=
    fun f q => suzukiSymmetricSeamStep_apply δ f q
  ext f q
  have h := hstep f q
  rw [suzukiSymmetricSeamStep, add_apply] at h
  have hshift : (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f q =
      f (q.1, q.2 - δ) := suzukiSeamShift_apply δ f q
  have hsum : ((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f +
      ContinuousLinearMap.adjoint
        (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f) q =
      f (q.1, q.2 - δ) + f (q.1, q.2 + δ) := h
  have hcoord : ((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f) q +
      (ContinuousLinearMap.adjoint
        (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f) q =
      f (q.1, q.2 - δ) + f (q.1, q.2 + δ) := hsum
  rw [hshift] at hcoord
  have hneg : (suzukiSeamShift (-δ) : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) f q =
      f (q.1, q.2 + δ) := by
    have hraw := suzukiSeamShift_apply (-δ) f q
    rw [sub_neg_eq_add] at hraw
    exact hraw
  rw [hneg]
  exact add_left_cancel hcoord

/-- A seam translation has operator norm at most one. -/
theorem norm_suzukiSeamShift_le (δ : SuzukiSeamValuation) :
    ‖(suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simp

/-- Each real symmetric valuation step has operator norm at most two. -/
theorem norm_suzukiSymmetricSeamStep_le (δ : SuzukiSeamValuation) :
    ‖suzukiSymmetricSeamStep δ‖ ≤ 2 := by
  have hadj : ‖ContinuousLinearMap.adjoint
      (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)‖ =
      ‖(suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _
  have h1 := norm_suzukiSeamShift_le δ
  calc ‖suzukiSymmetricSeamStep δ‖
      ≤ ‖(suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)‖ +
          ‖ContinuousLinearMap.adjoint
            (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)‖ :=
        norm_add_le _ _
    _ ≤ 1 + 1 := by rw [hadj]; linarith
    _ = 2 := by norm_num

/-- **Uniform bound for the finite prime adjacency.**  Its norm is at most twice the total
prime-power weight, so the exact finite-aperture prime symbol is a bounded operator. -/
theorem norm_suzukiFinitePrimeAdjacency_le
    {ι : Type*} (steps : ι → SuzukiSeamValuation) (weight : ι → ℝ) (s : Finset ι) :
    ‖suzukiFinitePrimeAdjacency steps weight s‖ ≤ 2 * ∑ i ∈ s, |weight i| := by
  classical
  calc ‖suzukiFinitePrimeAdjacency steps weight s‖
      ≤ ∑ i ∈ s, ‖(-(weight i : ℂ)) • suzukiSymmetricSeamStep (steps i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ s, 2 * |weight i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        calc |weight i| * ‖suzukiSymmetricSeamStep (steps i)‖
            ≤ |weight i| * 2 :=
              mul_le_mul_of_nonneg_left (norm_suzukiSymmetricSeamStep_le _) (abs_nonneg _)
          _ = 2 * |weight i| := by ring
    _ = 2 * ∑ i ∈ s, |weight i| := by rw [Finset.mul_sum]

/-! ## Explicit pruned action -/

/-- Coordinatewise action of the finite prime adjacency. -/
theorem suzukiFinitePrimeAdjacency_apply
    {ι : Type*} (steps : ι → SuzukiSeamValuation) (weight : ι → ℝ) (s : Finset ι)
    (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    suzukiFinitePrimeAdjacency steps weight s f q =
      -∑ i ∈ s, (weight i : ℂ) *
        (f (q.1, q.2 - steps i) + f (q.1, q.2 + steps i)) := by
  classical
  rw [suzukiFinitePrimeAdjacency, sum_apply, lp_finset_sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((-(weight i : ℂ)) • suzukiSymmetricSeamStep (steps i)) f =
      (-(weight i : ℂ)) • (suzukiSymmetricSeamStep (steps i) f) := rfl
  rw [this]
  change (-(weight i : ℂ)) * (suzukiSymmetricSeamStep (steps i) f q) = _
  rw [suzukiSymmetricSeamStep_apply]
  ring

/-- **Exact pruned transport.**  Outside the strict aperture the compressed carrier vanishes; at an
admissible vertex every neighbour is itself filtered by the aperture indicator, so a prime word is
counted only while all of its intermediate vertices stay inside the interval. -/
theorem suzukiSupportPrunedPrimeAdjacency_apply
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation) (weight : ι → ℝ) (s : Finset ι)
    (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    suzukiSupportPrunedPrimeAdjacency a steps weight s f q =
      (suzukiAdmissibleSeamVertices a).indicator
        (fun r : SuzukiSeamVertex =>
          -∑ i ∈ s, (weight i : ℂ) *
            ((suzukiAdmissibleSeamVertices a).indicator (fun j => f j) (r.1, r.2 - steps i) +
              (suzukiAdmissibleSeamVertices a).indicator (fun j => f j) (r.1, r.2 + steps i))) q := by
  classical
  by_cases hq : q ∈ suzukiAdmissibleSeamVertices a
  · rw [indicator_of_mem hq]
    show (lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        (suzukiFinitePrimeAdjacency steps weight s
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f))) q = _
    rw [lpCoordinateProjection_apply, indicator_of_mem hq,
      suzukiFinitePrimeAdjacency_apply]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ => ?_)
    rw [lpCoordinateProjection_apply, lpCoordinateProjection_apply]
  · rw [indicator_of_notMem hq]
    show (lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        (suzukiFinitePrimeAdjacency steps weight s
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f))) q = 0
    rw [lpCoordinateProjection_apply, indicator_of_notMem hq]

/-- An idempotent self-adjoint operator is a contraction. -/
private theorem norm_apply_le_of_idempotent_selfAdjoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : E →L[ℂ] E) (hidem : P ∘L P = P) (hsa : ContinuousLinearMap.adjoint P = P) (f : E) :
    ‖P f‖ ≤ ‖f‖ := by
  have hPP : P (P f) = P f := by
    have := congrArg (fun T => T f) hidem
    simpa using this
  have h1 : (inner ℂ (P f) (P f) : ℂ) = inner ℂ f (P f) := by
    have h := ContinuousLinearMap.adjoint_inner_left P (P f) f
    rw [hsa, hPP] at h
    exact h
  have h2 : ‖P f‖ ^ (2 : ℕ) = ‖(inner ℂ (P f) (P f) : ℂ)‖ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  have h3 : ‖(inner ℂ f (P f) : ℂ)‖ ≤ ‖f‖ * ‖P f‖ := norm_inner_le_norm _ _
  rw [h1] at h2
  nlinarith [norm_nonneg (P f), norm_nonneg f]

/-- The aperture coordinate projection is a contraction. -/
theorem norm_lpCoordinateProjection_le (a : ℝ) :
    ‖lpCoordinateProjection (suzukiAdmissibleSeamVertices a)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  have hidem : lpCoordinateProjection (suzukiAdmissibleSeamVertices a) ∘L
      lpCoordinateProjection (suzukiAdmissibleSeamVertices a) =
      lpCoordinateProjection (suzukiAdmissibleSeamVertices a) :=
    lpCoordinateProjection_idempotent _
  have hsa := lpCoordinateProjection_selfAdjoint (suzukiAdmissibleSeamVertices a)
  simpa using norm_apply_le_of_idempotent_selfAdjoint _ hidem hsa f

/-- The pruned carrier obeys the same uniform bound as the unpruned prime adjacency. -/
theorem norm_suzukiSupportPrunedPrimeAdjacency_le
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation) (weight : ι → ℝ) (s : Finset ι) :
    ‖suzukiSupportPrunedPrimeAdjacency a steps weight s‖ ≤ 2 * ∑ i ∈ s, |weight i| := by
  have hP := norm_lpCoordinateProjection_le (a := a)
  have hA := norm_suzukiFinitePrimeAdjacency_le steps weight s
  have h1 :
      ‖suzukiSupportPrunedPrimeAdjacency a steps weight s‖ ≤
        ‖lpCoordinateProjection (suzukiAdmissibleSeamVertices a)‖ *
          ‖suzukiFinitePrimeAdjacency steps weight s ∘L
            lpCoordinateProjection (suzukiAdmissibleSeamVertices a)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 :
      ‖suzukiFinitePrimeAdjacency steps weight s ∘L
          lpCoordinateProjection (suzukiAdmissibleSeamVertices a)‖ ≤
        ‖suzukiFinitePrimeAdjacency steps weight s‖ *
          ‖lpCoordinateProjection (suzukiAdmissibleSeamVertices a)‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  nlinarith [norm_nonneg (suzukiFinitePrimeAdjacency steps weight s),
    norm_nonneg (lpCoordinateProjection (suzukiAdmissibleSeamVertices a)),
    norm_nonneg (suzukiFinitePrimeAdjacency steps weight s ∘L
      lpCoordinateProjection (suzukiAdmissibleSeamVertices a)),
    norm_nonneg (suzukiSupportPrunedPrimeAdjacency a steps weight s)]

/-- Gamma-normalized positive adjacency obeys the same uniform bound. -/
theorem norm_suzukiGammaPositivePrimeAdjacency_le
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation) (weight : ι → ℝ) (s : Finset ι) :
    ‖suzukiGammaPositivePrimeAdjacency a steps weight s‖ ≤ 2 * ∑ i ∈ s, |weight i| := by
  rw [suzukiGammaPositivePrimeAdjacency, norm_neg]
  exact norm_suzukiSupportPrunedPrimeAdjacency_le a steps weight s

end GaloisForLFunctions.RHTower
