import GaloisForLFunctions.RHTower.SuzukiRootPortObservationGram

/-!
# Physical ordered paths in the support-pruned Suzuki seam

The full valuation translations commute.  This module proves that their exact strict-aperture
compressions need not commute: the aperture remembers which intermediate seam vertex a two-letter
path used.  Thus the physical oriented seam itself supplies chronological prime-word data before
the later scalar word coefficient abelianizes it.

This is deliberately only a source-carrier result.  It does not identify these ordered columns
with Route P's Julia channels or with a Type-B insertion representation; those remain separate
bridges.
-/

open Complex Set ContinuousLinearMap
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The physical oriented seam shift after strict-aperture compression. -/
def suzukiOrientedSupportPrunedShift (a : ℝ) (δ : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  P ∘L (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) ∘L P

/-- Before aperture compression, valuation translations form an abelian action. -/
theorem suzukiSeamShift_comp_commute (δ η : SuzukiSeamValuation) :
    (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) ∘L
        (suzukiSeamShift η : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) =
      (suzukiSeamShift η : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) ∘L
        (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) := by
  ext f q
  rcases q with ⟨root, ν⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change suzukiSeamShift δ (suzukiSeamShift η f) (root, ν) =
    suzukiSeamShift η (suzukiSeamShift δ f) (root, ν)
  rw [suzukiSeamShift_apply, suzukiSeamShift_apply,
    suzukiSeamShift_apply, suzukiSeamShift_apply]
  change f (root, ν - δ - η) = f (root, ν - η - δ)
  have hval : ν - δ - η = ν - η - δ := by
    simp only [sub_eq_add_neg]
    ac_rfl
  rw [hval]

/-- Both oriented roots retain the same open valuation-coordinate interval. -/
theorem suzukiAdmissibleSeamVertices_iff
    (a : ℝ) (q : SuzukiSeamVertex) :
    q ∈ suzukiAdmissibleSeamVertices a ↔
      0 < primeSeamCoordinate q.2 ∧ primeSeamCoordinate q.2 < 2 * a := by
  rcases q with ⟨root, ν⟩
  cases root <;> rw [suzukiAdmissibleSeamVertices, Set.mem_setOf_eq]
  · simp only [suzukiSeamLocation]
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith
  · simp only [suzukiSeamLocation]
    rw [abs_lt]
    constructor <;> intro h <;> constructor <;> linarith

/-- Exact coordinate action of an oriented support-pruned shift. -/
theorem suzukiOrientedSupportPrunedShift_apply
    (a : ℝ) (δ : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    suzukiOrientedSupportPrunedShift a δ f q =
      (suzukiAdmissibleSeamVertices a).indicator
        (fun r : SuzukiSeamVertex =>
          (suzukiAdmissibleSeamVertices a).indicator (fun s => f s) (r.1, r.2 - δ)) q := by
  by_cases hq : q ∈ suzukiAdmissibleSeamVertices a
  · rw [suzukiOrientedSupportPrunedShift]
    change lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      ((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q = _
    rw [lpCoordinateProjection_apply, indicator_of_mem hq]
    change suzukiSeamShift δ
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f) q = _
    rw [suzukiSeamShift_apply, lpCoordinateProjection_apply]
    rw [indicator_of_mem hq]
  · rw [suzukiOrientedSupportPrunedShift]
    change lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      ((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q = _
    rw [lpCoordinateProjection_apply, indicator_of_notMem hq, indicator_of_notMem hq]

/-- A pruned oriented shift vanishes at a vertex whenever the uniquely possible predecessor
coefficient vanishes. -/
theorem suzukiOrientedSupportPrunedShift_eq_zero_of_source_zero
    (a : ℝ) (δ : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex)
    (hf : f (q.1, q.2 - δ) = 0) :
    suzukiOrientedSupportPrunedShift a δ f q = 0 := by
  by_cases hq : q ∈ suzukiAdmissibleSeamVertices a
  · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq]
    by_cases hp : (q.1, q.2 - δ) ∈ suzukiAdmissibleSeamVertices a
    · rw [indicator_of_mem hp, hf]
    · rw [indicator_of_notMem hp]
  · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_notMem hq]

/-- A two-step oriented path vanishes if its unique source predecessor vanishes. -/
theorem suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
    (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex)
    (hf : f (q.1, q.2 - δ - η) = 0) :
    suzukiOrientedSupportPrunedShift a δ
        (suzukiOrientedSupportPrunedShift a η f) q = 0 := by
  apply suzukiOrientedSupportPrunedShift_eq_zero_of_source_zero
  apply suzukiOrientedSupportPrunedShift_eq_zero_of_source_zero
  exact hf

/-- A physical aperture boundary distinguishes the two orders of two oriented seam shifts.
The first product survives precisely when its intermediate vertex is retained; the reversed
product vanishes when its different intermediate vertex is pruned. -/
theorem suzukiOrientedSupportPrunedShift_ordered_path_asymmetry
    (a : ℝ) (δ η : SuzukiSeamValuation) (q : SuzukiSeamVertex)
    (hq : q ∈ suzukiAdmissibleSeamVertices a)
    (hqδ : (q.1, q.2 - δ) ∈ suzukiAdmissibleSeamVertices a)
    (hv : (q.1, q.2 - δ - η) ∈ suzukiAdmissibleSeamVertices a)
    (hqη : (q.1, q.2 - η) ∉ suzukiAdmissibleSeamVertices a) :
    suzukiOrientedSupportPrunedShift a δ
        (suzukiOrientedSupportPrunedShift a η
          (lp.single 2 (q.1, q.2 - δ - η) 1)) q = 1 ∧
      suzukiOrientedSupportPrunedShift a η
        (suzukiOrientedSupportPrunedShift a δ
          (lp.single 2 (q.1, q.2 - δ - η) 1)) q = 0 := by
  constructor
  · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
      indicator_of_mem hqδ, suzukiOrientedSupportPrunedShift_apply,
      indicator_of_mem hqδ, indicator_of_mem hv]
    simp [lp.single_apply]
  · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
      indicator_of_notMem hqη]

/-- Same-oriented seam shifts cannot distinguish their two orders between retained endpoints.
Thus physical word order requires a genuine oriented reversal, as in the later `2,3,7` witness. -/
theorem suzukiOrientedSupportPrunedShift_twoStep_agree_of_nonneg_coordinates
    (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex)
    (hδ : 0 ≤ primeSeamCoordinate δ) (hη : 0 ≤ primeSeamCoordinate η)
    (hq : q ∈ suzukiAdmissibleSeamVertices a)
    (hend : (q.1, q.2 - δ - η) ∈ suzukiAdmissibleSeamVertices a) :
    suzukiOrientedSupportPrunedShift a δ
        (suzukiOrientedSupportPrunedShift a η f) q =
      suzukiOrientedSupportPrunedShift a η
        (suzukiOrientedSupportPrunedShift a δ f) q := by
  have hmidδ : (q.1, q.2 - δ) ∈ suzukiAdmissibleSeamVertices a := by
    rw [suzukiAdmissibleSeamVertices_iff] at hq hend ⊢
    simp only [map_sub] at hq hend ⊢
    constructor <;> linarith
  have hval : q.2 - η - δ = q.2 - δ - η := by abel
  have hmidη : (q.1, q.2 - η) ∈ suzukiAdmissibleSeamVertices a := by
    rw [suzukiAdmissibleSeamVertices_iff] at hq hend ⊢
    simp only [map_sub] at hq hend ⊢
    constructor <;> linarith
  have hend' : (q.1, q.2 - η - δ) ∈ suzukiAdmissibleSeamVertices a := by
    rw [hval]
    exact hend
  have hleft : suzukiOrientedSupportPrunedShift a δ
      (suzukiOrientedSupportPrunedShift a η f) q = f (q.1, q.2 - δ - η) := by
    rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
      indicator_of_mem hmidδ, suzukiOrientedSupportPrunedShift_apply,
      indicator_of_mem hmidδ, indicator_of_mem hend]
  have hright : suzukiOrientedSupportPrunedShift a η
      (suzukiOrientedSupportPrunedShift a δ f) q = f (q.1, q.2 - η - δ) := by
    rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
      indicator_of_mem hmidη, suzukiOrientedSupportPrunedShift_apply,
      indicator_of_mem hmidη, indicator_of_mem hend']
  rw [hleft, hright, hval]

/-- Strict aperture pruning still preserves commutation of two nonnegative-displacement shifts.
The source of noncommutativity is therefore an oriented reversal, not unequal positive primes. -/
theorem suzukiOrientedSupportPrunedShift_comp_commute_of_nonneg_coordinates
    (a : ℝ) (δ η : SuzukiSeamValuation)
    (hδ : 0 ≤ primeSeamCoordinate δ) (hη : 0 ≤ primeSeamCoordinate η) :
    suzukiOrientedSupportPrunedShift a δ ∘L suzukiOrientedSupportPrunedShift a η =
      suzukiOrientedSupportPrunedShift a η ∘L suzukiOrientedSupportPrunedShift a δ := by
  ext f q
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  by_cases hq : q ∈ suzukiAdmissibleSeamVertices a
  · by_cases hend : (q.1, q.2 - δ - η) ∈ suzukiAdmissibleSeamVertices a
    · exact suzukiOrientedSupportPrunedShift_twoStep_agree_of_nonneg_coordinates
        a δ η f q hδ hη hq hend
    · have hval : q.2 - η - δ = q.2 - δ - η := by
        simp only [sub_eq_add_neg]
        ac_rfl
      have hend' : (q.1, q.2 - η - δ) ∉ suzukiAdmissibleSeamVertices a := by
        intro h
        apply hend
        rwa [hval] at h
      have hleft : suzukiOrientedSupportPrunedShift a δ
          (suzukiOrientedSupportPrunedShift a η f) q = 0 := by
        by_cases hmid : (q.1, q.2 - δ) ∈ suzukiAdmissibleSeamVertices a
        · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
            indicator_of_mem hmid, suzukiOrientedSupportPrunedShift_apply,
            indicator_of_mem hmid, indicator_of_notMem hend]
        · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
            indicator_of_notMem hmid]
      have hright : suzukiOrientedSupportPrunedShift a η
          (suzukiOrientedSupportPrunedShift a δ f) q = 0 := by
        by_cases hmid : (q.1, q.2 - η) ∈ suzukiAdmissibleSeamVertices a
        · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
            indicator_of_mem hmid, suzukiOrientedSupportPrunedShift_apply,
            indicator_of_mem hmid, indicator_of_notMem hend']
        · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_mem hq,
            indicator_of_notMem hmid]
      rw [hleft, hright]
  · rw [suzukiOrientedSupportPrunedShift_apply, indicator_of_notMem hq,
      suzukiOrientedSupportPrunedShift_apply, indicator_of_notMem hq]

/-- The physical symmetric prime step after strict aperture compression. -/
def suzukiSupportPrunedSymmetricSeamStep (a : ℝ) (δ : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  P ∘L suzukiSymmetricSeamStep δ ∘L P

/-- Compression of the physical symmetric step is exactly the sum of its two retained oriented
branches. -/
theorem suzukiSupportPrunedSymmetricSeamStep_eq_oriented_sum
    (a : ℝ) (δ : SuzukiSeamValuation) :
    suzukiSupportPrunedSymmetricSeamStep a δ =
      suzukiOrientedSupportPrunedShift a δ + suzukiOrientedSupportPrunedShift a (-δ) := by
  ext f q
  change lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      (suzukiSymmetricSeamStep δ
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q = _
  rw [suzukiSymmetricSeamStep]
  rw [suzukiSeamShift_adjoint]
  change lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      (((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) +
        (suzukiSeamShift (-δ) : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert))
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q =
    lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      ((suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q +
      lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
        ((suzukiSeamShift (-δ) : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices a) f)) q
  rw [add_apply, map_add]
  rfl

private def spEPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def spEPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩
private def spEPrimeSeven : Nat.Primes := ⟨7, Nat.prime_seven⟩

private def spEDeltaTwo : SuzukiSeamValuation :=
  suzukiPrimePowerStep (spEPrimeTwo, 1)

private def spEDeltaThree : SuzukiSeamValuation :=
  suzukiPrimePowerStep (spEPrimeThree, 1)

private def spEDeltaSeven : SuzukiSeamValuation :=
  suzukiPrimePowerStep (spEPrimeSeven, 1)

private def spEBaseValuation : SuzukiSeamValuation := spEDeltaSeven - spEDeltaTwo

private def spEAperture : ℝ :=
  (primeSeamCoordinate spEBaseValuation + primeSeamCoordinate spEDeltaTwo / 2) / 2

private theorem primeSeamCoordinate_spEDeltaTwo :
    primeSeamCoordinate spEDeltaTwo = Real.log 2 := by
  simp [spEDeltaTwo, spEPrimeTwo, primeSeamCoordinate_primePowerStep]

private theorem primeSeamCoordinate_spEDeltaThree :
    primeSeamCoordinate spEDeltaThree = Real.log 3 := by
  simp [spEDeltaThree, spEPrimeThree, primeSeamCoordinate_primePowerStep]

private theorem primeSeamCoordinate_spEDeltaSeven :
    primeSeamCoordinate spEDeltaSeven = Real.log 7 := by
  simp [spEDeltaSeven, spEPrimeSeven, primeSeamCoordinate_primePowerStep]

private theorem spE_log_two_add_log_three_lt_log_seven :
    Real.log 2 + Real.log 3 < Real.log 7 := by
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  norm_num
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem spE_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
private theorem spE_log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

private theorem spE_log_three_lt_log_seven : Real.log 3 < Real.log 7 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem spE_log_two_lt_log_three : Real.log 2 < Real.log 3 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem primeSeamCoordinate_spEBaseValuation :
    primeSeamCoordinate spEBaseValuation = Real.log 7 - Real.log 2 := by
  simp [spEBaseValuation, map_sub, primeSeamCoordinate_spEDeltaSeven,
    primeSeamCoordinate_spEDeltaTwo]

private theorem spEAperture_pos : 0 < spEAperture := by
  rw [spEAperture, primeSeamCoordinate_spEBaseValuation,
    primeSeamCoordinate_spEDeltaTwo]
  linarith [spE_log_two_lt_log_three, spE_log_three_lt_log_seven, spE_log_two_pos]

private theorem primeSeamCoordinate_spEBase_sub_three :
    primeSeamCoordinate (spEBaseValuation - spEDeltaThree) =
      Real.log 7 - Real.log 2 - Real.log 3 := by
  simp [map_sub, primeSeamCoordinate_spEBaseValuation,
    primeSeamCoordinate_spEDeltaThree]

private theorem primeSeamCoordinate_spEBase_add_two_sub_three :
    primeSeamCoordinate (spEBaseValuation + spEDeltaTwo - spEDeltaThree) =
      Real.log 7 - Real.log 2 + Real.log 2 - Real.log 3 := by
  simp [map_add, map_sub, primeSeamCoordinate_spEBaseValuation,
    primeSeamCoordinate_spEDeltaTwo, primeSeamCoordinate_spEDeltaThree]

private theorem primeSeamCoordinate_spEBase_add_two :
    primeSeamCoordinate (spEBaseValuation + spEDeltaTwo) =
      Real.log 7 - Real.log 2 + Real.log 2 := by
  simp [map_add, primeSeamCoordinate_spEBaseValuation,
    primeSeamCoordinate_spEDeltaTwo]

private theorem spE_left_admissible_iff (a : ℝ) (ν : SuzukiSeamValuation) :
    (SuzukiSeamRoot.left, ν) ∈ suzukiAdmissibleSeamVertices a ↔
      0 < primeSeamCoordinate ν ∧ primeSeamCoordinate ν < 2 * a := by
  simpa using suzukiAdmissibleSeamVertices_iff a (SuzukiSeamRoot.left, ν)

private theorem spE_base_admissible :
    (SuzukiSeamRoot.left, spEBaseValuation) ∈
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spE_left_admissible_iff, primeSeamCoordinate_spEBaseValuation, spEAperture,
    primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo]
  constructor <;> linarith [spE_log_two_lt_log_three, spE_log_three_lt_log_seven,
    spE_log_two_pos]

private theorem spE_base_sub_three_admissible :
    (SuzukiSeamRoot.left, spEBaseValuation - spEDeltaThree) ∈
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spE_left_admissible_iff, primeSeamCoordinate_spEBase_sub_three, spEAperture,
    primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo]
  constructor <;> linarith [spE_log_two_add_log_three_lt_log_seven, spE_log_three_pos,
    spE_log_two_pos]

private theorem spE_base_add_two_sub_three_admissible :
    (SuzukiSeamRoot.left, spEBaseValuation + spEDeltaTwo - spEDeltaThree) ∈
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spE_left_admissible_iff, primeSeamCoordinate_spEBase_add_two_sub_three,
    spEAperture, primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo]
  constructor <;> linarith [spE_log_two_lt_log_three, spE_log_three_lt_log_seven,
    spE_log_two_pos]

private theorem spE_base_add_two_not_admissible :
    (SuzukiSeamRoot.left, spEBaseValuation + spEDeltaTwo) ∉
      suzukiAdmissibleSeamVertices spEAperture := by
  intro h
  rw [spE_left_admissible_iff, primeSeamCoordinate_spEBase_add_two, spEAperture,
    primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo] at h
  linarith [spE_log_two_pos]

private def spEFinalVertex : SuzukiSeamVertex :=
  (SuzukiSeamRoot.left, spEBaseValuation + spEDeltaTwo - spEDeltaThree)

private def spESourceVector : SuzukiSeamHilbert :=
  lp.single 2 (SuzukiSeamRoot.left, spEBaseValuation) 1

private theorem spEFinalVertex_sub_two :
    spEFinalVertex.2 - spEDeltaTwo = spEBaseValuation - spEDeltaThree := by
  simp only [spEFinalVertex]
  abel

private theorem spEFinalVertex_sub_two_add_three :
    spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree) = spEBaseValuation := by
  simp only [spEFinalVertex]
  abel

private theorem spEFinalVertex_add_three :
    spEFinalVertex.2 - (-spEDeltaThree) = spEBaseValuation + spEDeltaTwo := by
  simp only [spEFinalVertex]
  abel

private theorem spEFinalVertex_admissible :
    spEFinalVertex ∈ suzukiAdmissibleSeamVertices spEAperture :=
  spE_base_add_two_sub_three_admissible

private theorem spEFinalVertex_sub_two_admissible :
    (spEFinalVertex.1, spEFinalVertex.2 - spEDeltaTwo) ∈
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spEFinalVertex_sub_two]
  exact spE_base_sub_three_admissible

private theorem spEFinalVertex_sub_two_add_three_admissible :
    (spEFinalVertex.1, spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) ∈
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spEFinalVertex_sub_two_add_three]
  exact spE_base_admissible

private theorem spEFinalVertex_add_three_not_admissible :
    (spEFinalVertex.1, spEFinalVertex.2 - (-spEDeltaThree)) ∉
      suzukiAdmissibleSeamVertices spEAperture := by
  rw [spEFinalVertex_add_three]
  exact spE_base_add_two_not_admissible

private theorem spESourceVector_zero_final_sub_two_sub_three :
    spESourceVector
      (spEFinalVertex.1, spEFinalVertex.2 - spEDeltaTwo - spEDeltaThree) = 0 := by
  have hne : (spEFinalVertex.1, spEFinalVertex.2 - spEDeltaTwo - spEDeltaThree) ≠
      (SuzukiSeamRoot.left, spEBaseValuation) := by
    intro h
    have hcoord := congrArg (fun v : SuzukiSeamVertex => primeSeamCoordinate v.2) h
    simp only [spEFinalVertex, map_sub, map_add] at hcoord
    rw [primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo,
      primeSeamCoordinate_spEDeltaThree] at hcoord
    linarith [spE_log_three_pos]
  simp [spESourceVector, lp.single_apply, hne.symm]

private theorem spESourceVector_zero_final_add_two_sub_three :
    spESourceVector
      (spEFinalVertex.1, spEFinalVertex.2 - (-spEDeltaTwo) - spEDeltaThree) = 0 := by
  have hne : (spEFinalVertex.1, spEFinalVertex.2 - (-spEDeltaTwo) - spEDeltaThree) ≠
      (SuzukiSeamRoot.left, spEBaseValuation) := by
    intro h
    have hcoord := congrArg (fun v : SuzukiSeamVertex => primeSeamCoordinate v.2) h
    simp only [spEFinalVertex, map_sub, map_add, map_neg] at hcoord
    rw [primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo,
      primeSeamCoordinate_spEDeltaThree] at hcoord
    linarith [spE_log_two_lt_log_three]
  have hne' : (spEFinalVertex.1, spEFinalVertex.2 + spEDeltaTwo - spEDeltaThree) ≠
      (SuzukiSeamRoot.left, spEBaseValuation) := by
    simpa only [sub_neg_eq_add] using hne
  simp [spESourceVector, lp.single_apply, hne'.symm]

private theorem spESourceVector_zero_final_add_two_add_three :
    spESourceVector
      (spEFinalVertex.1, spEFinalVertex.2 - (-spEDeltaTwo) - (-spEDeltaThree)) = 0 := by
  have hne : (spEFinalVertex.1, spEFinalVertex.2 - (-spEDeltaTwo) - (-spEDeltaThree)) ≠
      (SuzukiSeamRoot.left, spEBaseValuation) := by
    intro h
    have hcoord := congrArg (fun v : SuzukiSeamVertex => primeSeamCoordinate v.2) h
    simp only [spEFinalVertex, map_sub, map_add, map_neg] at hcoord
    rw [primeSeamCoordinate_spEBaseValuation, primeSeamCoordinate_spEDeltaTwo,
      primeSeamCoordinate_spEDeltaThree] at hcoord
    linarith [spE_log_two_pos]
  have hne' : (spEFinalVertex.1, spEFinalVertex.2 + spEDeltaTwo + spEDeltaThree) ≠
      (SuzukiSeamRoot.left, spEBaseValuation) := by
    simpa only [sub_neg_eq_add] using hne
  simp [spESourceVector, lp.single_apply, hne'.symm]

private theorem suzukiOrientedSupportPrunedShift_prime_237_ordered_path_asymmetry :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
          (lp.single 2 (spEFinalVertex.1,
            spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) 1)) spEFinalVertex = 1 ∧
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
          (lp.single 2 (spEFinalVertex.1,
            spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) 1)) spEFinalVertex = 0 := by
  exact suzukiOrientedSupportPrunedShift_ordered_path_asymmetry
    spEAperture spEDeltaTwo (-spEDeltaThree) spEFinalVertex
    spEFinalVertex_admissible spEFinalVertex_sub_two_admissible
    spEFinalVertex_sub_two_add_three_admissible spEFinalVertex_add_three_not_admissible

private theorem spE_oriented_prime_237_path_asymmetry :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
          spESourceVector) spEFinalVertex = 1 ∧
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
          spESourceVector) spEFinalVertex = 0 := by
  have h := suzukiOrientedSupportPrunedShift_prime_237_ordered_path_asymmetry
  rw [spEFinalVertex_sub_two_add_three] at h
  simpa [spESourceVector, spEFinalVertex] using h

private theorem spE_twoStep_two_three_zero :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
          spESourceVector) spEFinalVertex = 0 :=
  suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
    spEAperture spEDeltaTwo spEDeltaThree spESourceVector spEFinalVertex
    spESourceVector_zero_final_sub_two_sub_three

private theorem spE_twoStep_negTwo_three_zero :
    suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
          spESourceVector) spEFinalVertex = 0 :=
  suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
    spEAperture (-spEDeltaTwo) spEDeltaThree spESourceVector spEFinalVertex
    spESourceVector_zero_final_add_two_sub_three

private theorem spE_twoStep_negTwo_negThree_zero :
    suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
          spESourceVector) spEFinalVertex = 0 :=
  suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
    spEAperture (-spEDeltaTwo) (-spEDeltaThree) spESourceVector spEFinalVertex
    spESourceVector_zero_final_add_two_add_three

private theorem spE_symmetric_prime_23_forward :
    suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaTwo
        (suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaThree
          spESourceVector) spEFinalVertex = 1 := by
  rw [suzukiSupportPrunedSymmetricSeamStep_eq_oriented_sum,
    suzukiSupportPrunedSymmetricSeamStep_eq_oriented_sum]
  simp only [add_apply, map_add]
  change
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
          spESourceVector) spEFinalVertex +
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
          spESourceVector) spEFinalVertex +
      (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
          spESourceVector) spEFinalVertex +
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
          spESourceVector) spEFinalVertex) = 1
  rw [spE_twoStep_two_three_zero, spE_twoStep_negTwo_three_zero,
    spE_oriented_prime_237_path_asymmetry.1, spE_twoStep_negTwo_negThree_zero]
  norm_num

private theorem spE_twoStep_three_two_zero :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
          spESourceVector) spEFinalVertex = 0 := by
  apply suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
  rw [show spEFinalVertex.2 - spEDeltaThree - spEDeltaTwo =
      spEFinalVertex.2 - spEDeltaTwo - spEDeltaThree by
    simp only [sub_eq_add_neg]
    ac_rfl]
  exact spESourceVector_zero_final_sub_two_sub_three

private theorem spE_twoStep_three_negTwo_zero :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
          spESourceVector) spEFinalVertex = 0 := by
  apply suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
  rw [show spEFinalVertex.2 - spEDeltaThree - (-spEDeltaTwo) =
      spEFinalVertex.2 - (-spEDeltaTwo) - spEDeltaThree by
    simp only [sub_eq_add_neg]
    ac_rfl]
  exact spESourceVector_zero_final_add_two_sub_three

private theorem spE_twoStep_negThree_negTwo_zero :
    suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
          spESourceVector) spEFinalVertex = 0 := by
  apply suzukiOrientedSupportPrunedShift_twoStep_eq_zero_of_source_zero
  rw [show spEFinalVertex.2 - (-spEDeltaThree) - (-spEDeltaTwo) =
      spEFinalVertex.2 - (-spEDeltaTwo) - (-spEDeltaThree) by
    simp only [sub_eq_add_neg]
    ac_rfl]
  exact spESourceVector_zero_final_add_two_add_three

private theorem spE_symmetric_prime_23_reverse :
    suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaThree
        (suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaTwo
          spESourceVector) spEFinalVertex = 0 := by
  rw [suzukiSupportPrunedSymmetricSeamStep_eq_oriented_sum,
    suzukiSupportPrunedSymmetricSeamStep_eq_oriented_sum]
  simp only [add_apply, map_add]
  change
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
          spESourceVector) spEFinalVertex +
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
          spESourceVector) spEFinalVertex +
      (suzukiOrientedSupportPrunedShift spEAperture spEDeltaThree
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
          spESourceVector) spEFinalVertex +
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaTwo)
          spESourceVector) spEFinalVertex) = 0
  rw [spE_twoStep_three_two_zero, spE_oriented_prime_237_path_asymmetry.2,
    spE_twoStep_three_negTwo_zero, spE_twoStep_negThree_negTwo_zero]
  norm_num

private theorem spE_prime_237_pruned_shifts_do_not_commute :
    suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo ∘L
        suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree) ≠
      suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree) ∘L
        suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo := by
  intro h
  have hvalue := congrArg (fun T : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert =>
    T (lp.single 2 (spEFinalVertex.1,
      spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) 1) spEFinalVertex) h
  change suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
      (suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
        (lp.single 2 (spEFinalVertex.1,
          spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) 1)) spEFinalVertex =
    suzukiOrientedSupportPrunedShift spEAperture (-spEDeltaThree)
      (suzukiOrientedSupportPrunedShift spEAperture spEDeltaTwo
        (lp.single 2 (spEFinalVertex.1,
          spEFinalVertex.2 - spEDeltaTwo - (-spEDeltaThree)) 1)) spEFinalVertex at hvalue
  rw [suzukiOrientedSupportPrunedShift_prime_237_ordered_path_asymmetry.1,
    suzukiOrientedSupportPrunedShift_prime_237_ordered_path_asymmetry.2] at hvalue
  norm_num at hvalue

/-- **Physical source chronology.** Strict Suzuki aperture compression creates a pair of
oriented prime shifts whose two-step products differ. The witness is the literal `2,3,7` prime
configuration; no order is added after source formation. -/
theorem exists_suzukiOrientedSupportPrunedShift_noncommuting :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation),
      0 < a ∧ suzukiOrientedSupportPrunedShift a δ ∘L
          suzukiOrientedSupportPrunedShift a η ≠
      suzukiOrientedSupportPrunedShift a η ∘L suzukiOrientedSupportPrunedShift a δ :=
  ⟨spEAperture, spEDeltaTwo, -spEDeltaThree, spEAperture_pos,
    spE_prime_237_pruned_shifts_do_not_commute⟩

/-- **Literal reflected-cell history certificate.**  The noncommuting oriented pair in the
physical `2,3,7` configuration is specifically the positive prime-two atom followed by the
reflected prime-three atom.  Exporting these exact labels is essential for attaching a
source-defined reflected curvature cell to this history port. -/
theorem exists_suzukiOrientedSupportPrunedShift_primeTwo_negPrimeThree_noncommuting :
    ∃ a : ℝ, 0 < a ∧
      suzukiOrientedSupportPrunedShift a
          (suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1)) ∘L
          suzukiOrientedSupportPrunedShift a
            (-suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1)) ≠
        suzukiOrientedSupportPrunedShift a
            (-suzukiPrimePowerStep (⟨3, Nat.prime_three⟩, 1)) ∘L
          suzukiOrientedSupportPrunedShift a
            (suzukiPrimePowerStep (⟨2, Nat.prime_two⟩, 1)) := by
  refine ⟨spEAperture, spEAperture_pos, ?_⟩
  simpa [spEDeltaTwo, spEDeltaThree, spEPrimeTwo, spEPrimeThree] using
    spE_prime_237_pruned_shifts_do_not_commute

/-- **Literal oriented-history certificate.**  At one retained source/readout pair, the two
oriented prime shifts in the physical `2,3,7` configuration have amplitudes `1` and `0` in
opposite orders.  The negative shift is part of the source path, not a post hoc sign. -/
theorem exists_suzukiOrientedSupportPrunedShift_ordered_value_asymmetry :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex),
      0 < a ∧
        suzukiOrientedSupportPrunedShift a δ
          (suzukiOrientedSupportPrunedShift a η f) q = 1 ∧
        suzukiOrientedSupportPrunedShift a η
          (suzukiOrientedSupportPrunedShift a δ f) q = 0 :=
  ⟨spEAperture, spEDeltaTwo, -spEDeltaThree, spESourceVector, spEFinalVertex,
    spEAperture_pos, spE_oriented_prime_237_path_asymmetry⟩

/-- **Positive-label physical chronology.** Even though `+e₂` and `+e₃` commute as individual
oriented translations, their source-defined symmetric Suzuki prime steps retain both orientations
and have distinct two-letter products after strict aperture compression. -/
theorem exists_suzukiSupportPrunedSymmetricSeamStep_noncommuting :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation),
      0 < a ∧ suzukiSupportPrunedSymmetricSeamStep a δ ∘L
          suzukiSupportPrunedSymmetricSeamStep a η ≠
        suzukiSupportPrunedSymmetricSeamStep a η ∘L
          suzukiSupportPrunedSymmetricSeamStep a δ := by
  refine ⟨spEAperture, spEDeltaTwo, spEDeltaThree, spEAperture_pos, ?_⟩
  intro h
  have hvalue := congrArg (fun T : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert =>
    T spESourceVector spEFinalVertex) h
  change suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaTwo
      (suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaThree
        spESourceVector) spEFinalVertex =
    suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaThree
      (suzukiSupportPrunedSymmetricSeamStep spEAperture spEDeltaTwo
        spESourceVector) spEFinalVertex at hvalue
  rw [spE_symmetric_prime_23_forward, spE_symmetric_prime_23_reverse] at hvalue
  norm_num at hvalue

/-- **Literal ordered-history certificate.** At one retained source/readout pair, the two
positive-label symmetric prime steps from the physical `2,3,7` configuration have amplitudes
`1` and `0` in opposite orders.  In particular, an endpoint-coordinate-only carrier cannot be a
faithful model of the pruned source history. -/
theorem exists_suzukiSupportPrunedSymmetricSeamStep_ordered_value_asymmetry :
    ∃ (a : ℝ) (δ η : SuzukiSeamValuation) (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex),
      0 < a ∧
        suzukiSupportPrunedSymmetricSeamStep a δ
          (suzukiSupportPrunedSymmetricSeamStep a η f) q = 1 ∧
        suzukiSupportPrunedSymmetricSeamStep a η
          (suzukiSupportPrunedSymmetricSeamStep a δ f) q = 0 :=
  ⟨spEAperture, spEDeltaTwo, spEDeltaThree, spESourceVector, spEFinalVertex,
    spEAperture_pos, spE_symmetric_prime_23_forward, spE_symmetric_prime_23_reverse⟩

end GaloisForLFunctions.RHTower
