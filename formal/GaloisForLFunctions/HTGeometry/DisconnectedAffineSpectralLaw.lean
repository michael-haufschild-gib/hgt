import GaloisForLFunctions.HTGeometry.InfiniteGeneratorSupportLaw

/-!
# Disconnected affine spectral sectors

Two dynamically disconnected affine matrix families have an analytic product spectral branch
which is exactly the sum of their component branches. Every Boolean interaction packet meeting
both sectors therefore has zero irreducible spectral contrast.
-/

open scoped Matrix.Norms.Elementwise Kronecker BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Left injection as a finite-set embedding. -/
def sumInlEmbedding (E₁ E₂ : Type*) : E₁ ↪ Sum E₁ E₂ :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Right injection as a finite-set embedding. -/
def sumInrEmbedding (E₁ E₂ : Type*) : E₂ ↪ Sum E₁ E₂ :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Restrict a split coupling vector to its left sector. -/
def leftSplitCoupling
    {E₁ E₂ R : Type*} (coupling : Sum E₁ E₂ → R) : E₁ → R :=
  fun e => coupling (Sum.inl e)

/-- Restrict a split coupling vector to its right sector. -/
def rightSplitCoupling
    {E₁ E₂ R : Type*} (coupling : Sum E₁ E₂ → R) : E₂ → R :=
  fun e => coupling (Sum.inr e)

/-- Activating a packet in a split coupling space and then projecting left. -/
def leftPacketCoupling
    {E₁ E₂ R : Type*} [DecidableEq E₁] [DecidableEq E₂] [Zero R]
    (active : Finset (Sum E₁ E₂)) (z : Sum E₁ E₂ → R) : E₁ → R :=
  leftSplitCoupling (restrictInteractionPacket active z)

/-- Activating a packet in a split coupling space and then projecting right. -/
def rightPacketCoupling
    {E₁ E₂ R : Type*} [DecidableEq E₁] [DecidableEq E₂] [Zero R]
    (active : Finset (Sum E₁ E₂)) (z : Sum E₁ E₂ → R) : E₂ → R :=
  rightSplitCoupling (restrictInteractionPacket active z)

theorem leftPacketCoupling_insert_inr
    {E₁ E₂ R : Type*} [DecidableEq E₁] [DecidableEq E₂] [Zero R]
    (e : E₂) (active : Finset (Sum E₁ E₂)) (z : Sum E₁ E₂ → R) :
    leftPacketCoupling (insert (Sum.inr e) active) z =
      leftPacketCoupling active z := by
  funext i
  simp [leftPacketCoupling, leftSplitCoupling, restrictInteractionPacket]

theorem rightPacketCoupling_insert_inl
    {E₁ E₂ R : Type*} [DecidableEq E₁] [DecidableEq E₂] [Zero R]
    (e : E₁) (active : Finset (Sum E₁ E₂)) (z : Sum E₁ E₂ → R) :
    rightPacketCoupling (insert (Sum.inl e) active) z =
      rightPacketCoupling active z := by
  funext i
  simp [rightPacketCoupling, rightSplitCoupling, restrictInteractionPacket]

/-- Lift two independent interaction families to their product configuration space. -/
def splitAffineInteraction
    {E₁ E₂ ι κ R : Type*} [CommRing R]
    [DecidableEq ι] [DecidableEq κ]
    (interactionLeft : E₁ → Matrix ι ι R)
    (interactionRight : E₂ → Matrix κ κ R) :
    Sum E₁ E₂ → Matrix (ι × κ) (ι × κ) R
  | Sum.inl e => interactionLeft e ⊗ₖ (1 : Matrix κ κ R)
  | Sum.inr e => (1 : Matrix ι ι R) ⊗ₖ interactionRight e

/-- **Exact tensor reindexing core.** An affine family whose labels split between two tensor
sectors is literally the Kronecker sum of the two component affine families. -/
theorem affineMatrixFamily_splitAffineInteraction_eq_kroneckerSum
    {E₁ E₂ ι κ : Type*}
    [Fintype E₁] [Fintype E₂] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (H0Left : Matrix ι ι ℂ) (H0Right : Matrix κ κ ℂ)
    (interactionLeft : E₁ → Matrix ι ι ℂ)
    (interactionRight : E₂ → Matrix κ κ ℂ)
    (coupling : Sum E₁ E₂ → ℂ) :
    affineMatrixFamily
        (kroneckerSum H0Left H0Right)
        (splitAffineInteraction interactionLeft interactionRight)
        coupling =
      kroneckerSum
        (affineMatrixFamily H0Left interactionLeft
          (leftSplitCoupling coupling))
        (affineMatrixFamily H0Right interactionRight
          (rightSplitCoupling coupling)) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [affineMatrixFamily, kroneckerSum, splitAffineInteraction,
    leftSplitCoupling, rightSplitCoupling, Matrix.add_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
  ring_nf

/-- Split-coordinate projections are entire. -/
theorem leftSplitCoupling_analyticAt
    {E₁ E₂ : Type*} [Fintype E₁] [DecidableEq E₁]
    [Fintype E₂] [DecidableEq E₂] :
    AnalyticAt ℂ
      (leftSplitCoupling : (Sum E₁ E₂ → ℂ) → E₁ → ℂ) 0 := by
  apply AnalyticAt.pi
  intro e
  exact
    (ContinuousLinearMap.proj (R := ℂ) (Sum.inl e)).analyticAt
      (0 : Sum E₁ E₂ → ℂ)

/-- Split-coordinate projections are entire. -/
theorem rightSplitCoupling_analyticAt
    {E₁ E₂ : Type*} [Fintype E₁] [DecidableEq E₁]
    [Fintype E₂] [DecidableEq E₂] :
    AnalyticAt ℂ
      (rightSplitCoupling : (Sum E₁ E₂ → ℂ) → E₂ → ℂ) 0 := by
  apply AnalyticAt.pi
  intro e
  exact
    (ContinuousLinearMap.proj (R := ℂ) (Sum.inr e)).analyticAt
      (0 : Sum E₁ E₂ → ℂ)

/-- **Disconnected affine spectral law.** For any two finite affine complex matrix families with
simple uncoupled component levels, their disconnected Kronecker sum has an analytic spectral
branch equal to the sum of the component branches. Every interaction packet containing at least
one label from each sector has identically zero Möbius spectral response. No self-adjointness,
normality, positivity, or closed-system assumption is used. -/
theorem disconnectedAffineEigenvalueBranch_crossPacket_eq_zero
    {E₁ E₂ ι κ : Type*}
    [Fintype E₁] [DecidableEq E₁] [Fintype E₂] [DecidableEq E₂]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (energyLeft : ι → ℂ) (hinjLeft : Function.Injective energyLeft)
    (energyRight : κ → ℂ) (hinjRight : Function.Injective energyRight)
    (interactionLeft : E₁ → Matrix ι ι ℂ)
    (interactionRight : E₂ → Matrix κ κ ℂ)
    (x : ι) (y : κ) :
    ∃ branchLeft : (E₁ → ℂ) → ℂ,
      ∃ branchRight : (E₂ → ℂ) → ℂ,
        ∃ totalBranch : (Sum E₁ E₂ → ℂ) → ℂ,
          AnalyticAt ℂ branchLeft 0 ∧
          AnalyticAt ℂ branchRight 0 ∧
          AnalyticAt ℂ totalBranch 0 ∧
          branchLeft 0 = energyLeft x ∧
          branchRight 0 = energyRight y ∧
          totalBranch 0 = energyLeft x + energyRight y ∧
          (∀ᶠ coupling in 𝓝 0,
            matrixCharpolyRelation
              (affineMatrixFamily
                  (Matrix.diagonal energyLeft) interactionLeft coupling,
                branchLeft coupling) = 0) ∧
          (∀ᶠ coupling in 𝓝 0,
            matrixCharpolyRelation
              (affineMatrixFamily
                  (Matrix.diagonal energyRight) interactionRight coupling,
                branchRight coupling) = 0) ∧
          (∀ᶠ coupling in 𝓝 0,
            matrixCharpolyRelation
              (affineMatrixFamily
                  (kroneckerSum
                    (Matrix.diagonal energyLeft)
                    (Matrix.diagonal energyRight))
                  (splitAffineInteraction
                    interactionLeft interactionRight)
                  coupling,
                totalBranch coupling) = 0) ∧
          totalBranch =
            (fun coupling =>
              branchLeft (leftSplitCoupling coupling) +
                branchRight (rightSplitCoupling coupling)) ∧
          ∀ (z : Sum E₁ E₂ → ℂ)
              (left : Finset E₁) (right : Finset E₂),
            left.Nonempty → right.Nonempty →
            finsetMobiusResponse
              (left.map (sumInlEmbedding E₁ E₂) ∪
                right.map (sumInrEmbedding E₁ E₂))
              (fun active =>
                totalBranch (restrictInteractionPacket active z)) = 0 := by
  obtain ⟨branchLeft, hleft, hleft0, hleftRoot⟩ :=
    affineMatrixFamily_eigenvalueBranch
      energyLeft hinjLeft interactionLeft x
  obtain ⟨branchRight, hright, hright0, hrightRoot⟩ :=
    affineMatrixFamily_eigenvalueBranch
      energyRight hinjRight interactionRight y
  let totalBranch : (Sum E₁ E₂ → ℂ) → ℂ :=
    fun coupling =>
      branchLeft (leftSplitCoupling coupling) +
        branchRight (rightSplitCoupling coupling)
  have hleftLift :
      AnalyticAt ℂ
        (fun coupling : Sum E₁ E₂ → ℂ =>
          branchLeft (leftSplitCoupling coupling)) 0 := by
    exact hleft.comp_of_eq' leftSplitCoupling_analyticAt rfl
  have hrightLift :
      AnalyticAt ℂ
        (fun coupling : Sum E₁ E₂ → ℂ =>
          branchRight (rightSplitCoupling coupling)) 0 := by
    exact hright.comp_of_eq' rightSplitCoupling_analyticAt rfl
  have htotal : AnalyticAt ℂ totalBranch 0 :=
    hleftLift.add hrightLift
  have hleftTendsto :
      Tendsto
        (leftSplitCoupling : (Sum E₁ E₂ → ℂ) → E₁ → ℂ)
        (𝓝 0) (𝓝 0) :=
    leftSplitCoupling_analyticAt.continuousAt
  have hrightTendsto :
      Tendsto
        (rightSplitCoupling : (Sum E₁ E₂ → ℂ) → E₂ → ℂ)
        (𝓝 0) (𝓝 0) :=
    rightSplitCoupling_analyticAt.continuousAt
  have hleftRootLift :
      ∀ᶠ coupling : Sum E₁ E₂ → ℂ in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
              (Matrix.diagonal energyLeft) interactionLeft
                (leftSplitCoupling coupling),
            branchLeft (leftSplitCoupling coupling)) = 0 :=
    hleftTendsto.eventually hleftRoot
  have hrightRootLift :
      ∀ᶠ coupling : Sum E₁ E₂ → ℂ in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
              (Matrix.diagonal energyRight) interactionRight
                (rightSplitCoupling coupling),
            branchRight (rightSplitCoupling coupling)) = 0 :=
    hrightTendsto.eventually hrightRoot
  have htotalRoot :
      ∀ᶠ coupling : Sum E₁ E₂ → ℂ in 𝓝 0,
        matrixCharpolyRelation
          (affineMatrixFamily
              (kroneckerSum
                (Matrix.diagonal energyLeft)
                (Matrix.diagonal energyRight))
              (splitAffineInteraction
                interactionLeft interactionRight)
              coupling,
            totalBranch coupling) = 0 := by
    filter_upwards [hleftRootLift, hrightRootLift] with coupling hl hr
    have hleval :
        (affineMatrixFamily
            (Matrix.diagonal energyLeft) interactionLeft
              (leftSplitCoupling coupling)).charpoly.eval
          (branchLeft (leftSplitCoupling coupling)) = 0 := by
      rw [Matrix.eval_charpoly]
      exact hl
    have hreval :
        (affineMatrixFamily
            (Matrix.diagonal energyRight) interactionRight
              (rightSplitCoupling coupling)).charpoly.eval
          (branchRight (rightSplitCoupling coupling)) = 0 := by
      rw [Matrix.eval_charpoly]
      exact hr
    rw [
      affineMatrixFamily_splitAffineInteraction_eq_kroneckerSum]
    unfold matrixCharpolyRelation totalBranch
    rw [← Matrix.eval_charpoly]
    exact charpoly_eval_kroneckerSum_eq_zero
      _ _ hleval hreval
  refine ⟨branchLeft, branchRight, totalBranch,
    hleft, hright, htotal, hleft0, hright0, ?_,
    hleftRoot, hrightRoot, htotalRoot, rfl, ?_⟩
  · change branchLeft 0 + branchRight 0 =
      energyLeft x + energyRight y
    rw [hleft0, hright0]
  · intro z left right hleftNonempty hrightNonempty
    let leftPacket : Finset (Sum E₁ E₂) :=
      left.map (sumInlEmbedding E₁ E₂)
    let rightPacket : Finset (Sum E₁ E₂) :=
      right.map (sumInrEmbedding E₁ E₂)
    let leftResponse : Finset (Sum E₁ E₂) → ℂ :=
      fun active => branchLeft (leftPacketCoupling active z)
    let rightResponse : Finset (Sum E₁ E₂) → ℂ :=
      fun active => branchRight (rightPacketCoupling active z)
    have hresponse :
        (fun active =>
          totalBranch (restrictInteractionPacket active z)) =
          leftResponse + rightResponse := by
      funext active
      rfl
    rw [show left.map (sumInlEmbedding E₁ E₂) = leftPacket by rfl]
    rw [show right.map (sumInrEmbedding E₁ E₂) = rightPacket by rfl]
    rw [hresponse, finsetMobiusResponse_add]
    have hleftPacketNonempty : leftPacket.Nonempty := by
      simpa [leftPacket] using hleftNonempty
    have hrightPacketNonempty : rightPacket.Nonempty := by
      simpa [rightPacket] using hrightNonempty
    have hdisjoint : Disjoint leftPacket rightPacket := by
      rw [Finset.disjoint_left]
      intro e heleft heright
      simp only [leftPacket, rightPacket, Finset.mem_map] at heleft heright
      obtain ⟨el, hel, rfl⟩ := heleft
      obtain ⟨er, her, heq⟩ := heright
      cases heq
    have hleftZero :
        finsetMobiusResponse (leftPacket ∪ rightPacket)
          leftResponse = 0 := by
      obtain ⟨e, he⟩ := hrightPacketNonempty
      obtain ⟨er, her, rfl⟩ :
          ∃ er ∈ right, Sum.inr er = e := by
        simpa [rightPacket] using he
      apply finsetMobiusResponse_eq_zero_of_insert_invariant
        (Finset.mem_union_right leftPacket he)
      intro active
      unfold leftResponse
      rw [leftPacketCoupling_insert_inr]
    have hrightZero :
        finsetMobiusResponse (leftPacket ∪ rightPacket)
          rightResponse = 0 := by
      obtain ⟨e, he⟩ := hleftPacketNonempty
      obtain ⟨el, hel, rfl⟩ :
          ∃ el ∈ left, Sum.inl el = e := by
        simpa [leftPacket] using he
      apply finsetMobiusResponse_eq_zero_of_insert_invariant
        (Finset.mem_union_left rightPacket he)
      intro active
      unfold rightResponse
      rw [rightPacketCoupling_insert_inl]
    rw [hleftZero, hrightZero, add_zero]

end GaloisForLFunctions.HTGeometry
