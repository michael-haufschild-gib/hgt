import GaloisForLFunctions.HTGeometry.MultipleSineFaceOffStarNeutrality

/-!
# The canonical packet of a face

Each face `J` of the period set carries a canonical packet: the external translates of the
multiple-sine source of the complementary frame `Jᶜ`.  No choice enters — the complementary frame
is determined by the face, and the source is the corpus's canonical one.

For a maximal face, `Jᶜ` is a pair, the packet is a double-sine orbit, and the two analytic
interfaces of the face-gluing engine hold for it: the packet is differentially independent over the
constants, and each off-face direction moves it only by a differentially algebraic amount.
-/

open Filter Set Topology Complex
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

/-! ### Adjoining a packet absorbs differentially algebraic differences -/

universe u

/-- If an element differs from a member of an adjoined set by a differentially algebraic amount,
it is differentially algebraic over that adjunction. -/
theorem differentialAlgebraicOver_differentialAdjoin_of_sub
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (t : Set E) {y z : E} (hy : y ∈ differentialAdjoin F t)
    (h : DifferentialAlgebraicOver F (z - y)) :
    DifferentialAlgebraicOver ↥(differentialAdjoin F t) z := by
  letI : DifferentialAlgebra ↥(differentialAdjoin F t) E :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F t) c⟩
  have h1 : DifferentialAlgebraicOver ↥(differentialAdjoin F t) (z - y) :=
    differentialAlgebraicOver_mono h
  have h2 : DifferentialAlgebraicOver ↥(differentialAdjoin F t) y :=
    differentialAlgebraicOver_algebraMap
      (F := ↥(differentialAdjoin F t)) (E := E) ⟨y, hy⟩
  have hsum := differentialAlgebraicOver_add h1 h2
  rwa [sub_add_cancel] at hsum

/-! ### The packet of a face -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The canonical packet of a face: all external translates of the multiple-sine source of the
complementary frame. -/
def facePacket (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) (J : Finset ι) :
    Set (meroField (Set.univ : Set ℂ)) :=
  if h : (Jᶜ : Finset ι).Nonempty then
    Set.range (fun α : {k // k ∈ J} → ℤ =>
      addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) h))
  else ∅

theorem facePacket_eq (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im) {J : Finset ι}
    (h : (Jᶜ : Finset ι).Nonempty) :
    facePacket ω hω J
      = Set.range (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift ω J α) (frameSourceMero ω hω (Jᶜ : Finset ι) h)) := by
  rw [facePacket, dif_pos h]

/-! ### Atomicity of a maximal-face packet -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The packet of a maximal face is differentially independent over the constants.** -/
theorem diffIndepOn_facePacket {μ : ℂ} {rad : ι → ℝ} (hrad : ∀ k, 0 < rad k)
    (hind : LinearIndependent ℚ (fun k => μ * (rad k : ℂ)))
    (hω : ∀ k, 0 < (μ * (rad k : ℂ)).im)
    {J : Finset ι} (hcard : (Jᶜ : Finset ι).card = 2) :
    DiffIndepOn ℂ (facePacket (fun k => μ * (rad k : ℂ)) hω J) := by
  classical
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hcard
  have hne : (Jᶜ : Finset ι).Nonempty := by
    rw [hpair]
    exact ⟨i, by simp⟩
  have hS : ({i, j} : Finset ι).Nonempty := ⟨i, by simp⟩
  have hi : i ∉ J := by
    have : i ∈ (Jᶜ : Finset ι) := by rw [hpair]; simp
    exact Finset.mem_compl.mp this
  have hj : j ∉ J := by
    have : j ∈ (Jᶜ : Finset ι) := by rw [hpair]; simp
    exact Finset.mem_compl.mp this
  have hsrc : frameSourceMero (fun k => μ * (rad k : ℂ)) hω (Jᶜ : Finset ι) hne
      = frameSourceMero (fun k => μ * (rad k : ℂ)) hω ({i, j} : Finset ι) hS :=
    frameSourceMero_congr _ hω hpair hne hS
  have hfam := multipleSineCanonicalFaceOrbit_free hrad hind hω hij hi hj hS
  have hC : DifferentialIndependent ℂ
      (fun α : {k // k ∈ J} → ℤ =>
        addTranslationMeroEquiv (faceShift (fun k => μ * (rad k : ℂ)) J α)
          (frameSourceMero (fun k => μ * (rad k : ℂ)) hω ({i, j} : Finset ι) hS)) :=
    DifferentialIndependent.restrictScalarsTower hfam
  rw [facePacket_eq _ hω hne, hsrc]
  exact diffIndepOn_range_of_differentialIndependent hC

/-! ### Off-face neutrality of a maximal-face packet -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Every off-face direction moves the packet only by a differentially algebraic amount.** -/
theorem differentialAlgebraicOver_facePacket_offStar (ω : ι → ℂ) (hω : ∀ k, 0 < (ω k).im)
    {J : Finset ι} (hcard : (Jᶜ : Finset ι).card = 2) {q : ι} (hq : q ∉ J)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacket ω hω J) (n : ℤ) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv ((n : ℂ) * ω q) y - y) := by
  classical
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hcard
  have hne : (Jᶜ : Finset ι).Nonempty := by
    rw [hpair]
    exact ⟨i, by simp⟩
  have hS : ({i, j} : Finset ι).Nonempty := ⟨i, by simp⟩
  have hqmem : q ∈ ({i, j} : Finset ι) := by
    rw [← hpair]
    exact Finset.mem_compl.mpr hq
  have hqij : q = i ∨ q = j := by
    have := Finset.mem_insert.mp hqmem
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have hsrc : frameSourceMero ω hω (Jᶜ : Finset ι) hne
      = frameSourceMero ω hω ({i, j} : Finset ι) hS :=
    frameSourceMero_congr _ hω hpair hne hS
  rw [facePacket_eq ω hω hne, hsrc] at hy
  obtain ⟨α, rfl⟩ := hy
  exact differentialAlgebraicOver_translate_canonicalFace ω hω hij hS hqij
    (faceShift ω J α) n

/-- **Off-face rank neutrality in the shape the gluing engine consumes.**  Any translate, by an
integer multiple of an off-face direction, of a member of a finite packet subset is differentially
algebraic over the adjunction of that subset. -/
theorem differentialAlgebraicOver_adjoin_facePacket_offStar (ω : ι → ℂ)
    (hω : ∀ k, 0 < (ω k).im) {J : Finset ι} (hcard : (Jᶜ : Finset ι).card = 2)
    {q : ι} (hq : q ∉ J) (t : Set (meroField (Set.univ : Set ℂ)))
    (ht : t ⊆ facePacket ω hω J) {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ t) (n : ℤ) :
    DifferentialAlgebraicOver ↥(differentialAdjoin ℂ t)
      (addTranslationMeroEquiv ((n : ℂ) * ω q) y) := by
  refine differentialAlgebraicOver_differentialAdjoin_of_sub t
    (subset_differentialAdjoin ℂ t hy) ?_
  exact differentialAlgebraicOver_facePacket_offStar ω hω hcard hq (ht hy) n

end

end GaloisForLFunctions.HTGeometry
