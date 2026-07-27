import GaloisForLFunctions.HTGeometry.FacePacketFieldStability

/-!
# The structural translations restrict to automorphisms of the deeper face field

Stability of the deeper face field under a structural translation is not by itself enough for the
simultaneous-telescoping criterion: the translations have to restrict to *automorphisms* of that
field, so the inverse translation must preserve it too.  It does, by the same coface mechanism read
backwards, and the restricted maps are then genuine ring equivalences.

* `differentialAdjoin_translate_stable_of_generators` — stability from stability on generators;
* **`facePacketUnion_neg_translate_mem`** and
  **`differentialAdjoin_facePacketUnion_neg_translate_stable`** — the inverse direction;
* **`facePacketFieldTranslation`** — the structural translation as a ring automorphism of the
  deeper face field.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stability from stability on generators.**  If a translation maps every generator of the
generated differential field into that field, it maps the whole field into it. -/
theorem differentialAdjoin_translate_stable_of_generators
    (g : ℂ) (T : Set (meroField (Set.univ : Set ℂ)))
    (hgen : ∀ y ∈ T, addTranslationMeroEquiv g y ∈ differentialAdjoin ℂ T)
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ differentialAdjoin ℂ T) :
    addTranslationMeroEquiv g x ∈ differentialAdjoin ℂ T := by
  classical
  let K := differentialAdjoin ℂ T
  have hKclosed : DerivationClosed K := derivationClosed_differentialAdjoin ℂ T
  let p : ∀ y : meroField (Set.univ : Set ℂ), y ∈ differentialAdjoin ℂ T → Prop :=
    fun y _ => addTranslationMeroEquiv g y ∈ K
  change p x hx
  refine IntermediateField.adjoin_induction ℂ (p := p) ?_ ?_ ?_ ?_ ?_ hx
  · rintro y ⟨y₀, hy₀, n, rfl⟩
    have hy₀' : addTranslationMeroEquiv g y₀ ∈ K := hgen y₀ hy₀
    have hjet : addTranslationMeroEquiv g (differentialJet n y₀) =
        differentialJet n (addTranslationMeroEquiv g y₀) := by
      simpa using (addTranslationMeroDifferentialAlgEquiv g).map_differentialJet n y₀
    show addTranslationMeroEquiv g (differentialJet n y₀) ∈ K
    rw [hjet]
    exact hKclosed.differentialJet_mem hy₀' n
  · intro c
    show addTranslationMeroEquiv g _ ∈ K
    rw [addTranslationMeroEquiv_algebraMap_complex g c]
    exact K.algebraMap_mem c
  · intro y z _ _ hpy hpz
    show addTranslationMeroEquiv g (y + z) ∈ K
    rw [map_add]
    exact K.add_mem hpy hpz
  · intro y _ hpy
    show addTranslationMeroEquiv g y⁻¹ ∈ K
    rw [map_inv₀]
    exact K.inv_mem hpy
  · intro y z _ _ hpy hpz
    show addTranslationMeroEquiv g (y * z) ∈ K
    rw [map_mul]
    exact K.mul_mem hpy hpz

/-- **The inverse translation also moves the generators inside the generated field.**  Reading the
coface equation backwards expresses `sigma_(-tau_q) y` as `y` minus a member of the next packet. -/
theorem facePacketUnion_neg_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ facePacketUnion τ hτ S) :
    addTranslationMeroEquiv (-τ q) y ∈ differentialAdjoin ℂ (facePacketUnion τ hτ S) := by
  obtain ⟨L, hL, hyL⟩ := Set.mem_iUnion₂.mp hy
  obtain ⟨g, hg, rfl⟩ := hyL
  by_cases hqL : q ∈ L
  · refine subset_differentialAdjoin ℂ _ ?_
    refine Set.mem_iUnion₂.mpr ⟨L, hL, ?_⟩
    refine ⟨-τ q + g, ?_, ?_⟩
    · have h1 : ((-1 : ℤ) : ℂ) * τ q + g ∈ faceShiftLattice τ L :=
        faceShiftLattice_add_zsmul τ L hqL hg (-1)
      simpa using h1
    · rw [addTranslationMeroEquiv_add]
  · have hlat : -τ q + g ∈ faceShiftLattice τ (insert q L) := by
      have hgIns : g ∈ faceShiftLattice τ (insert q L) :=
        faceShiftLattice_mono τ (Finset.subset_insert q L) hg
      have h1 : ((-1 : ℤ) : ℂ) * τ q + g ∈ faceShiftLattice τ (insert q L) :=
        faceShiftLattice_add_zsmul τ (insert q L) (Finset.mem_insert_self q L) hgIns (-1)
      simpa using h1
    have hcoface := facePacket_coface τ hτ L hqL (-τ q + g)
    have hcancel : addTranslationMeroEquiv (τ q)
        (addTranslationMeroEquiv (-τ q + g)
          (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) := by
      have harg : τ q + (-τ q + g) = g := by ring
      rw [addTranslationMeroEquiv_add, harg]
    rw [hcancel] at hcoface
    have hnext : addTranslationMeroEquiv (-τ q + g)
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q L)) ∈
        differentialAdjoin ℂ (facePacketUnion τ hτ S) :=
      subset_differentialAdjoin ℂ _
        (Set.mem_iUnion₂.mpr ⟨insert q L, hS L hL hqL, ⟨-τ q + g, hlat, rfl⟩⟩)
    have hy' : addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ L) ∈
        differentialAdjoin ℂ (facePacketUnion τ hτ S) :=
      subset_differentialAdjoin ℂ _
        (Set.mem_iUnion₂.mpr ⟨L, hL, ⟨g, hg, rfl⟩⟩)
    have hsplit : addTranslationMeroEquiv (-τ q)
        (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L) -
          addTranslationMeroEquiv (-τ q + g)
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q L)) := by
      have hL2 : addTranslationMeroEquiv (-τ q)
          (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ L)) =
          addTranslationMeroEquiv (-τ q + g)
            (multipleEllipticGammaLogDerivFaceMero τ hτ L) :=
        addTranslationMeroEquiv_add _ _ _
      rw [hL2, ← hcoface]
      abel
    rw [hsplit]
    exact (differentialAdjoin ℂ (facePacketUnion τ hτ S)).sub_mem hy' hnext

/-- **The deeper face field is stable under the inverse translation.** -/
theorem differentialAdjoin_facePacketUnion_neg_translate_stable (τ : ι → ℂ)
    (hτ : ∀ i, 0 < (τ i).im) {S : Set (Finset ι)} (q : ι)
    (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ differentialAdjoin ℂ (facePacketUnion τ hτ S)) :
    addTranslationMeroEquiv (-τ q) x ∈ differentialAdjoin ℂ (facePacketUnion τ hτ S) :=
  differentialAdjoin_translate_stable_of_generators (-τ q) _
    (fun _y hy => facePacketUnion_neg_translate_mem τ hτ q hS hy) hx

/-- **The structural translation as an automorphism of the deeper face field.** -/
def facePacketFieldTranslation (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) {S : Set (Finset ι)}
    (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S) :
    differentialAdjoin ℂ (facePacketUnion τ hτ S) ≃+*
      differentialAdjoin ℂ (facePacketUnion τ hτ S) where
  toFun x := ⟨addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ)),
    differentialAdjoin_facePacketUnion_translate_stable τ hτ q hS x.2⟩
  invFun x := ⟨addTranslationMeroEquiv (-τ q) (x : meroField (Set.univ : Set ℂ)),
    differentialAdjoin_facePacketUnion_neg_translate_stable τ hτ q hS x.2⟩
  left_inv x := by
    apply Subtype.ext
    show addTranslationMeroEquiv (-τ q)
      (addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ))) = _
    rw [addTranslationMeroEquiv_add, neg_add_cancel, addTranslationMeroEquiv_zero_apply]
  right_inv x := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      (addTranslationMeroEquiv (-τ q) (x : meroField (Set.univ : Set ℂ))) = _
    rw [addTranslationMeroEquiv_add, add_neg_cancel, addTranslationMeroEquiv_zero_apply]
  map_mul' x y := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      ((x : meroField (Set.univ : Set ℂ)) * (y : meroField (Set.univ : Set ℂ))) = _
    rw [map_mul]
    rfl
  map_add' x y := by
    apply Subtype.ext
    show addTranslationMeroEquiv (τ q)
      ((x : meroField (Set.univ : Set ℂ)) + (y : meroField (Set.univ : Set ℂ))) = _
    rw [map_add]
    rfl

@[simp]
theorem facePacketFieldTranslation_coe (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {S : Set (Finset ι)} (q : ι) (hS : ∀ L ∈ S, q ∉ L → insert q L ∈ S)
    (x : differentialAdjoin ℂ (facePacketUnion τ hτ S)) :
    ((facePacketFieldTranslation τ hτ q hS x : differentialAdjoin ℂ (facePacketUnion τ hτ S)) :
        meroField (Set.univ : Set ℂ)) =
      addTranslationMeroEquiv (τ q) (x : meroField (Set.univ : Set ℂ)) := rfl

end

end GaloisForLFunctions
