import GaloisForLFunctions.HTGeometry.FacePacketFreeTelescoping
import GaloisForLFunctions.HTGeometry.FaceTranslateInjective
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaUnitPeriod
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTerminalFace
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary

/-!
# Freeness of the displacement labelling of a face packet

The displacement labelling sends a packet element to its defect in a surviving direction.  On the
external orbit of a face this is the coface translate,

`T_{τ q} (T_g Ψ_J) - T_g Ψ_J = T_g Ψ_{J ∪ {q}}`,

so the labelling is injective exactly when a translation of the external lattice fixing the deeper
face coordinate already fixes the face coordinate itself — a comparison of translation
stabilizers.

* `facePacketDisplacementSlice_coe` — the displacement is the coface translate;
* `faceShiftLattice_sub` — the external lattice is closed under differences;
* **`facePacketDisplacementSlice_injective_of_period`** — injectivity from the stabilizer
  comparison;
* `addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero` — every integer
  translation fixes every face coordinate, so the comparison only has to reach `ℤ`;
* `multipleEllipticGammaLogDerivFaceMero_fix_insert_of_fix` — a translation fixing a face
  coordinate fixes every deeper face coordinate;
* **`facePacketDisplacementSlice_injective_iff_subsingleton_of_terminal`** — with no surviving
  parameter on the deeper face the labelling is constant, so it is injective only on a
  subsingleton packet.
-/

open Filter Topology Set Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The external lattice is a group -/

omit [DecidableEq ι] in
/-- The external lattice of a face is closed under differences. -/
theorem faceShiftLattice_sub (τ : ι → ℂ) (J : Finset ι) {g₁ g₂ : ℂ}
    (h₁ : g₁ ∈ faceShiftLattice τ J) (h₂ : g₂ ∈ faceShiftLattice τ J) :
    g₁ - g₂ ∈ faceShiftLattice τ J := by
  obtain ⟨n₁, hn₁, rfl⟩ := h₁
  obtain ⟨n₂, hn₂, rfl⟩ := h₂
  refine ⟨n₁ - n₂, fun i hi => ?_, ?_⟩
  · simp [hn₁ i hi, hn₂ i hi]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    push_cast
    ring

/-! ## The displacement is the coface translate -/

/-- The displacement of an external translate of the face coordinate is the same translate of the
deeper face coordinate. -/
theorem facePacketDisplacementSlice_coe (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι)
    {q : ι} (hq : q ∉ J) (g : ℂ)
    (y : ↥(multipleEllipticGammaFacePacket τ hτ J))
    (hy : (y : meroField (Set.univ : Set ℂ)) =
      addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) :
    (facePacketDisplacementSlice τ hτ J hq y : meroField (Set.univ : Set ℂ)) =
      addTranslationMeroEquiv g
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) := by
  show addTranslationMeroEquiv (τ q) (y : meroField (Set.univ : Set ℂ)) -
      (y : meroField (Set.univ : Set ℂ)) = _
  rw [hy]
  exact facePacket_coface τ hτ J hq g

/-! ## Injectivity from a stabilizer comparison -/

/-- **The displacement labelling is injective as soon as the stabilizer of the deeper face
coordinate meets the external lattice inside the stabilizer of the face coordinate.**  Two packet
elements with the same displacement are external translates whose difference fixes the deeper face
coordinate; by hypothesis that difference fixes the face coordinate, so the two elements agree. -/
theorem facePacketDisplacementSlice_injective_of_period (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hper : ∀ h ∈ faceShiftLattice τ J,
      addTranslationMeroEquiv h
          (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
        multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) →
      addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
        multipleEllipticGammaLogDerivFaceMero τ hτ J) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) := by
  intro y₁ y₂ heq
  obtain ⟨g₁, hg₁, hy₁⟩ := y₁.2
  obtain ⟨g₂, hg₂, hy₂⟩ := y₂.2
  have hcoe : (facePacketDisplacementSlice τ hτ J hq y₁ :
        meroField (Set.univ : Set ℂ)) =
      (facePacketDisplacementSlice τ hτ J hq y₂ : meroField (Set.univ : Set ℂ)) :=
    congrArg Subtype.val heq
  rw [facePacketDisplacementSlice_coe τ hτ J hq g₁ y₁ hy₁.symm,
    facePacketDisplacementSlice_coe τ hτ J hq g₂ y₂ hy₂.symm] at hcoe
  have hfix : addTranslationMeroEquiv (g₁ - g₂)
      (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
      multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) := by
    have hmap := congrArg (addTranslationMeroEquiv (-g₂)) hcoe
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, neg_add_cancel,
      addTranslationMeroEquiv_zero_apply] at hmap
    rwa [show -g₂ + g₁ = g₁ - g₂ by ring] at hmap
  have hJfix := hper (g₁ - g₂) (faceShiftLattice_sub τ J hg₁ hg₂) hfix
  apply Subtype.ext
  rw [← hy₁, ← hy₂]
  show addTranslationMeroEquiv g₁ (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
    addTranslationMeroEquiv g₂ (multipleEllipticGammaLogDerivFaceMero τ hτ J)
  have hstep : addTranslationMeroEquiv g₂ (addTranslationMeroEquiv (g₁ - g₂)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
      addTranslationMeroEquiv g₁ (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
    rw [addTranslationMeroEquiv_add, show g₂ + (g₁ - g₂) = g₁ by ring]
  rw [← hstep, hJfix]

/-! ## Integer translations fix every face -/

/-- Every integer translation fixes every face coordinate of the hierarchy: the unit period
generates an integer subgroup of the translation stabilizer. -/
theorem addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) (m : ℤ) :
    addTranslationMeroEquiv (m : ℂ)
        (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      multipleEllipticGammaLogDerivFaceMero τ hτ J := by
  have hone : (1 : ℂ) ∈
      meromorphicTranslationStabilizer (multipleEllipticGammaLogDerivFaceMero τ hτ J) := by
    show addTranslationMeroEquiv (1 : ℂ)
      (multipleEllipticGammaLogDerivFaceMero τ hτ J) = _
    exact addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivFaceMero τ hτ J
  have hm := AddSubgroup.zsmul_mem
    (meromorphicTranslationStabilizer (multipleEllipticGammaLogDerivFaceMero τ hτ J)) hone m
  rw [show (m : ℤ) • (1 : ℂ) = (m : ℂ) by simp] at hm
  exact hm

/-- **Injectivity from an integral stabilizer.**  If every external lattice vector fixing the
deeper face coordinate is an integer, the displacement labelling is injective, because integers fix
every face coordinate. -/
theorem facePacketDisplacementSlice_injective_of_integral_period
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hint : ∀ h ∈ faceShiftLattice τ J,
      addTranslationMeroEquiv h
          (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
        multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) →
      ∃ m : ℤ, h = (m : ℂ)) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) := by
  refine facePacketDisplacementSlice_injective_of_period τ hτ J hq ?_
  intro h hmem hfix
  obtain ⟨m, rfl⟩ := hint h hmem hfix
  exact addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero τ hτ J m

/-! ## Climbing the face tower -/

/-- A translation fixing a face coordinate fixes every deeper face coordinate: the coface
difference commutes with translation. -/
theorem multipleEllipticGammaLogDerivFaceMero_fix_insert_of_fix
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (L : Finset ι) {i : ι} (hi : i ∉ L) {h : ℂ}
    (hfix : addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      multipleEllipticGammaLogDerivFaceMero τ hτ L) :
    addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert i L)) =
      multipleEllipticGammaLogDerivFaceMero τ hτ (insert i L) := by
  rw [← multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ L i hi, map_sub, hfix]
  congr 1
  rw [addTranslationMeroEquiv_add, add_comm, ← addTranslationMeroEquiv_add, hfix]

/-! ## The terminal face -/

/-- With every parameter deleted the face coordinate is the constant `-2πi`, which every
translation fixes. -/
theorem addTranslationMeroEquiv_multipleEllipticGammaLogDerivFaceMero_univ
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (β : ℂ) :
    addTranslationMeroEquiv β
        (multipleEllipticGammaLogDerivFaceMero τ hτ (Finset.univ : Finset ι)) =
      multipleEllipticGammaLogDerivFaceMero τ hτ (Finset.univ : Finset ι) := by
  letI : IsEmpty (MultipleEllipticGammaFaceIndex (Finset.univ : Finset ι)) :=
    ⟨fun i => by simpa using i.2⟩
  exact addTranslationMeroEquiv_multipleEllipticGammaLogDerivMero_isEmpty
    (multipleEllipticGammaFaceParameters τ (Finset.univ : Finset ι)) (fun i => hτ i) β

/-- **The displacement labelling is constant at the terminal face.**  When the deeper face has no
surviving parameter its coordinate is a constant, so every packet element has the same
displacement. -/
theorem facePacketDisplacementSlice_eq_of_terminal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hfull : insert q J = (Finset.univ : Finset ι))
    (y₁ y₂ : ↥(multipleEllipticGammaFacePacket τ hτ J)) :
    facePacketDisplacementSlice τ hτ J hq y₁ =
      facePacketDisplacementSlice τ hτ J hq y₂ := by
  obtain ⟨g₁, _, hy₁⟩ := y₁.2
  obtain ⟨g₂, _, hy₂⟩ := y₂.2
  apply Subtype.ext
  rw [facePacketDisplacementSlice_coe τ hτ J hq g₁ y₁ hy₁.symm,
    facePacketDisplacementSlice_coe τ hτ J hq g₂ y₂ hy₂.symm, hfull,
    addTranslationMeroEquiv_multipleEllipticGammaLogDerivFaceMero_univ τ hτ g₁,
    addTranslationMeroEquiv_multipleEllipticGammaLogDerivFaceMero_univ τ hτ g₂]

/-- **The freeness hypothesis is unsatisfiable at the terminal face beyond a one-element packet.**
With no surviving parameter on the deeper face, injectivity of the displacement labelling is
equivalent to the packet being a subsingleton. -/
theorem facePacketDisplacementSlice_injective_iff_subsingleton_of_terminal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hfull : insert q J = (Finset.univ : Finset ι)) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
      Subsingleton ↥(multipleEllipticGammaFacePacket τ hτ J) := by
  constructor
  · intro hinj
    exact ⟨fun a b => hinj (facePacketDisplacementSlice_eq_of_terminal τ hτ J hq hfull a b)⟩
  · intro hsub a b _
    exact Subsingleton.elim a b

/-! ## Freeness is exactly the stabilizer comparison -/

omit [DecidableEq ι] in
/-- The external lattice contains the trivial shift. -/
theorem faceShiftLattice_zero (τ : ι → ℂ) (J : Finset ι) :
    (0 : ℂ) ∈ faceShiftLattice τ J :=
  ⟨0, fun _ _ => rfl, by simp⟩

/-- **Freeness of the displacement labelling is exactly a comparison of translation
stabilizers.**  The labelling is injective if and only if every external lattice shift fixing the
deeper face coordinate already fixes the face coordinate. -/
theorem facePacketDisplacementSlice_injective_iff_period
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
      ∀ h ∈ faceShiftLattice τ J,
        addTranslationMeroEquiv h
            (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
          multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) →
        addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
          multipleEllipticGammaLogDerivFaceMero τ hτ J := by
  constructor
  · intro hinj h hmem hfix
    have hy₁ : addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) ∈
        multipleEllipticGammaFacePacket τ hτ J := ⟨h, hmem, rfl⟩
    have hy₂ : addTranslationMeroEquiv 0 (multipleEllipticGammaLogDerivFaceMero τ hτ J) ∈
        multipleEllipticGammaFacePacket τ hτ J := ⟨0, faceShiftLattice_zero τ J, rfl⟩
    have hdisp : facePacketDisplacementSlice τ hτ J hq ⟨_, hy₁⟩ =
        facePacketDisplacementSlice τ hτ J hq ⟨_, hy₂⟩ := by
      apply Subtype.ext
      rw [facePacketDisplacementSlice_coe τ hτ J hq h ⟨_, hy₁⟩ rfl,
        facePacketDisplacementSlice_coe τ hτ J hq 0 ⟨_, hy₂⟩ rfl,
        addTranslationMeroEquiv_zero_apply, hfix]
    have := congrArg Subtype.val (hinj hdisp)
    simpa [addTranslationMeroEquiv_zero_apply] using this
  · exact facePacketDisplacementSlice_injective_of_period τ hτ J hq

/-- **The stabilizer comparison holds on every face with at least two surviving parameters.**  An
external lattice shift fixing the deeper face coordinate fixes the face coordinate itself. -/
theorem multipleEllipticGammaLogDerivFaceMero_period_comparison
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hcard : 2 ≤ (((insert q J))ᶜ).card)
    {h : ℂ} (hmem : h ∈ faceShiftLattice τ J)
    (hfix : addTranslationMeroEquiv h
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
      multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) :
    addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      multipleEllipticGammaLogDerivFaceMero τ hτ J :=
  (facePacketDisplacementSlice_injective_iff_period τ hτ J hq).mp
    (facePacketDisplacementSlice_injective τ hτ hQ J hq hcard) h hmem hfix

/-- **At the terminal face freeness degenerates to invariance of the face coordinate under its own
external lattice.**  With no surviving parameter on the deeper face the stabilizer condition is
vacuous, so the labelling is injective exactly when every external shift is a period. -/
theorem facePacketDisplacementSlice_injective_iff_period_of_terminal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (J : Finset ι) {q : ι} (hq : q ∉ J)
    (hfull : insert q J = (Finset.univ : Finset ι)) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
      ∀ h ∈ faceShiftLattice τ J,
        addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
          multipleEllipticGammaLogDerivFaceMero τ hτ J := by
  rw [facePacketDisplacementSlice_injective_iff_period τ hτ J hq]
  constructor
  · intro hcmp h hmem
    refine hcmp h hmem ?_
    rw [hfull]
    exact addTranslationMeroEquiv_multipleEllipticGammaLogDerivFaceMero_univ τ hτ h
  · intro hall h hmem _
    exact hall h hmem

/-- **Freeness trichotomy of the displacement labelling.**  Freeness is always the stabilizer
comparison; it holds outright once the deeper face keeps at least two parameters, and at the
terminal face it collapses to invariance of the face coordinate under its own external lattice. -/
theorem facePacketDisplacementSlice_freeness_trichotomy
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) :
    (Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
        ∀ h ∈ faceShiftLattice τ J,
          addTranslationMeroEquiv h
              (multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J)) =
            multipleEllipticGammaLogDerivFaceMero τ hτ (insert q J) →
          addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
            multipleEllipticGammaLogDerivFaceMero τ hτ J) ∧
      (2 ≤ (((insert q J))ᶜ).card →
        Function.Injective (facePacketDisplacementSlice τ hτ J hq)) ∧
      (insert q J = (Finset.univ : Finset ι) →
        (Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
          ∀ h ∈ faceShiftLattice τ J,
            addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
              multipleEllipticGammaLogDerivFaceMero τ hτ J)) :=
  ⟨facePacketDisplacementSlice_injective_iff_period τ hτ J hq,
    fun hcard => facePacketDisplacementSlice_injective τ hτ hQ J hq hcard,
    fun hfull => facePacketDisplacementSlice_injective_iff_period_of_terminal τ hτ J hq hfull⟩

end

end GaloisForLFunctions
