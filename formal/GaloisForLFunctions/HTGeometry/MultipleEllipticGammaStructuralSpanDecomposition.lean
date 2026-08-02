import GaloisForLFunctions.HTGeometry.OrderTwoStructuralTranslateDecomposition

/-!
# Structural translates span the face packets modulo differentially algebraic functions

For a finite period family of any order, the union of all external face packets spans a subspace of
the global meromorphic field that is stable under every structural translation: translating in a
deleted direction stays inside the same packet, and translating in a surviving direction changes
the element by a telescoped sum of translates of the next face.

Consequently every structural translate of the top primitive is a finite `ℂ`-linear combination of
face-packet coordinates.  Splitting the faces into those retaining at least two periods and the
boundary faces retaining fewer, and using that the boundary packets are differentially algebraic,
gives the exact hierarchy identification: modulo a differentially algebraic error, an arbitrary
structural translate is a linear combination of the jointly independent deep packet coordinates.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The full packet span -/

/-- The union of the external translation packets of every deletion face. -/
def multipleEllipticGammaTotalPacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    Set (meroField (Set.univ : Set ℂ)) :=
  facePacketUnion τ hτ (Set.univ : Set (Finset ι))

theorem multipleEllipticGammaLogDerivMero_mem_totalPacket
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaLogDerivMero τ hτ ∈ multipleEllipticGammaTotalPacket τ hτ := by
  refine Set.mem_iUnion₂.mpr ⟨∅, Set.mem_univ _, ⟨0, ⟨0, fun _ _ => rfl, by simp⟩, ?_⟩⟩
  show addTranslationMeroEquiv (0 : ℂ) (multipleEllipticGammaLogDerivFaceMero τ hτ ∅) = _
  rw [addTranslationMeroEquiv_zero_apply, multipleEllipticGammaLogDerivFaceMero_empty]

/-- Translating a packet element in a *deleted* direction stays in the same packet. -/
theorem facePacket_translate_nsmul_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {p : ι} (hp : p ∈ J) (m : ℕ)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    addTranslationMeroEquiv ((m : ℂ) * τ p) y ∈ multipleEllipticGammaFacePacket τ hτ J := by
  obtain ⟨g, hg, rfl⟩ := hy
  refine ⟨(m : ℂ) * τ p + g, ?_, ?_⟩
  · simpa using faceShiftLattice_add_zsmul τ J hp hg (m : ℤ)
  · rw [addTranslationMeroEquiv_add]

/-- Translating a packet element in a *surviving* direction changes it by a telescoped sum of
translates of the next face. -/
theorem facePacket_translate_nsmul_sub_eq_sum (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {p : ι} (hp : p ∉ J) (m : ℕ) (g : ℂ) :
    addTranslationMeroEquiv ((m : ℂ) * τ p)
          (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) -
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) =
      ∑ k ∈ Finset.range m, addTranslationMeroEquiv (g + (k : ℂ) * τ p)
        (multipleEllipticGammaLogDerivFaceMero τ hτ (insert p J)) := by
  have htel := multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum τ hτ J hp m
  have hswap : addTranslationMeroEquiv ((m : ℂ) * τ p)
      (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) =
      addTranslationMeroEquiv g
        (addTranslationMeroEquiv ((m : ℂ) * τ p)
          (multipleEllipticGammaLogDerivFaceMero τ hτ J)) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [hswap, ← map_sub, htel, map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [addTranslationMeroEquiv_add]

theorem facePacket_translate_nsmul_sub_mem_span (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (J : Finset ι) {p : ι} (hp : p ∉ J) (m : ℕ)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ J) :
    addTranslationMeroEquiv ((m : ℂ) * τ p)
          (addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J)) -
        addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) ∈
      Submodule.span ℂ (multipleEllipticGammaTotalPacket τ hτ) := by
  rw [facePacket_translate_nsmul_sub_eq_sum τ hτ J hp m g]
  refine Submodule.sum_mem _ fun k _ => Submodule.subset_span ?_
  refine Set.mem_iUnion₂.mpr ⟨insert p J, Set.mem_univ _, ⟨g + (k : ℂ) * τ p, ?_, rfl⟩⟩
  have hgJ : g ∈ faceShiftLattice τ (insert p J) :=
    faceShiftLattice_mono τ (Finset.subset_insert p J) hg
  have hstep := faceShiftLattice_add_zsmul τ (insert p J) (Finset.mem_insert_self p J) hgJ (k : ℤ)
  simpa [add_comm] using hstep

/-- **The total packet span is translation stable.** -/
theorem multipleEllipticGammaTotalPacket_span_translate_mem
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (p : ι) (m : ℕ)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ Submodule.span ℂ (multipleEllipticGammaTotalPacket τ hτ)) :
    addTranslationMeroEquiv ((m : ℂ) * τ p) x ∈
      Submodule.span ℂ (multipleEllipticGammaTotalPacket τ hτ) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨J, -, hyJ⟩ := Set.mem_iUnion₂.mp hy
      by_cases hp : p ∈ J
      · exact Submodule.subset_span (Set.mem_iUnion₂.mpr ⟨J, Set.mem_univ _,
          facePacket_translate_nsmul_mem τ hτ J hp m hyJ⟩)
      · obtain ⟨g, hg, rfl⟩ := hyJ
        have hy' : addTranslationMeroEquiv g (multipleEllipticGammaLogDerivFaceMero τ hτ J) ∈
            Submodule.span ℂ (multipleEllipticGammaTotalPacket τ hτ) :=
          Submodule.subset_span (Set.mem_iUnion₂.mpr ⟨J, Set.mem_univ _, ⟨g, hg, rfl⟩⟩)
        have hsub := facePacket_translate_nsmul_sub_mem_span τ hτ J hp m hg
        simpa using Submodule.add_mem _ hsub hy'
  | zero => simp
  | add y z _ _ ihy ihz => simpa [map_add] using Submodule.add_mem _ ihy ihz
  | smul c y _ ih =>
      have hsmul : addTranslationMeroEquiv ((m : ℂ) * τ p) (c • y) =
          c • addTranslationMeroEquiv ((m : ℂ) * τ p) y := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          addTranslationMeroEquiv_algebraMap_complex]
      rw [hsmul]
      exact Submodule.smul_mem _ c ih

/-- **Every structural translate of the top primitive lies in the packet span.** -/
theorem multipleEllipticGammaStructuralTranslate_mem_span
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (n : ι → ℕ) (T : Finset ι) :
    addTranslationMeroEquiv (∑ i ∈ T, (n i : ℂ) * τ i)
        (multipleEllipticGammaLogDerivMero τ hτ) ∈
      Submodule.span ℂ (multipleEllipticGammaTotalPacket τ hτ) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simpa [addTranslationMeroEquiv_zero_apply] using
        Submodule.subset_span (multipleEllipticGammaLogDerivMero_mem_totalPacket τ hτ)
  | @insert p T hpT ih =>
      have hsum : ∑ i ∈ insert p T, (n i : ℂ) * τ i =
          (n p : ℂ) * τ p + ∑ i ∈ T, (n i : ℂ) * τ i := Finset.sum_insert hpT
      rw [hsum, ← addTranslationMeroEquiv_add]
      exact multipleEllipticGammaTotalPacket_span_translate_mem τ hτ p (n p) ih

/-! ## Splitting off the differentially algebraic boundary -/

theorem multipleEllipticGammaTotalPacket_eq_union (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    multipleEllipticGammaTotalPacket τ hτ =
      facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card} ∪
        facePacketUnion τ hτ {J : Finset ι | (Jᶜ).card < 2} := by
  have hcover : (Set.univ : Set (Finset ι)) =
      {J : Finset ι | 2 ≤ (Jᶜ).card} ∪ {J : Finset ι | (Jᶜ).card < 2} := by
    ext J
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
    omega
  rw [multipleEllipticGammaTotalPacket, hcover, facePacketUnion, facePacketUnion,
    facePacketUnion, Set.biUnion_union]

/-- Every element of the span of the boundary packets is differentially algebraic. -/
theorem differentialAlgebraicOver_mem_span_boundaryPacket
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ Submodule.span ℂ (facePacketUnion τ hτ {J : Finset ι | (Jᶜ).card < 2})) :
    DifferentialAlgebraicOver ℂ x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨J, hJ, hyJ⟩ := Set.mem_iUnion₂.mp hy
      exact differentialAlgebraicOver_facePacket_of_compl_lt_two τ hτ hQ hι J hJ hyJ
  | zero => exact differentialAlgebraicOver_zero
  | add y z _ _ ihy ihz => exact differentialAlgebraicOver_add ihy ihz
  | smul c y _ ih =>
      rw [Algebra.smul_def]
      exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap c) ih

/-- **Hierarchy identification.**  Modulo a differentially algebraic error, every structural
translate of the top primitive is a finite `ℂ`-linear combination of the jointly independent deep
face-packet coordinates. -/
theorem multipleEllipticGammaStructuralTranslate_eq_deepSpan_add_differentialAlgebraic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (n : ι → ℕ) (T : Finset ι) :
    ∃ y d : meroField (Set.univ : Set ℂ),
      y ∈ Submodule.span ℂ (facePacketUnion τ hτ {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
        DifferentialAlgebraicOver ℂ d ∧
        addTranslationMeroEquiv (∑ i ∈ T, (n i : ℂ) * τ i)
            (multipleEllipticGammaLogDerivMero τ hτ) = y + d := by
  have hmem := multipleEllipticGammaStructuralTranslate_mem_span τ hτ n T
  rw [multipleEllipticGammaTotalPacket_eq_union τ hτ, Submodule.span_union] at hmem
  obtain ⟨y, hy, d, hd, hsum⟩ := Submodule.mem_sup.mp hmem
  exact ⟨y, d, hy, differentialAlgebraicOver_mem_span_boundaryPacket τ hτ hQ hι hd, hsum.symm⟩

end

end GaloisForLFunctions
