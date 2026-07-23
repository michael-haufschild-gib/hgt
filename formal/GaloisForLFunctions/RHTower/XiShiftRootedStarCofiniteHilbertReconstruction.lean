import GaloisForLFunctions.RHTower.XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction

/-!
# Rooted-star equivalence of Xi defect and pair reconstruction

A finite defect packet is the edge packet of the star obtained by adjoining one zero-labelled
root and orienting every edge away from it. For both corrected integral shifts and raw even
shifts, the literal pair family then reduces exactly to the original defect family because the
root defect vanishes.

Consequently single-defect cofinite Hilbert reconstruction, rooted-star pair reconstruction,
pointed-incidence independence, real incidence-coordinate dual recovery, and Kirchhoff rigidity
all have the same unconditional collision classification. An arbitrary injective zero-preserving
reparametrization of the corrected shifts leaves this complete raw/corrected phase unchanged.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Add one distinguished zero-labelled root to a finite shift packet. -/
def xiShiftRootedStarLabel {I : Type*} (shift : I → ℕ) : Option I → ℕ
  | none => 0
  | some i => shift i

/-- Every rooted-star edge starts at the adjoined zero-labelled root. -/
def xiShiftRootedStarTail {I : Type*} : I → Option I :=
  fun _ => none

/-- Rooted-star edge `i` ends at the vertex carrying the original label `i`. -/
def xiShiftRootedStarHead {I : Type*} : I → Option I :=
  fun i => some i

/-- Adjoining the zero-labelled root is injective exactly when the original labels are distinct
and avoid zero. -/
theorem xiShiftRootedStarLabel_injective_iff
    {I : Type} (shift : I → ℕ) :
    Function.Injective (xiShiftRootedStarLabel shift) ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  constructor
  · intro hlabel
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact Option.some.inj (hlabel hij)
    · intro i hi
      have : some i = none := hlabel (by simp [xiShiftRootedStarLabel, hi])
      exact Option.some_ne_none i this
  · rintro ⟨hshift, hnonzero⟩ a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some j =>
            exact (hnonzero j (by
              simpa [xiShiftRootedStarLabel] using hab.symm)).elim
    | some i =>
        cases b with
        | none =>
            exact (hnonzero i (by
              simpa [xiShiftRootedStarLabel] using hab)).elim
        | some j =>
            exact congrArg some (hshift (by
              simpa [xiShiftRootedStarLabel] using hab))

/-- The corrected-Xi edge family on the zero-rooted star is literally the original defect
family, not merely equivalent at the level of independence. -/
theorem xiTransverseShiftPairDifferenceRotatedFamily_rootedStar_eq_defectFamily
    {d : ℕ} (shift : Fin d → ℕ) :
    xiTransverseShiftPairDifferenceRotatedFamily
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead =
      xiTransverseShiftPrimeDefectRotatedFamily shift := by
  funext i z
  simp [xiTransverseShiftPairDifferenceRotatedFamily,
    xiTransverseShiftPrimeDefectRotatedFamily,
    xiShiftRootedStarLabel, xiShiftRootedStarTail, xiShiftRootedStarHead,
    xiTransverseShiftPrimeDefect, xiTransverseShiftRawLogDerivDefect,
    xiTransverseShiftArchimedeanCorrection]

/-- The raw even-shift edge family on the zero-rooted star is literally the original raw defect
family. -/
theorem xiEvenShiftRawPairDifferenceRotatedFamily_rootedStar_eq_defectFamily
    {d : ℕ} (grade : Fin d → ℕ) :
    xiEvenShiftRawPairDifferenceRotatedFamily
        (xiShiftRootedStarLabel grade)
        xiShiftRootedStarTail xiShiftRootedStarHead =
      xiEvenShiftRawLogDerivDefectRotatedFamily grade := by
  funext i z
  simp [xiEvenShiftRawPairDifferenceRotatedFamily,
    xiEvenShiftRawLogDerivDefectRotatedFamily,
    xiShiftRootedStarLabel, xiShiftRootedStarTail, xiShiftRootedStarHead]

/-- **Corrected rooted-star reduction.** Complete pair reconstruction on the zero-rooted star is
exactly complete reconstruction of the original corrected defect packet. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift := by
  simp only [XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction,
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction,
    xiTransverseShiftPairDifferenceRotatedFamily_rootedStar_eq_defectFamily]

/-- **Raw rooted-star reduction.** Complete pair reconstruction on the raw zero-rooted star is
exactly complete reconstruction of the original raw defect packet. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel grade)
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade := by
  simp only [XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction,
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction,
    xiEvenShiftRawPairDifferenceRotatedFamily_rootedStar_eq_defectFamily]

/-- The pointed-incidence condition of the zero-rooted star discharges exactly to distinct,
nonzero original shift labels. -/
theorem xiTransverseShiftPairIncidenceIndependent_rootedStar_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPairIncidenceIndependent
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  calc
    _ ↔ XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead).symm
    _ ↔ XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect shift
    _ ↔ _ := xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff shift

/-- Real unisolvent reconstruction on the zero-rooted incidence star has the same exact
collision-free classification. -/
theorem pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    PointedCollisionIncidenceCoordinateReconstruction
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  calc
    _ ↔ XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead).symm
    _ ↔ XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect shift
    _ ↔ _ := xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff shift

/-- Injective zero-preserving reparametrization preserves exactly the collision/nonloop condition
of a finite shift packet. -/
theorem injective_comp_and_ne_zero_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    (Function.Injective (embed ∘ grade) ∧
        ∀ i, (embed ∘ grade) i ≠ 0) ↔
      Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · rintro ⟨hcomp, hne⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply hcomp
      exact congrArg embed hij
    · intro i hi
      apply hne i
      simp only [Function.comp_apply, hi, hzero]
  · rintro ⟨hgrade, hne⟩
    refine ⟨hinj.comp hgrade, ?_⟩
    intro i hi
    apply hne i
    apply hinj
    exact hi.trans hzero.symm

/-- **Universal single-defect raw/corrected phase invariance.** Every injective zero-preserving
reparametrization of corrected integral shifts has exactly the raw even-shift reconstruction
phase. Doubling and identity are special cases. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction (embed ∘ grade) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff]
  exact (injective_comp_and_ne_zero_iff grade embed hinj hzero).symm

/-- **Universal rooted-star Xi Hilbert phase.** Raw defect reconstruction simultaneously
characterizes every injectively reparametrized corrected defect packet, both corresponding
zero-rooted pair packets, real incidence-coordinate reconstruction, and the intrinsic
collision/nonloop condition. -/
theorem xiDefectRootedStarCofiniteHilbertPhase_reparam_iff
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction (embed ∘ grade) ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          (xiShiftRootedStarLabel (embed ∘ grade))
          xiShiftRootedStarTail xiShiftRootedStarHead ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
          (xiShiftRootedStarLabel grade)
          xiShiftRootedStarTail xiShiftRootedStarHead ∧
        PointedCollisionIncidenceCoordinateReconstruction
          (xiShiftRootedStarLabel grade) 0
          xiShiftRootedStarTail xiShiftRootedStarHead ∧
        Function.Injective grade ∧ ∀ i, grade i ≠ 0 := by
  constructor
  · intro hraw
    have hcondition :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).1 hraw
    have hcorrected :=
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).1 hraw
    exact ⟨hcorrected,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        (embed ∘ grade)).2 hcorrected,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        grade).2 hraw,
      (pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff
        grade).2 hcondition,
      hcondition⟩
  · rintro ⟨hcorrected, _hcorrectedStar, _hrawStar, _hcoordinate, _hcondition⟩
    exact
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).2 hcorrected

end

end RHTower
