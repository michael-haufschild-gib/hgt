import GaloisForLFunctions.RHTower.XiShiftRootedStarCofiniteHilbertReconstruction

/-!
# Canonical incidence-Gram realization of Xi edge reconstruction

The pointed collision quotient carries a fixed real Euclidean incidence Gram: every edge is its
complete incidence row on all occupied nonloop labels. This module identifies positivity and
positive volume of that canonical finite Hilbert metric with literal cofinite reconstruction of
arbitrary corrected and raw Xi edge families.

Unlike analytic evaluation Grams and unisolvent coordinate reconstruction, the canonical
incidence Gram has no chosen nodes or existential certificate. The same fixed matrix also
classifies single-defect packets through their zero-rooted star realization and remains invariant
entry-for-entry under every injective zero-preserving shift reparametrization.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every corrected or raw Xi pair-difference canonical incidence Gram is positive semidefinite,
without a reconstruction hypothesis. -/
theorem xiPairDifferenceCanonicalIncidenceGram_posSemidef
    {V E : Type} [Fintype V] [Fintype E]
    (shift : V → ℕ) (tail head : E → V) :
    (pointedCollisionIncidenceGram shift 0 tail head).PosSemidef :=
  pointedCollisionIncidenceGram_posSemidef shift 0 tail head

/-- Canonical Xi pair-difference incidence volume is unconditionally nonnegative. -/
theorem xiPairDifferenceCanonicalIncidenceGram_det_nonneg
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]
    (shift : V → ℕ) (tail head : E → V) :
    0 ≤ (pointedCollisionIncidenceGram shift 0 tail head).det :=
  pointedCollisionIncidenceGram_det_nonneg shift 0 tail head

/-- Corrected-Xi cofinite edge reconstruction is exactly positivity of the fixed real incidence
Gram of its occupied-shift quotient. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      (pointedCollisionIncidenceGram shift 0 tail head).PosDef := by
  calc
    _ ↔ XiTransverseShiftPairIncidenceIndependent shift tail head :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        shift tail head
    _ ↔ _ := by
      exact (pointedCollisionIncidenceGram_posDef_iff_univ_indep
        (C := ℂ) shift 0 tail head).symm

/-- Corrected-Xi cofinite edge reconstruction is also exactly positive canonical incidence
volume. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      0 < (pointedCollisionIncidenceGram shift 0 tail head).det := by
  calc
    _ ↔ XiTransverseShiftPairIncidenceIndependent shift tail head :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        shift tail head
    _ ↔ _ := by
      exact (pointedCollisionIncidenceGram_det_pos_iff_univ_indep
        (C := ℂ) shift 0 tail head).symm

/-- **Corrected-Xi singular-phase law.** The canonical incidence volume vanishes exactly when
cofinite corrected pair reconstruction fails. -/
theorem
    xiTransverseShiftPairDifferenceIncidenceGram_det_eq_zero_iff_not_cofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (shift : V → ℕ) (tail head : Fin d → V) :
    (pointedCollisionIncidenceGram shift 0 tail head).det = 0 ↔
      ¬XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        shift tail head := by
  calc
    _ ↔ ¬XiTransverseShiftPairIncidenceIndependent shift tail head := by
      simpa [XiTransverseShiftPairIncidenceIndependent] using
        pointedCollisionIncidenceGram_det_eq_zero_iff_not_univ_indep
          (C := ℂ) shift 0 tail head
    _ ↔ _ :=
      (not_congr
        (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence
          shift tail head)).symm

/-- Raw even-Xi cofinite edge reconstruction has the identical fixed incidence-Gram
classification. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      (pointedCollisionIncidenceGram grade 0 tail head).PosDef := by
  calc
    _ ↔ XiEvenShiftRawPairIncidenceIndependent grade tail head :=
      xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        grade tail head
    _ ↔ _ := by
      exact (pointedCollisionIncidenceGram_posDef_iff_univ_indep
        (C := ℂ) grade 0 tail head).symm

/-- Raw even-Xi reconstruction is exactly positive volume of the canonical incidence Gram. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ↔
      0 < (pointedCollisionIncidenceGram grade 0 tail head).det := by
  calc
    _ ↔ XiEvenShiftRawPairIncidenceIndependent grade tail head :=
      xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
        grade tail head
    _ ↔ _ := by
      exact (pointedCollisionIncidenceGram_det_pos_iff_univ_indep
        (C := ℂ) grade 0 tail head).symm

/-- **Raw-Xi singular-phase law.** Zero canonical incidence volume is exactly failure of raw
pair-difference reconstruction. -/
theorem
    xiEvenShiftRawPairDifferenceIncidenceGram_det_eq_zero_iff_not_cofiniteHilbertReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (tail head : Fin d → V) :
    (pointedCollisionIncidenceGram grade 0 tail head).det = 0 ↔
      ¬XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
        grade tail head := by
  calc
    _ ↔ ¬XiEvenShiftRawPairIncidenceIndependent grade tail head := by
      simpa [XiEvenShiftRawPairIncidenceIndependent] using
        pointedCollisionIncidenceGram_det_eq_zero_iff_not_univ_indep
          (C := ℂ) grade 0 tail head
    _ ↔ _ :=
      (not_congr
        (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidence
          grade tail head)).symm

/-- **Exact Xi incidence-metric entry law.** Every arbitrary corrected or raw pair metric entry
is the signed collision count of its four endpoint grades, with grade zero deleted. -/
theorem xiPairDifferenceCanonicalIncidenceGram_apply
    {V E : Type} [Fintype V] [Fintype E]
    (shift : V → ℕ) (tail head : E → V) (e f : E) :
    pointedCollisionIncidenceGram shift 0 tail head e f =
      (if shift (head e) = shift (head f) ∧ shift (head e) ≠ 0
        then 1 else 0) -
      (if shift (head e) = shift (tail f) ∧ shift (head e) ≠ 0
        then 1 else 0) -
      (if shift (tail e) = shift (head f) ∧ shift (tail e) ≠ 0
        then 1 else 0) +
      (if shift (tail e) = shift (tail f) ∧ shift (tail e) ≠ 0
        then 1 else 0) := by
  rw [pointedCollisionIncidenceGram_apply]
  simp only [pointedCollisionIncidenceEndpointKernel_eq]

/-- An Xi edge has canonical squared incidence length zero, one, or two according as it is a
grade-collision loop, is incident to grade zero, or joins two distinct nonzero grades. -/
theorem xiPairDifferenceCanonicalIncidenceGram_apply_self
    {V E : Type} [Fintype V] [Fintype E]
    (shift : V → ℕ) (tail head : E → V) (e : E) :
    pointedCollisionIncidenceGram shift 0 tail head e e =
      if shift (head e) = shift (tail e) then 0
      else if shift (head e) = 0 ∨ shift (tail e) = 0
      then 1 else 2 := by
  exact pointedCollisionIncidenceGram_apply_self shift 0 tail head e

/-- One Xi pair edge lies in the canonical metric radical exactly when its endpoint grades
collide. -/
theorem xiPairDifferenceCanonicalIncidenceGram_apply_self_eq_zero_iff
    {V E : Type} [Fintype V] [Fintype E]
    (shift : V → ℕ) (tail head : E → V) (e : E) :
    pointedCollisionIncidenceGram shift 0 tail head e e = 0 ↔
      shift (head e) = shift (tail e) := by
  exact pointedCollisionIncidenceGram_apply_self_eq_zero_iff
    shift 0 tail head e

/-- An individual Xi pair edge has strictly positive canonical Hilbert energy exactly when its
endpoint grades are distinct, independently of every other edge. -/
theorem xiPairDifferenceCanonicalIncidenceGram_apply_self_pos_iff
    {V E : Type} [Fintype V] [Fintype E]
    (shift : V → ℕ) (tail head : E → V) (e : E) :
    0 < pointedCollisionIncidenceGram shift 0 tail head e e ↔
      shift (head e) ≠ shift (tail e) := by
  exact pointedCollisionIncidenceGram_apply_self_pos_iff
    shift 0 tail head e

/-- **Exact raw/corrected canonical-metric identity.** An injective zero-preserving shift
reparametrization changes the occupied coordinate names but preserves the complete incidence Gram
entry-for-entry, independently of whether reconstruction holds. -/
theorem xiPairDifferenceCanonicalIncidenceGram_reparam_eq
    {V E : Type} [Fintype V] [Fintype E]
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : E → V) :
    pointedCollisionIncidenceGram
        (embed ∘ grade) 0 tail head =
      pointedCollisionIncidenceGram grade 0 tail head := by
  calc
    _ = pointedCollisionIncidenceGram
        (embed ∘ grade) (embed 0) tail head := by rw [hzero]
    _ = _ := pointedCollisionIncidenceGram_comp_injective_eq
      grade 0 embed hinj tail head

/-- Doubling raw even-shift grades leaves their corrected canonical incidence metric literally
unchanged, strengthening raw/corrected phase equivalence to equality of the fixed matrices. -/
theorem xiPairDifferenceCanonicalIncidenceGram_double_eq
    {V E : Type} [Fintype V] [Fintype E]
    (grade : V → ℕ) (tail head : E → V) :
    pointedCollisionIncidenceGram
        (fun v => 2 * grade v) 0 tail head =
      pointedCollisionIncidenceGram grade 0 tail head := by
  have hdouble : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.zero_lt_succ 1) hab
  simpa [Function.comp_def] using
    xiPairDifferenceCanonicalIncidenceGram_reparam_eq
      grade (fun n : ℕ => 2 * n) hdouble rfl tail head

/-- Exact metric invariance persists after adjoining the zero-labelled root: corrected and raw
single-defect star packets have the same canonical incidence Gram for every injective
zero-preserving reparametrization. -/
theorem xiRootedStarCanonicalIncidenceGram_reparam_eq
    {I : Type} [Fintype I]
    (grade : I → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) :
    pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel grade) 0
        xiShiftRootedStarTail xiShiftRootedStarHead := by
  have hlabel :
      xiShiftRootedStarLabel (embed ∘ grade) =
        embed ∘ xiShiftRootedStarLabel grade := by
    funext v
    cases v <;> simp [xiShiftRootedStarLabel, hzero]
  rw [hlabel]
  exact xiPairDifferenceCanonicalIncidenceGram_reparam_eq
    (xiShiftRootedStarLabel grade) embed hinj hzero
    xiShiftRootedStarTail xiShiftRootedStarHead

/-- Every injective zero-preserving corrected-shift reparametrization is classified by the same
canonical Gram formed from the original raw grades. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_rawIncidenceGram_posDef
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head ↔
      (pointedCollisionIncidenceGram grade 0 tail head).PosDef := by
  calc
    _ ↔ XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
        grade embed hinj hzero tail head
    _ ↔ _ :=
      xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
        grade tail head

/-- The universal reparametrized corrected phase is likewise positive canonical raw-incidence
volume. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_rawIncidenceGram_det_pos
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head ↔
      0 < (pointedCollisionIncidenceGram grade 0 tail head).det := by
  calc
    _ ↔ XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
        grade embed hinj hzero tail head
    _ ↔ _ :=
      xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
        grade tail head

/-- Under every injective zero-preserving reparametrization, corrected canonical incidence volume
vanishes exactly when raw pair reconstruction fails. -/
theorem
    xiPairDifferenceCanonicalIncidenceGram_reparam_det_eq_zero_iff_not_rawReconstruction
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    (pointedCollisionIncidenceGram
      (embed ∘ grade) 0 tail head).det = 0 ↔
      ¬XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
        grade tail head := by
  calc
    _ ↔ ¬XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head :=
      xiTransverseShiftPairDifferenceIncidenceGram_det_eq_zero_iff_not_cofiniteHilbertReconstruction
        (embed ∘ grade) tail head
    _ ↔ _ :=
      not_congr
        (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
          grade embed hinj hzero tail head)

/-- A corrected single-defect packet reconstructs exactly when the canonical incidence Gram of
its zero-rooted star is positive definite. -/
theorem
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift ↔
      (pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).PosDef := by
  calc
    _ ↔ XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        shift).symm
    _ ↔ _ :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
        (xiShiftRootedStarLabel shift)
        xiShiftRootedStarTail xiShiftRootedStarHead

/-- A raw single-defect packet has the same canonical rooted-star incidence-Gram certificate. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      (pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel grade) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).PosDef := by
  calc
    _ ↔ XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction
        (xiShiftRootedStarLabel grade)
        xiShiftRootedStarTail xiShiftRootedStarHead :=
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_rootedStar_iff_defect
        grade).symm
    _ ↔ _ :=
      xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
        (xiShiftRootedStarLabel grade)
        xiShiftRootedStarTail xiShiftRootedStarHead

/-- **Exact rooted-star metric classification.** The canonical incidence Gram is the identity
matrix exactly off the Xi collision and zero-label locus. Thus every valid rooted-star packet is
not merely positive definite: its incidence rows are canonically orthonormal. -/
theorem xiRootedStarCanonicalIncidenceGram_eq_one_iff
    {d : ℕ} (shift : Fin d → ℕ) :
    pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) ↔
      Function.Injective shift ∧ ∀ i, shift i ≠ 0 := by
  constructor
  · intro hgram
    have hpos :
        (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel shift) 0
          xiShiftRootedStarTail xiShiftRootedStarHead).PosDef := by
      rw [hgram]
      exact Matrix.PosDef.one
    exact (xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff shift).1
      ((xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
        shift).2 hpos)
  · intro hcollisionFree
    have hlabel :
        Function.Injective (xiShiftRootedStarLabel shift) :=
      (xiShiftRootedStarLabel_injective_iff shift).2 hcollisionFree
    change
      pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel shift)
          ((xiShiftRootedStarLabel shift) none)
          (fun _ : Fin d => none) (fun i : Fin d => some i) =
        (1 : Matrix (Fin d) (Fin d) ℝ)
    exact
      pointedCollisionIncidenceGram_rootedStar_eq_one_of_injective
        (xiShiftRootedStarLabel shift) hlabel

/-- The rooted-star canonical incidence volume has no intermediate values: it is one precisely
off the collision locus and zero on it. -/
theorem xiRootedStarCanonicalIncidenceGram_det_eq_ite
    {d : ℕ} (shift : Fin d → ℕ) :
    (pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).det =
      if Function.Injective shift ∧ ∀ i, shift i ≠ 0 then 1 else 0 := by
  classical
  by_cases hcollisionFree :
      Function.Injective shift ∧ ∀ i, shift i ≠ 0
  · rw [if_pos hcollisionFree,
      (xiRootedStarCanonicalIncidenceGram_eq_one_iff shift).2 hcollisionFree]
    simp
  · rw [if_neg hcollisionFree]
    have hnotPosDef :
        ¬(pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel shift) 0
          xiShiftRootedStarTail xiShiftRootedStarHead).PosDef := by
      intro hpos
      have hreconstruction :=
        (xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
          shift).2 hpos
      exact hcollisionFree
        ((xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff shift).1
          hreconstruction)
    rw [pointedCollisionIncidenceGram] at hnotPosDef ⊢
    by_contra hdet
    exact hnotPosDef
      ((Matrix.posSemidef_gram ℝ _).posDef_iff_det_ne_zero.mpr hdet)

/-- Corrected single-defect reconstruction is equivalent to the exact unit canonical incidence
metric, discharging the weaker positive-definiteness interface. -/
theorem
    xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one
    {d : ℕ} (shift : Fin d → ℕ) :
    XiTransverseShiftPrimeDefectCofiniteHilbertReconstruction shift ↔
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff,
    xiRootedStarCanonicalIncidenceGram_eq_one_iff]

/-- Raw single-defect reconstruction has the same exact unit canonical incidence metric. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one
    {d : ℕ} (grade : Fin d → ℕ) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel grade) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff,
    xiRootedStarCanonicalIncidenceGram_eq_one_iff]

/-- The existential rooted-star coordinate-reconstruction interface is exactly the concrete unit
canonical incidence metric. -/
theorem
    pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff_incidenceGram_eq_one
    {d : ℕ} (shift : Fin d → ℕ) :
    PointedCollisionIncidenceCoordinateReconstruction
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead ↔
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff,
    xiRootedStarCanonicalIncidenceGram_eq_one_iff]

/-- **Rooted-star metric/Kirchhoff closure.** Absence of a nonzero conserved real flow is
equivalent to the exact unit incidence metric, not merely to an abstract independence condition. -/
theorem xiRootedStarKirchhoffRigidity_iff_incidenceGram_eq_one
    {d : ℕ} (shift : Fin d → ℕ) :
    (∀ weight : Fin d → ℝ,
      (∀ q : pointedCollisionIncidenceVertex
          (xiShiftRootedStarLabel shift) 0,
        (∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel shift) 0
              (xiShiftRootedStarHead e) = q then weight e else 0) =
          ∑ e, if pointedCollisionIncidenceVertexOf
              (xiShiftRootedStarLabel shift) 0
              (xiShiftRootedStarTail e) = q then weight e else 0) →
        ∀ e, weight e = 0) ↔
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
  calc
    _ ↔ PointedCollisionIncidenceCoordinateReconstruction
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead :=
      (pointedCollisionIncidenceCoordinateReconstruction_iff_vertexConservation
        (xiShiftRootedStarLabel shift) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).symm
    _ ↔ _ :=
      pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff_incidenceGram_eq_one
        shift

/-- Raw Xi reconstruction is equivalent to the exact unit incidence metric of every injectively
reparametrized corrected rooted-star packet. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarIncidenceGram_eq_one
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_eq_one,
    xiRootedStarCanonicalIncidenceGram_reparam_eq grade embed hinj hzero]

/-- The reparametrized corrected rooted-star incidence volume is one exactly in the raw
reconstruction phase. -/
theorem xiRootedStarCanonicalIncidenceGram_reparam_det_eq_one_iff_rawReconstruction
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    (pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).det = 1 ↔
      XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade := by
  constructor
  · intro hdet
    have hpos :
        (pointedCollisionIncidenceGram
          (xiShiftRootedStarLabel (embed ∘ grade)) 0
          xiShiftRootedStarTail xiShiftRootedStarHead).PosDef := by
      have hne :
          (pointedCollisionIncidenceGram
            (xiShiftRootedStarLabel (embed ∘ grade)) 0
            xiShiftRootedStarTail xiShiftRootedStarHead).det ≠ 0 := by
        rw [hdet]
        norm_num
      rw [pointedCollisionIncidenceGram] at hne ⊢
      exact (Matrix.posSemidef_gram ℝ _).posDef_iff_det_ne_zero.mpr hne
    have hcorrected :=
      (xiTransverseShiftPrimeDefectCofiniteHilbertReconstruction_iff_rootedStarIncidenceGram_posDef
        (embed ∘ grade)).2 hpos
    exact
      (xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_correctedReparam
        grade embed hinj hzero).2 hcorrected
  · intro hraw
    rw [(xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarIncidenceGram_eq_one
      grade embed hinj hzero).1 hraw]
    simp

/-- Failure of raw reconstruction is exactly zero canonical incidence volume after every
injective zero-preserving corrected reparametrization. -/
theorem xiRootedStarCanonicalIncidenceGram_reparam_det_eq_zero_iff_not_rawReconstruction
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    (pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead).det = 0 ↔
      ¬XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade := by
  constructor
  · intro hdet hraw
    have hone :=
      (xiRootedStarCanonicalIncidenceGram_reparam_det_eq_one_iff_rawReconstruction
        grade embed hinj hzero).2 hraw
    linarith
  · intro hnotRaw
    rw [xiRootedStarCanonicalIncidenceGram_reparam_eq grade embed hinj hzero,
      xiRootedStarCanonicalIncidenceGram_det_eq_ite]
    have hnotCollisionFree :
        ¬(Function.Injective grade ∧ ∀ i, grade i ≠ 0) := by
      intro hcollisionFree
      exact hnotRaw
        ((xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff grade).2
          hcollisionFree)
    rw [if_neg hnotCollisionFree]

/-- Raw reconstruction discharges the existential incidence-coordinate interface for every
injectively reparametrized corrected rooted-star packet. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarCoordinateReconstruction
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      PointedCollisionIncidenceCoordinateReconstruction
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead := by
  calc
    _ ↔ pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarIncidenceGram_eq_one
        grade embed hinj hzero
    _ ↔ _ :=
      (pointedCollisionIncidenceCoordinateReconstruction_xiRootedStar_iff_incidenceGram_eq_one
        (embed ∘ grade)).symm

/-- Raw reconstruction is also exactly Kirchhoff rigidity of every reparametrized corrected
rooted-star incidence network. -/
theorem
    xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarKirchhoffRigidity
    {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ)
    (hinj : Function.Injective embed) (hzero : embed 0 = 0) :
    XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
      (∀ weight : Fin d → ℝ,
        (∀ q : pointedCollisionIncidenceVertex
            (xiShiftRootedStarLabel (embed ∘ grade)) 0,
          (∑ e, if pointedCollisionIncidenceVertexOf
                (xiShiftRootedStarLabel (embed ∘ grade)) 0
                (xiShiftRootedStarHead e) = q then weight e else 0) =
            ∑ e, if pointedCollisionIncidenceVertexOf
                (xiShiftRootedStarLabel (embed ∘ grade)) 0
                (xiShiftRootedStarTail e) = q then weight e else 0) →
          ∀ e, weight e = 0) := by
  calc
    _ ↔ pointedCollisionIncidenceGram
        (xiShiftRootedStarLabel (embed ∘ grade)) 0
        xiShiftRootedStarTail xiShiftRootedStarHead =
        (1 : Matrix (Fin d) (Fin d) ℝ) :=
      xiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction_iff_reparamRootedStarIncidenceGram_eq_one
        grade embed hinj hzero
    _ ↔ _ :=
      (xiRootedStarKirchhoffRigidity_iff_incidenceGram_eq_one
        (embed ∘ grade)).symm

/-- **Universal canonical incidence-Gram Xi phase.** Reparametrized corrected reconstruction
simultaneously detects raw reconstruction, fixed canonical Gram positivity and volume,
unisolvent coordinate dual recovery, and absence of a nonzero real Kirchhoff circulation. -/
theorem xiPairDifferenceCanonicalIncidenceGramCofiniteHilbertPhase_reparam_iff
    {V : Type} [Fintype V] {d : ℕ}
    (grade : V → ℕ) (embed : ℕ → ℕ) (hinj : Function.Injective embed)
    (hzero : embed 0 = 0) (tail head : Fin d → V) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
        (embed ∘ grade) tail head ↔
      XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction grade tail head ∧
        (pointedCollisionIncidenceGram grade 0 tail head).PosDef ∧
        0 < (pointedCollisionIncidenceGram grade 0 tail head).det ∧
        PointedCollisionIncidenceCoordinateReconstruction grade 0 tail head ∧
        (∀ weight : Fin d → ℝ,
          (∀ q : pointedCollisionIncidenceVertex grade 0,
            (∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (head e) = q then weight e else 0) =
              ∑ e, if pointedCollisionIncidenceVertexOf grade 0
                (tail e) = q then weight e else 0) →
            ∀ e, weight e = 0) := by
  constructor
  · intro hcorrected
    have hraw :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
        grade embed hinj hzero tail head).1 hcorrected
    exact ⟨hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_posDef
        grade tail head).1 hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceGram_det_pos
        grade tail head).1 hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_incidenceCoordinateReconstruction
        grade tail head).1 hraw,
      (xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_vertexConservation
        grade tail head).1 hraw⟩
  · rintro ⟨hraw, _hgram, _hdet, _hcoordinate, _hkirchhoff⟩
    exact
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_reparam_iff_raw
        grade embed hinj hzero tail head).2 hraw

end

end RHTower
