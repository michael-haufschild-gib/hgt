import GaloisForLFunctions.RHTower.XiRootDeletedCanonicalReconstructionGraphicConnector
import GaloisForLFunctions.RHTower.XiCanonicalIncidenceGramHilbertPhase

/-!
# Root-deleted canonical vertex recovery and Xi edge Hilbert phases

Exact root-deleted valuation reconstruction discharges the injective-label hypothesis in the
HTGeometry specialization from pointed collision incidence to ordinary rooted incidence.  Once
that fixed vertex reconstruction is available, corrected and raw Xi edge reconstruction,
positive canonical edge Gram, positive edge volume, and failure through zero volume are governed
by the ordinary rooted graphic matroid.

The joint vertex-and-edge phase is unconditional: it holds exactly when all vertex labels are
distinct and the rooted edge packet has no nonzero Kirchhoff circulation.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexOrder Differential

/-- **Canonical-reconstruction discharge of the collision quotient.**  Exact fixed nonroot
valuation recovery supplies injectivity, so the pointed collision-incidence matroid becomes the
ordinary rooted incidence matroid over every coefficient field. -/
theorem
    pointedCollisionIncidenceMatroid_eq_rooted_of_xiRootDeletedCanonicalReconstruction
    {C : Type} [Field C] {N : ℕ} {E : Type}
    [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : E → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    pointedCollisionIncidenceMatroid (C := C) shift 0 tail head =
      rootedIncidenceMatroid (C := C) root tail head := by
  have hinjective :=
    (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
      root shift hroot p).1 hrec
  simpa [hroot] using
    (pointedCollisionIncidenceMatroid_eq_rootedIncidenceMatroid_of_injective
      (C := C) shift root hinjective tail head)

/-- Under one fixed canonical vertex reconstruction, corrected Xi edge reconstruction is exactly
ordinary rooted graphic independence; no collision quotient remains. -/
theorem
    xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_rootedIncidence_of_rootDeletedCanonicalReconstruction
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : Fin d → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  rw [xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_incidence]
  change (pointedCollisionIncidenceMatroid
    (C := ℂ) shift 0 tail head).Indep Set.univ ↔ _
  rw [
    pointedCollisionIncidenceMatroid_eq_rooted_of_xiRootDeletedCanonicalReconstruction
      root shift hroot p tail head hrec]

/-- The same fixed canonical vertex reconstruction identifies raw even-Xi edge recovery with
ordinary rooted graphic independence. -/
theorem
    xiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction_iff_rootedIncidence_of_rootDeletedCanonicalReconstruction
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : Fin d → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  calc
    _ ↔ XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction
          shift tail head :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_raw
        shift tail head).symm
    _ ↔ _ :=
      xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_rootedIncidence_of_rootDeletedCanonicalReconstruction
        root shift hroot p tail head hrec

/-- Canonical edge-Gram positivity becomes ordinary real rooted graphic independence after fixed
nonroot vertex reconstruction. -/
theorem
    pointedCollisionIncidenceGram_posDef_iff_rootedIncidence_of_xiRootDeletedCanonicalReconstruction
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : E → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    (pointedCollisionIncidenceGram shift 0 tail head).PosDef ↔
      (rootedIncidenceMatroid (C := ℝ) root tail head).Indep Set.univ := by
  rw [pointedCollisionIncidenceGram_posDef_iff_univ_indep (C := ℝ),
    pointedCollisionIncidenceMatroid_eq_rooted_of_xiRootDeletedCanonicalReconstruction
      (C := ℝ) root shift hroot p tail head hrec]

/-- Positive canonical edge volume has the same rooted graphic classification. -/
theorem
    pointedCollisionIncidenceGram_det_pos_iff_rootedIncidence_of_xiRootDeletedCanonicalReconstruction
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : E → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    0 < (pointedCollisionIncidenceGram shift 0 tail head).det ↔
      (rootedIncidenceMatroid (C := ℝ) root tail head).Indep Set.univ := by
  rw [pointedCollisionIncidenceGram_det_pos_iff_univ_indep (C := ℝ),
    pointedCollisionIncidenceMatroid_eq_rooted_of_xiRootDeletedCanonicalReconstruction
      (C := ℝ) root shift hroot p tail head hrec]

/-- The complementary singular phase is literal zero canonical edge volume exactly when the
ordinary rooted edge packet is dependent. -/
theorem
    pointedCollisionIncidenceGram_det_eq_zero_iff_not_rootedIncidence_of_xiRootDeletedCanonicalReconstruction
    {N : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : E → Fin (N + 1))
    (hrec :
      XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p) :
    (pointedCollisionIncidenceGram shift 0 tail head).det = 0 ↔
      ¬(rootedIncidenceMatroid (C := ℝ) root tail head).Indep Set.univ := by
  rw [pointedCollisionIncidenceGram_det_eq_zero_iff_not_univ_indep (C := ℝ),
    pointedCollisionIncidenceMatroid_eq_rooted_of_xiRootDeletedCanonicalReconstruction
      (C := ℝ) root shift hroot p tail head hrec]

/-- **Joint canonical vertex/edge Hilbert phase.**  Exact fixed recovery of every nonroot vertex
coefficient together with complete corrected-Xi edge recovery is equivalent to distinct rooted
labels and ordinary rooted graphic independence. -/
theorem
    xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      Function.Injective shift ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  constructor
  · rintro ⟨hvertex, hedge⟩
    have hinjective :=
      (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
        root shift hroot p).1 hvertex
    have hrooted :=
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_rootedIncidence_of_rootDeletedCanonicalReconstruction
        root shift hroot p tail head hvertex).1 hedge
    exact ⟨hinjective, hrooted⟩
  · rintro ⟨hinjective, hrooted⟩
    have hvertex :=
      (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_injective
        root shift hroot p).2 hinjective
    exact ⟨hvertex,
      (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_rootedIncidence_of_rootDeletedCanonicalReconstruction
        root shift hroot p tail head hvertex).2 hrooted⟩

/-- **Prime-free root-deleted vertex/edge Hilbert phase.**  Complete nonroot prime-jet recovery
after every finite prime deletion, together with complete corrected-Xi edge recovery, is exactly
injectivity of the rooted labeling plus ordinary rooted graphic independence.  The auxiliary
prime used by canonical valuation recovery is discharged internally. -/
theorem
    xiTransverseRootDeletedPrimeJetAperturePairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (m : ℕ)
    (tail head : Fin d → Fin (N + 1)) :
    XiTransverseRootDeletedPrimeJetApertureCofiniteHilbertReconstruction
          root shift m ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      Function.Injective shift ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction
          root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head :=
      and_congr
        (xiTransverseRootDeletedPrimeValuationCanonicalReconstruction_iff_cofiniteApertureHilbertReconstruction
          root shift hroot p m).symm
        Iff.rfl
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
        root shift hroot p tail head

/-- The joint raw even-Xi phase has the identical rooted graphic classification. -/
theorem
    xiTransverseRootDeletedCanonicalRawPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ∧
        XiEvenShiftRawPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      Function.Injective shift ∧
        (rootedIncidenceMatroid (C := ℂ) root tail head).Indep Set.univ := by
  calc
    _ ↔ XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ∧
          XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head :=
      and_congr Iff.rfl
        (xiTransverseShiftPairDifferenceCofiniteHilbertReconstruction_iff_raw
          shift tail head).symm
    _ ↔ _ :=
      xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
        root shift hroot p tail head

/-- **Joint phase as an exact Kirchhoff law.**  Fixed vertex recovery and corrected Xi edge
recovery hold together exactly when labels are distinct and every complex flow conserved at all
vertices is zero.  The root conservation equation is discharged by total incidence. -/
theorem
    xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_vertexConservation
    {N d : ℕ}
    (root : Fin (N + 1)) (shift : Fin (N + 1) → ℕ)
    (hroot : shift root = 0) (p : Nat.Primes)
    (tail head : Fin d → Fin (N + 1)) :
    XiTransverseRootDeletedPrimeValuationCanonicalReconstruction root shift p ∧
        XiTransverseShiftPairDifferenceCofiniteHilbertReconstruction shift tail head ↔
      Function.Injective shift ∧
        ∀ weight : Fin d → ℂ,
          (∀ v : Fin (N + 1),
            (∑ e, if head e = v then weight e else 0) =
              ∑ e, if tail e = v then weight e else 0) →
            ∀ e, weight e = 0 := by
  rw [
    xiTransverseRootDeletedCanonicalPairDifferenceCofiniteHilbertPhase_iff_rootedIncidence
      root shift hroot p tail head,
    rootedIncidenceMatroid_univ_indep_iff_vertex_conservation]

end

end RHTower
