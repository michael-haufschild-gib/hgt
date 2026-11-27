import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.CechSupport
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechFaces
import Mathlib.Order.Interval.Set.OrdConnected

/-! Acyclicity of an augmented joined complex shifts the cohomology of
its lower face to the cohomology supported on nonempty mixed intersections. -/

noncomputable section

open CategoryTheory GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

variable {ι κ : Type}

def nonemptyIntersections (T : Type) : Set (Finset T) := {s | s.Nonempty}

theorem nonemptyIntersections_ordConnected (T : Type) : (nonemptyIntersections T).OrdConnected := by
  constructor
  intro s hs t _ u hu
  exact hs.mono hu.1

def joinedSupport (P : Set (Finset ι)) (Q : Set (Finset κ)) : Set (Finset (ι ⊕ₗ κ)) :=
  {s | lft s ∈ P ∧ rgt s ∈ Q}

theorem joinedSupport_ordConnected {P : Set (Finset ι)} {Q : Set (Finset κ)}
    (hP : P.OrdConnected) (hQ : Q.OrdConnected) : (joinedSupport P Q).OrdConnected := by
  constructor
  intro s hs t ht u hu
  exact ⟨hP.out' hs.1 ht.1 ⟨lft_monotone hu.1, lft_monotone hu.2⟩,
    hQ.out' hs.2 ht.2 ⟨rgt_monotone hu.1, rgt_monotone hu.2⟩⟩

private theorem left_join_subset (P : Set (Finset ι)) :
    joinedSupport P (nonemptyIntersections κ) ⊆ lft ⁻¹' P := fun _ h => h.1

theorem left_join_upper (P : Set (Finset ι)) ⦃s t : Finset (ι ⊕ₗ κ)⦄
    (hs : s ∈ joinedSupport P (nonemptyIntersections κ)) (ht : t ∈ lft ⁻¹' P) (h : s ⊆ t) :
    t ∈ joinedSupport P (nonemptyIntersections κ) :=
  ⟨ht, hs.2.mono (rgt_monotone h)⟩

private theorem right_join_subset (P : Set (Finset κ)) :
    joinedSupport (nonemptyIntersections ι) P ⊆ rgt ⁻¹' P := fun _ h => h.2

theorem right_join_upper (P : Set (Finset κ)) ⦃s t : Finset (ι ⊕ₗ κ)⦄
    (hs : s ∈ joinedSupport (nonemptyIntersections ι) P) (ht : t ∈ rgt ⁻¹' P) (h : s ⊆ t) :
    t ∈ joinedSupport (nonemptyIntersections ι) P :=
  ⟨hs.1.mono (lft_monotone h), ht⟩

variable {R : Type} [CommRing R] [LinearOrder ι] [LinearOrder κ]
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ)) [∀ s, Module R (D.obj s)]
  (hD : ∀ {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) (r : R) (x : D.obj s),
    D.res h (r • x) = r • D.res h x)

private abbrev leftFaceComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  (D.leftSlice (∅ : Finset κ)).linearComplex (D.leftSlice_linear (R := R) hD ∅)

private abbrev rightFaceComplex : CochainComplex (ModuleCat.{0} R) ℕ :=
  (D.rightSlice (∅ : Finset ι)).linearComplex (D.rightSlice_linear (R := R) hD ∅)

/-- The lower face of the augmented right support compares with the
joined support whose right intersections are nonempty. -/
theorem nonempty_homology_equiv_leftJoin_succ
    (P : Set (Finset ι)) (hP : P.OrdConnected)
    (ha : ((D.truncate (R := R) ((@lft ι κ) ⁻¹' P) (hP.preimage_mono lft_monotone)).linearComplex
      (D.truncate_linear _ _ hD)).Acyclic) (n : ℕ) :
    let Q := (@lft ι κ) ⁻¹' P
    let T := joinedSupport P (nonemptyIntersections κ)
    let hQ : Q.OrdConnected := hP.preimage_mono lft_monotone
    let hT := joinedSupport_ordConnected hP (nonemptyIntersections_ordConnected κ)
    let hS := supportDiff_ordConnected hQ (left_join_upper P)
    Nonempty (((D.truncate (R := R) (Q \ T) hS).leftFaceComplex
      (D.truncate_linear (Q \ T) hS hD)).homology n ≃ₗ[R]
      ((D.truncate T hT).linearComplex (D.truncate_linear T hT hD)).homology (n + 1)) := by
  let Q := (@lft ι κ) ⁻¹' P
  let T := joinedSupport P (nonemptyIntersections κ)
  let hQ : Q.OrdConnected := hP.preimage_mono lft_monotone
  let hT := joinedSupport_ordConnected hP (nonemptyIntersections_ordConnected κ)
  let hS := supportDiff_ordConnected hQ (left_join_upper P)
  let A := D.truncate (R := R) (Q \ T) hS
  let hA {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) (r : R) (x : A.obj s) :
      A.res h (r • x) = r • A.res h x :=
    D.truncate_linear (Q \ T) hS hD h r x
  have hzero (s : Finset (ι ⊕ₗ κ)) (hs : rgt s ≠ ∅) : Subsingleton (A.obj s) :=
    D.subsingleton_truncate_obj (Q \ T) hS s fun hz => hz.2
      ⟨hz.1, Finset.nonempty_iff_ne_empty.mpr hs⟩
  obtain ⟨E⟩ := D.nonempty_homology_equiv_truncate_succ hT hQ
    (left_join_subset P) (left_join_upper P) hD ha n
  exact ⟨(HomologicalComplex.homologyMapIso (A.linearComplexIsoLeftFace hA hzero).symm n).toLinearEquiv.trans E⟩

/-- The lower face of the augmented left support compares with the
joined support whose left intersections are nonempty. -/
theorem nonempty_homology_equiv_rightJoin_succ
    (P : Set (Finset κ)) (hP : P.OrdConnected)
    (ha : ((D.truncate (R := R) ((@rgt ι κ) ⁻¹' P) (hP.preimage_mono rgt_monotone)).linearComplex
      (D.truncate_linear _ _ hD)).Acyclic) (n : ℕ) :
    let Q := (@rgt ι κ) ⁻¹' P
    let T := joinedSupport (nonemptyIntersections ι) P
    let hQ : Q.OrdConnected := hP.preimage_mono rgt_monotone
    let hT := joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι) hP
    let hS := supportDiff_ordConnected hQ (right_join_upper P)
    Nonempty (((D.truncate (R := R) (Q \ T) hS).rightFaceComplex
      (D.truncate_linear (Q \ T) hS hD)).homology n ≃ₗ[R]
      ((D.truncate T hT).linearComplex (D.truncate_linear T hT hD)).homology (n + 1)) := by
  let Q := (@rgt ι κ) ⁻¹' P
  let T := joinedSupport (nonemptyIntersections ι) P
  let hQ : Q.OrdConnected := hP.preimage_mono rgt_monotone
  let hT := joinedSupport_ordConnected (nonemptyIntersections_ordConnected ι) hP
  let hS := supportDiff_ordConnected hQ (right_join_upper P)
  let A := D.truncate (R := R) (Q \ T) hS
  let hA {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) (r : R) (x : A.obj s) :
      A.res h (r • x) = r • A.res h x :=
    D.truncate_linear (Q \ T) hS hD h r x
  have hzero (s : Finset (ι ⊕ₗ κ)) (hs : lft s ≠ ∅) : Subsingleton (A.obj s) :=
    D.subsingleton_truncate_obj (Q \ T) hS s fun hz => hz.2
      ⟨Finset.nonempty_iff_ne_empty.mpr hs, hz.1⟩
  obtain ⟨E⟩ := D.nonempty_homology_equiv_truncate_succ hT hQ
    (right_join_subset P) (right_join_upper P) hD ha n
  exact ⟨(HomologicalComplex.homologyMapIso (A.linearComplexIsoRightFace hA hzero).symm n).toLinearEquiv.trans E⟩

end HTGeometry.FinsetCechDatum
