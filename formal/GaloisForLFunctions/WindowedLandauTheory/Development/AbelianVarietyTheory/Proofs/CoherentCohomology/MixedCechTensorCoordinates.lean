import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.JoinedCechDatum
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ScalarCechGrading
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! The tensor product of the two unaugmented cochain modules has one
coordinate on each pair of nonempty intersections. -/

noncomputable section

open TensorProduct GlobalTheory.WH

namespace HTGeometry.FinsetCechDatum

variable {K : Type} [Field K]

private def nonemptyCoordinates {T : Type} [LinearOrder T]
    (A : FinsetCechDatum.{0} T) [∀ s, Module K (A.obj s)] :
    A.regular (K := K) ≃ₗ[K] (∀ s : {s : Finset T // s.Nonempty}, A.obj s.1) where
  toFun x s := x.1 s.1
  invFun y := ⟨fun s => if hs : s.Nonempty then y ⟨s, hs⟩ else 0, by
    change (if hs : (∅ : Finset T).Nonempty then y ⟨∅, hs⟩ else 0) = 0
    simp⟩
  left_inv x := Subtype.ext (funext fun I => by
    rcases I.eq_empty_or_nonempty with rfl | hI
    · change (if hs : (∅ : Finset T).Nonempty then
          (fun s : {s : Finset T // s.Nonempty} => x.1 s.1) ⟨∅, hs⟩ else 0) = x.1 ∅
      rw [dif_neg Finset.not_nonempty_empty]
      exact x.2.symm
    · exact dif_pos hI)
  right_inv x := funext fun I => dif_pos I.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  (A : FinsetCechDatum.{0} ι) (B : FinsetCechDatum.{0} κ)
  (D : FinsetCechDatum.{0} (ι ⊕ₗ κ))
  [∀ s, Module K (A.obj s)] [∀ t, Module K (B.obj t)] [∀ u, Module K (D.obj u)]

variable (hzero : ∀ s t, ¬ (s.Nonempty ∧ t.Nonempty) → Subsingleton (D.obj (uni s t)))

private def mixedCoordinates :
    D.regular (K := K) ≃ₗ[K]
      (∀ s : {s : Finset ι // s.Nonempty}, ∀ t : {t : Finset κ // t.Nonempty}, D.obj (uni s.1 t.1)) := by
  classical
  let Y := ∀ s : {s : Finset ι // s.Nonempty}, ∀ t : {t : Finset κ // t.Nonempty}, D.obj (uni s.1 t.1)
  let π : D.regular (K := K) →ₗ[K] Y :=
    { toFun := fun x s t => x.1 (uni s.1 t.1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.ofBijective π ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    funext u
    rw [← uni_lft_rgt u]
    by_cases e : (lft u).Nonempty ∧ (rgt u).Nonempty
    · exact congrFun (congrFun h ⟨lft u, e.1⟩) ⟨rgt u, e.2⟩
    · exact (hzero _ _ e).elim _ _
  · intro y
    let a (s : Finset ι) (t : Finset κ) : D.obj (uni s t) :=
      if hs : s.Nonempty then if ht : t.Nonempty then y ⟨s, hs⟩ ⟨t, ht⟩ else 0 else 0
    let x := (D.cochainSlices K).symm a
    have hx (s : Finset ι) (t : Finset κ) : x (uni s t) = a s t :=
      congrFun (congrFun ((D.cochainSlices K).apply_symm_apply a) s) t
    have h₀ : Subsingleton (D.obj (∅ : Finset (ι ⊕ₗ κ))) :=
      (uni_empty_empty (ι := ι) (κ := κ)) ▸ hzero ∅ ∅ (fun e => Finset.not_nonempty_empty e.1)
    refine ⟨⟨x, h₀.elim _ _⟩, ?_⟩
    funext s t
    change x (uni s.1 t.1) = y s t
    rw [hx]
    simp only [a, dif_pos s.2, dif_pos t.2]

variable [Fintype ι] [Fintype κ]
  (e : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
    (A.obj s ⊗[K] B.obj t ≃ₗ[K] D.obj (uni s t)))

/-- The coefficient isomorphisms on the mixed intersections give a linear
equivalence from the tensor cochains onto the joined cochains. -/
def mixedTensorEquiv : A.regular (K := K) ⊗[K] B.regular (K := K) ≃ₗ[K] D.regular (K := K) :=
  TensorProduct.congr (nonemptyCoordinates A) (nonemptyCoordinates B) ≪≫ₗ
    TensorProduct.piLeft K _ _ ≪≫ₗ
    (LinearEquiv.piCongrRight fun s => TensorProduct.piRight K K
      (A.obj (s : {s : Finset ι // s.Nonempty}).1) _) ≪≫ₗ
    (LinearEquiv.piCongrRight fun s => LinearEquiv.piCongrRight fun t => e s.1 t.1 s.2 t.2) ≪≫ₗ
    (mixedCoordinates D hzero).symm

theorem mixedTensorEquiv_tmul (a : A.regular (K := K)) (b : B.regular (K := K))
    (s : Finset ι) (t : Finset κ) (hs : s.Nonempty) (ht : t.Nonempty) :
    (mixedTensorEquiv A B D hzero e (a ⊗ₜ b)).1 (uni s t) =
      e s t hs ht (a.1 s ⊗ₜ b.1 t) := by
  let c := mixedCoordinates (K := K) D hzero
  let z := (TensorProduct.congr (nonemptyCoordinates A) (nonemptyCoordinates B)) (a ⊗ₜ[K] b)
  let w := (TensorProduct.piLeft K _ _ ≪≫ₗ
    (LinearEquiv.piCongrRight fun s => TensorProduct.piRight K K
      (A.obj (s : {s : Finset ι // s.Nonempty}).1) _) ≪≫ₗ
      (LinearEquiv.piCongrRight fun s => LinearEquiv.piCongrRight fun t => e s.1 t.1 s.2 t.2)) z
  have h := congrFun (congrFun (c.apply_symm_apply w) ⟨s, hs⟩) ⟨t, ht⟩
  change (mixedTensorEquiv A B D hzero e (a ⊗ₜ b)).1 (uni s t) = w ⟨s, hs⟩ ⟨t, ht⟩ at h
  refine h.trans ?_
  simp [w, z, nonemptyCoordinates]

end HTGeometry.FinsetCechDatum
