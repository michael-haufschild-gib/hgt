import GaloisForLFunctions.HTGeometry.ContinuousAffineDefect
import GaloisForLFunctions.HTGeometry.MultivariateEntireAffinePullback
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Separation of finite affine node packets

For finitely many distinct affine automorphisms and finitely many evaluation rows, a generic base
configuration makes every row-by-frame image node distinct.  Each forbidden collision is contained
in the zero fiber of one proper continuous affine scalar observation; finitely many open dense
complements therefore have nonempty intersection.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Apply one affine frame to one row of a base configuration. -/
def affineNodeMap {d : ℕ} {row ι : Type*}
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x : row × ι) : (row → Fin d → ℂ) →ᴬ[ℂ] (Fin d → ℂ) :=
  (frame x.2).toContinuousAffineMap.comp
    (ContinuousLinearMap.proj x.1).toContinuousAffineMap

@[simp]
theorem affineNodeMap_apply {d : ℕ} {row ι : Type*}
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x : row × ι) (base : row → Fin d → ℂ) :
    affineNodeMap frame x base = frame x.2 (base x.1) :=
  rfl

/-- One coordinate of the difference between two row-by-frame image nodes. -/
def affineNodeDifferenceCoordinate {d : ℕ} {row ι : Type*}
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x y : row × ι) (k : Fin d) : (row → Fin d → ℂ) →ᴬ[ℂ] ℂ :=
  (ContinuousLinearMap.proj k).toContinuousAffineMap.comp (affineNodeMap frame x) -
    (ContinuousLinearMap.proj k).toContinuousAffineMap.comp (affineNodeMap frame y)

@[simp]
theorem affineNodeDifferenceCoordinate_apply {d : ℕ} {row ι : Type*}
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (x y : row × ι) (k : Fin d) (base : row → Fin d → ℂ) :
    affineNodeDifferenceCoordinate frame x y k base =
      frame x.2 (base x.1) k - frame y.2 (base y.1) k :=
  rfl

/-- Every pair of distinct row-by-frame occurrences is separated by some coordinate observation
at some base configuration. -/
theorem exists_affineNodeDifferenceCoordinate_ne_zero
    {d : ℕ} (hd : 0 < d) {row ι : Type*} [DecidableEq row]
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (hframe : Function.Injective frame)
    (x y : row × ι) (hxy : x ≠ y) :
    ∃ k : Fin d, ∃ base : row → Fin d → ℂ,
      affineNodeDifferenceCoordinate frame x y k base ≠ 0 := by
  rcases x with ⟨a, i⟩
  rcases y with ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    have hij : i ≠ j := by
      intro hij
      apply hxy
      simp [hij]
    have hef : frame i ≠ frame j := fun h ↦ hij (hframe h)
    have hpoint : ∃ z : Fin d → ℂ, frame i z ≠ frame j z := by
      by_contra h
      apply hef
      ext z
      exact not_ne_iff.mp ((not_exists.mp h) z)
    obtain ⟨z, hz⟩ := hpoint
    have hcoord : ∃ k : Fin d, frame i z k ≠ frame j z k := by
      by_contra h
      apply hz
      funext k
      exact not_ne_iff.mp ((not_exists.mp h) k)
    obtain ⟨k, hk⟩ := hcoord
    refine ⟨k, fun _ ↦ z, ?_⟩
    simpa using sub_ne_zero.mpr hk
  · let k : Fin d := ⟨0, hd⟩
    let onePoint : Fin d → ℂ := fun _ ↦ 1
    let base : row → Fin d → ℂ :=
      Function.update
        (Function.update (fun _ ↦ 0) a ((frame i).symm 0))
        b ((frame j).symm onePoint)
    refine ⟨k, base, ?_⟩
    simp [affineNodeDifferenceCoordinate_apply, base, hab, onePoint, k]

/-- Distinct ordered occurrence pairs. -/
abbrev DistinctAffineOccurrences (row ι : Type*) :=
  {p : (row × ι) × (row × ι) // p.1 ≠ p.2}

/-- A chosen scalar collision detector for one distinct occurrence pair. -/
def affineOccurrenceCollisionDetector
    {d : ℕ} (hd : 0 < d) {row ι : Type*} [DecidableEq row]
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (hframe : Function.Injective frame)
    (q : DistinctAffineOccurrences row ι) :
    (row → Fin d → ℂ) →ᴬ[ℂ] ℂ :=
  affineNodeDifferenceCoordinate frame q.1.1 q.1.2
    (Classical.choose
      (exists_affineNodeDifferenceCoordinate_ne_zero hd frame hframe q.1.1 q.1.2 q.2))

theorem affineOccurrenceCollisionDetector_has_witness
    {d : ℕ} (hd : 0 < d) {row ι : Type*} [DecidableEq row]
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (hframe : Function.Injective frame)
    (q : DistinctAffineOccurrences row ι) :
    ∃ base : row → Fin d → ℂ,
      affineOccurrenceCollisionDetector hd frame hframe q base ≠ 0 := by
  let h := exists_affineNodeDifferenceCoordinate_ne_zero
    hd frame hframe q.1.1 q.1.2 q.2
  exact ⟨Classical.choose (Classical.choose_spec h), Classical.choose_spec (Classical.choose_spec h)⟩

/-- **Finite affine node-packet separation.** For positive dimension, finitely many distinct
affine automorphisms admit a base configuration whose full row-by-frame image packet is injective. -/
theorem exists_injective_affineNodePacket
    {d : ℕ} (hd : 0 < d) {row ι : Type*}
    [Fintype row] [DecidableEq row] [Fintype ι] [DecidableEq ι]
    (frame : ι → (Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))
    (hframe : Function.Injective frame) :
    ∃ base : row → Fin d → ℂ,
      Function.Injective (fun x : row × ι ↦ frame x.2 (base x.1)) := by
  let bad : DistinctAffineOccurrences row ι → Set (row → Fin d → ℂ) := fun q ↦
    {base | affineOccurrenceCollisionDetector hd frame hframe q base = 0}
  have hbad : ∀ q, IsNowhereDense (bad q) := by
    intro q
    obtain ⟨base, hbase⟩ := affineOccurrenceCollisionDetector_has_witness hd frame hframe q
    exact isNowhereDense_continuousAffineMap_zero_of_witness
      (affineOccurrenceCollisionDetector hd frame hframe q) base hbase
  have hopen : ∀ q, IsOpen (bad q)ᶜ := fun q ↦
    (isClosed_continuousAffineMap_zero
      (affineOccurrenceCollisionDetector hd frame hframe q)).isOpen_compl
  have hdense : ∀ q, Dense (bad q)ᶜ := fun q ↦
    interior_eq_empty_iff_dense_compl.mp
      ((isClosed_continuousAffineMap_zero
        (affineOccurrenceCollisionDetector hd frame hframe q)).isNowhereDense_iff.mp (hbad q))
  have hall : Dense (⋂ q, (bad q)ᶜ) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨base, hbase⟩ := hall.nonempty
  refine ⟨base, ?_⟩
  intro x y hxy
  by_contra hne
  let q : DistinctAffineOccurrences row ι := ⟨(x, y), hne⟩
  have hnot : base ∉ bad q := by
    simpa using hbase q
  apply hnot
  change affineOccurrenceCollisionDetector hd frame hframe q base = 0
  apply sub_eq_zero.mpr
  exact congrFun hxy
    (Classical.choose
      (exists_affineNodeDifferenceCoordinate_ne_zero hd frame hframe q.1.1 q.1.2 q.2))

end

end GaloisForLFunctions.HTGeometry
