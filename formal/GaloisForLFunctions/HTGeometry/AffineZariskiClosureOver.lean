import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Basic

/-!
# Affine Zariski closure over a coefficient ring

The Zariski closure of a set of points of affine space `ι → L`, relative to a coefficient ring `K`
mapping into `L`, built directly from polynomial zero loci.  The Galois connection between zero
loci and vanishing ideals gives extensivity, monotonicity, idempotence, and the universal property
of a closure operator; Zariski-closed sets are stable under arbitrary intersections and finite
unions, so they are the closed sets of a topology.

`ZariskiDenseOver K X` says that the closure of `X` is everything.  Density passes to supersets,
which is the only property a density hypothesis is used through when a closure of a dense set is
compared with a minimal dense closed subgroup.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι K L : Type*} [CommRing K] [CommRing L] [Algebra K L]

/-- Common zero locus of a family of polynomials over `K`. -/
def zariskiZeroLocusOver (S : Set (MvPolynomial ι K)) : Set (ι → L) :=
  {x | ∀ P ∈ S, MvPolynomial.aeval x P = 0}

/-- Polynomials over `K` vanishing on every point of `X`. -/
def zariskiVanishingIdealOver (X : Set (ι → L)) : Ideal (MvPolynomial ι K) where
  carrier := {P | ∀ x ∈ X, MvPolynomial.aeval x P = 0}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ x hx
    simp [hP x hx, hQ x hx]
  smul_mem' := by
    intro P Q hQ x hx
    simp [hQ x hx]

@[simp]
theorem mem_zariskiZeroLocusOver_iff {S : Set (MvPolynomial ι K)} {x : ι → L} :
    x ∈ zariskiZeroLocusOver (L := L) S ↔ ∀ P ∈ S, MvPolynomial.aeval x P = 0 :=
  Iff.rfl

@[simp]
theorem mem_zariskiVanishingIdealOver_iff {X : Set (ι → L)} {P : MvPolynomial ι K} :
    P ∈ zariskiVanishingIdealOver (K := K) X ↔ ∀ x ∈ X, MvPolynomial.aeval x P = 0 :=
  Iff.rfl

/-- Zero loci and vanishing ideals form the defining Zariski Galois connection. -/
theorem subset_zariskiZeroLocusOver_iff {X : Set (ι → L)} {S : Set (MvPolynomial ι K)} :
    X ⊆ zariskiZeroLocusOver S ↔
      S ⊆ (zariskiVanishingIdealOver (K := K) (L := L) X : Set (MvPolynomial ι K)) := by
  constructor
  · intro h P hP x hx
    exact h hx P hP
  · intro h x hx P hP
    exact h hP x hx

/-- Affine Zariski closure over `K`, evaluated in the `K`-algebra `L`. -/
def zariskiClosureOver (K : Type*) {ι L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (X : Set (ι → L)) : Set (ι → L) :=
  zariskiZeroLocusOver
    (zariskiVanishingIdealOver (K := K) (L := L) X : Set (MvPolynomial ι K))

/-- A set is Zariski closed when it is a common polynomial zero locus. -/
def IsZariskiClosedOver (K : Type*) {ι L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (X : Set (ι → L)) : Prop :=
  ∃ S : Set (MvPolynomial ι K), zariskiZeroLocusOver S = X

/-- Every set lies in its Zariski closure. -/
theorem subset_zariskiClosureOver (X : Set (ι → L)) : X ⊆ zariskiClosureOver K X := by
  intro x hx P hP
  exact hP x hx

/-- Zariski closure is monotone. -/
theorem zariskiClosureOver_mono {X Y : Set (ι → L)} (hXY : X ⊆ Y) :
    zariskiClosureOver K X ⊆ zariskiClosureOver K Y := by
  intro x hx P hPY
  exact hx P fun y hy => hPY y (hXY hy)

/-- Every polynomial zero locus is Zariski closed. -/
theorem isZariskiClosedOver_zariskiZeroLocusOver (S : Set (MvPolynomial ι K)) :
    IsZariskiClosedOver K (L := L) (zariskiZeroLocusOver S) :=
  ⟨S, rfl⟩

/-- The Zariski closure is Zariski closed. -/
theorem isZariskiClosedOver_zariskiClosureOver (X : Set (ι → L)) :
    IsZariskiClosedOver K (zariskiClosureOver K X) :=
  isZariskiClosedOver_zariskiZeroLocusOver _

/-- Universal property: the Zariski closure is contained in every closed superset. -/
theorem zariskiClosureOver_minimal {X Z : Set (ι → L)} (hXZ : X ⊆ Z)
    (hZ : IsZariskiClosedOver K Z) : zariskiClosureOver K X ⊆ Z := by
  obtain ⟨S, rfl⟩ := hZ
  intro x hx P hPS
  exact hx P fun y hy => hXZ hy P hPS

/-- Zariski closure is idempotent. -/
theorem zariskiClosureOver_idempotent (X : Set (ι → L)) :
    zariskiClosureOver K (zariskiClosureOver K X) = zariskiClosureOver K X := by
  apply Set.Subset.antisymm
  · exact zariskiClosureOver_minimal (subset_refl (zariskiClosureOver K X))
      (isZariskiClosedOver_zariskiClosureOver X)
  · exact subset_zariskiClosureOver _

/-- A set is Zariski closed exactly when it equals its own closure. -/
theorem isZariskiClosedOver_iff_zariskiClosureOver_eq {X : Set (ι → L)} :
    IsZariskiClosedOver K X ↔ zariskiClosureOver K X = X := by
  constructor
  · intro hX
    apply Set.Subset.antisymm
    · exact zariskiClosureOver_minimal (subset_refl X) hX
    · exact subset_zariskiClosureOver X
  · intro hX
    rw [← hX]
    exact isZariskiClosedOver_zariskiClosureOver X

/-- An arbitrary intersection of Zariski-closed sets is Zariski closed. -/
theorem isZariskiClosedOver_sInter (C : Set (Set (ι → L)))
    (hC : ∀ X ∈ C, IsZariskiClosedOver K X) : IsZariskiClosedOver K (⋂₀ C) := by
  classical
  refine ⟨⋃ X : {X // X ∈ C}, (zariskiVanishingIdealOver (K := K) (L := L) X.1 :
    Set (MvPolynomial ι K)), ?_⟩
  ext x
  constructor
  · intro hx X hX
    have hclosed := (isZariskiClosedOver_iff_zariskiClosureOver_eq (K := K)).mp (hC X hX)
    rw [← hclosed]
    intro P hP
    exact hx P (Set.mem_iUnion.mpr ⟨⟨X, hX⟩, hP⟩)
  · intro hx P hP
    obtain ⟨⟨X, hX⟩, hPX⟩ := Set.mem_iUnion.mp hP
    exact hPX x (hx X hX)

section Topology

variable {ι K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The empty set is Zariski closed. -/
theorem isZariskiClosedOver_empty :
    IsZariskiClosedOver K (∅ : Set (ι → L)) := by
  refine ⟨{1}, ?_⟩
  ext x
  simp [zariskiZeroLocusOver]

/-- The whole affine space is Zariski closed. -/
theorem isZariskiClosedOver_univ :
    IsZariskiClosedOver K (Set.univ : Set (ι → L)) := by
  refine ⟨∅, ?_⟩
  ext x
  simp [zariskiZeroLocusOver]

/-- Finite unions of Zariski-closed sets are Zariski closed. -/
theorem IsZariskiClosedOver.union {X Y : Set (ι → L)}
    (hX : IsZariskiClosedOver K X) (hY : IsZariskiClosedOver K Y) :
    IsZariskiClosedOver K (X ∪ Y) := by
  classical
  obtain ⟨S, hS⟩ := hX
  obtain ⟨T, hT⟩ := hY
  refine ⟨{R | ∃ P ∈ S, ∃ Q ∈ T, R = P * Q}, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxX : x ∈ X
    · exact Or.inl hxX
    · right
      have hxnotS : x ∉ zariskiZeroLocusOver (L := L) S := by
        rw [hS]; exact hxX
      have hexP : ∃ P ∈ S, MvPolynomial.aeval x P ≠ (0 : L) := by
        simpa [zariskiZeroLocusOver] using hxnotS
      obtain ⟨P, hPS, hPne⟩ := hexP
      rw [← hT]
      intro Q hQT
      have hPQ := hx (P * Q) ⟨P, hPS, Q, hQT, rfl⟩
      rw [map_mul] at hPQ
      exact (mul_eq_zero.mp hPQ).resolve_left hPne
  · rintro (hxX | hxY) R ⟨P, hPS, Q, hQT, rfl⟩
    · have hxS : x ∈ zariskiZeroLocusOver (L := L) S := by rw [hS]; exact hxX
      rw [map_mul, hxS P hPS, zero_mul]
    · have hxT : x ∈ zariskiZeroLocusOver (L := L) T := by rw [hT]; exact hxY
      rw [map_mul, hxT Q hQT, mul_zero]

end Topology

/-- **Zariski density.**  A set whose Zariski closure is the whole affine space. -/
def ZariskiDenseOver (K : Type*) {ι L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    (X : Set (ι → L)) : Prop :=
  zariskiClosureOver K X = Set.univ

/-- Density passes to supersets. -/
theorem ZariskiDenseOver.mono {X Y : Set (ι → L)} (hX : ZariskiDenseOver K X) (hXY : X ⊆ Y) :
    ZariskiDenseOver K Y := by
  apply Set.eq_univ_of_univ_subset
  rw [← hX]
  exact zariskiClosureOver_mono hXY

/-- A dense set is contained in no proper closed subset. -/
theorem ZariskiDenseOver.eq_univ_of_isZariskiClosedOver {X Z : Set (ι → L)}
    (hX : ZariskiDenseOver K X) (hXZ : X ⊆ Z) (hZ : IsZariskiClosedOver K Z) :
    Z = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← hX]
  exact zariskiClosureOver_minimal hXZ hZ

end

end GaloisForLFunctions.HTGeometry
