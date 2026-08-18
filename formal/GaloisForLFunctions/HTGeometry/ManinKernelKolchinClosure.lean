import GaloisForLFunctions.HTGeometry.MultiplicationTailFixedField
import GaloisForLFunctions.HTGeometry.AffineZariskiClosureOver

/-!
# The Kolchin closure of the primary torsion is the Manin kernel

The Manin kernel of an Abelian variety over a differential field is characterised by three
properties: it is Kolchin closed, it contains the torsion, and it is contained in every
Zariski-dense Kolchin-closed differential algebraic subgroup.  This file proves the consequence
used by the multiplication-tail argument: if the primary torsion of one fixed multiplication is
already Zariski dense, then its Kolchin closure is exactly the Manin kernel.

Both a set-level form and a subgroup form are given.  In the subgroup form the group of points is
an abstract commutative group with an injective differential-algebraic coordinatisation, and
minimality is only required against subgroups, as in the classical statement.

Combined with the tower identity for translation fixed fields, this identifies the stable
multiplication tail with the field of Manin-kernel invariants.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The set-level identification -/

variable {ι K : Type*} [Field K] [Differential K]

/-- **The Kolchin closure of a Zariski-dense set is the minimal dense closed set containing it.**
If `Asharp` is Kolchin closed, contains `T`, and is contained in every Zariski-dense Kolchin-closed
set, and if `T` is already Zariski dense, then the Kolchin closure of `T` is `Asharp`. -/
theorem kolchinClosureOver_eq_of_zariskiDense_of_minimal
    (T Asharp : Set (ι → K))
    (hAclosed : IsKolchinClosedOver K Asharp)
    (hTA : T ⊆ Asharp)
    (hmin : ∀ H : Set (ι → K), IsKolchinClosedOver K H → ZariskiDenseOver K H → Asharp ⊆ H)
    (hdense : ZariskiDenseOver K T) :
    kolchinClosureOver K T = Asharp := by
  apply Set.Subset.antisymm
  · exact kolchinClosureOver_minimal hTA hAclosed
  · exact hmin _ (isKolchinClosedOver_kolchinClosureOver T)
      (hdense.mono (subset_kolchinClosureOver T))

/-- The same statement for the union of an increasing tower, which is the shape produced by the
`m`-primary torsion. -/
theorem kolchinClosureOver_iUnion_eq_of_zariskiDense_of_minimal
    {ι' : Type*} (T : ι' → Set (ι → K)) (Asharp : Set (ι → K))
    (hAclosed : IsKolchinClosedOver K Asharp)
    (hTA : ∀ n, T n ⊆ Asharp)
    (hmin : ∀ H : Set (ι → K), IsKolchinClosedOver K H → ZariskiDenseOver K H → Asharp ⊆ H)
    (hdense : ZariskiDenseOver K (⋃ n, T n)) :
    kolchinClosureOver K (⋃ n, T n) = Asharp := by
  refine kolchinClosureOver_eq_of_zariskiDense_of_minimal _ Asharp hAclosed ?_ hmin hdense
  exact Set.iUnion_subset hTA

/-! ### The subgroup form -/

variable {P : Type*} [AddCommGroup P]

/-- A subgroup of points is Kolchin closed when its coordinate image is. -/
def IsKolchinClosedSubgroup (K : Type*) {ι P : Type*} [Field K] [Differential K] [AddCommGroup P]
    (coord : P → (ι → K)) (H : AddSubgroup P) : Prop :=
  IsKolchinClosedOver K (coord '' (H : Set P))

/-- A subgroup of points is Zariski dense when its coordinate image is. -/
def IsZariskiDenseSubgroup (K : Type*) {ι P : Type*} [Field K] [Differential K] [AddCommGroup P]
    (coord : P → (ι → K)) (H : AddSubgroup P) : Prop :=
  ZariskiDenseOver K (coord '' (H : Set P))

/-- **The Manin-kernel identification.**  Let `coord` be an injective coordinatisation of a group
of points.  Let `Asharp` be Kolchin closed, contain every stage of a torsion tower, and be
contained in every Zariski-dense Kolchin-closed subgroup.  If the union of the tower is Zariski
dense and `Hcl` is a subgroup whose coordinate image is the Kolchin closure of that union, then
`Hcl = Asharp`. -/
theorem eq_maninKernel_of_kolchinClosure_of_zariskiDense
    {ι' : Type*} (coord : P → (ι → K)) (hcoord : Function.Injective coord)
    (T : ι' → AddSubgroup P) (Asharp Hcl : AddSubgroup P)
    (hAclosed : IsKolchinClosedSubgroup K coord Asharp)
    (hTA : ∀ n, T n ≤ Asharp)
    (hmin : ∀ H : AddSubgroup P, IsKolchinClosedSubgroup K coord H →
      IsZariskiDenseSubgroup K coord H → Asharp ≤ H)
    (hdense : ZariskiDenseOver K (⋃ n, coord '' ((T n : AddSubgroup P) : Set P)))
    (hHcl : coord '' (Hcl : Set P)
      = kolchinClosureOver K (⋃ n, coord '' ((T n : AddSubgroup P) : Set P))) :
    Hcl = Asharp := by
  have hclosed : IsKolchinClosedSubgroup K coord Hcl := by
    rw [IsKolchinClosedSubgroup, hHcl]
    exact isKolchinClosedOver_kolchinClosureOver _
  have hdenseHcl : IsZariskiDenseSubgroup K coord Hcl := by
    rw [IsZariskiDenseSubgroup, hHcl]
    exact hdense.mono (subset_kolchinClosureOver _)
  have hle : Asharp ≤ Hcl := hmin Hcl hclosed hdenseHcl
  have hTsubset : (⋃ n, coord '' ((T n : AddSubgroup P) : Set P)) ⊆ coord '' (Asharp : Set P) := by
    refine Set.iUnion_subset fun n => ?_
    exact Set.image_mono (fun p hp => hTA n hp)
  have hge : coord '' (Hcl : Set P) ⊆ coord '' (Asharp : Set P) := by
    rw [hHcl]
    exact kolchinClosureOver_minimal hTsubset hAclosed
  refine le_antisymm ?_ hle
  intro p hp
  have hmem : coord p ∈ coord '' (Asharp : Set P) := hge ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hqp⟩ := hmem
  rwa [hcoord hqp] at hq

/-! ### The multiplication tail is the field of Manin-kernel invariants -/

variable {L : Type*} [Field L] [Algebra K L] [Differential L]

/-- **Equation (6) of the Manin-horizon theorem.**  The stable intersection of the tower of
translation fixed fields is the field fixed by the Manin kernel.  The tower step is the
Kolchin-closure identity for fixed fields; the closure is identified with the Manin kernel by
Zariski density of the primary torsion and minimality of the kernel. -/
theorem iInf_differentialTranslationFixedField_eq_maninKernel
    {ι' : Type*} (translation : (ι → K) → DifferentialAlgEquiv K L)
    (T : ι' → Set (ι → K)) (Asharp : Set (ι → K))
    (hstab : ∀ z : L, IsKolchinClosedOver K {a : ι → K | (translation a).toAlgEquiv z = z})
    (hAclosed : IsKolchinClosedOver K Asharp)
    (hTA : ∀ n, T n ⊆ Asharp)
    (hmin : ∀ H : Set (ι → K), IsKolchinClosedOver K H → ZariskiDenseOver K H → Asharp ⊆ H)
    (hdense : ZariskiDenseOver K (⋃ n, T n)) :
    (⨅ n, differentialTranslationFixedField translation (T n))
      = differentialTranslationFixedField translation Asharp := by
  rw [iInf_differentialTranslationFixedField_eq_kolchinClosure translation T hstab]
  rw [kolchinClosureOver_iUnion_eq_of_zariskiDense_of_minimal T Asharp hAclosed hTA hmin hdense]

/-! ### The constant-coefficient case -/

/-- The points all of whose coordinates are differential constants form a Kolchin-closed set: it
is the zero locus of the first-order coordinate jets. -/
theorem isKolchinClosedOver_constantPoints :
    IsKolchinClosedOver K {a : ι → K | ∀ i, (a i)′ = 0} := by
  refine ⟨Set.range fun i : ι => (MvPolynomial.X (i, 1) : DifferentialPolynomial ι K), ?_⟩
  ext a
  constructor
  · intro ha i
    have h := ha _ ⟨i, rfl⟩
    rw [differentialPolynomialEvalOver_X] at h
    simpa [differentialJet] using h
  · rintro ha P ⟨i, rfl⟩
    rw [differentialPolynomialEvalOver_X]
    simpa [differentialJet] using ha i

/-- **The constant-coefficient horizon.**  If the deck points are constant and Zariski dense, and
the Manin kernel is minimal among Zariski-dense Kolchin-closed sets, then the closure controlling
the horizon is exactly the group of constant translations. -/
theorem kolchinClosureOver_eq_constantPoints_of_zariskiDense
    (T : Set (ι → K)) (hTconst : T ⊆ {a : ι → K | ∀ i, (a i)′ = 0})
    (hmin : ∀ H : Set (ι → K), IsKolchinClosedOver K H → ZariskiDenseOver K H →
      {a : ι → K | ∀ i, (a i)′ = 0} ⊆ H)
    (hdense : ZariskiDenseOver K T) :
    kolchinClosureOver K T = {a : ι → K | ∀ i, (a i)′ = 0} :=
  kolchinClosureOver_eq_of_zariskiDense_of_minimal T _ isKolchinClosedOver_constantPoints
    hTconst hmin hdense

end

end GaloisForLFunctions.HTGeometry
