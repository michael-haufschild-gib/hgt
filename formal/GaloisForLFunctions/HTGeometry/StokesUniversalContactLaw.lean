import GaloisForLFunctions.HTGeometry.StokesDecoratedCore
import GaloisForLFunctions.HTGeometry.StokesEnergyTree

/-!
# Universal complementary-contact law for finite fission data

A certified finite fission datum carries the two canonical finite encodings of one object: a
rooted least-common-ancestor tree and its positive pendant-cut coordinates.  Both are required to
realize the rescaled decorated core matrix.  The capstone theorems combine strict tomography,
four-point additivity, strict negative type, and explicit Euclidean realization.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Decorated core energy obtained by polarizing complementary contact. -/
def DecoratedStokesCore.energy {n : ℕ} (g : DecoratedStokesCore n) (i j : Fin n) : ℝ :=
  2 * g.realContactMatrix i j - g.realContactMatrix i i - g.realContactMatrix j j

/-- Exact finite fission datum with rooted-tree and positive-cut certificates for the same
complementary-contact matrix. -/
structure CertifiedFissionDatum (n m : ℕ) where
  core : DecoratedStokesCore n
  rooted : core.RootedRealization
  cuts : RootedCutContact n m
  cut_contact_eq : ∀ i j, cuts.contact i j = rooted.tree.contact i j

namespace CertifiedFissionDatum

/-- Rooted-tree energy is the energy computed directly from the decorated core. -/
theorem rooted_energy_eq_core {n m : ℕ} (datum : CertifiedFissionDatum n m) (i j : Fin n) :
    datum.rooted.tree.energy i j = datum.core.energy i j := by
  simp only [RootedContactTree.energy, DecoratedStokesCore.energy]
  rw [datum.rooted.contact_eq, datum.rooted.contact_eq, datum.rooted.contact_eq]

/-- Positive-cut energy is the energy computed directly from the decorated core. -/
theorem cut_energy_eq_core {n m : ℕ} (datum : CertifiedFissionDatum n m) (i j : Fin n) :
    datum.cuts.energy i j = datum.core.energy i j := by
  simp only [RootedCutContact.energy, DecoratedStokesCore.energy]
  rw [datum.cut_contact_eq, datum.cut_contact_eq, datum.cut_contact_eq]
  rw [datum.rooted.contact_eq, datum.rooted.contact_eq, datum.rooted.contact_eq]

/-- Strict diagonal contact separation in integral core coordinates. -/
theorem strict_core_obstruction {n m : ℕ} (datum : CertifiedFissionDatum n m)
    {i j : Fin n} (hij : i ≠ j) :
    (datum.core.ramification j : ℤ) * (datum.core.B i i - 1) <
      (datum.core.ramification i : ℤ) * datum.core.B i j :=
  datum.rooted.strictCoreObstruction hij

/-- The canonical hierarchy reconstructed from the decorated core is laminar. -/
theorem hierarchy_laminar {n m : ℕ} (datum : CertifiedFissionDatum n m)
    {A B : Set (Fin n)} (hA : A ∈ datum.rooted.tree.hierarchy)
    (hB : B ∈ datum.rooted.tree.hierarchy) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B :=
  datum.rooted.tree.hierarchy_laminar hA hB

/-- Two certified fission data with one decorated core have the same labelled branching
hierarchy. -/
theorem hierarchy_unique {n m₁ m₂ : ℕ} {core : DecoratedStokesCore n}
    (left : CertifiedFissionDatum n m₁) (right : CertifiedFissionDatum n m₂)
    (hleft : left.core = core) (hright : right.core = core) :
    left.rooted.tree.hierarchy = right.rooted.tree.hierarchy := by
  apply RootedContactTree.hierarchy_eq_of_contact_eq
  intro i j
  rw [left.rooted.contact_eq, right.rooted.contact_eq, hleft, hright]

/-- Decorated-core energy is strictly positive away from the diagonal. -/
theorem core_energy_pos_of_ne {n m : ℕ} (datum : CertifiedFissionDatum n m)
    {i j : Fin n} (hij : i ≠ j) : 0 < datum.core.energy i j := by
  rw [← datum.cut_energy_eq_core]
  exact datum.cuts.energy_pos_of_ne hij

/-- Decorated-core energy satisfies the four-point tree condition. -/
theorem core_energy_fourPoint {n m : ℕ} (datum : CertifiedFissionDatum n m)
    (i j k l : Fin n) :
    MaxTwice (datum.core.energy i j + datum.core.energy k l)
      (datum.core.energy i k + datum.core.energy j l)
      (datum.core.energy i l + datum.core.energy j k) := by
  simpa only [datum.rooted_energy_eq_core] using datum.rooted.tree.energy_fourPoint i j k l

/-- Decorated-core energy has strict negative type. -/
theorem core_energy_strict_negative_type {n m : ℕ} (datum : CertifiedFissionDatum n m)
    {x : Fin n → ℝ} (hsum : ∑ i, x i = 0) (hx : x ≠ 0) :
    (∑ i, ∑ j, x i * x j * datum.core.energy i j) < 0 := by
  simp_rw [← datum.cut_energy_eq_core]
  exact datum.cuts.energy_strict_negative_type hsum hx

/-- Explicit Euclidean feature coordinates whose squared distance is decorated-core energy. -/
theorem core_energy_explicit_sqEmbedding {n m : ℕ} (datum : CertifiedFissionDatum n m)
    (i j : Fin n) :
    (∑ e, (datum.cuts.toPositivePendantCutFamily.feature i e -
      datum.cuts.toPositivePendantCutFamily.feature j e) ^ 2) = datum.core.energy i j := by
  rw [← datum.cut_energy_eq_core]
  exact datum.cuts.energy_has_explicit_sqEmbedding i j

/-- Universal contact package: strict integral separation, four-point additivity, strict negative
type, and explicit squared-Euclidean realization all follow from one complementary-contact
matrix. -/
theorem universal_contact_package {n m : ℕ} (datum : CertifiedFissionDatum n m) :
    (∀ i j, i ≠ j →
      (datum.core.ramification j : ℤ) * (datum.core.B i i - 1) <
        (datum.core.ramification i : ℤ) * datum.core.B i j) ∧
    (∀ i j k l,
      MaxTwice (datum.core.energy i j + datum.core.energy k l)
        (datum.core.energy i k + datum.core.energy j l)
        (datum.core.energy i l + datum.core.energy j k)) ∧
    (∀ x : Fin n → ℝ, (∑ i, x i = 0) → x ≠ 0 →
      (∑ i, ∑ j, x i * x j * datum.core.energy i j) < 0) := by
  exact ⟨fun _ _ hij => datum.strict_core_obstruction hij,
    fun _ _ _ _ => datum.core_energy_fourPoint _ _ _ _,
    fun _ hsum hx => datum.core_energy_strict_negative_type hsum hx⟩

end CertifiedFissionDatum

end IrregularStokes
end GaloisForLFunctions
