import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Circle characters of profinite groups

Every continuous circle character of a compact totally disconnected group
has open kernel, finite image, and finite order. An open subgroup whose image
lies in a small circle arc must map trivially: all positive powers remain in
that arc. This supplies the finite-conductor mechanism in Lemma 3.3 of
arXiv:2610.23742 without assuming that continuity alone makes kernels open.
-/

noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry.ProfiniteCircleCharacters

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A small arc contains no nontrivial subgroup of the circle. -/
theorem isOpen_ker (χ : G →ₜ* Circle) : IsOpen (χ.toMonoidHom.ker : Set G) := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((Circle.isOpen_centeredArc (π / 2)).preimage χ.continuous)
    (show (1 : G) ∈ χ ⁻¹' Circle.centeredArc (π / 2) from by
      change χ 1 ∈ Circle.centeredArc (π / 2)
      rw [map_one, Circle.mem_centeredArc (by linarith [pi_pos])]
      simpa using (half_pos pi_pos))
  apply Subgroup.isOpen_of_openSubgroup χ.toMonoidHom.ker (U := U.toOpenSubgroup)
  intro g hg
  change χ g = 1
  apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
  intro n _
  have h : χ (g ^ n) ∈ Circle.centeredArc (π / 2) := hU (U.pow_mem hg n)
  simpa only [map_pow] using h

/-- Every continuous circle character is constant on open cosets of its kernel. -/
theorem isLocallyConstant (χ : G →ₜ* Circle) : IsLocallyConstant χ := by
  apply IsLocallyConstant.iff_isOpen_fiber_apply.mpr
  intro x
  have heq : χ ⁻¹' {χ x} = (fun y : G => y * x⁻¹) ⁻¹' (χ.toMonoidHom.ker : Set G) := by
    ext y
    change χ y = χ x ↔ χ (y * x⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [heq]
  exact (isOpen_ker χ).preimage (continuous_id.mul continuous_const)

/-- Compactness makes the open-kernel quotient, hence the character image, finite. -/
theorem finite_range (χ : G →ₜ* Circle) : (Set.range χ).Finite := by
  letI : Finite (G ⧸ χ.toMonoidHom.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_ker χ)
  letI : Finite χ.toMonoidHom.range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ.toMonoidHom).toEquiv
  change (χ.toMonoidHom.range : Set Circle).Finite
  exact Set.toFinite _

/-- One positive exponent kills every value of the character. -/
theorem exists_uniform_exponent (χ : G →ₜ* Circle) :
    ∃ n : ℕ, 0 < n ∧ ∀ g : G, χ g ^ n = 1 := by
  have hr : (χ.toMonoidHom.range : Set Circle).Finite := finite_range χ
  letI : Finite χ.toMonoidHom.range := hr.to_subtype
  refine ⟨Nat.card χ.toMonoidHom.range, Nat.card_pos, fun g => ?_⟩
  exact congrArg (fun z : χ.toMonoidHom.range => (z : Circle))
    (pow_card_eq_one' (x := ⟨χ g, ⟨g, rfl⟩⟩))

#print axioms isOpen_ker
#print axioms finite_range
#print axioms exists_uniform_exponent

end GaloisForLFunctions.HTGeometry.ProfiniteCircleCharacters
