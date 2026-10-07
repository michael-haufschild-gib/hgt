import GaloisForLFunctions.RHTower.XiMarkedMonodromyMap
import GaloisForLFunctions.HTGeometry.PointedPacketTransport
import GaloisForLFunctions.HTGeometry.FiniteNormalPackets
import Mathlib.Algebra.Group.Subgroup.Finite

open Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.XiMarkedMonodromy

noncomputable section

/-- One common conjugator places an entire kernel packet into the actual joint image. -/
theorem exists_common_conjugate_packet {ι : Type*} [Finite ι]
    (A : Finset ℝ) (a : A) (q : ι → TargetGroup)
    (hq : ∀ i, zeroWinding (q i) = 1) :
    ∃ g : TargetGroup, ∀ i,
      Pi.mulSingle a (g * q i * g⁻¹) ∈ (jointMap A).range := by
  classical
  have hrep (i : ι) : ∃ p : Path targetHalf targetHalf,
      FundamentalGroup.fromPath ⟦p⟧ = q i := Quotient.exists_rep (q i)
  choose p hp using hrep
  have hw (i : ι) : Bottcher.wind (fun z : Target => (z : ℂ))
      continuous_subtype_val (fun z => z.2.1) (p i) = 0 := by
    have h := normalizedWindingHom_mk targetToPunctured (p i)
    change zeroWinding (FundamentalGroup.fromPath ⟦p i⟧) =
      Multiplicative.ofAdd (Bottcher.wind (fun z : Target => (z : ℂ))
        continuous_subtype_val (fun z => z.2.1) (p i)) at h
    rw [hp i, hq i] at h
    exact congrArg Multiplicative.toAdd h.symm
  obtain ⟨s, _, hs, l, hl⟩ := exists_marked_source_loop_packet A a 0 p hw
  let α := PathConnectedSpace.somePath (sourceZero A) s
  let g : TargetGroup := .fromPath
    ⟦(α.map (coordinate A a).continuous).cast (coordinate_sourceZero A a).symm hs.symm⟧
  let u (i : ι) := FundamentalGroup.fundamentalGroupMulEquivOfPath α.symm
    (FundamentalGroup.fromPath ⟦l i⟧)
  refine ⟨g⁻¹, fun i => ⟨u i, ?_⟩⟩
  funext b
  by_cases hba : b = a
  · subst b
    simp only [Pi.mulSingle_eq_same, inv_inv]
    change FundamentalGroup.mapOfEq (coordinate A a) (coordinate_sourceZero A a) (u i) = _
    have hi := fundamentalGroup_mapOfEq_transport (coordinate A a)
      (coordinate_sourceZero A a) hs α (l i)
    change FundamentalGroup.mapOfEq (coordinate A a) (coordinate_sourceZero A a) (u i) =
      g⁻¹ * FundamentalGroup.mapOfEq (coordinate A a) hs
        (FundamentalGroup.fromPath ⟦l i⟧) * g at hi
    rw [fundamentalGroup_mapOfEq_mk, (hl i).1, hp i] at hi
    exact hi
  · rw [Pi.mulSingle_eq_of_ne hba]
    exact fundamentalGroup_mapOfEq_transport_null (coordinate A b)
      (coordinate_sourceZero A b) α (l i) ((hl i).2 b hba)

/-- Every finite group sees the complete zero-winding kernel in a selected coordinate. -/
theorem finite_image_contains_coordinate_kernel (A : Finset ℝ) (a : A)
    {G : Type*} [Group G] [Finite G] (f : JointGroup A →* G)
    (q : TargetGroup) (hq : zeroWinding q = 1) :
    f (Pi.mulSingle a q) ∈ ((jointMap A).range).map f := by
  classical
  let e : TargetGroup →* JointGroup A := MonoidHom.mulSingle (fun _ : A => TargetGroup) a
  let H := ((jointMap A).range).comap e
  have hpacket (T : Finset TargetGroup) (hT : ∀ x ∈ T, x ∈ zeroWinding.ker) :
      ∃ g, ∀ x ∈ T, g * x * g⁻¹ ∈ H := by
    obtain ⟨g, hg⟩ := exists_common_conjugate_packet A a (fun x : T => x.val)
      (fun x => hT x x.2)
    exact ⟨g, fun x hx => hg ⟨x, hx⟩⟩
  have hh := map_le_of_finite_normal_packets zeroWinding.ker H hpacket (f.comp e)
  have hm : f (e q) ∈ H.map (f.comp e) := hh ⟨q, hq, rfl⟩
  obtain ⟨p, hp, hpf⟩ := hm
  exact ⟨e p, hp, hpf⟩

/-- Finite images contain the full product of the individual zero-winding kernels. -/
theorem finite_image_contains_product_kernel (A : Finset ℝ)
    {G : Type*} [Group G] [Finite G] (f : JointGroup A →* G)
    (q : JointGroup A) (hq : ∀ a, zeroWinding (q a) = 1) :
    f q ∈ ((jointMap A).range).map f := by
  classical
  have h : q ∈ (((jointMap A).range).map f).comap f :=
    Subgroup.pi_mem_of_mulSingle_mem q fun a =>
      finite_image_contains_coordinate_kernel A a f (q a) (hq a)
  exact h

end

end RHTower.XiMarkedMonodromy
