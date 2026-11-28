import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CountableOperatorEigenvalue
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Basic

/-! Smooth irreducible complex representations of separable topological
groups have countable rank. Schur's lemma then gives a smooth character
for any continuous central subgroup. -/

noncomputable section

open Cardinal

namespace Representation

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hs : ∀ v : V, IsOpen {g : G | ρ g v = v})

include hs in
private theorem countable_smooth_orbit (v : V) : (Set.range fun g => ρ g v).Countable := by
  obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense G
  refine (hD.image fun g => ρ g v).mono ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _
    ((hs v).preimage (continuous_const_mul g⁻¹)) ⟨g, by
      change ρ (g⁻¹ * g) v = v
      rw [inv_mul_cancel, map_one, Module.End.one_apply]⟩
  have hx' : ρ (g⁻¹ * x) v = v := hx
  refine ⟨x, hxD, ?_⟩
  change ρ x v = ρ g v
  conv_rhs => rw [← hx']
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

private theorem nontrivial_of_irreducible [ρ.IsIrreducible] : Nontrivial V :=
  IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

include hs in
theorem rank_le_aleph0_of_smooth_irreducible [ρ.IsIrreducible] :
    Module.rank ℂ V ≤ ℵ₀ := by
  letI := nontrivial_of_irreducible ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g => ρ g v), fun g w hw => by
      induction hw using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * k, by
          change ρ (g * k) v = ρ g (ρ k v)
          rw [map_mul, Module.End.mul_apply]⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx⟩
  have hvW : v ∈ W := Submodule.subset_span ⟨1, by
    change ρ 1 v = v
    rw [map_one, Module.End.one_apply]⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left fun h => hv (by
    rw [h] at hvW
    exact hvW)
  have hspan : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW
  rw [← rank_top, ← hspan]
  exact (rank_span_le _).trans (le_aleph0_iff_set_countable.mpr (countable_smooth_orbit ρ hs v))

include hs in
theorem exists_eq_smul_of_smooth_irreducible [ρ.IsIrreducible] (T : ρ.IntertwiningMap ρ) :
    ∃ c : ℂ, ∀ v, T v = c • v := by
  letI := nontrivial_of_irreducible ρ
  obtain ⟨c, hc⟩ := GlobalTheory.NonUnitShift.exists_not_isUnit_sub
    (rank_le_aleph0_of_smooth_irreducible ρ hs) T.toLinearMap
  let S : ρ.IntertwiningMap ρ := T - c • .id ρ
  rcases Representation.IsIrreducible.bijective_or_eq_zero S with hb | hz
  · exact (hc ((Module.End.isUnit_iff _).mpr hb)).elim
  · exact ⟨c, fun v => sub_eq_zero.mp (congrArg (fun f : ρ.IntertwiningMap ρ => f v) hz)⟩

include hs in
theorem exists_smooth_centralCharacter [ρ.IsIrreducible]
    {Z : Type} [Group Z] [TopologicalSpace Z] (ι : Z →* G) (hι : Continuous ι)
    (hc : ∀ z g, Commute (ι z) g) :
    ∃ ω : Z →* ℂˣ, IsOpen (ω.ker : Set Z) ∧ ∀ z v, ρ (ι z) v = (ω z : ℂ) • v := by
  letI := nontrivial_of_irreducible ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have key (z : Z) : ∃ c : ℂ, ∀ w, ρ (ι z) w = c • w := by
    let T : ρ.IntertwiningMap ρ := ⟨ρ (ι z), fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, (hc z g).eq]⟩
    exact exists_eq_smul_of_smooth_irreducible ρ hs T
  choose c hc' using key
  let cHom : Z →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by
        change c 1 • v = (1 : ℂ) • v
        rw [← hc', map_one, map_one, Module.End.one_apply, one_smul])
      map_mul' := fun x y => smul_left_injective ℂ hv (by
        change c (x * y) • v = (c x * c y) • v
        simp only [← hc', mul_smul, map_mul, Module.End.mul_apply]) }
  let ω := cHom.toHomUnits
  refine ⟨ω, ?_, hc'⟩
  have he : (ω.ker : Set Z) = ι ⁻¹' {g : G | ρ g v = v} := by
    ext z
    change ω z = 1 ↔ ρ (ι z) v = v
    rw [hc']
    exact ⟨fun hz => by
      have hz' := congrArg Units.val hz
      change c z = 1 at hz'
      rw [hz', one_smul],
      fun hz => Units.ext (smul_left_injective ℂ hv (hz.trans (one_smul _ _).symm))⟩
  rw [he]
  exact (hs v).preimage hι

end Representation

#print axioms Representation.exists_smooth_centralCharacter
