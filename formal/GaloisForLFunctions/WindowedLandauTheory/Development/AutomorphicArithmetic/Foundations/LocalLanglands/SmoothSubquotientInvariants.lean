import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompactSmoothInvariants
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothSubrepresentation
import Mathlib.RepresentationTheory.Subrepresentation

/-! Compact fixed vectors lift through smooth quotients. In particular,
if a subquotient has a nonzero fixed vector, so does the ambient
representation. -/

noncomputable section

namespace Representation

variable {G V W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

theorem exists_fixed_preimage_of_compact (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v})
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (w : W) (hw : ∀ k : K, σ k.val w = w) :
    ∃ v : V, (∀ k : K, ρ k.val v = v) ∧ f v = w := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : Representation ℂ K V := ρ.comp K.subtype
  let s : Representation ℂ K W := σ.comp K.subtype
  let p : r.IntertwiningMap s :=
    ⟨f.toLinearMap, fun k => f.isIntertwining' k.val⟩
  have hr (v : V) : IsOpen {k : K | r k v = v} := (hρ v).preimage continuous_subtype_val
  have hs (w : W) : IsOpen {k : K | s k w = w} := by
    obtain ⟨v, rfl⟩ := hf w
    apply s.isOpen_vectorStabilizer_of_open_subgroup (H := r.vectorStabilizer v) (hr v)
    intro k hk
    change s k (p v) = p v
    rw [← IntertwiningMap.isIntertwining r s p k v]
    exact congrArg p (show r k v = v from hk)
  obtain ⟨u, rfl⟩ := hf w
  have hc := invariants_isCompl_coinvariantKer_of_compact r hr
  have hu : u ∈ r.invariants ⊔ Coinvariants.ker r := hc.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
  have hpv : p v ∈ s.invariants := by
    intro k
    rw [← IntertwiningMap.isIntertwining r s p k v, hv k]
  change p (v + z) ∈ s.invariants at hw
  rw [map_add, add_comm] at hw
  have hpz : p z ∈ s.invariants := (s.invariants.add_mem_iff_left hpv).mp hw
  have hcoin : p z ∈ Coinvariants.ker s := (Coinvariants.mk_eq_zero s).mp (by
    rw [← Coinvariants.map_mk p z, (Coinvariants.mk_eq_zero r).mpr hz, map_zero])
  have hz₀ := Submodule.disjoint_def.mp (invariants_isCompl_coinvariantKer_of_compact s hs).disjoint
    (p z) hpz hcoin
  exact ⟨v, hv, by change p v = p (v + z); rw [map_add, hz₀, add_zero]⟩

theorem exists_nonzero_fixed_of_subquotient (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hρ : ∀ v : V, IsOpen {g : G | ρ g v = v}) (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap σ) (hf : Function.Surjective f)
    (w : W) (hw : ∀ k : K, σ k.val w = w) (hw₀ : w ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ k : K, ρ k.val v = v := by
  obtain ⟨v, hv, he⟩ :=
    exists_fixed_preimage_of_compact K hK (ρ.smooth_subrepresentation S hρ) f hf w hw
  refine ⟨v.val, fun hz => hw₀ ?_, fun k => congrArg Subtype.val (hv k)⟩
  rw [← he, show v = 0 from Subtype.ext hz, map_zero]

end Representation

#print axioms Representation.exists_fixed_preimage_of_compact
#print axioms Representation.exists_nonzero_fixed_of_subquotient
