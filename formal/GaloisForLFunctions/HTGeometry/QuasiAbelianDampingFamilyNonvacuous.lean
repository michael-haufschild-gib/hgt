import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedLiftConstruction

/-!
# The damping interface is inhabited

An interface whose hypotheses cannot be met proves nothing.  This file certifies that
`AbeDampingPacketData` — hence `AbeDampedFactorExtension` — is genuinely satisfiable, by exhibiting
the degenerate extension of a factor by itself: the complement has rank `0`, the partial Poincaré
sum is the seed, and the majorant is vacuous because there is no nonzero complement index.

The construction is only a consistency certificate; the content of the card is the *nontrivial*
damping family, where the complement has positive rank.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- A family indexed by a finite type is trivially locally normally summable. -/
theorem summableLocallyUniformlyOn_of_fintype {ι : Type*} [Fintype ι]
    {β : Type*} [TopologicalSpace β] (f : ι → β → ℂ) (s : Set β) :
    SummableLocallyUniformlyOn f s := by
  classical
  refine ⟨fun x => ∑ i, f i x, ?_⟩
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn]
  intro v hv x hx
  refine ⟨s, self_mem_nhdsWithin, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨Finset.univ, fun S hS y _ => ?_⟩
  have hSu : S = Finset.univ := Finset.eq_univ_of_forall fun i => hS (Finset.mem_univ i)
  rw [hSu]
  exact refl_mem_uniformity hv

instance : Fintype (Fin 0 → ℤ) := by
  have : Finite (Fin 0 → ℤ) := Finite.of_subsingleton
  exact Fintype.ofFinite _

/-- **The damping interface is satisfiable**: a factor extends itself with a rank-zero
complement. -/
theorem hasAbeDampingFamily_self {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) : HasAbeDampingFamily.{u} 0 ψ ψ := by
  intro I _ _ w m lowerColumn
  refine ⟨?_⟩
  exact
    { le := le_rfl
      compat := fun η hη => rfl
      comp := 0
      comp_mem := fun z => by simpa using Γ.zero_mem
      decomp := fun δ hδ => ⟨δ, hδ, 0, by simp⟩
      seed := fun _ j => (lowerColumn j).1
      seed_mem := fun _ j => (lowerColumn j).2
      seed_jet := fun _ _ _ => rfl
      normal := fun _ _ => summableLocallyUniformlyOn_of_fintype _ _
      majorant := ⟨fun _ => 0, fun _ => 1, 0, 1, 0, fun i => i.elim0, one_pos, le_rfl,
        fun B _ z i j hz => absurd (Subsingleton.elim z 0) hz⟩ }

/-- The degenerate extension itself. -/
def abeDampedFactorExtensionSelf {d : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) : AbeDampedFactorExtension.{u} ψ ψ :=
  abeDampedFactorExtensionOfDampingFamily le_rfl (hasAbeDampingFamily_self ψ)

end

end GaloisForLFunctions.HTGeometry
