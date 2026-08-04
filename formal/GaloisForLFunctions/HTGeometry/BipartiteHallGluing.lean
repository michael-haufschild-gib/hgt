import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Bipartite Hall gluing by overlap compensation

Suppose an input splits into disjoint layers `S₀` and `W₀`.  A forward
family expands `S₀` into `C ⊆ W`.  The part of `C` already hidden inside
`W₀` does not increase output dimension.  If a reverse family expands that
exact overlap into a disjoint sector `Cstar ⊆ S`, the lost dimension is paid
back exactly.  This rank identity is the abstract mixed-sector mechanism
needed to glue singlet and nonsinglet Hall expansion.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hall expansion in one layer, with every overlap paid back through a
disjoint reverse channel, glues across a direct-sum decomposition. -/
theorem bipartiteHall_overlapCompensation_finrank
    {𝕜 X : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [FiniteDimensional 𝕜 X]
    (S W S₀ W₀ C Cstar Yout : Submodule 𝕜 X)
    (hSW : Disjoint S W)
    (hS₀S : S₀ ≤ S) (hW₀W : W₀ ≤ W)
    (hCW : C ≤ W) (hCstarS : Cstar ≤ S)
    (hforward : Module.finrank 𝕜 S₀ ≤ Module.finrank 𝕜 C)
    (hreverse : Module.finrank 𝕜 ((C ⊓ W₀) : Submodule 𝕜 X) ≤
      Module.finrank 𝕜 Cstar)
    (hout : (W₀ ⊔ C) ⊔ Cstar ≤ Yout) :
    Module.finrank 𝕜 ((S₀ ⊔ W₀) : Submodule 𝕜 X) ≤
      Module.finrank 𝕜 Yout := by
  have hinput_disjoint : Disjoint S₀ W₀ := hSW.mono hS₀S hW₀W
  have houtput_disjoint : Disjoint (W₀ ⊔ C) Cstar :=
    hSW.symm.mono (sup_le hW₀W hCW) hCstarS
  have hinput := Submodule.finrank_sup_add_finrank_inf_eq S₀ W₀
  have hmiddle := Submodule.finrank_sup_add_finrank_inf_eq W₀ C
  have houtput :=
    Submodule.finrank_sup_add_finrank_inf_eq (W₀ ⊔ C) Cstar
  rw [inf_comm C W₀] at hreverse
  rw [disjoint_iff.mp hinput_disjoint, finrank_bot] at hinput
  rw [disjoint_iff.mp houtput_disjoint, finrank_bot] at houtput
  have houtRank : Module.finrank 𝕜
      (((W₀ ⊔ C) ⊔ Cstar) : Submodule 𝕜 X) ≤
      Module.finrank 𝕜 Yout := Submodule.finrank_mono hout
  omega

end

end GaloisForLFunctions.HTGeometry
