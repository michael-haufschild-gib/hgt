import GaloisForLFunctions.HTGeometry.KaehlerDifferentialGeneration
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionFreeQuotient

/-!
# The Kähler module modulo torsion is free over the operator ring

For a differential field `K` finitely differentially generated over a field of constants `C`, the
relative Kähler module `Ω[K⁄C]` is generated over `K[∂;δ]` by the differentials of the generators,
so any torsion-free quotient of it — in particular `M_K = Ω/Tor` — is a free `K[∂;δ]`-module.

* `span_diffOp_D_eq_top` — the operator ring generates from the differentials of the generators;
* `free_quotient_kaehler_of_torsionFree` — **the structure statement for `M_K`**.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K] [IsConstantBase C K]

/-- **The differentials of a differential generating set generate over the operator ring.** -/
theorem span_diffOp_D_eq_top {S : Set K} (hS : differentialAdjoin C S = ⊤) :
    Submodule.span (DiffOp K) (KaehlerDifferential.D C K '' S) = ⊤ := by
  set N : Submodule (DiffOp K) (Ω[K⁄C]) :=
    Submodule.span (DiffOp K) (KaehlerDifferential.D C K '' S) with hN
  have hres : Submodule.restrictScalars K N = ⊤ := by
    refine eq_top_of_connection_stable (IsConstantBase.deriv_algebraMap (C := C) (K := K))
      (Submodule.restrictScalars K N) ?_ hS ?_
    · intro ω hω
      have hmem : (DiffOp.mono 1 1 : DiffOp K) • ω ∈ N := N.smul_mem _ hω
      rwa [partial_smul_eq_connection] at hmem
    · intro s hs
      exact Submodule.subset_span ⟨s, hs, rfl⟩
  rwa [Submodule.restrictScalars_eq_top_iff] at hres

/-- **A torsion-free quotient of the Kähler module of a finitely differentially generated extension
is free over the operator ring.** -/
theorem free_quotient_kaehler_of_torsionFree {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤)
    (N : Submodule (DiffOp K) (Ω[K⁄C]))
    (htf : ∀ (r : DiffOp K) (x : (Ω[K⁄C]) ⧸ N), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free (DiffOp K) ((Ω[K⁄C]) ⧸ N) := by
  classical
  have hspan : Submodule.span (DiffOp K)
      (Set.range fun i => N.mkQ (KaehlerDifferential.D C K (y i))) = ⊤ := by
    have himg : Submodule.map N.mkQ
        (Submodule.span (DiffOp K) (KaehlerDifferential.D C K '' Set.range y)) = ⊤ := by
      rw [span_diffOp_D_eq_top hy, Submodule.map_top, N.range_mkQ]
    rw [Submodule.map_span] at himg
    have hset : (N.mkQ : Ω[K⁄C] → (Ω[K⁄C]) ⧸ N) ''
        (KaehlerDifferential.D C K '' Set.range y)
        = Set.range fun i => N.mkQ (KaehlerDifferential.D C K (y i)) := by
      rw [← Set.image_comp, ← Set.range_comp]
      rfl
    rwa [hset] at himg
  exact DiffOp.free_of_torsionFree_of_fg _ hspan htf

end

end GaloisForLFunctions.HTGeometry
