import GaloisForLFunctions.HTGeometry.CDGAModuleColimit
import GaloisForLFunctions.HTGeometry.CDGACellInvariance

/-!
# Cohomology commutes with filtered colimits of differential graded modules

A cocycle of the colimit of a directed system of differential graded modules is already a cocycle at
some stage, and a coboundary of the colimit is already a coboundary at some stage.  Consequently a
family of morphisms which is a quasi-isomorphism at every stage induces a quasi-isomorphism of the
colimits, and the same holds for the degree-zero cocycles, so full quasi-isomorphisms pass to the
colimit as well.

* `moduleCocycle_at_stage` : a cocycle of the colimit comes from a cocycle at a stage.
* `colimModuleHom_isQuasiIso` : a stagewise quasi-isomorphism has quasi-isomorphic colimit.
* `colimModuleHom_isQuasiIsoFull` : the same for full quasi-isomorphisms.
-/

universe u v v' w

namespace GaloisForLFunctions.HTGeometry

section Stage

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {ι : Type v'} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)} (φ : ∀ i j, i ≤ j → CDGAModuleHom (P i) (P j))
  [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h]

/-- **A cocycle of the colimit comes from a cocycle at a stage.** -/
theorem moduleCocycle_at_stage (n : ℕ) (ξ : colimModuleDeg φ n)
    (hξ : colimModuleD φ n ξ = 0) :
    ∃ (i : ι) (u : M i n), (P i).d n u = 0 ∧
      Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) i u = ξ := by
  obtain ⟨i, u, rfl⟩ := Module.DirectLimit.exists_of ξ
  rw [colimModuleD_of] at hξ
  obtain ⟨j, hij, hzero⟩ := Module.DirectLimit.of.zero_exact hξ
  refine ⟨j, (φ i j hij).toFun n u, ?_, ?_⟩
  · rw [← (φ i j hij).map_d n u]
    exact hzero
  · exact Module.DirectLimit.of_f

end Stage

section ColimitQuasiIso

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {ι : Type v'} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {M : ι → ℕ → Type w} [∀ i n, AddCommGroup (M i n)] [∀ i n, Module R (M i n)]
  {P : ∀ i, CDGAModuleStructure A (M i)} (φ : ∀ i j, i ≤ j → CDGAModuleHom (P i) (P j))
  [∀ n : ℕ, DirectedSystem (fun i => M i n) fun i j h => moduleDegTransition φ n i j h]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {Q : ∀ i, CDGAModuleStructure A (N i)} (ψ : ∀ i j, i ≤ j → CDGAModuleHom (Q i) (Q j))
  [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h]
  (Θ : ∀ i, CDGAModuleHom (P i) (Q i))
  (hΘ : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (m : M i n),
    (Θ j).toFun n ((φ i j hij).toFun n m) = (ψ i j hij).toFun n ((Θ i).toFun n m))

include hΘ

/-- **A stagewise quasi-isomorphism induces a quasi-isomorphism of the colimits.** -/
theorem colimModuleHom_isQuasiIso (hqi : ∀ i, (Θ i).IsQuasiIso) :
    (colimModuleHom φ ψ Θ hΘ).IsQuasiIso := by
  intro n
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    refine Quotient.inductionOn' c ?_ hc
    intro ξ hξ
    obtain ⟨ζ, hζ⟩ : ∃ ζ : colimModuleDeg ψ n,
        colimModuleHomFun φ ψ Θ hΘ (n + 1) (ξ : colimModuleDeg φ (n + 1))
          = colimModuleD ψ n ζ :=
      (Submodule.Quotient.mk_eq_zero _).1 hξ
    obtain ⟨i, u, hud, huξ⟩ := moduleCocycle_at_stage φ (n + 1) (ξ : colimModuleDeg φ (n + 1)) ξ.2
    obtain ⟨i', z, rfl⟩ := Module.DirectLimit.exists_of ζ
    obtain ⟨m, him, hi'm⟩ := exists_ge_ge i i'
    set um : M m (n + 1) := moduleDegTransition φ (n + 1) i m him u with hum
    set zm : N m n := moduleDegTransition ψ n i' m hi'm z with hzm
    have huof : Module.DirectLimit.of R ι (fun i => M i (n + 1))
        (moduleDegTransition φ (n + 1)) m um = (ξ : colimModuleDeg φ (n + 1)) := by
      rw [hum, Module.DirectLimit.of_f, huξ]
    have hzof : Module.DirectLimit.of R ι (fun i => N i n) (moduleDegTransition ψ n) m zm
        = Module.DirectLimit.of R ι (fun i => N i n) (moduleDegTransition ψ n) i' z := by
      rw [hzm, Module.DirectLimit.of_f]
    have humd : (P m).d (n + 1) um = 0 := by
      show (P m).d (n + 1) ((φ i m him).toFun (n + 1) u) = 0
      rw [← (φ i m him).map_d (n + 1) u, hud]
      exact (φ i m him).mapₗ (n + 2) |>.map_zero
    have hstage : Module.DirectLimit.of R ι (fun i => N i (n + 1))
        (moduleDegTransition ψ (n + 1)) m ((Θ m).toFun (n + 1) um - (Q m).d n zm) = 0 := by
      rw [map_sub, ← colimModuleD_of ψ, ← colimModuleHomFun_of φ ψ Θ hΘ, huof, hzof, hζ, sub_self]
    obtain ⟨m', hmm', hzero⟩ := Module.DirectLimit.of.zero_exact hstage
    have hum'd : (P m').d (n + 1) ((φ m m' hmm').toFun (n + 1) um) = 0 := by
      rw [← (φ m m' hmm').map_d (n + 1) um, humd]
      exact (φ m m' hmm').mapₗ (n + 2) |>.map_zero
    have himg : (Θ m').toFun (n + 1) ((φ m m' hmm').toFun (n + 1) um)
        = (Q m').d n ((ψ m m' hmm').toFun n zm) := by
      rw [map_sub] at hzero
      have h1 : moduleDegTransition ψ (n + 1) m m' hmm' ((Θ m).toFun (n + 1) um)
          = (Θ m').toFun (n + 1) ((φ m m' hmm').toFun (n + 1) um) :=
        (hΘ m m' hmm' (n + 1) um).symm
      have h2 : moduleDegTransition ψ (n + 1) m m' hmm' ((Q m).d n zm)
          = (Q m').d n ((ψ m m' hmm').toFun n zm) := (ψ m m' hmm').map_d n zm
      rw [h1, h2] at hzero
      exact sub_eq_zero.1 hzero
    have hclass : (Θ m').cohomologyMap n
        (Submodule.Quotient.mk ⟨(φ m m' hmm').toFun (n + 1) um, hum'd⟩) = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨(ψ m m' hmm').toFun n zm, himg⟩
    have hzero' : (Submodule.Quotient.mk
        ⟨(φ m m' hmm').toFun (n + 1) um, hum'd⟩ : (P m').cohomology n) = 0 :=
      (injective_iff_map_eq_zero _).1 (hqi m' n).1 _ hclass
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 hzero'
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine ⟨Module.DirectLimit.of R ι (fun i => M i n) (moduleDegTransition φ n) m' y, ?_⟩
    show (ξ : colimModuleDeg φ (n + 1)) = colimModuleD φ n _
    rw [colimModuleD_of, ← hy]
    show (ξ : colimModuleDeg φ (n + 1))
      = Module.DirectLimit.of R ι (fun i => M i (n + 1)) (moduleDegTransition φ (n + 1)) m'
        (moduleDegTransition φ (n + 1) m m' hmm' um)
    rw [Module.DirectLimit.of_f, huof]
  · intro c
    refine Quotient.inductionOn' c fun η => ?_
    obtain ⟨i, w, hwd, hwη⟩ :=
      moduleCocycle_at_stage ψ (n + 1) (η : colimModuleDeg ψ (n + 1)) η.2
    obtain ⟨a, ha⟩ := (hqi i n).2 (Submodule.Quotient.mk ⟨w, hwd⟩)
    refine Quotient.inductionOn' a ?_ ha
    intro u hu
    have hud : (P i).d (n + 1) (u : M i (n + 1)) = 0 := u.2
    obtain ⟨z, hz⟩ : ∃ z : N i n,
        (Θ i).toFun (n + 1) (u : M i (n + 1)) - w = (Q i).d n z :=
      (Submodule.Quotient.eq _).1 hu
    refine ⟨Submodule.Quotient.mk ⟨Module.DirectLimit.of R ι (fun i => M i (n + 1))
      (moduleDegTransition φ (n + 1)) i (u : M i (n + 1)), ?_⟩, ?_⟩
    · show colimModuleD φ (n + 1) _ = 0
      rw [colimModuleD_of, hud]
      exact map_zero _
    · refine (Submodule.Quotient.eq _).2 ?_
      refine ⟨Module.DirectLimit.of R ι (fun i => N i n) (moduleDegTransition ψ n) i z, ?_⟩
      show colimModuleHomFun φ ψ Θ hΘ (n + 1) _ - (η : colimModuleDeg ψ (n + 1))
        = colimModuleD ψ n _
      rw [colimModuleHomFun_of φ ψ Θ hΘ, colimModuleD_of ψ, ← hwη, ← map_sub, hz]

/-- **A stagewise full quasi-isomorphism induces a full quasi-isomorphism of the colimits.**  The
degree-zero cocycles are handled exactly like the cohomology: a cocycle of the colimit and a
vanishing of the colimit are both already visible at a stage. -/
theorem colimModuleHom_isQuasiIsoFull (hqi : ∀ i, (Θ i).IsQuasiIsoFull) :
    (colimModuleHom φ ψ Θ hΘ).IsQuasiIsoFull := by
  refine ⟨⟨?_, ?_⟩, colimModuleHom_isQuasiIso φ ψ Θ hΘ fun i => (hqi i).2⟩
  · refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
    obtain ⟨i, u, hud, huξ⟩ := moduleCocycle_at_stage φ 0 (ξ : colimModuleDeg φ 0) ξ.2
    have himg : Module.DirectLimit.of R ι (fun i => N i 0) (moduleDegTransition ψ 0) i
        ((Θ i).toFun 0 u) = 0 := by
      rw [← colimModuleHomFun_of φ ψ Θ hΘ, huξ]
      exact congrArg Subtype.val hξ
    obtain ⟨j, hij, hzero⟩ := Module.DirectLimit.of.zero_exact himg
    have hujd : (P j).d 0 ((φ i j hij).toFun 0 u) = 0 := by
      rw [← (φ i j hij).map_d 0 u, hud]
      exact (φ i j hij).mapₗ 1 |>.map_zero
    have hΘj : (Θ j).toFun 0 ((φ i j hij).toFun 0 u) = 0 := by
      rw [hΘ i j hij 0 u]
      exact hzero
    have hzero' : ((φ i j hij).toFun 0 u) = 0 := by
      have := (injective_iff_map_eq_zero _).1 (hqi j).1.1
        (⟨(φ i j hij).toFun 0 u, hujd⟩ : (P j).cocycles 0)
      exact congrArg Subtype.val (this (Subtype.ext hΘj))
    have hof : Module.DirectLimit.of R ι (fun i => M i 0) (moduleDegTransition φ 0) j
        (moduleDegTransition φ 0 i j hij u)
      = Module.DirectLimit.of R ι (fun i => M i 0) (moduleDegTransition φ 0) i u :=
      Module.DirectLimit.of_f
    refine Subtype.ext ?_
    show (ξ : colimModuleDeg φ 0) = 0
    rw [← huξ, ← hof]
    show Module.DirectLimit.of R ι (fun i => M i 0) (moduleDegTransition φ 0) j
      ((φ i j hij).toFun 0 u) = 0
    rw [hzero']
    exact map_zero _
  · intro η
    obtain ⟨i, w, hwd, hwη⟩ := moduleCocycle_at_stage ψ 0 (η : colimModuleDeg ψ 0) η.2
    obtain ⟨u, hu⟩ := (hqi i).1.2 (⟨w, hwd⟩ : (Q i).cocycles 0)
    have hud : (P i).d 0 (u : M i 0) = 0 := u.2
    refine ⟨⟨Module.DirectLimit.of R ι (fun i => M i 0) (moduleDegTransition φ 0) i
      (u : M i 0), ?_⟩, ?_⟩
    · show colimModuleD φ 0 _ = 0
      rw [colimModuleD_of, hud]
      exact map_zero _
    · refine Subtype.ext ?_
      show colimModuleHomFun φ ψ Θ hΘ 0 _ = (η : colimModuleDeg ψ 0)
      rw [colimModuleHomFun_of φ ψ Θ hΘ, ← hwη]
      exact congrArg _ (congrArg Subtype.val hu)

end ColimitQuasiIso

end GaloisForLFunctions.HTGeometry
