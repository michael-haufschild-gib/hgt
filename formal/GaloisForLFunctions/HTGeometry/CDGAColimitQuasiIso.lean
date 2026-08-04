import GaloisForLFunctions.HTGeometry.CDGAColimit

/-!
# Cohomology commutes with filtered colimits of algebras

A cocycle of the colimit of a directed system of commutative differential graded algebras is
already a cocycle at some stage, and a coboundary of the colimit is already a coboundary at some
stage.  Consequently a family of morphisms which is a quasi-isomorphism at every stage induces a
quasi-isomorphism of the colimits.

* `cocycle_at_stage` : a cocycle of the colimit comes from a cocycle at a stage.
* `colimHom_isQuasiIso` : a stagewise quasi-isomorphism has quasi-isomorphic colimit.
-/

set_option maxHeartbeats 1000000

universe u v w

namespace GaloisForLFunctions.HTGeometry

section QuasiIso

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι]
  {X : ι → ℕ → Type w} [∀ i n, AddCommGroup (X i n)] [∀ i n, Module R (X i n)]
  {A : ∀ i, CDGAStructure R (X i)} (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j))
  [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h]

/-- **A cocycle of the colimit comes from a cocycle at a stage.** -/
theorem cocycle_at_stage (n : ℕ) (ξ : colimDeg φ (n + 1))
    (hξ : colimD φ (n + 1) ξ = 0) :
    ∃ (i : ι) (x : X i (n + 1)), (A i).d (n + 1) x = 0 ∧
      Module.DirectLimit.of R ι (fun i => X i (n + 1)) (degTransition φ (n + 1)) i x = ξ := by
  obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of ξ
  rw [colimD_of] at hξ
  obtain ⟨j, hij, hzero⟩ := Module.DirectLimit.of.zero_exact hξ
  refine ⟨j, (φ i j hij).toFun (n + 1) x, ?_, ?_⟩
  · rw [← (φ i j hij).map_d (n + 1) x]
    exact hzero
  · exact Module.DirectLimit.of_f

end QuasiIso

section ColimitQuasiIso

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι]
  {X : ι → ℕ → Type w} [∀ i n, AddCommGroup (X i n)] [∀ i n, Module R (X i n)]
  {A : ∀ i, CDGAStructure R (X i)} (φ : ∀ i j, i ≤ j → CDGAHom (A i) (A j))
  [∀ n : ℕ, DirectedSystem (fun i => X i n) fun i j h => degTransition φ n i j h]
  {Y : ι → ℕ → Type w} [∀ i n, AddCommGroup (Y i n)] [∀ i n, Module R (Y i n)]
  {B : ∀ i, CDGAStructure R (Y i)} (ψ : ∀ i j, i ≤ j → CDGAHom (B i) (B j))
  [∀ n : ℕ, DirectedSystem (fun i => Y i n) fun i j h => degTransition ψ n i j h]
  (Θ : ∀ i, CDGAHom (A i) (B i))
  (hΘ : ∀ (i j : ι) (hij : i ≤ j) (n : ℕ) (x : X i n),
    (Θ j).toFun n ((φ i j hij).toFun n x) = (ψ i j hij).toFun n ((Θ i).toFun n x))

include hΘ

/-- **A stagewise quasi-isomorphism induces a quasi-isomorphism of the colimits.** -/
theorem colimHom_isQuasiIso (hqi : ∀ i, (Θ i).IsQuasiIso) :
    (colimHom φ ψ Θ hΘ).IsQuasiIso := by
  intro n
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    refine Quotient.inductionOn' c ?_ hc
    intro ξ hξ
    -- the image is a coboundary of the colimit
    obtain ⟨ζ, hζ⟩ : ∃ ζ : colimDeg ψ n,
        colimHomFun φ ψ Θ hΘ (n + 1) (ξ : colimDeg φ (n + 1)) = colimD ψ n ζ :=
      (Submodule.Quotient.mk_eq_zero _).1 hξ
    -- both sides come from a common stage
    obtain ⟨i, x, hxd, hxξ⟩ := cocycle_at_stage φ n (ξ : colimDeg φ (n + 1)) ξ.2
    obtain ⟨i', z, rfl⟩ := Module.DirectLimit.exists_of ζ
    obtain ⟨m, him, hi'm⟩ := exists_ge_ge i i'
    set xm : X m (n + 1) := degTransition φ (n + 1) i m him x with hxm
    set zm : Y m n := degTransition ψ n i' m hi'm z with hzm
    have hxof : Module.DirectLimit.of R ι (fun i => X i (n + 1)) (degTransition φ (n + 1)) m xm =
        (ξ : colimDeg φ (n + 1)) := by
      rw [hxm, Module.DirectLimit.of_f, hxξ]
    have hzof : Module.DirectLimit.of R ι (fun i => Y i n) (degTransition ψ n) m zm =
        Module.DirectLimit.of R ι (fun i => Y i n) (degTransition ψ n) i' z := by
      rw [hzm, Module.DirectLimit.of_f]
    have hxmd : (A m).d (n + 1) xm = 0 := by
      show (A m).d (n + 1) ((φ i m him).toFun (n + 1) x) = 0
      rw [← (φ i m him).map_d (n + 1) x, hxd]
      exact (φ i m him).mapₗ (n + 2) |>.map_zero
    have hstage : Module.DirectLimit.of R ι (fun i => Y i (n + 1)) (degTransition ψ (n + 1)) m
        ((Θ m).toFun (n + 1) xm - (B m).d n zm) = 0 := by
      rw [map_sub, ← colimD_of ψ, ← colimHomFun_of φ ψ Θ hΘ, hxof, hzof, hζ, sub_self]
    obtain ⟨m', hmm', hzero⟩ := Module.DirectLimit.of.zero_exact hstage
    -- at that stage the image of the class vanishes
    have hxm'd : (A m').d (n + 1) ((φ m m' hmm').toFun (n + 1) xm) = 0 := by
      rw [← (φ m m' hmm').map_d (n + 1) xm, hxmd]
      exact (φ m m' hmm').mapₗ (n + 2) |>.map_zero
    have himg : (Θ m').toFun (n + 1) ((φ m m' hmm').toFun (n + 1) xm) =
        (B m').d n ((ψ m m' hmm').toFun n zm) := by
      rw [map_sub] at hzero
      have h1 : degTransition ψ (n + 1) m m' hmm' ((Θ m).toFun (n + 1) xm) =
          (Θ m').toFun (n + 1) ((φ m m' hmm').toFun (n + 1) xm) :=
        (hΘ m m' hmm' (n + 1) xm).symm
      have h2 : degTransition ψ (n + 1) m m' hmm' ((B m).d n zm) =
          (B m').d n ((ψ m m' hmm').toFun n zm) := (ψ m m' hmm').map_d n zm
      rw [h1, h2] at hzero
      exact sub_eq_zero.1 hzero
    have hclass : (Θ m').cohomologyMap n
        (Submodule.Quotient.mk ⟨(φ m m' hmm').toFun (n + 1) xm, hxm'd⟩) = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      exact ⟨(ψ m m' hmm').toFun n zm, himg⟩
    have hzero' : (Submodule.Quotient.mk
        ⟨(φ m m' hmm').toFun (n + 1) xm, hxm'd⟩ : (A m').cohomology n) = 0 :=
      (injective_iff_map_eq_zero _).1 (hqi m' n).1 _ hclass
    obtain ⟨u, hu⟩ := (Submodule.Quotient.mk_eq_zero _).1 hzero'
    -- so the class in the colimit vanishes
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    refine ⟨Module.DirectLimit.of R ι (fun i => X i n) (degTransition φ n) m' u, ?_⟩
    show (ξ : colimDeg φ (n + 1)) = colimD φ n _
    rw [colimD_of, ← hu]
    show (ξ : colimDeg φ (n + 1)) =
      Module.DirectLimit.of R ι (fun i => X i (n + 1)) (degTransition φ (n + 1)) m'
        (degTransition φ (n + 1) m m' hmm' xm)
    rw [Module.DirectLimit.of_f, hxof]
  · intro c
    refine Quotient.inductionOn' c fun η => ?_
    obtain ⟨i, w, hwd, hwη⟩ := cocycle_at_stage ψ n (η : colimDeg ψ (n + 1)) η.2
    obtain ⟨a, ha⟩ := (hqi i n).2 (Submodule.Quotient.mk ⟨w, hwd⟩)
    refine Quotient.inductionOn' a ?_ ha
    intro x hx
    have hxd : (A i).d (n + 1) (x : X i (n + 1)) = 0 := x.2
    obtain ⟨z, hz⟩ : ∃ z : Y i n,
        (Θ i).toFun (n + 1) (x : X i (n + 1)) - w = (B i).d n z :=
      (Submodule.Quotient.eq _).1 hx
    refine ⟨Submodule.Quotient.mk ⟨Module.DirectLimit.of R ι (fun i => X i (n + 1))
      (degTransition φ (n + 1)) i (x : X i (n + 1)), ?_⟩, ?_⟩
    · show colimD φ (n + 1) _ = 0
      rw [colimD_of, hxd]
      exact map_zero _
    · refine (Submodule.Quotient.eq _).2 ?_
      refine ⟨Module.DirectLimit.of R ι (fun i => Y i n) (degTransition ψ n) i z, ?_⟩
      show colimHomFun φ ψ Θ hΘ (n + 1) _ - (η : colimDeg ψ (n + 1)) = colimD ψ n _
      rw [colimHomFun_of φ ψ Θ hΘ, colimD_of ψ, ← hwη, ← map_sub, hz]

end ColimitQuasiIso

end GaloisForLFunctions.HTGeometry
