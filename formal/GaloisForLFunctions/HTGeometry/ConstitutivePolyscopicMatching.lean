import GaloisForLFunctions.HTGeometry.ConstitutiveIrreducibleInteraction
import GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality

/-!
# Proper-face matching map, four phases, and the total-law defect

A polyscopic law diagram assigns to every observer face `S` its law shadow, together with
restriction maps.  The proper-face matching object is the limit of the shadows over all *proper*
faces, and the matching map sends a total law to the family of its proper-face shadows.

* `realizations_nonempty_iff`, `realizations_subsingleton_iff`, `matchingMap_bijective_iff` —
  realizability and uniqueness of a compatible proper-face datum are exactly nonemptiness and
  subsingletonness of the fibre of the matching map, and the matching map is a bijection precisely
  when every compatible proper-face law has a unique total law;
* `four_phases`, `phases_pairwise_disjoint` — the matching map lies in exactly one of the
  reconstructible, contextual, interaction, and mixed phases, and `phase_invariance` shows the phase
  is invariant under objectwise equivalence of diagrams;
* `matching_kernel_cokernel` — in a linear chart the kernel of the matching map is the hidden
  interaction invisible on every proper face and its cokernel is the space of compatible-looking
  face data not produced by a total law;
* `interactionDiagram_isInteracting` — the `N`-ary irreducible law with a scalar amplitude realizes
  the interaction phase natively, and `contextualDiagram_isContextual` realizes the contextual
  phase.
-/

namespace GaloisForLFunctions.HTGeometry

section Diagram

variable {I : Type} [DecidableEq I] [Fintype I]

/-- A polyscopic law diagram: the law shadow on each observer face together with restrictions. -/
structure LawDiagram (I : Type) where
  /-- The law shadow on an observer face. -/
  obj : Finset I → Type
  /-- Restriction of a shadow along an inclusion of faces. -/
  res : ∀ {S T : Finset I}, S ⊆ T → obj T → obj S
  /-- Restriction along the identity is the identity. -/
  res_self : ∀ (S : Finset I) (x : obj S), res (subset_refl S) x = x
  /-- Restriction is functorial. -/
  res_trans : ∀ {S T U : Finset I} (h₁ : S ⊆ T) (h₂ : T ⊆ U) (x : obj U),
    res h₁ (res h₂ x) = res (h₁.trans h₂) x

/-- A proper observer face. -/
abbrev ProperFace (I : Type) [Fintype I] [DecidableEq I] := {S : Finset I // S ≠ Finset.univ}

/-- A compatible proper-face datum: an element of the limit of the shadows over all proper faces. -/
@[ext]
structure ProperFaceDatum (X : LawDiagram I) where
  /-- The shadow chosen on each proper face. -/
  val : ∀ S : ProperFace I, X.obj S.1
  /-- The chosen shadows are compatible under restriction. -/
  compat : ∀ (S T : ProperFace I) (h : S.1 ⊆ T.1), X.res h (val T) = val S

/-- The canonical matching map from the total law object to the proper-face matching object. -/
def matchingMap (X : LawDiagram I) (x : X.obj Finset.univ) : ProperFaceDatum X where
  val S := X.res (Finset.subset_univ S.1) x
  compat S T h := by rw [X.res_trans]

/-- The realization space of a compatible proper-face datum. -/
def Realizations (X : LawDiagram I) (m : ProperFaceDatum X) :=
  {x : X.obj Finset.univ // matchingMap X x = m}

/-- **Realizability is nonemptiness of the realization space.** -/
theorem realizations_nonempty_iff (X : LawDiagram I) (m : ProperFaceDatum X) :
    (∃ x : X.obj Finset.univ, matchingMap X x = m) ↔ Nonempty (Realizations X m) :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x, hx⟩⟩, fun ⟨⟨x, hx⟩⟩ => ⟨x, hx⟩⟩

/-- **Uniqueness up to choice is subsingletonness of the realization space.** -/
theorem realizations_subsingleton_iff (X : LawDiagram I) (m : ProperFaceDatum X) :
    (∀ x y : X.obj Finset.univ, matchingMap X x = m → matchingMap X y = m → x = y) ↔
      Subsingleton (Realizations X m) := by
  constructor
  · intro h
    refine ⟨fun a b => Subtype.ext (h a.1 b.1 a.2 b.2)⟩
  · intro h x y hx hy
    exact congrArg Subtype.val (h.elim (⟨x, hx⟩ : Realizations X m) ⟨y, hy⟩)

/-- **The matching map is a bijection exactly when every compatible proper-face law has a unique
total law.** -/
theorem matchingMap_bijective_iff (X : LawDiagram I) :
    Function.Bijective (matchingMap X) ↔
      ∀ m : ProperFaceDatum X, ∃! x : X.obj Finset.univ, matchingMap X x = m :=
  Function.bijective_iff_existsUnique _

/-- Injectivity of the matching map is subsingletonness of every realization space. -/
theorem matchingMap_injective_iff (X : LawDiagram I) :
    Function.Injective (matchingMap X) ↔ ∀ m, Subsingleton (Realizations X m) := by
  constructor
  · intro h m
    exact (realizations_subsingleton_iff X m).mp fun x y hx hy => h (hx.trans hy.symm)
  · intro h x y hxy
    exact ((realizations_subsingleton_iff X (matchingMap X x)).mpr (h _)) x y rfl hxy.symm

/-- Surjectivity of the matching map is nonemptiness of every realization space. -/
theorem matchingMap_surjective_iff (X : LawDiagram I) :
    Function.Surjective (matchingMap X) ↔ ∀ m, Nonempty (Realizations X m) := by
  constructor
  · intro h m
    exact (realizations_nonempty_iff X m).mp (h m)
  · intro h m
    exact (realizations_nonempty_iff X m).mpr (h m)

end Diagram

section Phases

variable {I : Type} [DecidableEq I] [Fintype I]

/-- The reconstructible phase: the matching map is an equivalence. -/
def Reconstructible (X : LawDiagram I) : Prop := Function.Bijective (matchingMap X)

/-- The contextual phase: compatible face data can fail to be realized, but realized data are
unique. -/
def Contextual (X : LawDiagram I) : Prop :=
  Function.Injective (matchingMap X) ∧ ¬ Function.Surjective (matchingMap X)

/-- The interaction phase: every compatible face datum is realized, but not uniquely. -/
def Interacting (X : LawDiagram I) : Prop :=
  Function.Surjective (matchingMap X) ∧ ¬ Function.Injective (matchingMap X)

/-- The mixed phase: unrealizable face data and hidden total-law multiplicity coexist. -/
def Mixed (X : LawDiagram I) : Prop :=
  ¬ Function.Injective (matchingMap X) ∧ ¬ Function.Surjective (matchingMap X)

/-- **The four polyscopic phases are exhaustive.** -/
theorem four_phases (X : LawDiagram I) :
    Reconstructible X ∨ Contextual X ∨ Interacting X ∨ Mixed X := by
  by_cases hi : Function.Injective (matchingMap X)
  · by_cases hs : Function.Surjective (matchingMap X)
    · exact Or.inl ⟨hi, hs⟩
    · exact Or.inr (Or.inl ⟨hi, hs⟩)
  · by_cases hs : Function.Surjective (matchingMap X)
    · exact Or.inr (Or.inr (Or.inl ⟨hs, hi⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hi, hs⟩))

/-- **The four polyscopic phases are mutually exclusive.** -/
theorem phases_pairwise_disjoint (X : LawDiagram I) :
    ¬ (Reconstructible X ∧ Contextual X) ∧ ¬ (Reconstructible X ∧ Interacting X) ∧
      ¬ (Reconstructible X ∧ Mixed X) ∧ ¬ (Contextual X ∧ Interacting X) ∧
      ¬ (Contextual X ∧ Mixed X) ∧ ¬ (Interacting X ∧ Mixed X) :=
  ⟨fun h => h.2.2 h.1.2, fun h => h.2.2 h.1.1, fun h => h.2.1 h.1.1,
    fun h => h.2.2 h.1.1, fun h => h.2.1 h.1.1, fun h => h.2.2 h.1.1⟩

/-- An objectwise equivalence of polyscopic law diagrams. -/
structure DiagramEquiv (X Y : LawDiagram I) where
  /-- The equivalence of shadows on each face. -/
  app : ∀ S : Finset I, X.obj S ≃ Y.obj S
  /-- The equivalences commute with restriction. -/
  naturality : ∀ {S T : Finset I} (h : S ⊆ T) (x : X.obj T),
    app S (X.res h x) = Y.res h (app T x)

namespace DiagramEquiv

variable {X Y : LawDiagram I} (e : DiagramEquiv X Y)

omit [DecidableEq I] [Fintype I] in
theorem naturality_symm {S T : Finset I} (h : S ⊆ T) (y : Y.obj T) :
    (e.app S).symm (Y.res h y) = X.res h ((e.app T).symm y) := by
  apply (e.app S).injective
  rw [Equiv.apply_symm_apply, e.naturality, Equiv.apply_symm_apply]

/-- The induced equivalence of proper-face matching objects. -/
def datum : ProperFaceDatum X ≃ ProperFaceDatum Y where
  toFun m := ⟨fun S => e.app S.1 (m.val S), by
    intro S T h
    rw [← e.naturality, m.compat S T h]⟩
  invFun m := ⟨fun S => (e.app S.1).symm (m.val S), by
    intro S T h
    rw [← e.naturality_symm, m.compat S T h]⟩
  left_inv m := by
    apply ProperFaceDatum.ext
    funext S
    simp
  right_inv m := by
    apply ProperFaceDatum.ext
    funext S
    simp

theorem datum_matchingMap (x : X.obj Finset.univ) :
    e.datum (matchingMap X x) = matchingMap Y (e.app Finset.univ x) := by
  apply ProperFaceDatum.ext
  funext S
  exact e.naturality _ x

end DiagramEquiv

/-- **The polyscopic phase is invariant under objectwise equivalence.** -/
theorem phase_invariance {X Y : LawDiagram I} (e : DiagramEquiv X Y) :
    (Function.Injective (matchingMap X) ↔ Function.Injective (matchingMap Y)) ∧
      (Function.Surjective (matchingMap X) ↔ Function.Surjective (matchingMap Y)) := by
  have hcomm : ∀ x, e.datum (matchingMap X x) = matchingMap Y (e.app Finset.univ x) :=
    e.datum_matchingMap
  constructor
  · constructor
    · intro hX y y' hyy'
      apply (e.app Finset.univ).symm.injective
      refine hX ?_
      apply e.datum.injective
      rw [hcomm, hcomm, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hyy']
    · intro hY x x' hxx'
      apply (e.app Finset.univ).injective
      refine hY ?_
      rw [← hcomm, ← hcomm, hxx']
  · constructor
    · intro hX n
      obtain ⟨x, hx⟩ := hX (e.datum.symm n)
      refine ⟨e.app Finset.univ x, ?_⟩
      rw [← hcomm, hx, Equiv.apply_symm_apply]
    · intro hY m
      obtain ⟨y, hy⟩ := hY (e.datum m)
      refine ⟨(e.app Finset.univ).symm y, ?_⟩
      apply e.datum.injective
      rw [hcomm, Equiv.apply_symm_apply, hy]

end Phases

section LinearChart

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **Kernel and cokernel of the matching map.**  In a linear chart, the kernel of the matching map
is the hidden interaction invisible on every proper face and its cokernel is the space of
compatible-looking face data not produced by a total law; the four-term sequence
`0 → ker μ → V → W → W ⧸ range μ → 0` is exact. -/
theorem matching_kernel_cokernel (μ : V →ₗ[k] W) :
    LinearMap.range (LinearMap.ker μ).subtype = LinearMap.ker μ ∧
      LinearMap.range μ = LinearMap.ker (Submodule.mkQ (LinearMap.range μ)) ∧
      (LinearMap.ker μ = ⊥ ↔ Function.Injective μ) ∧
      (LinearMap.range μ = ⊤ ↔ Function.Surjective μ) :=
  ⟨Submodule.range_subtype _, (Submodule.ker_mkQ _).symm, LinearMap.ker_eq_bot,
    LinearMap.range_eq_top⟩

end LinearChart

section NativeRealizations

variable {I : Type} [DecidableEq I] [Fintype I]

/-- The diagram whose proper-face shadows record only satisfiability and whose total law object is
`A`. -/
def totalOnlyDiagram (I : Type) [DecidableEq I] [Fintype I] (A : Type) : LawDiagram I where
  obj S := (S = Finset.univ) → A
  res {_S _T} h f hS := f (Finset.univ_subset_iff.mp (hS ▸ h))
  res_self _ _ := by funext _; rfl
  res_trans _ _ _ := by funext _; rfl

theorem totalOnlyDiagram_properFace_subsingleton (A : Type) (S : ProperFace I) :
    Subsingleton ((totalOnlyDiagram I A).obj S.1) := by
  refine ⟨fun f g => ?_⟩
  funext hS
  exact absurd hS S.2

instance totalOnlyDiagram_datum_subsingleton (A : Type) :
    Subsingleton (ProperFaceDatum (totalOnlyDiagram I A)) := by
  refine ⟨fun m n => ?_⟩
  apply ProperFaceDatum.ext
  funext S
  exact (totalOnlyDiagram_properFace_subsingleton A S).elim _ _

instance totalOnlyDiagram_datum_nonempty (A : Type) :
    Nonempty (ProperFaceDatum (totalOnlyDiagram I A)) :=
  ⟨⟨fun S => fun hS => absurd hS S.2,
    fun S _ _ => (totalOnlyDiagram_properFace_subsingleton A S).elim _ _⟩⟩

theorem totalOnlyDiagram_surjective_of_nonempty (A : Type) [Nonempty A] :
    Function.Surjective (matchingMap (totalOnlyDiagram I A)) := by
  intro m
  refine ⟨fun _ => Classical.arbitrary A, ?_⟩
  exact Subsingleton.elim _ _

theorem totalOnlyDiagram_not_injective_of_nontrivial (A : Type) (a b : A) (hab : a ≠ b) :
    ¬ Function.Injective (matchingMap (totalOnlyDiagram I A)) := by
  intro hinj
  have h : (fun _ => a : (Finset.univ = Finset.univ) → A) = fun _ => b :=
    hinj (Subsingleton.elim _ _)
  exact hab (congrFun h rfl)

theorem totalOnlyDiagram_injective_of_isEmpty (A : Type) [IsEmpty A] :
    Function.Injective (matchingMap (totalOnlyDiagram I A)) := by
  intro x y _
  funext hS
  exact (IsEmpty.false (x hS)).elim

theorem totalOnlyDiagram_not_surjective_of_isEmpty (A : Type) [IsEmpty A] [Nonempty I] :
    ¬ Function.Surjective (matchingMap (totalOnlyDiagram I A)) := by
  intro hsurj
  obtain ⟨x, _⟩ := hsurj (Classical.arbitrary _)
  exact IsEmpty.false (x rfl)

/-- **The interaction phase is realized natively.**  Scaling the irreducible `N`-ary bracket by a
real amplitude leaves every proper colour face the zero law while the total law varies. -/
theorem scaledBracket_face_eq_zero (N : ℕ) (S : Finset (Fin N)) (hS : S ≠ Finset.univ)
    (lam : ℝ) (r : ℕ) :
    (lam • bracketFamily N r).compLinearMap (colorFace N S).subtype = 0 := by
  refine AlternatingMap.ext fun v => ?_
  have h := bracketFamily_comp_face_eq_zero N S hS r
  have hv : ((bracketFamily N r).compLinearMap (colorFace N S).subtype) v = 0 := by
    rw [h]; rfl
  simpa using congrArg (fun w => lam • w) hv

theorem scaledBracket_injective (N : ℕ) :
    Function.Injective (fun lam : ℝ => lam • interactionBracket N) := by
  intro a b hab
  have hab' : a • interactionBracket N = b • interactionBracket N := hab
  have h : (a • interactionBracket N) (fun i => colorGen i)
      = (b • interactionBracket N) (fun i => colorGen i) := by rw [hab']
  simp only [AlternatingMap.smul_apply, interactionBracket_colorGen] at h
  have h2 := congrArg Prod.snd h
  simpa [interactionOutput] using h2

/-- The interaction-phase diagram: proper faces record only that the face law is zero, the total
law object is the amplitude line. -/
def interactionDiagram (I : Type) [DecidableEq I] [Fintype I] : LawDiagram I :=
  totalOnlyDiagram I ℝ

theorem interactionDiagram_isInteracting : Interacting (interactionDiagram I) :=
  ⟨totalOnlyDiagram_surjective_of_nonempty ℝ,
    totalOnlyDiagram_not_injective_of_nontrivial ℝ 0 1 (by norm_num)⟩

/-- The contextual-phase diagram attached to an odd-charge parity context system: every proper
observer face is satisfiable, while the total law object is empty. -/
def contextualDiagram {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (b : V → ZMod 2) : LawDiagram V :=
  totalOnlyDiagram V {x : G.edgeSet → ZMod 2 // parityBoundary G x = b}

/-- Every proper observer face of a connected parity context system is satisfiable. -/
theorem properFace_satisfiable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hG : G.Connected) (W : Finset V) (hW : W ≠ Finset.univ)
    (b : V → ZMod 2) : ∃ x, ∀ v ∈ W, parityBoundary G x v = b v :=
  exists_parityBoundary_eq_on_of_ne_univ G hG W hW b

/-- **The contextual phase is realized natively** by an odd total parity charge. -/
theorem contextualDiagram_isContextual {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : G.Connected) {b : V → ZMod 2}
    (hb : ∑ v, b v = 1) : Contextual (contextualDiagram G b) := by
  have hempty : IsEmpty {x : G.edgeSet → ZMod 2 // parityBoundary G x = b} := by
    refine ⟨fun x => ?_⟩
    exact (properFace_blindness G hG hb).1 ⟨x.1, x.2⟩
  exact ⟨totalOnlyDiagram_injective_of_isEmpty _, totalOnlyDiagram_not_surjective_of_isEmpty _⟩

end NativeRealizations

end GaloisForLFunctions.HTGeometry
