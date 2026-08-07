import GaloisForLFunctions.HTGeometry.CDGARelTensorRight
import GaloisForLFunctions.HTGeometry.CDGATensorColimit

/-!
# The tensor product over the algebra commutes with filtered colimits

A relation of the tensor product over the colimit is a finite combination of relators, and each
relator involves one element of the colimit, so all of them are already visible at a single stage.
Combined with the fact that the graded tensor product commutes with the colimit, this makes the
quotient commute with it too.

* `HTGeometry.relTensorDegTransition` : the transitions of the system of quotients.
* `HTGeometry.relTensorColimEquiv` : the comparison, an isomorphism.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)] [∀ i n, Module R (N i n)]
  {Q : ∀ i, CDGAModuleStructure A (N i)} (P : CDGAModuleStructure A M)
  (ψ : ∀ i j, i ≤ j → CDGAModuleHom (Q i) (Q j))

/-- The system of tensor products over the algebra, as differential graded modules. -/
noncomputable def relTensorSystem (i j : ι) (h : i ≤ j) :
    CDGAModuleHom (relTensorModule P (Q i)) (relTensorModule P (Q j)) :=
  relTensorMapRight P (ψ i j h)

/-- The transitions of the system of tensor products over the algebra. -/
noncomputable def relTensorDegTransition (n : ℕ) (i j : ι) (h : i ≤ j) :
    RelTensorCarrier P (Q i) n →ₗ[R] RelTensorCarrier P (Q j) n :=
  (relTensorMapRight P (ψ i j h)).mapₗ n

variable [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h]

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
/-- Functoriality in the right variable composes. -/
theorem tensorMapRight_comp_apply {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (n : ℕ)
    (z : TensorCarrier (R := R) M (N i) n) :
    (tensorMapRight P (ψ j k hjk)).toFun n ((tensorMapRight P (ψ i j hij)).toFun n z)
      = (tensorMapRight P (ψ i k (hij.trans hjk))).toFun n z := by
  funext p
  show TensorProduct.map LinearMap.id ((ψ j k hjk).mapₗ p.1.2)
      (TensorProduct.map LinearMap.id ((ψ i j hij).mapₗ p.1.2) (z p))
    = TensorProduct.map LinearMap.id ((ψ i k (hij.trans hjk)).mapₗ p.1.2) (z p)
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
  refine congrArg (fun L : N i p.1.2 →ₗ[R] N k p.1.2 =>
    (TensorProduct.map (LinearMap.id : M p.1.1 →ₗ[R] M p.1.1) L) (z p)) ?_
  exact LinearMap.ext fun v =>
    DirectedSystem.map_map (f := fun i j h => moduleDegTransition ψ p.1.2 i j h) hij hjk v

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
/-- The transition of a relation with itself is the identity. -/
theorem tensorMapRight_self_apply {i : ι} (h : i ≤ i) (n : ℕ)
    (z : TensorCarrier (R := R) M (N i) n) :
    (tensorMapRight P (ψ i i h)).toFun n z = z := by
  funext p
  show TensorProduct.map LinearMap.id ((ψ i i h).mapₗ p.1.2) (z p) = z p
  rw [show ((ψ i i h).mapₗ p.1.2) = LinearMap.id from LinearMap.ext fun v =>
    DirectedSystem.map_self (f := fun i j h => moduleDegTransition ψ p.1.2 i j h) v,
    TensorProduct.map_id]
  rfl

instance relTensorDirectedSystem (n : ℕ) :
    DirectedSystem (fun i => RelTensorCarrier P (Q i) n)
      fun i j h => relTensorDegTransition P ψ n i j h where
  map_self := by
    intro i f
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg Submodule.Quotient.mk (tensorMapRight_self_apply P ψ le_rfl n z)
  map_map := by
    intro k j i hij hjk f
    refine Quotient.inductionOn' f fun z => ?_
    exact congrArg Submodule.Quotient.mk (tensorMapRight_comp_apply P ψ hij hjk n z)

instance relTensorSystemDirectedSystem (n : ℕ) :
    DirectedSystem (fun i => RelTensorCarrier P (Q i) n)
      fun i j h => moduleDegTransition (relTensorSystem P ψ) n i j h :=
  inferInstanceAs (DirectedSystem (fun i => RelTensorCarrier P (Q i) n)
    fun i j h => relTensorDegTransition P ψ n i j h)

/-- The comparison from the colimit of the quotients to the quotient over the colimit. -/
noncomputable def relTensorColimMap (n : ℕ) :
    colimModuleDeg (relTensorSystem P ψ) n →ₗ[R] RelTensorCarrier P (colimModule ψ) n :=
  Module.DirectLimit.lift R ι _ _
    (fun i => (relTensorMapRight P (colimModuleOf ψ i)).mapₗ n)
    (fun i j hij f => by
      refine Quotient.inductionOn' f fun z => ?_
      refine congrArg Submodule.Quotient.mk ?_
      funext p
      show TensorProduct.map LinearMap.id ((colimModuleOf ψ j).mapₗ p.1.2)
          (TensorProduct.map LinearMap.id ((ψ i j hij).mapₗ p.1.2) (z p))
        = TensorProduct.map LinearMap.id ((colimModuleOf ψ i).mapₗ p.1.2) (z p)
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
      refine congrArg (fun L : N i p.1.2 →ₗ[R] colimModuleDeg ψ p.1.2 =>
        (TensorProduct.map (LinearMap.id : M p.1.1 →ₗ[R] M p.1.1) L) (z p)) ?_
      exact LinearMap.ext fun v => Module.DirectLimit.of_f)

omit [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h] in
@[simp] theorem relTensorColimMap_of (n : ℕ) (i : ι) (f : RelTensorCarrier P (Q i) n) :
    relTensorColimMap P ψ n
        ((colimModuleOf (relTensorSystem P ψ) i).toFun n f)
      = (relTensorMapRight P (colimModuleOf ψ i)).toFun n f := by
  rw [colimModuleOf_eq]
  simp only [relTensorColimMap, Module.DirectLimit.lift_of]
  rfl

omit [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h] in
/-- The graded comparison factors the canonical maps from the stages. -/
theorem tensorMapRight_colimOf {i j : ι} (hij : i ≤ j) (n : ℕ)
    (z : TensorCarrier (R := R) M (N i) n) :
    (tensorMapRight P (colimModuleOf ψ j)).toFun n ((tensorMapRight P (ψ i j hij)).toFun n z)
      = (tensorMapRight P (colimModuleOf ψ i)).toFun n z := by
  funext p
  show TensorProduct.map LinearMap.id ((colimModuleOf ψ j).mapₗ p.1.2)
      (TensorProduct.map LinearMap.id ((ψ i j hij).mapₗ p.1.2) (z p))
    = TensorProduct.map LinearMap.id ((colimModuleOf ψ i).mapₗ p.1.2) (z p)
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
  refine congrArg (fun L : N i p.1.2 →ₗ[R] colimModuleDeg ψ p.1.2 =>
    (TensorProduct.map (LinearMap.id : M p.1.1 →ₗ[R] M p.1.1) L) (z p)) ?_
  exact LinearMap.ext fun v => Module.DirectLimit.of_f

/-- The graded comparison of the colimits is the canonical map from a stage. -/
theorem tensorColimEquiv_eq_tensorMapRight (n : ℕ) (i : ι)
    (z : TensorCarrier (R := R) M (N i) n) :
    tensorColimEquiv ψ n
        (Module.DirectLimit.of R ι (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
          (piTransition (tensorFamilyTransition (M := M) ψ n)) i z)
      = (tensorMapRight P (colimModuleOf ψ i)).toFun n z := by
  funext p
  rw [tensorColimEquiv_of]
  rfl

omit [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h] in
/-- **A relation over the colimit is already a relation at a stage.** -/
theorem relTensorRel_colim_at_stage (n : ℕ)
    (g : TensorCarrier (R := R) M (colimModuleDeg ψ) n)
    (hg : g ∈ relTensorRel P (colimModule ψ) n) :
    ∃ (j : ι) (y : TensorCarrier (R := R) M (N j) n), y ∈ relTensorRel P (Q j) n ∧
      (tensorMapRight P (colimModuleOf ψ j)).toFun n y = g := by
  refine Submodule.span_induction
    (p := fun h _ => ∃ (j : ι) (y : TensorCarrier (R := R) M (N j) n),
      y ∈ relTensorRel P (Q j) n ∧
      (tensorMapRight P (colimModuleOf ψ j)).toFun n y = h) ?_ ?_ ?_ ?_ hg
  · rintro h ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, V, rfl⟩
    obtain ⟨i, v, rfl⟩ := Module.DirectLimit.exists_of V
    exact ⟨i, relTensorRelator P (Q i) hα hβ hn hn' x m v,
      relTensorRelator_mem P (Q i) hα hβ hn hn' x m v,
      tensorMapRight_relTensorRelator P (colimModuleOf ψ i) hα hβ hn hn' x m v⟩
  · exact ⟨Classical.arbitrary ι, 0, Submodule.zero_mem _,
      ((tensorMapRight P (colimModuleOf ψ (Classical.arbitrary ι))).mapₗ n).map_zero⟩
  · rintro g₁ g₂ _ _ ⟨j₁, y₁, hy₁, hg₁⟩ ⟨j₂, y₂, hy₂, hg₂⟩
    obtain ⟨j, hj₁, hj₂⟩ := exists_ge_ge j₁ j₂
    refine ⟨j, (tensorMapRight P (ψ j₁ j hj₁)).toFun n y₁
        + (tensorMapRight P (ψ j₂ j hj₂)).toFun n y₂,
      Submodule.add_mem _ (relTensorRel_map_right P (ψ j₁ j hj₁) n y₁ hy₁)
        (relTensorRel_map_right P (ψ j₂ j hj₂) n y₂ hy₂), ?_⟩
    rw [(tensorMapRight P (colimModuleOf ψ j)).map_add, tensorMapRight_colimOf,
      tensorMapRight_colimOf, hg₁, hg₂]
  · rintro r g₁ _ ⟨j₁, y₁, hy₁, hg₁⟩
    exact ⟨j₁, r • y₁, Submodule.smul_mem _ _ hy₁, by
      rw [(tensorMapRight P (colimModuleOf ψ j₁)).map_smul, hg₁]⟩

theorem relTensorColimMap_surjective (n : ℕ) :
    Function.Surjective (relTensorColimMap P ψ n) := by
  intro g
  refine Quotient.inductionOn' g fun z => ?_
  obtain ⟨i, w, hw⟩ := Module.DirectLimit.exists_of ((tensorColimEquiv ψ n).symm z)
  have hz : (tensorMapRight P (colimModuleOf ψ i)).toFun n w = z := by
    rw [← tensorColimEquiv_eq_tensorMapRight P ψ n i w, hw]
    exact (tensorColimEquiv ψ n).apply_symm_apply z
  refine ⟨(colimModuleOf (relTensorSystem P ψ) i).toFun n (Submodule.Quotient.mk w), ?_⟩
  rw [relTensorColimMap_of]
  exact congrArg Submodule.Quotient.mk hz

theorem relTensorColimMap_injective (n : ℕ) :
    Function.Injective (relTensorColimMap P ψ n) := by
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ => ?_
  obtain ⟨i, f, rfl⟩ := colimModuleOf_exists (relTensorSystem P ψ) n ξ
  revert hξ
  refine Quotient.inductionOn' f fun z hz => ?_
  rw [relTensorColimMap_of] at hz
  have hmem : (tensorMapRight P (colimModuleOf ψ i)).toFun n z
      ∈ relTensorRel P (colimModule ψ) n := (Submodule.Quotient.mk_eq_zero _).1 hz
  obtain ⟨j, y, hy, hgy⟩ := relTensorRel_colim_at_stage P ψ n _ hmem
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  obtain ⟨A, hA⟩ : ∃ A : tensorColimFamily (R := R) (M := M) (N := N) n k,
    A = (tensorMapRight P (ψ i k hik)).toFun n z := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : tensorColimFamily (R := R) (M := M) (N := N) n k,
    B = (tensorMapRight P (ψ j k hjk)).toFun n y := ⟨_, rfl⟩
  have hzero : Module.DirectLimit.of R ι
      (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
      (piTransition (tensorFamilyTransition (M := M) ψ n)) k (A - B) = 0 := by
    refine (tensorColimEquiv ψ n).injective ?_
    rw [map_sub (Module.DirectLimit.of R ι
        (fun i => tensorColimFamily (R := R) (M := M) (N := N) n i)
        (piTransition (tensorFamilyTransition (M := M) ψ n)) k) A B,
      map_sub (tensorColimEquiv ψ n),
      tensorColimEquiv_eq_tensorMapRight P ψ n k A,
      tensorColimEquiv_eq_tensorMapRight P ψ n k B, hA, hB,
      tensorMapRight_colimOf, tensorMapRight_colimOf, hgy, sub_self,
      map_zero (tensorColimEquiv ψ n)]
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.of.zero_exact hzero
  have hpi : ∀ u : tensorColimFamily (R := R) (M := M) (N := N) n k,
      piTransition (tensorFamilyTransition (M := M) ψ n) k l hkl u
        = (tensorMapRight P (ψ k l hkl)).toFun n u := by
    intro u
    funext p
    rfl
  rw [map_sub (piTransition (tensorFamilyTransition (M := M) ψ n) k l hkl) A B,
    hpi A, hpi B, hA, hB, tensorMapRight_comp_apply P ψ hik hkl,
    tensorMapRight_comp_apply P ψ hjk hkl, sub_eq_zero] at hl
  have hstage : (tensorMapRight P (ψ i l (hik.trans hkl))).toFun n z
      ∈ relTensorRel P (Q l) n := by
    rw [hl]
    exact relTensorRel_map_right P (ψ j l (hjk.trans hkl)) n y hy
  have hof : (colimModuleOf (relTensorSystem P ψ) l).toFun n
      ((relTensorSystem P ψ i l (hik.trans hkl)).toFun n (Submodule.Quotient.mk z))
    = (colimModuleOf (relTensorSystem P ψ) i).toFun n (Submodule.Quotient.mk z) :=
    colimModuleOf_trans (relTensorSystem P ψ) (hik.trans hkl) n _
  show (colimModuleOf (relTensorSystem P ψ) i).toFun n (Submodule.Quotient.mk z) = 0
  rw [← hof, show (relTensorSystem P ψ i l (hik.trans hkl)).toFun n (Submodule.Quotient.mk z)
      = (0 : RelTensorCarrier P (Q l) n) from
    (Submodule.Quotient.mk_eq_zero _).2 hstage]
  exact ((colimModuleOf (relTensorSystem P ψ) l).mapₗ n).map_zero

/-- **The tensor product over the algebra commutes with a filtered colimit.** -/
noncomputable def relTensorColimEquiv (n : ℕ) :
    colimModuleDeg (relTensorSystem P ψ) n ≃ₗ[R] RelTensorCarrier P (colimModule ψ) n :=
  LinearEquiv.ofBijective (relTensorColimMap P ψ n)
    ⟨relTensorColimMap_injective P ψ n, relTensorColimMap_surjective P ψ n⟩

/-- **The comparison is a morphism of differential graded modules.** -/
noncomputable def relTensorColimHom :
    CDGAModuleHom (colimModule (relTensorSystem P ψ)) (relTensorModule P (colimModule ψ)) where
  toFun n f := relTensorColimMap P ψ n f
  map_add n f f' := map_add (relTensorColimMap P ψ n) f f'
  map_smul n c f := map_smul (relTensorColimMap P ψ n) c f
  map_act := by
    intro c a m h x f
    obtain ⟨i, g, rfl⟩ := colimModuleOf_exists (relTensorSystem P ψ) a f
    show relTensorColimMap P ψ m (colimModuleAct (relTensorSystem P ψ) h x _)
      = relTensorAct P (colimModule ψ) h x (relTensorColimMap P ψ a _)
    rw [colimModuleAct_colimOf, relTensorColimMap_of, relTensorColimMap_of]
    exact (relTensorMapRight P (colimModuleOf ψ i)).map_act h x g
  map_d := by
    intro n f
    obtain ⟨i, g, rfl⟩ := colimModuleOf_exists (relTensorSystem P ψ) n f
    show relTensorColimMap P ψ (n + 1) (colimModuleD (relTensorSystem P ψ) n _)
      = relTensorD P (colimModule ψ) n (relTensorColimMap P ψ n _)
    rw [colimModuleD_colimOf, relTensorColimMap_of, relTensorColimMap_of]
    exact (relTensorMapRight P (colimModuleOf ψ i)).map_d n g

theorem relTensorColimHom_isQuasiIsoFull : (relTensorColimHom P ψ).IsQuasiIsoFull :=
  CDGAModuleHom.IsQuasiIsoFull.of_bijective fun n =>
    ⟨relTensorColimMap_injective P ψ n, relTensorColimMap_surjective P ψ n⟩

section Naturality

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  (P' : CDGAModuleStructure A M') (φ : CDGAModuleHom P P')

/-- The two functorialities commute on the tensor product over the algebra. -/
theorem relTensorMapLeft_relTensorMapRight {i j : ι} (hij : i ≤ j) (n : ℕ)
    (f : RelTensorCarrier P (Q i) n) :
    (relTensorMapLeft φ (Q j)).toFun n ((relTensorSystem P ψ i j hij).toFun n f)
      = (relTensorSystem P' ψ i j hij).toFun n ((relTensorMapLeft φ (Q i)).toFun n f) := by
  refine Quotient.inductionOn' f fun z => ?_
  refine congrArg Submodule.Quotient.mk ?_
  exact congrFun (congrArg (fun H : CDGAModuleHom (tensorModule P (Q i)) (tensorModule P' (Q j)) =>
    H.toFun n) (tensorMapLeft_comp_tensorMapRight φ (Q i) (Q j) (ψ i j hij))) z

/-- The comparison of the colimits is natural in the left variable. -/
theorem relTensorColimHom_naturality :
    (relTensorMapLeft φ (colimModule ψ)).comp (relTensorColimHom P ψ)
      = (relTensorColimHom P' ψ).comp (colimModuleHom (relTensorSystem P ψ)
          (relTensorSystem P' ψ) (fun i => relTensorMapLeft φ (Q i))
          (fun i j hij n f => relTensorMapLeft_relTensorMapRight P ψ P' φ hij n f)) := by
  refine CDGAModuleHom.hom_ext fun n ξ => ?_
  obtain ⟨i, f, rfl⟩ := colimModuleOf_exists (relTensorSystem P ψ) n ξ
  refine Quotient.inductionOn' f fun z => ?_
  show (relTensorMapLeft φ (colimModule ψ)).toFun n
      (relTensorColimMap P ψ n
        ((colimModuleOf (relTensorSystem P ψ) i).toFun n (Submodule.Quotient.mk z)))
    = relTensorColimMap P' ψ n (colimModuleHomFun (relTensorSystem P ψ) (relTensorSystem P' ψ)
        (fun i => relTensorMapLeft φ (Q i))
        (fun i j hij n f => relTensorMapLeft_relTensorMapRight P ψ P' φ hij n f) n
        ((colimModuleOf (relTensorSystem P ψ) i).toFun n (Submodule.Quotient.mk z)))
  rw [relTensorColimMap_of, colimModuleHomFun_of, relTensorColimMap_of]
  refine congrArg Submodule.Quotient.mk ?_
  exact congrFun (congrArg
    (fun H : CDGAModuleHom (tensorModule P (Q i)) (tensorModule P' (colimModule ψ)) => H.toFun n)
    (tensorMapLeft_comp_tensorMapRight φ (Q i) (colimModule ψ) (colimModuleOf ψ i))) z

/-- **Tensoring the colimit over the algebra preserves full quasi-isomorphisms** as soon as every
stage does. -/
theorem relTensorMapLeft_colim_isQuasiIsoFull
    (hstage : ∀ i, (relTensorMapLeft φ (Q i)).IsQuasiIsoFull) :
    (relTensorMapLeft φ (colimModule ψ)).IsQuasiIsoFull := by
  have h1 : (colimModuleHom (relTensorSystem P ψ) (relTensorSystem P' ψ)
      (fun i => relTensorMapLeft φ (Q i))
      (fun i j hij n f => relTensorMapLeft_relTensorMapRight P ψ P' φ hij n f)).IsQuasiIsoFull :=
    colimModuleHom_isQuasiIsoFull _ _ _ _ hstage
  have h2 := CDGAModuleHom.IsQuasiIsoFull.comp (relTensorColimHom_isQuasiIsoFull P' ψ) h1
  rw [← relTensorColimHom_naturality P ψ P' φ] at h2
  exact CDGAModuleHom.IsQuasiIsoFull.of_comp_left h2 (relTensorColimHom_isQuasiIsoFull P ψ)

end Naturality

end GaloisForLFunctions.HTGeometry
