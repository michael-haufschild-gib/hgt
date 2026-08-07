import GaloisForLFunctions.HTGeometry.CDGARelTensorShift
import GaloisForLFunctions.HTGeometry.CDGARelTensorConst

/-!
# The shift comparison descends to the tensor product over the algebra

The relations are stable under the shift comparison, which is exactly the hypothesis of
`Submodule.liftQ`, so the comparison descends: `M ⊗_A N[−k]` maps to the shift of `M ⊗_A N`.

* `HTGeometry.relTensorShiftMap` : the descended comparison.
* `HTGeometry.relTensorRel_shift_of_forall` : and it is injective.
* `HTGeometry.relTensorConstMap` : the constant exchange descends too.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

section ShiftDescent

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (k : ℕ)

/-- The shift comparison composed with the quotient maps, before descent. -/
noncomputable def relTensorShiftPre (n : ℕ) :
    TensorCarrier (R := R) M (ShiftCarrier N k) n →ₗ[R]
      ShiftCarrier (fun m => RelTensorCarrier P Q m) k n where
  toFun z := fun r => Submodule.Quotient.mk
    (tensorShiftMap (R := R) (M := M) (N := N) k n z r)
  map_add' z z' := by
    funext r
    show Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n (z + z') r) = _
    rw [map_add]
    rfl
  map_smul' c z := by
    funext r
    show Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n (c • z) r) = _
    rw [map_smul]
    rfl

theorem relTensorShiftPre_ker (n : ℕ) (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    (hz : z ∈ relTensorRel P (shiftModule Q k) n) :
    relTensorShiftPre P Q k n z = 0 := by
  funext r
  exact (Submodule.Quotient.mk_eq_zero _).2 (relTensorRel_tensorShiftMap P Q k n z hz r)

/-- **The shift comparison descends to the tensor product over the algebra.** -/
noncomputable def relTensorShiftMap (n : ℕ) :
    RelTensorCarrier P (shiftModule Q k) n →ₗ[R]
      ShiftCarrier (fun m => RelTensorCarrier P Q m) k n :=
  Submodule.liftQ _ (relTensorShiftPre P Q k n)
    (fun z hz => relTensorShiftPre_ker P Q k n z hz)

@[simp] theorem relTensorShiftMap_mk (n : ℕ)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n) (r : {a : ℕ // a + k = n}) :
    relTensorShiftMap P Q k n (Submodule.Quotient.mk z) r
      = Submodule.Quotient.mk (tensorShiftMap (R := R) (M := M) (N := N) k n z r) := rfl

/-- **The descended comparison is surjective**, because the comparison and the quotient maps are. -/
theorem relTensorShiftMap_surjective (n : ℕ) :
    Function.Surjective (relTensorShiftMap P Q k n) := by
  intro g
  obtain ⟨z, hz⟩ : ∃ z : TensorCarrier (R := R) M (ShiftCarrier N k) n,
      ∀ r, Submodule.Quotient.mk
        (tensorShiftMap (R := R) (M := M) (N := N) k n z r) = g r := by
    classical
    obtain ⟨y, hy⟩ : ∃ y : ShiftCarrier (TensorCarrier (R := R) M N) k n,
        ∀ r, Submodule.Quotient.mk (y r) = g r := by
      refine ⟨fun r => Quotient.out (g r), fun r => ?_⟩
      exact Quotient.out_eq (g r)
    obtain ⟨z, hz⟩ := tensorShiftMap_surjective (R := R) (M := M) (N := N) k n y
    exact ⟨z, fun r => by rw [hz]; exact hy r⟩
  exact ⟨Submodule.Quotient.mk z, funext hz⟩

/-- The index of a shifted degree is a subsingleton: it is determined by the degree. -/
instance shiftIndexSubsingleton (k n : ℕ) : Subsingleton {a : ℕ // a + k = n} :=
  ⟨fun p q => Subtype.ext (by
    have h1 := p.2
    have h2 := q.2
    omega)⟩

/-- The shift comparison as an equivalence. -/
noncomputable def tensorShiftEquiv (n : ℕ) :
    TensorCarrier (R := R) M (ShiftCarrier N k) n
      ≃ₗ[R] ShiftCarrier (TensorCarrier (R := R) M N) k n :=
  LinearEquiv.ofBijective (tensorShiftMap (R := R) (M := M) (N := N) k n)
    (tensorShiftMap_bijective k n)

@[simp] theorem tensorShiftEquiv_apply (n : ℕ)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n) :
    tensorShiftEquiv (R := R) (M := M) (N := N) k n z
      = tensorShiftMap (R := R) (M := M) (N := N) k n z := rfl

/-- **The descended comparison is injective**: an element whose image is a relation in every
shifted degree was already a relation.  The preimage of a relator is the relator with the cell
argument transported back across the shift. -/
theorem relTensorRel_shift_of_forall (n : ℕ)
    (z : TensorCarrier (R := R) M (ShiftCarrier N k) n)
    (hz : ∀ r : {a : ℕ // a + k = n},
      tensorShiftMap (R := R) (M := M) (N := N) k n z r ∈ relTensorRel P Q r.1) :
    z ∈ relTensorRel P (shiftModule Q k) n := by
  by_cases hk : k ≤ n
  · obtain ⟨j, hj⟩ : ∃ j, j + k = n := ⟨n - k, by omega⟩
    have key : ∀ w : TensorCarrier (R := R) M N j, w ∈ relTensorRel P Q j →
        (tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm
            ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m) k j n hj).symm w)
          ∈ relTensorRel P (shiftModule Q k) n := by
      intro w hw
      refine Submodule.span_induction
        (p := fun w' _ => (tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm
          ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m) k j n hj).symm w')
          ∈ relTensorRel P (shiftModule Q k) n) ?_ ?_ ?_ ?_ hw
      · rintro w' ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, v₀, rfl⟩
        subst hα
        obtain rfl : β = c + b := by omega
        have hpre : (tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm
            ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m) k j n hj).symm
              (relTensorRelator P Q rfl rfl hn hn' x m v₀))
            = relTensorRelator P (shiftModule Q k) (rfl : c + a = c + a)
              (show c + (b + k) = c + b + k by omega)
              (show (c + a, b + k).1 + (c + a, b + k).2 = n by omega)
              (show (a, c + b + k).1 + (a, c + b + k).2 = n by omega) x m
              ((shiftEvalAt (R := R) (M := N) k b (b + k) rfl).symm v₀) := by
          refine (tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm_apply_eq.2 ?_
          refine ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m)
            k j n hj).symm_apply_eq).2 ?_
          show relTensorRelator P Q rfl rfl hn hn' x m v₀
            = tensorShiftMap (R := R) (M := M) (N := N) k n _ ⟨j, hj⟩
          rw [tensorShiftMap_relTensorRelator P Q k
            (show (c + a, b + k).1 + (c + a, b + k).2 = n by omega)
            (show (a, c + b + k).1 + (a, c + b + k).2 = n by omega) x m
            ((shiftEvalAt (R := R) (M := N) k b (b + k) rfl).symm v₀) ⟨j, hj⟩,
            LinearEquiv.apply_symm_apply]
        rw [hpre]
        exact relTensorRelator_mem P (shiftModule Q k) _ _ _ _ x m _
      · rw [map_zero, map_zero]
        exact Submodule.zero_mem _
      · intro w₁ w₂ _ _ h₁ h₂
        rw [map_add, map_add]
        exact Submodule.add_mem _ h₁ h₂
      · intro r w₁ _ h₁
        rw [map_smul, map_smul]
        exact Submodule.smul_mem _ _ h₁
    have hz' : z = (tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm
        ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m) k j n hj).symm
          (tensorShiftMap (R := R) (M := M) (N := N) k n z ⟨j, hj⟩)) := by
      refine ((tensorShiftEquiv (R := R) (M := M) (N := N) k n).symm_apply_eq).2 ?_ |>.symm
      refine ((shiftEvalAt (R := R) (M := fun m => TensorCarrier (R := R) M N m)
        k j n hj).symm_apply_eq).2 ?_
      rfl
    rw [hz']
    exact key _ (hz ⟨j, hj⟩)
  · have hn : n < k := not_le.1 hk
    have hsub : Subsingleton (TensorCarrier (R := R) M (ShiftCarrier N k) n) := by
      refine ⟨fun f g => funext fun p => ?_⟩
      have hp2 : p.1.1 + p.1.2 = n := p.2
      haveI := tensorShift_component_subsingleton (R := R) (M := M) (N := N)
        (b := p.1.2) (show p.1.2 < k by omega) p.1.1
      exact Subsingleton.elim _ _
    rw [show z = 0 from Subsingleton.elim _ _]
    exact Submodule.zero_mem _

/-- **The descended comparison is injective.** -/
theorem relTensorShiftMap_injective (n : ℕ) :
    Function.Injective (relTensorShiftMap P Q k n) := by
  refine fun a b => Quotient.inductionOn₂' a b fun z z' hzz => ?_
  refine (Submodule.Quotient.eq _).2 ?_
  refine relTensorRel_shift_of_forall P Q k n (z - z') fun r => ?_
  have h := congrFun hzz r
  have hmap : tensorShiftMap (R := R) (M := M) (N := N) k n (z - z') r
      = tensorShiftMap (R := R) (M := M) (N := N) k n z r
        - tensorShiftMap (R := R) (M := M) (N := N) k n z' r := by
    rw [map_sub]
    rfl
  rw [hmap]
  exact (Submodule.Quotient.eq _).1 h

theorem relTensorShiftMap_bijective (n : ℕ) :
    Function.Bijective (relTensorShiftMap P Q k n) :=
  ⟨relTensorShiftMap_injective P Q k n, relTensorShiftMap_surjective P Q k n⟩

/-- **Tensoring over the algebra commutes with the degree shift.** -/
noncomputable def relTensorShiftEquiv (n : ℕ) :
    RelTensorCarrier P (shiftModule Q k) n
      ≃ₗ[R] ShiftCarrier (fun m => RelTensorCarrier P Q m) k n :=
  LinearEquiv.ofBijective (relTensorShiftMap P Q k n) (relTensorShiftMap_bijective P Q k n)

end ShiftDescent

section ConstDescent

variable (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
  {V : Type w} [AddCommGroup V] [Module R V]

/-- The constant exchange as a bilinear map into the quotient. -/
noncomputable def relTensorConstBil (n : ℕ) :
    TensorCarrier (R := R) M N n →ₗ[R] V →ₗ[R]
      RelTensorCarrier P (tensorConstModule Q V) n :=
  TensorProduct.curry
    ((relTensorRel P (tensorConstModule Q V) n).mkQ.comp
      (tensorConstExchange (R := R) (M := M) (N := N) V n).toLinearMap)

@[simp] theorem relTensorConstBil_apply (n : ℕ) (x : TensorCarrier (R := R) M N n) (w : V) :
    relTensorConstBil P Q (V := V) n x w
      = Submodule.Quotient.mk
        (tensorConstExchange (R := R) (M := M) (N := N) V n (x ⊗ₜ[R] w)) := rfl

/-- It kills the relations in the first slot. -/
theorem relTensorConstBil_ker (n : ℕ) (x : TensorCarrier (R := R) M N n)
    (hx : x ∈ relTensorRel P Q n) : relTensorConstBil P Q (V := V) n x = 0 := by
  refine LinearMap.ext fun w => ?_
  show Submodule.Quotient.mk
    (tensorConstExchange (R := R) (M := M) (N := N) V n (x ⊗ₜ[R] w)) = 0
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine relTensorRel_tensorConstExchange P Q n (x ⊗ₜ[R] w) ?_
  exact Submodule.subset_span ⟨x, hx, w, rfl⟩

/-- The descended bilinear map. -/
noncomputable def relTensorConstBilQ (n : ℕ) :
    RelTensorCarrier P Q n →ₗ[R] V →ₗ[R] RelTensorCarrier P (tensorConstModule Q V) n :=
  Submodule.liftQ _ (relTensorConstBil P Q (V := V) n)
    (fun x hx => relTensorConstBil_ker P Q n x hx)

/-- **The constant exchange descends to the tensor product over the algebra.** -/
noncomputable def relTensorConstMap (n : ℕ) :
    TensorProduct R (RelTensorCarrier P Q n) V →ₗ[R]
      RelTensorCarrier P (tensorConstModule Q V) n :=
  TensorProduct.lift (relTensorConstBilQ P Q (V := V) n)

@[simp] theorem relTensorConstMap_mk_tmul (n : ℕ) (x : TensorCarrier (R := R) M N n) (w : V) :
    relTensorConstMap P Q (V := V) n (Submodule.Quotient.mk x ⊗ₜ[R] w)
      = Submodule.Quotient.mk
        (tensorConstExchange (R := R) (M := M) (N := N) V n (x ⊗ₜ[R] w)) := rfl

/-- The descended map computes the exchange on the whole tensor product. -/
theorem relTensorConstMap_rTensor (n : ℕ)
    (y : TensorProduct R (TensorCarrier (R := R) M N n) V) :
    relTensorConstMap P Q (V := V) n
        (LinearMap.rTensor V (relTensorRel P Q n).mkQ y)
      = Submodule.Quotient.mk
        (tensorConstExchange (R := R) (M := M) (N := N) V n y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => rfl
  | add y y' hy hy' =>
      rw [map_add, map_add, hy, hy', map_add, Submodule.Quotient.mk_add]

/-- **The descended map is surjective.** -/
theorem relTensorConstMap_surjective (n : ℕ) :
    Function.Surjective (relTensorConstMap P Q (V := V) n) := by
  intro g
  refine Quotient.inductionOn' g fun z => ?_
  refine ⟨LinearMap.rTensor V (relTensorRel P Q n).mkQ
    ((tensorConstExchange (R := R) (M := M) (N := N) V n).symm z), ?_⟩
  rw [relTensorConstMap_rTensor, LinearEquiv.apply_symm_apply]
  rfl

/-- A relator is additive in its cell argument. -/
theorem relTensorRelator_add_cell {c a b n α β : ℕ} (hα : c + a = α) (hβ : c + b = β)
    (hn : (α, b).1 + (α, b).2 = n) (hn' : (a, β).1 + (a, β).2 = n) (x : X c) (m : M a)
    (v v' : N b) :
    relTensorRelator P Q hα hβ hn hn' x m (v + v')
      = relTensorRelator P Q hα hβ hn hn' x m v + relTensorRelator P Q hα hβ hn hn' x m v' := by
  simp only [relTensorRelator]
  rw [TensorProduct.tmul_add, tensorSingle_add, Q.act_add_right, TensorProduct.tmul_add,
    tensorSingle_add, smul_add]
  abel

/-- The inverse of the descended constant exchange, before descent. -/
noncomputable def relTensorConstInvPre (n : ℕ) :
    TensorCarrier (R := R) M (fun m => TensorProduct R (N m) V) n →ₗ[R]
      TensorProduct R (RelTensorCarrier P Q n) V :=
  (LinearMap.rTensor V (relTensorRel P Q n).mkQ).comp
    (tensorConstExchange (R := R) (M := M) (N := N) V n).symm.toLinearMap

theorem relTensorConstInvPre_ker (n : ℕ)
    (z : TensorCarrier (R := R) M (fun m => TensorProduct R (N m) V) n)
    (hz : z ∈ relTensorRel P (tensorConstModule Q V) n) :
    relTensorConstInvPre P Q (V := V) n z = 0 := by
  refine Submodule.span_induction
    (p := fun g _ => relTensorConstInvPre P Q (V := V) n g = 0) ?_ ?_ ?_ ?_ hz
  · rintro g ⟨c, a, b, α, β, hα, hβ, hn, hn', x, m, u, rfl⟩
    induction u using TensorProduct.induction_on with
    | zero =>
        rw [relTensorRelator_zero_cell P (tensorConstModule Q V) hα hβ hn hn' x m, map_zero]
    | tmul v w =>
        rw [← tensorConstExchange_relTensorRelator P Q hα hβ hn hn' x m v w]
        show LinearMap.rTensor V (relTensorRel P Q n).mkQ
          ((tensorConstExchange (R := R) (M := M) (N := N) V n).symm
            ((tensorConstExchange (R := R) (M := M) (N := N) V n)
              (relTensorRelator P Q hα hβ hn hn' x m v ⊗ₜ[R] w))) = 0
        rw [LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul,
          show (relTensorRel P Q n).mkQ (relTensorRelator P Q hα hβ hn hn' x m v) = 0 from
            (Submodule.Quotient.mk_eq_zero _).2
              (relTensorRelator_mem P Q hα hβ hn hn' x m v),
          TensorProduct.zero_tmul]
    | add u u' hu hu' =>
        rw [relTensorRelator_add_cell P (tensorConstModule Q V) hα hβ hn hn' x m u u',
          map_add, hu, hu', add_zero]
  · exact map_zero _
  · intro g g' _ _ hg hg'
    rw [map_add, hg, hg', add_zero]
  · intro r g _ hg
    rw [map_smul, hg, smul_zero]

/-- **The inverse of the descended constant exchange.** -/
noncomputable def relTensorConstInv (n : ℕ) :
    RelTensorCarrier P (tensorConstModule Q V) n →ₗ[R]
      TensorProduct R (RelTensorCarrier P Q n) V :=
  Submodule.liftQ _ (relTensorConstInvPre P Q (V := V) n)
    (fun z hz => relTensorConstInvPre_ker P Q n z hz)

/-- **The descended constant exchange is injective.** -/
theorem relTensorConstMap_injective (n : ℕ) :
    Function.Injective (relTensorConstMap P Q (V := V) n) := by
  have hleft : ∀ y : TensorProduct R (RelTensorCarrier P Q n) V,
      relTensorConstInv P Q (V := V) n (relTensorConstMap P Q (V := V) n y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul u w =>
        refine Quotient.inductionOn' u fun x => ?_
        show relTensorConstInv P Q (V := V) n
          (Submodule.Quotient.mk
            (tensorConstExchange (R := R) (M := M) (N := N) V n (x ⊗ₜ[R] w))) = _
        show LinearMap.rTensor V (relTensorRel P Q n).mkQ
          ((tensorConstExchange (R := R) (M := M) (N := N) V n).symm
            ((tensorConstExchange (R := R) (M := M) (N := N) V n) (x ⊗ₜ[R] w))) = _
        rw [LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul]
        rfl
    | add y y' hy hy' =>
        rw [map_add, map_add, hy, hy']
  exact Function.LeftInverse.injective hleft

theorem relTensorConstMap_bijective (n : ℕ) :
    Function.Bijective (relTensorConstMap P Q (V := V) n) :=
  ⟨relTensorConstMap_injective P Q n, relTensorConstMap_surjective P Q n⟩

/-- **Tensoring over the algebra commutes with a constant coefficient module.** -/
noncomputable def relTensorConstEquiv (n : ℕ) :
    TensorProduct R (RelTensorCarrier P Q n) V
      ≃ₗ[R] RelTensorCarrier P (tensorConstModule Q V) n :=
  LinearEquiv.ofBijective (relTensorConstMap P Q (V := V) n)
    (relTensorConstMap_bijective P Q n)

end ConstDescent

end GaloisForLFunctions.HTGeometry
