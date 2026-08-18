import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Polynomial.Basic
import GaloisForLFunctions.HTGeometry.AlgebraDiscriminantBaseChange

/-!
# Descending a finite free polynomial algebra to a subfield

Let `B` be a free algebra of rank `n` over `K[X]` with basis `e`, and let `E` be a subfield of `K`
containing every coefficient of the structure constants of `e` and of the coordinates of `1`.  Then
the `E[X]`-span of `e` is an `E[X]`-subalgebra `B₀` of `B`, free of rank `n` with the same basis, and

```text
K[X] ⊗[E[X]] B₀  ≅  B          (as K[X]-algebras)
algebraMap E[X] K[X] (discr E[X] e₀) = discr K[X] e
```

so the étale hypothesis descends: a unit discriminant over `K[X]` forces a unit discriminant over
`E[X]`, because an injective map of fields preserves the degree of a polynomial.

This is the descent half of the transfer of the complex simple-connectedness theorem to an arbitrary
algebraically closed field of characteristic zero: the subfield is chosen countable, and the
countable field is then embedded into `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial
open scoped TensorProduct

set_option maxHeartbeats 1600000

variable {E K B : Type*} [Field E] [Field K]
  [Algebra E[X] K[X]] [CommRing B] [Algebra K[X] B] [Algebra E[X] B]
  [IsScalarTower E[X] K[X] B]
  {n : ℕ} (e : Module.Basis (Fin n) K[X] B)

variable (hinj : Function.Injective (algebraMap E[X] K[X]))
  (hmul : ∀ i j k, e.repr (e i * e j) k ∈ Set.range (algebraMap E[X] K[X]))
  (hone : ∀ k, e.repr 1 k ∈ Set.range (algebraMap E[X] K[X]))

include hmul in
theorem descent_span_mul_mem :
    ∀ x ∈ Submodule.span E[X] (Set.range e), ∀ y ∈ Submodule.span E[X] (Set.range e),
      x * y ∈ Submodule.span E[X] (Set.range e) := by
  have hbase : ∀ i j : Fin n, e i * e j ∈ Submodule.span E[X] (Set.range e) := by
    intro i j
    have hsum := e.sum_repr (e i * e j)
    rw [← hsum]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    obtain ⟨q, hq⟩ := hmul i j k
    rw [← hq, IsScalarTower.algebraMap_smul (A := K[X]) (R := E[X]) (M := B)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxm =>
      obtain ⟨i, rfl⟩ := hxm
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hym =>
          obtain ⟨j, rfl⟩ := hym
          exact hbase i j
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [Algebra.mul_smul_comm]; exact Submodule.smul_mem _ _ hu
  | zero => intro y _; simp
  | add u v _ _ hu hv => intro y hy; rw [add_mul]; exact Submodule.add_mem _ (hu y hy) (hv y hy)
  | smul c u _ hu => intro y hy; rw [Algebra.smul_mul_assoc]; exact Submodule.smul_mem _ _ (hu y hy)

include hone in
theorem descent_span_one_mem : (1 : B) ∈ Submodule.span E[X] (Set.range e) := by
  have hsum := e.sum_repr (1 : B)
  rw [← hsum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  obtain ⟨q, hq⟩ := hone k
  rw [← hq, IsScalarTower.algebraMap_smul (A := K[X]) (R := E[X]) (M := B)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The `E[X]`-subalgebra spanned by a basis whose structure constants descend. -/
def descentSubalgebra : Subalgebra E[X] B where
  carrier := (Submodule.span E[X] (Set.range e) : Set B)
  mul_mem' := fun {x y} hx hy => descent_span_mul_mem e hmul x hx y hy
  one_mem' := descent_span_one_mem e hone
  add_mem' := fun {x y} hx hy => Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' := fun q => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (descent_span_one_mem e hone)

/-- The basis vectors of the descended subalgebra. -/
noncomputable def descentVec (i : Fin n) : descentSubalgebra e hmul hone :=
  ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩

theorem descentVec_val (i : Fin n) : ((descentVec e hmul hone i : descentSubalgebra e hmul hone) :
    B) = e i := rfl

include hinj in
theorem descentVec_linearIndependent :
    LinearIndependent E[X] (descentVec e hmul hone) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : ∑ j, (algebraMap E[X] K[X] (g j)) • e j = 0 := by
    have hval := congrArg (Subtype.val) hg
    simpa [descentVec, IsScalarTower.algebraMap_smul (A := K[X]) (R := E[X]) (M := B)] using hval
  have hz := (Fintype.linearIndependent_iff.mp e.linearIndependent) _ hg' i
  exact hinj (by simpa using hz)

theorem descentVec_span :
    ⊤ ≤ Submodule.span E[X] (Set.range (descentVec e hmul hone)) := by
  classical
  intro x _
  have h1 : Submodule.map (Subalgebra.val (descentSubalgebra e hmul hone)).toLinearMap ⊤
      = Submodule.span E[X] (Set.range e) := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have h2 : Submodule.map (Subalgebra.val (descentSubalgebra e hmul hone)).toLinearMap
      (Submodule.span E[X] (Set.range (descentVec e hmul hone)))
      = Submodule.span E[X] (Set.range e) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp [Set.mem_image, Set.mem_range, descentVec]
  have hinj2 : Function.Injective
      (Submodule.map (Subalgebra.val (descentSubalgebra e hmul hone)).toLinearMap) :=
    Submodule.map_injective_of_injective Subtype.val_injective
  have h3 := hinj2 (h1.trans h2.symm)
  rw [← h3]
  trivial

/-- The basis of the descended subalgebra. -/
noncomputable def descentBasis :
    Module.Basis (Fin n) E[X] (descentSubalgebra e hmul hone) :=
  Module.Basis.mk (descentVec_linearIndependent e hinj hmul hone) (descentVec_span e hmul hone)

@[simp] theorem descentBasis_apply (i : Fin n) :
    descentBasis e hinj hmul hone i = descentVec e hmul hone i :=
  Module.Basis.mk_apply _ _ _

/-- The canonical map from the base change of the descended subalgebra. -/
noncomputable def descentBaseChangeHom :
    K[X] ⊗[E[X]] (descentSubalgebra e hmul hone) →ₐ[K[X]] B :=
  AlgHom.liftEquiv E[X] K[X] (descentSubalgebra e hmul hone) B
    (Subalgebra.val (descentSubalgebra e hmul hone))

include hinj in
theorem descentBaseChangeHom_basis (i : Fin n) :
    descentBaseChangeHom e hmul hone
        (((descentBasis e hinj hmul hone).baseChange K[X]) i) = e i := by
  rw [Module.Basis.baseChange_apply]
  show (1 : K[X]) • ((descentBasis e hinj hmul hone i : descentSubalgebra e hmul hone) : B) = e i
  rw [one_smul, descentBasis_apply, descentVec_val]

include hinj in
theorem descentBaseChangeHom_bijective :
    Function.Bijective (descentBaseChangeHom e hmul hone) := by
  classical
  set L := ((descentBasis e hinj hmul hone).baseChange K[X]).equiv e (Equiv.refl (Fin n)) with hLdef
  have heq : (descentBaseChangeHom e hmul hone).toLinearMap = (L : _ →ₗ[K[X]] B) := by
    refine Module.Basis.ext ((descentBasis e hinj hmul hone).baseChange K[X]) (fun i => ?_)
    show descentBaseChangeHom e hmul hone _ = _
    rw [descentBaseChangeHom_basis e hinj hmul hone i, hLdef, LinearEquiv.coe_coe,
      Module.Basis.equiv_apply]
    rfl
  have hb : Function.Bijective ((descentBaseChangeHom e hmul hone).toLinearMap) := by
    rw [heq]; exact L.bijective
  exact hb

/-- The base change of the descended subalgebra is the original algebra. -/
noncomputable def descentBaseChangeEquiv :
    K[X] ⊗[E[X]] (descentSubalgebra e hmul hone) ≃ₐ[K[X]] B :=
  AlgEquiv.ofBijective (descentBaseChangeHom e hmul hone)
    (descentBaseChangeHom_bijective e hinj hmul hone)


theorem isUnit_of_isUnit_map {E' K' : Type*} [Field E'] [Field K'] (φ : E' →+* K') {d : E'[X]}
    (h : IsUnit (d.map φ)) : IsUnit d := by
  rw [Polynomial.isUnit_iff_degree_eq_zero] at h ⊢
  rwa [Polynomial.degree_map_eq_of_injective φ.injective] at h

include hinj in
theorem discr_descentBasis :
    algebraMap E[X] K[X] (Algebra.discr E[X] (descentBasis e hinj hmul hone))
      = Algebra.discr K[X] e := by
  classical
  haveI : Module.Free E[X] (descentSubalgebra e hmul hone) :=
    Module.Free.of_basis (descentBasis e hinj hmul hone)
  haveI : Module.Finite E[X] (descentSubalgebra e hmul hone) :=
    Module.Finite.of_basis (descentBasis e hinj hmul hone)
  rw [← discr_baseChange E[X] K[X] (descentSubalgebra e hmul hone)
    (descentBasis e hinj hmul hone)]
  have hcomp : ⇑(descentBaseChangeEquiv e hinj hmul hone) ∘
      ⇑((descentBasis e hinj hmul hone).baseChange K[X]) = ⇑e := by
    funext i
    exact descentBaseChangeHom_basis e hinj hmul hone i
  rw [Algebra.discr_eq_discr_of_algEquiv ⇑((descentBasis e hinj hmul hone).baseChange K[X])
    (descentBaseChangeEquiv e hinj hmul hone), hcomp]

end GaloisForLFunctions.HTGeometry
