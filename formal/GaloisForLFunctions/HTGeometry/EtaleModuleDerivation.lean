import GaloisForLFunctions.HTGeometry.TraceDualBasisSeparability

/-!
# Derivations of an étale algebra with values in a module

The vanishing of derivations over the base holds for derivations into an arbitrary module, with the
same separability computation:

```text
derivation_module_eq_zero :  Derivation A B M = 0   for every B-module M
derivation_module_ext     :  two R-derivations B → M agreeing on the image of A are equal
```

The module-valued form is what identifies a derivation constructed downstairs with one constructed
upstairs: to compare `∂̄ (1 ⊗ b)` with `1 ⊗ ∂ b` one compares two derivations `B → B̄`, with `B̄`
viewed as a `B`-module, and their difference is an `A`-derivation, hence zero.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [Module.Free A B] [Module.Finite A B]
  {n : ℕ} (e : Module.Basis (Fin n) A B) (hd : IsUnit (Algebra.discr A e))

include hd in
theorem sum_swap_traceDual_module (β : B → B → M)
    (h1 : ∀ (a : A) (u v : B), β (a • u) v = a • β u v)
    (h3 : ∀ (a : A) (u v : B), β u (a • v) = a • β u v)
    (hadd1 : ∀ (u u' v : B), β (u + u') v = β u v + β u' v)
    (hadd2 : ∀ (u v v' : B), β u (v + v') = β u v + β u v')
    (hz1 : ∀ v : B, β 0 v = 0) (hz2 : ∀ u : B, β u 0 = 0)
    (b : B) :
    ∑ i, β (b * e i) (traceDual e i) = ∑ i, β (e i) (b * traceDual e i) := by
  classical
  have hsum1 : ∀ (c : Fin n → A) (v : B),
      β (∑ j, c j • e j) v = ∑ j, c j • β (e j) v := by
    intro c v
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp [hz1]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd1, h1, ih]
  have hsum2 : ∀ (c : Fin n → A) (u : B),
      β u (∑ j, c j • traceDual e j) = ∑ j, c j • β u (traceDual e j) := by
    intro c u
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp [hz2]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj, hadd2, h3, ih]
  have hL : ∀ i : Fin n, β (b * e i) (traceDual e i)
      = ∑ j, (e.repr (b * e i) j) • β (e j) (traceDual e i) := by
    intro i
    set c : Fin n → A := fun j => e.repr (b * e i) j with hc
    have hbe : b * e i = ∑ j, c j • e j := (e.sum_repr (b * e i)).symm
    rw [hbe, hsum1]
    exact Finset.sum_congr rfl (fun j _ => by rw [repr_sum_apply])
  have hR : ∀ i : Fin n, β (e i) (b * traceDual e i)
      = ∑ j, (e.repr (b * e j) i) • β (e i) (traceDual e j) := by
    intro i
    rw [mul_traceDual e hd b i, hsum2]
  rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_congr rfl (fun i _ => hR i),
    Finset.sum_comm]

include hd in
/-- **A finite free algebra with unit discriminant has no nonzero derivations over the base, with
values in any module.** -/
theorem derivation_module_eq_zero (D : Derivation A B M) : D = 0 := by
  ext b
  have hswap := sum_swap_traceDual_module e hd (fun u v => v • D u)
    (fun a u v => by rw [Derivation.map_smul, smul_comm])
    (fun a u v => by rw [smul_assoc])
    (fun u u' v => by rw [map_add, smul_add])
    (fun u v v' => by rw [add_smul])
    (fun v => by rw [map_zero, smul_zero])
    (fun u => by rw [zero_smul]) b
  have hL : ∑ i, traceDual e i • D (b * e i)
      = b • (∑ i, traceDual e i • D (e i)) + (∑ i, e i * traceDual e i) • D b := by
    rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [D.leibniz, smul_add]
    congr 1
    · rw [smul_comm]
    · rw [smul_smul, mul_comm]
  have hR : ∑ i, (traceDual e i) • D (e i) = ∑ i, (traceDual e i) • D (e i) := rfl
  have hR2 : ∑ i, (b * traceDual e i) • D (e i) = b • ∑ i, (traceDual e i) • D (e i) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_smul]
  rw [hL, hR2, sum_mul_traceDual e hd, one_smul] at hswap
  have hzero : b • (∑ i, traceDual e i • D (e i)) + D b
      = b • (∑ i, traceDual e i • D (e i)) + 0 := by
    rw [add_zero]; exact hswap
  have : D b = 0 := add_left_cancel hzero
  simpa using this


section Ext

variable {R : Type*} [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
  [Module R M] [IsScalarTower R B M]

include hd in
/-- **Two derivations into a module agreeing on the base agree.** -/
theorem derivation_module_ext (D₁ D₂ : Derivation R B M)
    (h : ∀ a : A, D₁ (algebraMap A B a) = D₂ (algebraMap A B a)) : D₁ = D₂ := by
  set D : Derivation R B M := D₁ - D₂ with hD
  have hzero : ∀ a : A, D (algebraMap A B a) = 0 := by
    intro a
    rw [hD]
    show D₁ (algebraMap A B a) - D₂ (algebraMap A B a) = 0
    rw [h a, sub_self]
  have hDA : ∀ (a : A) (b : B), D (a • b) = a • D b := by
    intro a b
    have hsm : (a • b : B) = algebraMap A B a * b := Algebra.smul_def a b
    rw [hsm, D.leibniz, hzero a, smul_zero, add_zero, ← IsScalarTower.algebraMap_smul B a (D b)]
  let D' : Derivation A B M :=
    { toFun := fun b => D b
      map_add' := fun x y => map_add D x y
      map_smul' := fun a b => hDA a b
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := fun x y => D.leibniz x y }
  have hD'0 : D' = 0 := derivation_module_eq_zero e hd D'
  ext b
  have hall : D b = 0 := by
    have := congrArg (fun (F : Derivation A B M) => F b) hD'0
    simpa [D'] using this
  rw [hD] at hall
  show D₁ b = D₂ b
  have h2 : D₁ b - D₂ b = 0 := hall
  rw [sub_eq_zero] at h2
  exact h2

end Ext

end GaloisForLFunctions.HTGeometry
