import Mathlib
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.DerivedPullback

/-!
# Internal support preservation

Every construction performed *after* passage to the incompatibility modules inherits their
annihilator, hence cannot move or enlarge their support.  The closure properties of the class of
modules killed by a fixed scalar are collected first:

* `smul_eq_zero_sub`, `smul_eq_zero_quotient`, `smul_eq_zero_prod`, `smul_eq_zero_pi` — sub-,
  quotient-, and (co)product-stability;
* `smul_eq_zero_tensor_left`, `smul_eq_zero_tensor_right` — tensor stability on either side;
* `smul_eq_zero_hom_source`, `smul_eq_zero_hom_target` — `Hom` stability on either side;
* `smul_eq_zero_quotRange` — the cokernel of multiplication by the scalar is killed by it, and
  `smul_eq_zero_kerSmul` for the kernel.

Support is then read off by localisation:

* `subsingleton_localizedModule` — a module killed by `t` localises to zero wherever `t` is
  inverted, so nothing built from the incompatibility modules has support off the identity wall.

Finally the endomorphism ring of the source orientation line is the identity fibre itself:

* `endQuotEquiv` — `End_R(R ⧸ I) ≅ R ⧸ I`.
-/

namespace GaloisForLFunctions.HTGeometry.DerivedSelection

open TensorProduct

universe u v w

section Closure

variable {R : Type u} [CommRing R] {t : R} {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]

theorem smul_eq_zero_sub (hM : ∀ m : M, t • m = 0) (p : Submodule R M) (x : p) : t • x = 0 :=
  Subtype.ext (hM (x : M))

theorem smul_eq_zero_quotient (hM : ∀ m : M, t • m = 0) (p : Submodule R M) (x : M ⧸ p) :
    t • x = 0 := by
  obtain ⟨y, rfl⟩ := p.mkQ_surjective x
  rw [← map_smul, hM y, map_zero]

theorem smul_eq_zero_prod (hM : ∀ m : M, t • m = 0) (hN : ∀ n : N, t • n = 0) (x : M × N) :
    t • x = 0 :=
  Prod.ext (hM x.1) (hN x.2)

theorem smul_eq_zero_pi {ι : Type*} {P : ι → Type v} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (hP : ∀ i, ∀ m : P i, t • m = 0) (x : ∀ i, P i) : t • x = 0 :=
  funext fun i => hP i (x i)

theorem smul_eq_zero_tensor_right (hN : ∀ n : N, t • n = 0) (z : M ⊗[R] N) : t • z = 0 := by
  induction z with
  | zero => simp
  | tmul m n =>
      have h : t • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (t • n) := by rw [tmul_smul]
      rw [h, hN n, tmul_zero]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

theorem smul_eq_zero_tensor_left (hM : ∀ m : M, t • m = 0) (z : M ⊗[R] N) : t • z = 0 := by
  induction z with
  | zero => simp
  | tmul m n =>
      have h : t • (m ⊗ₜ[R] n) = (t • m) ⊗ₜ[R] n := by rw [smul_tmul']
      rw [h, hM m, zero_tmul]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

theorem smul_eq_zero_hom_source (hM : ∀ m : M, t • m = 0) (f : M →ₗ[R] N) :
    t • f = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.smul_apply, ← f.map_smul, hM x, map_zero, LinearMap.zero_apply]

theorem smul_eq_zero_hom_target (hN : ∀ n : N, t • n = 0) (f : M →ₗ[R] N) :
    t • f = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.smul_apply, hN (f x), LinearMap.zero_apply]

theorem smul_eq_zero_quotRange (x : M ⧸ LinearMap.range (t • LinearMap.id : M →ₗ[R] M)) :
    t • x = 0 := by
  obtain ⟨y, rfl⟩ := (LinearMap.range (t • LinearMap.id : M →ₗ[R] M)).mkQ_surjective x
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨y, rfl⟩

theorem smul_eq_zero_kerSmul (x : ↥(LinearMap.ker (t • LinearMap.id : M →ₗ[R] M))) :
    t • x = 0 := by
  refine Subtype.ext ?_
  show t • (x : M) = 0
  exact LinearMap.mem_ker.1 x.2

end Closure

section Localization

variable {R : Type u} [CommRing R] {t : R} {M : Type u} [AddCommGroup M] [Module R M]

/-- **Support preservation.**  A module killed by `t` localises to zero as soon as `t` is
inverted. -/
theorem subsingleton_localizedModule (S : Submonoid R) (hS : t ∈ S)
    (hM : ∀ m : M, t • m = 0) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun x y => ?_⟩
  induction x using LocalizedModule.induction_on with
  | h m s =>
      induction y using LocalizedModule.induction_on with
      | h m' s' =>
          rw [LocalizedModule.mk_eq]
          refine ⟨⟨t, hS⟩, ?_⟩
          have h1 : (⟨t, hS⟩ : S) • m = 0 := hM m
          have h2 : (⟨t, hS⟩ : S) • m' = 0 := hM m'
          rw [smul_comm, h1, smul_zero, smul_comm, h2, smul_zero]

/-- Away from the identity wall the incompatibility modules vanish. -/
theorem subsingleton_localizedModule_atPrime (p : Ideal R) [p.IsPrime] (hp : t ∉ p)
    (hM : ∀ m : M, t • m = 0) : Subsingleton (LocalizedModule p.primeCompl M) :=
  subsingleton_localizedModule p.primeCompl hp hM

end Localization

section EndQuot

variable {R : Type u} [CommRing R] (I : Ideal R)

theorem end_apply_eq_mul (f : Module.End R (R ⧸ I)) (x : R ⧸ I) : f x = x * f 1 := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hy : (Ideal.Quotient.mk I y) = y • (1 : R ⧸ I) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [hy, map_smul]
  simp [Algebra.smul_def]

/-- **Theorem 8A.2 (8A.4).**  The endomorphism ring of the source orientation line is the identity
fibre itself. -/
noncomputable def endQuotEquiv : Module.End R (R ⧸ I) ≃+* (R ⧸ I) where
  toFun f := f 1
  invFun a :=
    { toFun := fun x => a * x
      map_add' := fun x y => by ring
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, Algebra.smul_def]
        ring }
  left_inv f := by
    refine LinearMap.ext fun x => ?_
    show f 1 * x = f x
    rw [end_apply_eq_mul I f x, mul_comm]
  right_inv a := by
    show a * 1 = a
    rw [mul_one]
  map_mul' f g := by
    show (f * g) 1 = f 1 * g 1
    rw [Module.End.mul_apply, end_apply_eq_mul I f (g 1), mul_comm]
  map_add' f g := rfl

@[simp] theorem endQuotEquiv_apply (f : Module.End R (R ⧸ I)) : endQuotEquiv I f = f 1 := rfl

end EndQuot

end GaloisForLFunctions.HTGeometry.DerivedSelection
