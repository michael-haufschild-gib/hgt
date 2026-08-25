import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtensionSimple
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2
import Mathlib.Algebra.Module.Bimodule
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open MulOpposite

noncomputable section

universe u

/-- Any two simple modules over an Artinian simple ring are linearly equivalent. -/
theorem simpleModules_linearEquiv_of_isSimpleRing_isArtinianRing
    (R M N : Type*) [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [IsSimpleRing R] [IsArtinianRing R]
    [IsSimpleModule R M] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  obtain ⟨J, ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  letI : IsSimpleModule R I := IsSimpleModule.congr eM.symm
  letI : IsSimpleModule R J := IsSimpleModule.congr eN.symm
  exact ⟨eM.trans (((IsSimpleRing.isIsotypic R R) J I).some.trans eN.symm)⟩

/-- A separate carrier for the automorphism-twisted bimodule. -/
structure EmbeddedFieldTwist (D : Type u) where
  down : D

def embeddedFieldTwistEquiv (D : Type u) : EmbeddedFieldTwist D ≃ D where
  toFun := EmbeddedFieldTwist.down
  invFun := EmbeddedFieldTwist.mk
  left_inv _ := rfl
  right_inv _ := rfl

theorem EmbeddedFieldTwist.down_injective (D : Type u) :
    Function.Injective (EmbeddedFieldTwist.down : EmbeddedFieldTwist D → D) :=
  (embeddedFieldTwistEquiv D).injective

instance embeddedFieldTwistNontrivial
    (D : Type u) [Nontrivial D] : Nontrivial (EmbeddedFieldTwist D) :=
  (embeddedFieldTwistEquiv D).nontrivial

noncomputable instance embeddedFieldTwistAddCommGroup
    (D : Type u) [AddCommGroup D] : AddCommGroup (EmbeddedFieldTwist D) :=
  (embeddedFieldTwistEquiv D).addCommGroup

noncomputable instance embeddedFieldTwistModule
    (D : Type u) [DivisionRing D] : Module D (EmbeddedFieldTwist D) :=
  (embeddedFieldTwistEquiv D).module D

@[simp] theorem EmbeddedFieldTwist.down_zero
    (D : Type u) [AddCommGroup D] :
    EmbeddedFieldTwist.down (0 : EmbeddedFieldTwist D) = 0 := rfl

@[simp] theorem EmbeddedFieldTwist.down_smul
    (D : Type u) [DivisionRing D] (d : D) (x : EmbeddedFieldTwist D) :
    (d • x).down = d * x.down := rfl

noncomputable instance embeddedFieldTwistMopModule
    (D : Type u) [DivisionRing D] : Module Dᵐᵒᵖ (EmbeddedFieldTwist D) :=
  (embeddedFieldTwistEquiv D).module Dᵐᵒᵖ

@[reducible] noncomputable def embeddedFieldTwistBaseModule
    (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] :
    Module K (EmbeddedFieldTwist D) :=
  (embeddedFieldTwistEquiv D).module K

theorem embeddedFieldTwistBaseIsScalarTower
    (K D : Type u) [Field K] [DivisionRing D] [Algebra K D] :
    letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
    IsScalarTower K D (EmbeddedFieldTwist D) := by
  letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
  refine ⟨?_⟩
  intro k d x
  apply EmbeddedFieldTwist.down_injective D
  change (k • d) * x.down = k • (d * x.down)
  exact smul_mul_assoc k d x.down

variable (K L D : Type u) [Field K] [Field L] [DivisionRing D]
  [Algebra K L] [Algebra K D] [Module.Finite K D]
variable (iota : L →ₐ[K] D)

/-- Inclusion of the opposite embedded field into the opposite division algebra. -/
def embeddedFieldMopRingHom : Lᵐᵒᵖ →+* Dᵐᵒᵖ :=
  iota.toRingHom.op

/-- Right multiplication by the embedded field. -/
@[reducible] def embeddedFieldMopModule : Module Lᵐᵒᵖ D :=
  Module.compHom D (embeddedFieldMopRingHom K L D iota)

@[simp] theorem embeddedFieldMop_smul (x : Lᵐᵒᵖ) (d : D) :
    letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
    x • d = d * iota x.unop := rfl

theorem embeddedFieldMopIsScalarTower :
    letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
    IsScalarTower K Lᵐᵒᵖ D := by
  letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
  refine ⟨?_⟩
  intro k x d
  change d * iota (k • x.unop) = k • (d * iota x.unop)
  rw [map_smul, Algebra.smul_def, Algebra.smul_def]
  rw [← mul_assoc, (Algebra.commutes k d).symm, mul_assoc]

theorem embeddedFieldMopSMulCommClass :
    letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
    SMulCommClass D Lᵐᵒᵖ D := by
  letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
  refine ⟨?_⟩
  intro a x d
  change a * (d * iota x.unop) = (a * d) * iota x.unop
  rw [mul_assoc]

/-- The division algebra is simple under the left-`D`, right-`L` enveloping action. -/
theorem embeddedFieldRelative_isSimpleModule :
    letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
    letI : IsScalarTower K Lᵐᵒᵖ D := embeddedFieldMopIsScalarTower K L D iota
    letI : SMulCommClass D Lᵐᵒᵖ D := embeddedFieldMopSMulCommClass K L D iota
    letI : Module (D ⊗[K] Lᵐᵒᵖ) D := TensorProduct.Algebra.module
    IsSimpleModule (D ⊗[K] Lᵐᵒᵖ) D := by
  letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
  letI : IsScalarTower K Lᵐᵒᵖ D := embeddedFieldMopIsScalarTower K L D iota
  letI : SMulCommClass D Lᵐᵒᵖ D := embeddedFieldMopSMulCommClass K L D iota
  letI : Module (D ⊗[K] Lᵐᵒᵖ) D := TensorProduct.Algebra.module
  rw [isSimpleModule_iff]
  apply IsSimpleOrder.of_forall_eq_top
  intro P hP
  obtain ⟨y, hyP, hy⟩ : ∃ y : D, y ∈ P ∧ y ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt
      (bot_lt_iff_ne_bot.mpr hP : ⊥ < P)
    exact ⟨y, hy, by simpa using hy0⟩
  apply top_unique
  intro x hx
  have hmem := P.smul_mem
    ((x * y⁻¹) ⊗ₜ[K] MulOpposite.op (1 : L)) hyP
  simpa [TensorProduct.Algebra.smul_def, hy] using hmem

/-- Right multiplication twisted by a `K`-automorphism of the embedded field. -/
def twistedEmbeddedFieldMopRingHom (sigma : L ≃ₐ[K] L) : Lᵐᵒᵖ →+* Dᵐᵒᵖ :=
  (embeddedFieldMopRingHom K L D iota).comp (AlgEquiv.op sigma).toRingHom

@[reducible] def twistedEmbeddedFieldMopModule (sigma : L ≃ₐ[K] L) :
    Module Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
  Module.compHom (EmbeddedFieldTwist D) (twistedEmbeddedFieldMopRingHom K L D iota sigma)

@[simp] theorem twistedEmbeddedFieldMop_smul_down (sigma : L ≃ₐ[K] L)
    (x : Lᵐᵒᵖ) (d : EmbeddedFieldTwist D) :
    letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
      twistedEmbeddedFieldMopModule K L D iota sigma
    (x • d).down = d.down * iota (sigma x.unop) := rfl

theorem twistedEmbeddedFieldMopIsScalarTower (sigma : L ≃ₐ[K] L) :
    letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
    letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
    IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) := by
  letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
  letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
  refine ⟨?_⟩
  intro k x d
  apply EmbeddedFieldTwist.down_injective
  change d.down * iota (sigma (k • x.unop)) =
    k • (d.down * iota (sigma x.unop))
  rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
  rw [← mul_assoc, (Algebra.commutes k d.down).symm, mul_assoc]

theorem twistedEmbeddedFieldMopSMulCommClass (sigma : L ≃ₐ[K] L) :
    letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
    SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) := by
  letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
  refine ⟨?_⟩
  intro a x d
  apply EmbeddedFieldTwist.down_injective
  change a * (d.down * iota (sigma x.unop)) =
    (a * d.down) * iota (sigma x.unop)
  rw [mul_assoc]

theorem twistedEmbeddedFieldRelative_isSimpleModule (sigma : L ≃ₐ[K] L) :
    letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
    letI : IsScalarTower K D (EmbeddedFieldTwist D) :=
      embeddedFieldTwistBaseIsScalarTower K D
    letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
    letI : IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
      twistedEmbeddedFieldMopIsScalarTower K L D iota sigma
    letI : SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
      twistedEmbeddedFieldMopSMulCommClass K L D iota sigma
    letI : Module (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := TensorProduct.Algebra.module
    IsSimpleModule (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := by
  letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
  letI : IsScalarTower K D (EmbeddedFieldTwist D) :=
    embeddedFieldTwistBaseIsScalarTower K D
  letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
  letI : IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopIsScalarTower K L D iota sigma
  letI : SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopSMulCommClass K L D iota sigma
  letI : Module (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := TensorProduct.Algebra.module
  rw [isSimpleModule_iff]
  apply IsSimpleOrder.of_forall_eq_top
  intro P hP
  obtain ⟨y, hyP, hy⟩ : ∃ y : EmbeddedFieldTwist D, y ∈ P ∧ y ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := SetLike.exists_of_lt
      (bot_lt_iff_ne_bot.mpr hP : ⊥ < P)
    exact ⟨y, hy, by simpa using hy0⟩
  apply top_unique
  intro x hx
  have hyDown : y.down ≠ 0 := by
    intro h
    apply hy
    apply EmbeddedFieldTwist.down_injective
    simpa using h
  have hmem := P.smul_mem
    ((x.down * y.down⁻¹) ⊗ₜ[K] MulOpposite.op (1 : L)) hyP
  have heq :
      ((x.down * y.down⁻¹) ⊗ₜ[K] MulOpposite.op (1 : L)) • y = x := by
    apply EmbeddedFieldTwist.down_injective
    simpa [TensorProduct.Algebra.smul_def, hyDown]
  exact heq ▸ hmem

/-- The relative enveloping ring is simple: it is the scalar extension of the central
division algebra to the opposite embedded field. -/
theorem embeddedFieldRelative_isSimpleRing [Algebra.IsCentral K D] :
    IsSimpleRing (D ⊗[K] Lᵐᵒᵖ) := by
  let A : CSA.{u, u} K :=
    { carrier := D
      isCentral := inferInstance
      isSimple := inferInstance
      fin_dim := inferInstance }
  letI : IsAzumaya K D := csa_isAzumaya A
  exact IsSimpleRing.of_ringEquiv
    (Algebra.TensorProduct.comm K D Lᵐᵒᵖ).symm.toRingEquiv
    (isSimpleRing_scalarExtension (K := K) (L := Lᵐᵒᵖ) (A := D))

/-- The ordinary and automorphism-twisted relative bimodules are equivalent. This is the
module-theoretic core of Skolem–Noether for an embedded field. -/
noncomputable def embeddedFieldTwistedLinearEquiv [Algebra.IsCentral K D]
    (sigma : L ≃ₐ[K] L) :
    letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
    letI : IsScalarTower K Lᵐᵒᵖ D := embeddedFieldMopIsScalarTower K L D iota
    letI : SMulCommClass D Lᵐᵒᵖ D := embeddedFieldMopSMulCommClass K L D iota
    letI : Module (D ⊗[K] Lᵐᵒᵖ) D := TensorProduct.Algebra.module
    letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
    letI : IsScalarTower K D (EmbeddedFieldTwist D) :=
      embeddedFieldTwistBaseIsScalarTower K D
    letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
    letI : IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
      twistedEmbeddedFieldMopIsScalarTower K L D iota sigma
    letI : SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
      twistedEmbeddedFieldMopSMulCommClass K L D iota sigma
    letI : Module (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := TensorProduct.Algebra.module
    D ≃ₗ[D ⊗[K] Lᵐᵒᵖ] EmbeddedFieldTwist D := by
  letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
  letI : IsScalarTower K Lᵐᵒᵖ D := embeddedFieldMopIsScalarTower K L D iota
  letI : SMulCommClass D Lᵐᵒᵖ D := embeddedFieldMopSMulCommClass K L D iota
  letI : Module (D ⊗[K] Lᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
  letI : IsScalarTower K D (EmbeddedFieldTwist D) :=
    embeddedFieldTwistBaseIsScalarTower K D
  letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
  letI : IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopIsScalarTower K L D iota sigma
  letI : SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopSMulCommClass K L D iota sigma
  letI : Module (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := TensorProduct.Algebra.module
  letI : Module.Finite K L :=
    Module.Finite.of_injective iota.toLinearMap iota.injective
  letI : IsSimpleRing (D ⊗[K] Lᵐᵒᵖ) :=
    embeddedFieldRelative_isSimpleRing K L D
  letI : IsArtinianRing (D ⊗[K] Lᵐᵒᵖ) :=
    IsArtinianRing.of_finite K (D ⊗[K] Lᵐᵒᵖ)
  letI : IsSimpleModule (D ⊗[K] Lᵐᵒᵖ) D :=
    embeddedFieldRelative_isSimpleModule K L D iota
  letI : IsSimpleModule (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldRelative_isSimpleModule K L D iota sigma
  exact (simpleModules_linearEquiv_of_isSimpleRing_isArtinianRing
    (D ⊗[K] Lᵐᵒᵖ) D (EmbeddedFieldTwist D)).some

/-- **Skolem–Noether for an embedded field.** Every base-field automorphism of the embedded
field is implemented inside the finite-dimensional central division algebra by a unit. -/
theorem exists_unit_intertwining_embeddedField [Algebra.IsCentral K D]
    (sigma : L ≃ₐ[K] L) :
    ∃ u : Dˣ, ∀ x : L, iota x * (u : D) = (u : D) * iota (sigma x) := by
  letI : Module Lᵐᵒᵖ D := embeddedFieldMopModule K L D iota
  letI : IsScalarTower K Lᵐᵒᵖ D := embeddedFieldMopIsScalarTower K L D iota
  letI : SMulCommClass D Lᵐᵒᵖ D := embeddedFieldMopSMulCommClass K L D iota
  letI : Module (D ⊗[K] Lᵐᵒᵖ) D := TensorProduct.Algebra.module
  letI : Module K (EmbeddedFieldTwist D) := embeddedFieldTwistBaseModule K D
  letI : IsScalarTower K D (EmbeddedFieldTwist D) :=
    embeddedFieldTwistBaseIsScalarTower K D
  letI : Module Lᵐᵒᵖ (EmbeddedFieldTwist D) := twistedEmbeddedFieldMopModule K L D iota sigma
  letI : IsScalarTower K Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopIsScalarTower K L D iota sigma
  letI : SMulCommClass D Lᵐᵒᵖ (EmbeddedFieldTwist D) :=
    twistedEmbeddedFieldMopSMulCommClass K L D iota sigma
  letI : Module (D ⊗[K] Lᵐᵒᵖ) (EmbeddedFieldTwist D) := TensorProduct.Algebra.module
  let e := embeddedFieldTwistedLinearEquiv K L D iota sigma
  let d : D := (e 1).down
  have hd : d ≠ 0 := by
    intro h
    have he1 : e 1 = 0 := by
      apply EmbeddedFieldTwist.down_injective
      change d = 0
      exact h
    have : (1 : D) = 0 := e.injective (by simpa using he1)
    exact one_ne_zero this
  refine ⟨Units.mk0 d hd, ?_⟩
  intro x
  have hleft := e.map_smul
    ((iota x) ⊗ₜ[K] MulOpposite.op (1 : L)) (1 : D)
  have hright := e.map_smul
    ((1 : D) ⊗ₜ[K] MulOpposite.op x) (1 : D)
  calc
    iota x * d = (e (iota x)).down := by
      simpa [TensorProduct.Algebra.smul_def, d] using
        congrArg EmbeddedFieldTwist.down hleft.symm
    _ = d * iota (sigma x) := by
      simpa [TensorProduct.Algebra.smul_def, d] using
        congrArg EmbeddedFieldTwist.down hright

/-- A single Skolem–Noether unit intertwines every power of the automorphism. -/
theorem exists_unit_intertwining_embeddedField_powers [Algebra.IsCentral K D]
    (sigma : L ≃ₐ[K] L) :
    ∃ u : Dˣ, ∀ (n : ℕ) (x : L),
      iota x * (u : D) ^ n = (u : D) ^ n * iota ((sigma ^ n) x) := by
  obtain ⟨u, hu⟩ := exists_unit_intertwining_embeddedField K L D iota sigma
  refine ⟨u, ?_⟩
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        iota x * (u : D) ^ (n + 1) =
            (iota x * (u : D) ^ n) * (u : D) := by rw [pow_succ, mul_assoc]
        _ = ((u : D) ^ n * iota ((sigma ^ n) x)) * (u : D) := by rw [ih]
        _ = (u : D) ^ n * (iota ((sigma ^ n) x) * (u : D)) := by rw [mul_assoc]
        _ = (u : D) ^ n * ((u : D) * iota (sigma ((sigma ^ n) x))) := by
          rw [hu]
        _ = (u : D) ^ (n + 1) * iota ((sigma ^ (n + 1)) x) := by
          have hs : (sigma ^ (n + 1)) x = sigma ((sigma ^ n) x) := by
            rw [pow_succ']
            rfl
          rw [hs, pow_succ, ← mul_assoc]

/-- Universe-polymorphic chosen generator for a cyclic Galois group. -/
noncomputable def cyclicGaloisGeneratorAnyUniverse
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)] : Gal(L/K) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose

theorem cyclicGaloisGeneratorAnyUniverse_spec
    (K L : Type u) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)] :
    ∀ sigma : Gal(L/K), sigma ∈ Subgroup.zpowers (cyclicGaloisGeneratorAnyUniverse K L) :=
  (IsCyclic.exists_generator (α := Gal(L/K))).choose_spec

theorem cyclicGaloisGeneratorAnyUniverse_pow_finrank
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] :
    cyclicGaloisGeneratorAnyUniverse K L ^ Module.finrank K L = 1 := by
  have horder : orderOf (cyclicGaloisGeneratorAnyUniverse K L) = Module.finrank K L := by
    calc
      orderOf (cyclicGaloisGeneratorAnyUniverse K L) = Nat.card Gal(L/K) :=
        orderOf_eq_card_of_forall_mem_zpowers
          (cyclicGaloisGeneratorAnyUniverse_spec K L)
      _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [← horder]
  exact pow_orderOf_eq_one _

/-- For a finite cyclic Galois embedded field, a normalizing unit has degree-th power in the
centralizer of the field. This is the parameter-producing step in the crossed-product theorem. -/
theorem exists_cyclicGaloisNormalizer_power_mem_centralizer
    [Algebra.IsCentral K D] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] :
    ∃ u : Dˣ,
      (∀ x : L, iota x * (u : D) =
        (u : D) * iota (cyclicGaloisGeneratorAnyUniverse K L x)) ∧
      (∀ x : L, Commute (iota x) ((u : D) ^ Module.finrank K L)) := by
  obtain ⟨u, hu⟩ := exists_unit_intertwining_embeddedField_powers K L D iota
    (cyclicGaloisGeneratorAnyUniverse K L)
  refine ⟨u, ?_, ?_⟩
  · intro x
    simpa using hu 1 x
  · intro x
    have h := hu (Module.finrank K L) x
    rw [cyclicGaloisGeneratorAnyUniverse_pow_finrank K L] at h
    exact h

end


end GaloisForLFunctions.HTGeometry.ABHN
