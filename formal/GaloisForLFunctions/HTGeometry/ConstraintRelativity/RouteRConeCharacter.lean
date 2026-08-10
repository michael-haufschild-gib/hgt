import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.RelativeConeExactness

/-!
# The Route-R source complex and its relative cone character

The Route-R source datum is an algebra with a prime automorphism, an augmentation and a bilateral
Stokes regulator.  It presents a three-term cochain complex `A → A ⊕ ℂ → ℂ`, the regulator descends
to its degree-one cohomology, and the retained class `η = (0,1)` has regulator value one.  Any
comparison into a resolved complex therefore carries a relative cone character whose value on the
retained class is the physical coefficient.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## Complexes concentrated in three degrees -/

section Piece

variable {k : Type*} [Field k]

/-- Three modules placed in degrees `0`, `1`, `2`, with zero elsewhere. -/
def pieceCat (M₀ M₁ M₂ : ModuleCat.{0} k) : ℤ → ModuleCat.{0} k
  | 0 => M₀
  | 1 => M₁
  | 2 => M₂
  | _ => ModuleCat.of k PUnit

variable {M₀ M₁ M₂ : ModuleCat.{0} k}

/-- The three-term complex `M₀ → M₁ → M₂`, extended by zero. -/
noncomputable def truncComplex (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) :
    ZCochain k (fun n => (pieceCat M₀ M₁ M₂ n : Type)) where
  d
    | 0 => d₀
    | 1 => d₁
    | 2 => 0
    | Int.ofNat (_ + 3) => 0
    | Int.negSucc _ => 0
  d_squared n x := by
    match n with
    | 0 => exact h x
    | 1 => rfl
    | 2 => rfl
    | Int.ofNat (_ + 3) => rfl
    | Int.negSucc 0 =>
      show d₀ ((0 : (pieceCat M₀ M₁ M₂ (Int.negSucc 0) : Type) →ₗ[k] (M₀ : Type)) x) = 0
      rw [LinearMap.zero_apply, map_zero]
    | Int.negSucc (_ + 1) => rfl

@[simp] theorem truncComplex_d_zero (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) : (truncComplex d₀ d₁ h).d 0 = d₀ := rfl

@[simp] theorem truncComplex_d_one (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) : (truncComplex d₀ d₁ h).d 1 = d₁ := rfl

end Piece
/-! ## The Route-R source datum -/

section RouteR

/-- A Route-R source datum: a prime transport `α`, an augmentation `ε` killed by the transport
defect, and a bilateral Stokes regulator `reg` that computes the augmentation on that defect. -/
structure RouteRSource (A : Type) [AddCommGroup A] [Module ℂ A] where
  /-- The prime transport. -/
  α : A →ₗ[ℂ] A
  /-- The augmentation. -/
  ε : A →ₗ[ℂ] ℂ
  /-- The bilateral Stokes regulator. -/
  reg : A →ₗ[ℂ] ℂ
  /-- The augmentation is transport invariant. -/
  eps_alpha : ∀ x, ε (α x) = ε x
  /-- The regulator computes the augmentation on the transport defect. -/
  reg_comm : ∀ x, reg (α x - x) = ε x

namespace RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)

/-- **Card `(RRC.6)`.**  The degree-zero differential `x ↦ (α x − x, ε x)`. -/
noncomputable def D₀ : A →ₗ[ℂ] (A × ℂ) := LinearMap.prod (S.α - LinearMap.id) S.ε

/-- **Card `(RRC.6)`.**  The degree-one differential `(y, z) ↦ ε y`. -/
noncomputable def D₁ : (A × ℂ) →ₗ[ℂ] ℂ := S.ε.comp (LinearMap.fst ℂ A ℂ)

theorem D₁_comp_D₀ (x : A) : S.D₁ (S.D₀ x) = 0 := by
  show S.ε (S.α x - x) = 0
  rw [map_sub, S.eps_alpha, sub_self]

/-- **Card `(RRC.5)`.**  The Route-R source complex `A → A ⊕ ℂ → ℂ`. -/
noncomputable def complex :
    ZCochain ℂ (fun n => (pieceCat (ModuleCat.of ℂ A) (ModuleCat.of ℂ (A × ℂ))
      (ModuleCat.of ℂ ℂ) n : Type)) :=
  truncComplex S.D₀ S.D₁ S.D₁_comp_D₀

/-- **Card `(RRC.7)`.**  The retained source class `η = (0, 1)`. -/
noncomputable def eta : (A × ℂ) := (0, 1)

theorem eta_mem_cocycles : (S.eta : A × ℂ) ∈ S.complex.cocycles 0 := by
  show S.D₁ S.eta = 0
  show S.ε (0 : A) = 0
  exact map_zero _

/-- **Card `(RRC.8)`.**  The bilateral Stokes regulator on degree-one cochains. -/
noncomputable def regulator : (A × ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ A ℂ - S.reg.comp (LinearMap.fst ℂ A ℂ)

/-- **Card `(RRC.8)`.**  The regulator kills coboundaries, hence descends. -/
theorem regulator_comp_D₀ (x : A) : S.regulator (S.D₀ x) = 0 := by
  show S.ε x - S.reg (S.α x - x) = 0
  rw [S.reg_comm, sub_self]

/-- **Card `(RRC.9)`.**  The regulator of the retained class is one. -/
theorem regulator_eta : S.regulator S.eta = 1 := by
  show (1 : ℂ) - S.reg (0 : A) = 1
  rw [map_zero, sub_zero]

/-- **Card `(RRC.9)`.**  The descended regulator on degree-one source cohomology. -/
noncomputable def regulatorBar : S.complex.cohomology 0 →ₗ[ℂ] ℂ :=
  sourceCharacter (C := S.complex) (-1) S.regulator fun b => S.regulator_comp_D₀ b

theorem regulatorBar_eta :
    S.regulatorBar (S.complex.cls ⟨S.eta, S.eta_mem_cocycles⟩) = 1 := S.regulator_eta

/-- **Card `(RRC.13)`, `(RRC.27)`.**  The physical character attached to a coefficient and a
physical value. -/
noncomputable def physChar {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) :
    (A × ℂ) →ₗ[ℂ] V :=
  (LinearMap.toSpanSingleton ℂ V v).comp ((cρ • LinearMap.id).comp S.regulator)

theorem physChar_comp_D₀ {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) (x : A) :
    S.physChar cρ v (S.D₀ x) = 0 := by
  show (cρ • S.regulator (S.D₀ x)) • v = 0
  rw [S.regulator_comp_D₀, smul_zero, zero_smul]

theorem physChar_eta {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) :
    S.physChar cρ v S.eta = cρ • v := by
  show (cρ • S.regulator S.eta) • v = cρ • v
  rw [S.regulator_eta, smul_eq_mul, mul_one]

end RouteRSource

/-! ## The relative cone character -/

section ConeCharacter

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)
  {Nfam : ℤ → Type} [∀ n, AddCommGroup (Nfam n)] [∀ n, Module ℂ (Nfam n)]
  {X : ZCochain ℂ Nfam} (Φ : ZCochainMap S.complex X)

/-- **Card `(RRC.11)`.**  A resolved primitive for the retained class produces a cone cocycle:
this is the class `κ = (L, η)`. -/
theorem cone_cocycle_of_primitive (L : Nfam 0) (hL : Φ.f 1 S.eta = X.d 0 L) :
    ((L, S.eta) : Nfam (-1 + 1) × (A × ℂ)) ∈ (coneComplex Φ).cocycles (-1) := by
  show (coneComplex Φ).d 0 (L, S.eta) = 0
  rw [coneComplex_d_apply]
  refine Prod.ext ?_ ?_
  · show X.d 0 L - Φ.f 1 S.eta = 0
    rw [hL, sub_self]
  · show -(S.complex.d 1 S.eta) = 0
    have h : S.complex.d 1 S.eta = 0 := S.eta_mem_cocycles
    rw [h, neg_zero]

/-- **Card `(RRC.31)`, boxed.**  The relative cone character of the retained class is the physical
coefficient: the value depends only on the retained source class, never on the chosen resolved
primitive. -/
theorem coneCharacter_retained {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V)
    (y : (coneComplex Φ).cocycles (-1))
    (hy : (y : Nfam (-1 + 1) × (A × ℂ)).2 = S.eta) :
    coneCharacter Φ (-1) (S.physChar cρ v) (fun b => S.physChar_comp_D₀ cρ v b)
        ((coneComplex Φ).cls y)
      = cρ • v := by
  rw [coneCharacter_cls, hy, S.physChar_eta]

/-- The character of the retained class computes the source character on the relative-law class it
names in the kernel of the comparison. -/
theorem coneCharacterRel_retained {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V)
    (z : (coneComplex Φ).cohomology (-1) ⧸
      LinearMap.range ((coneInc Φ).cohomologyMap (-1))) :
    coneCharacterRel Φ (-1) (S.physChar cρ v) (fun b => S.physChar_comp_D₀ cρ v b) z
      = sourceCharacter (C := S.complex) (-1) (S.physChar cρ v)
          (fun b => S.physChar_comp_D₀ cρ v b)
          ((coneRelativeLawEquiv Φ (-1) z : S.complex.cohomology 0)) :=
  coneCharacterRel_eq Φ (-1) _ _ z

end ConeCharacter

end RouteR

end HTGeometry.ConstraintRelativity
