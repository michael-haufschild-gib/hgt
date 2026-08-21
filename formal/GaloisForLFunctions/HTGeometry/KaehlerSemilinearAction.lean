import GaloisForLFunctions.HTGeometry.KaehlerConnection

/-!
# The semilinear action of a differential automorphism on Kähler differentials

A ring automorphism `σ` of `K` fixing the base `C` induces a `σ`-semilinear automorphism of
`Ω[K⁄C]`, characterised by `σ_* (d b) = d (σ b)` and `σ_* (a • ω) = σ(a) • σ_* ω`.  When `σ`
commutes with the derivation it commutes with the canonical connection, so it is an automorphism of
`Ω[K⁄C]` as a module over the Ore ring `K[∂; δ]`, semilinear over `σ`.

The construction is the same one-line universal-property argument as the connection: twist the
scalars of `Ω[K⁄C]` by `σ`, observe that `b ↦ d (σ b)` is a `C`-derivation into the twisted module,
and lift.

* `TwistedKaehler` — the scalar-twisted module;
* `kaehlerSemilinear`, `kaehlerSemilinear_D`, `kaehlerSemilinear_smul`;
* `kaehlerSemilinear_kaehlerConnection` — the commutation with the connection;
* `kaehlerSemilinear_symm_kaehlerSemilinear` — it is an automorphism.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

/-- `Ω[K⁄C]` with its scalars twisted by a ring automorphism of `K`. -/
structure TwistedKaehler (C K : Type*) [CommRing C] [CommRing K] [Algebra C K] (σ : K ≃+* K) where
  /-- The underlying differential. -/
  val : Ω[K⁄C]

namespace TwistedKaehler

variable {σ : K ≃+* K}

@[ext] theorem ext {x y : TwistedKaehler C K σ} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp_all

instance : Add (TwistedKaehler C K σ) := ⟨fun x y => ⟨x.val + y.val⟩⟩
instance : Zero (TwistedKaehler C K σ) := ⟨⟨0⟩⟩
instance : Neg (TwistedKaehler C K σ) := ⟨fun x => ⟨-x.val⟩⟩

@[simp] theorem add_val (x y : TwistedKaehler C K σ) : (x + y).val = x.val + y.val := rfl
@[simp] theorem zero_val : (0 : TwistedKaehler C K σ).val = 0 := rfl
@[simp] theorem neg_val (x : TwistedKaehler C K σ) : (-x).val = -x.val := rfl

instance : AddCommGroup (TwistedKaehler C K σ) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp
  add_zero x := by ext; simp
  neg_add_cancel x := by ext; simp
  add_comm x y := by ext; simp [add_comm]

instance : SMul K (TwistedKaehler C K σ) := ⟨fun a x => ⟨σ a • x.val⟩⟩

@[simp] theorem smul_val (a : K) (x : TwistedKaehler C K σ) : (a • x).val = σ a • x.val := rfl

instance : Module K (TwistedKaehler C K σ) where
  one_smul x := by ext; simp
  mul_smul a b x := by ext; simp [mul_smul]
  smul_zero a := by ext; simp
  smul_add a x y := by ext; simp [smul_add]
  add_smul a b x := by ext; simp [add_smul]
  zero_smul x := by ext; simp

instance : Module C (TwistedKaehler C K σ) := Module.compHom _ (algebraMap C K)

theorem algebraMap_smul (c : C) (x : TwistedKaehler C K σ) :
    c • x = (algebraMap C K c) • x := rfl

instance : IsScalarTower C K (TwistedKaehler C K σ) :=
  ⟨fun c a x => by rw [algebraMap_smul, Algebra.smul_def, mul_smul]⟩

/-- The underlying differential, as an additive map. -/
def valHom : TwistedKaehler C K σ →+ Ω[K⁄C] where
  toFun x := x.val
  map_zero' := rfl
  map_add' _ _ := rfl

end TwistedKaehler

/-- The twisted derivation `b ↦ d (σ b)`. -/
def twistedKaehlerDerivation {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) :
    Derivation C K (TwistedKaehler C K σ) where
  toLinearMap :=
    { toFun := fun b => ⟨KaehlerDifferential.D C K (σ b)⟩
      map_add' := by
        intro a b
        ext
        simp [map_add]
      map_smul' := by
        intro c b
        ext
        show KaehlerDifferential.D C K (σ (c • b))
          = σ (algebraMap C K c) • KaehlerDifferential.D C K (σ b)
        rw [hσ c, Algebra.smul_def, map_mul, hσ c, Derivation.leibniz,
          Derivation.map_algebraMap, smul_zero, add_zero] }
  map_one_eq_zero' := by
    ext
    simp [Derivation.map_one_eq_zero]
  leibniz' := by
    intro a b
    ext
    show KaehlerDifferential.D C K (σ (a * b))
      = (a • (⟨KaehlerDifferential.D C K (σ b)⟩ : TwistedKaehler C K σ)
          + b • (⟨KaehlerDifferential.D C K (σ a)⟩ : TwistedKaehler C K σ)).val
    rw [map_mul, Derivation.leibniz]
    rfl

/-- The lift of the twisted derivation. -/
def twistedKaehlerLift {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) :
    Ω[K⁄C] →ₗ[K] TwistedKaehler C K σ :=
  (twistedKaehlerDerivation hσ).liftKaehlerDifferential

/-- **The semilinear action of `σ` on Kähler differentials.** -/
def kaehlerSemilinear {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) : Ω[K⁄C] →+ Ω[K⁄C] where
  toFun ω := (twistedKaehlerLift hσ ω).val
  map_zero' := by simp
  map_add' x y := by simp

@[simp] theorem kaehlerSemilinear_D {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) (b : K) :
    kaehlerSemilinear hσ (KaehlerDifferential.D C K b) = KaehlerDifferential.D C K (σ b) := by
  show (twistedKaehlerLift hσ (KaehlerDifferential.D C K b)).val = _
  rw [twistedKaehlerLift, (twistedKaehlerDerivation hσ).liftKaehlerDifferential_comp_D]
  rfl

/-- **Semilinearity.** -/
theorem kaehlerSemilinear_smul {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) (a : K) (ω : Ω[K⁄C]) :
    kaehlerSemilinear hσ (a • ω) = σ a • kaehlerSemilinear hσ ω := by
  show (twistedKaehlerLift hσ (a • ω)).val = _
  rw [map_smul]
  rfl

variable [Differential K]

/-- **The semilinear action commutes with the canonical connection** when `σ` commutes with the
derivation. -/
theorem kaehlerSemilinear_kaehlerConnection {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c)
    (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (hσδ : ∀ x : K, σ (Differential.deriv x) = Differential.deriv (σ x)) (ω : Ω[K⁄C]) :
    kaehlerSemilinear hσ (kaehlerConnection hC ω)
      = kaehlerConnection hC (kaehlerSemilinear hσ ω) := by
  have hmem : ω ∈ (⊤ : Submodule K (Ω[K⁄C])) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [kaehlerConnection_D, kaehlerSemilinear_D, kaehlerSemilinear_D, hσδ b,
        kaehlerConnection_D]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [kaehlerConnection_smul, map_add, kaehlerSemilinear_smul, kaehlerSemilinear_smul, hx,
        kaehlerSemilinear_smul, kaehlerConnection_smul, hσδ a]

omit [Differential K] in
/-- The inverse automorphism also fixes the base. -/
theorem symm_fixes {σ : K ≃+* K} (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) (c : C) :
    σ.symm (algebraMap C K c) = algebraMap C K c := by
  apply σ.injective
  rw [RingEquiv.apply_symm_apply, hσ c]

omit [Differential K] in
/-- **The semilinear action of the inverse automorphism inverts it**, so `σ_*` is a semilinear
automorphism of the Kähler module. -/
theorem kaehlerSemilinear_symm_kaehlerSemilinear {σ : K ≃+* K}
    (hσ : ∀ c : C, σ (algebraMap C K c) = algebraMap C K c) (ω : Ω[K⁄C]) :
    kaehlerSemilinear (σ := σ.symm) (symm_fixes hσ) (kaehlerSemilinear hσ ω) = ω := by
  have hmem : ω ∈ (⊤ : Submodule K (Ω[K⁄C])) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [kaehlerSemilinear_D, kaehlerSemilinear_D, RingEquiv.symm_apply_apply]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [kaehlerSemilinear_smul, kaehlerSemilinear_smul, hx, RingEquiv.symm_apply_apply]

end

end GaloisForLFunctions.HTGeometry
