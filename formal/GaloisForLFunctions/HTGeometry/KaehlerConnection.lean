import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOre

/-!
# The canonical connection on Kähler differentials of a differential field

For a differential ring `K` over a ring of constants `C`, the relative Kähler module `Ω[K⁄C]`
carries a canonical connection

`∇ (a · d b) = δ(a) · d b + a · d (δ b)`,

which makes it a module over the Ore ring `K[∂; δ]`.  This file constructs `∇` from the universal
property, with no presentation and no choice of differential generators.

The construction is the first jet module: on `Ω[K⁄C] × Ω[K⁄C]` put the twisted scalar action
`a • (ω, ω') = (a ω, a ω' + δ(a) ω)`.  The map `b ↦ (d b, d (δ b))` is then a `C`-derivation into
that module — the Leibniz rule for the second component is exactly the two cross terms of `δ` —
so it factors through `Ω[K⁄C]`.  Its first component is the identity, and its second component is
the connection.

* `KaehlerJet` — the twisted first jet module;
* `kaehlerJetDerivation`, `kaehlerLift`, `base_kaehlerLift`;
* `kaehlerConnection`, `kaehlerConnection_D`, `kaehlerConnection_smul` — the defining law;
* `kaehlerConnection_unique` — the connection is determined by those two laws;
* `diffOpSMul`, `diffOpSMul_mono`, `diffOpSMul_dpartial`, `diffOpSMul_mul`,
  `kaehlerDiffOpModule` — the resulting module structure over the Ore ring `K[∂; δ]`.

`HypertranscendentalKaehlerClockSymbol.kaehlerConnectionDifferential` builds the same map from the
`kerTotal` presentation; `kaehlerConnection_unique` identifies the two.  The construction here is
kept because it is import-light: the module structure over the operator ring needs only the two
defining laws, not the presentation.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (C K : Type*) [CommRing C] [CommRing K] [Algebra C K] [Differential K]

/-- Pairs of Kähler differentials, with the connection-twisted scalar action. -/
structure KaehlerJet where
  /-- The value. -/
  base : Ω[K⁄C]
  /-- The derivative. -/
  jet : Ω[K⁄C]

namespace KaehlerJet

variable {C K}

omit [Differential K] in
@[ext] theorem ext {x y : KaehlerJet C K} (hb : x.base = y.base) (hj : x.jet = y.jet) : x = y := by
  cases x
  cases y
  simp_all

instance : Add (KaehlerJet C K) := ⟨fun x y => ⟨x.base + y.base, x.jet + y.jet⟩⟩
instance : Zero (KaehlerJet C K) := ⟨⟨0, 0⟩⟩
instance : Neg (KaehlerJet C K) := ⟨fun x => ⟨-x.base, -x.jet⟩⟩

omit [Differential K] in
@[simp] theorem add_base (x y : KaehlerJet C K) : (x + y).base = x.base + y.base := rfl
omit [Differential K] in
@[simp] theorem add_jet (x y : KaehlerJet C K) : (x + y).jet = x.jet + y.jet := rfl
omit [Differential K] in
@[simp] theorem zero_base : (0 : KaehlerJet C K).base = 0 := rfl
omit [Differential K] in
@[simp] theorem zero_jet : (0 : KaehlerJet C K).jet = 0 := rfl
omit [Differential K] in
@[simp] theorem neg_base (x : KaehlerJet C K) : (-x).base = -x.base := rfl
omit [Differential K] in
@[simp] theorem neg_jet (x : KaehlerJet C K) : (-x).jet = -x.jet := rfl

instance : AddCommGroup (KaehlerJet C K) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]

instance : SMul K (KaehlerJet C K) :=
  ⟨fun a x => ⟨a • x.base, a • x.jet + (Differential.deriv a) • x.base⟩⟩

@[simp] theorem smul_base (a : K) (x : KaehlerJet C K) : (a • x).base = a • x.base := rfl
@[simp] theorem smul_jet (a : K) (x : KaehlerJet C K) :
    (a • x).jet = a • x.jet + (Differential.deriv a) • x.base := rfl

instance : Module K (KaehlerJet C K) where
  one_smul x := by
    ext
    · simp
    · simp [Derivation.map_one_eq_zero]
  mul_smul a b x := by
    ext
    · simp [mul_smul]
    · simp only [smul_jet, smul_base, mul_smul, Derivation.leibniz, add_smul, smul_add,
        smul_eq_mul]
      rw [smul_comm b (Differential.deriv a) x.base]
      abel
  smul_zero a := by ext <;> simp
  smul_add a x y := by
    ext
    · simp [smul_add]
    · simp only [smul_jet, add_jet, add_base, smul_add]
      abel
  add_smul a b x := by
    ext
    · simp [add_smul]
    · simp only [smul_jet, add_jet, add_smul, map_add]
      abel
  zero_smul x := by ext <;> simp

instance : Module C (KaehlerJet C K) := Module.compHom _ (algebraMap C K)

theorem algebraMap_smul (c : C) (x : KaehlerJet C K) :
    c • x = (algebraMap C K c) • x := rfl

instance : IsScalarTower C K (KaehlerJet C K) :=
  ⟨fun c a x => by
    rw [algebraMap_smul, Algebra.smul_def, mul_smul]⟩

/-- The base component, as a `K`-linear map. -/
def baseHom : KaehlerJet C K →ₗ[K] Ω[K⁄C] where
  toFun x := x.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KaehlerJet

variable {C K}

/-- The underlying map of the first-jet derivation. -/
def kaehlerJetFun (b : K) : KaehlerJet C K :=
  ⟨KaehlerDifferential.D C K b, KaehlerDifferential.D C K (Differential.deriv b)⟩

@[simp] theorem kaehlerJetFun_base (b : K) :
    (kaehlerJetFun (C := C) (K := K) b).base = KaehlerDifferential.D C K b := rfl

@[simp] theorem kaehlerJetFun_jet (b : K) :
    (kaehlerJetFun (C := C) (K := K) b).jet
      = KaehlerDifferential.D C K (Differential.deriv b) := rfl

/-- The first-jet derivation `b ↦ (d b, d (δ b))`. -/
def kaehlerJetDerivation (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) :
    Derivation C K (KaehlerJet C K) where
  toLinearMap :=
    { toFun := kaehlerJetFun
      map_add' := by
        intro a b
        ext <;> simp [map_add]
      map_smul' := by
        intro c b
        have hmul : Differential.deriv ((algebraMap C K c) * b)
            = (algebraMap C K c) * Differential.deriv b := by
          rw [Derivation.leibniz, hC c, smul_zero, add_zero, smul_eq_mul]
        ext
        · show KaehlerDifferential.D C K (c • b)
            = (algebraMap C K c) • KaehlerDifferential.D C K b
          rw [Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
        · show KaehlerDifferential.D C K (Differential.deriv (c • b))
            = (algebraMap C K c) • KaehlerDifferential.D C K (Differential.deriv b)
              + (Differential.deriv (algebraMap C K c)) • KaehlerDifferential.D C K b
          rw [hC c, zero_smul, add_zero, Algebra.smul_def, hmul, Derivation.leibniz,
            Derivation.map_algebraMap, smul_zero, add_zero] }
  map_one_eq_zero' := by
    ext <;> simp [Derivation.map_one_eq_zero]
  leibniz' := by
    intro a b
    ext
    · show KaehlerDifferential.D C K (a * b)
        = (a • kaehlerJetFun (C := C) b + b • kaehlerJetFun (C := C) a).base
      simp only [KaehlerJet.add_base, KaehlerJet.smul_base, kaehlerJetFun_base,
        Derivation.leibniz]
    · show KaehlerDifferential.D C K (Differential.deriv (a * b))
        = (a • kaehlerJetFun (C := C) b + b • kaehlerJetFun (C := C) a).jet
      simp only [KaehlerJet.add_jet, KaehlerJet.smul_jet,
        kaehlerJetFun_base, kaehlerJetFun_jet, Derivation.leibniz, map_add, smul_eq_mul]
      abel

/-- The lift of the first-jet derivation to the Kähler module. -/
def kaehlerLift (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) :
    Ω[K⁄C] →ₗ[K] KaehlerJet C K :=
  (kaehlerJetDerivation hC).liftKaehlerDifferential

@[simp] theorem kaehlerLift_D (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) (b : K) :
    kaehlerLift hC (KaehlerDifferential.D C K b) = kaehlerJetFun (C := C) b :=
  (kaehlerJetDerivation hC).liftKaehlerDifferential_comp_D b

/-- **The lift is a section**: its base component is the identity. -/
theorem base_kaehlerLift (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) (ω : Ω[K⁄C]) :
    (kaehlerLift hC ω).base = ω := by
  have hEq : (KaehlerJet.baseHom).comp (kaehlerLift hC) = LinearMap.id := by
    refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
    show KaehlerJet.baseHom (kaehlerLift hC (KaehlerDifferential.D C K b))
      = KaehlerDifferential.D C K b
    rw [kaehlerLift_D]
    rfl
  exact congrArg (fun φ : Ω[K⁄C] →ₗ[K] Ω[K⁄C] => φ ω) hEq

/-- **The canonical connection on Kähler differentials.** -/
def kaehlerConnection (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) :
    Ω[K⁄C] →+ Ω[K⁄C] where
  toFun ω := (kaehlerLift hC ω).jet
  map_zero' := by simp
  map_add' x y := by simp

@[simp] theorem kaehlerConnection_D (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (b : K) :
    kaehlerConnection hC (KaehlerDifferential.D C K b)
      = KaehlerDifferential.D C K (Differential.deriv b) := by
  show (kaehlerLift hC (KaehlerDifferential.D C K b)).jet = _
  rw [kaehlerLift_D]
  rfl

/-- **The defining law of the connection.** -/
theorem kaehlerConnection_smul (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (a : K) (ω : Ω[K⁄C]) :
    kaehlerConnection hC (a • ω)
      = a • kaehlerConnection hC ω + (Differential.deriv a) • ω := by
  show (kaehlerLift hC (a • ω)).jet = _
  rw [map_smul]
  show a • (kaehlerLift hC ω).jet + (Differential.deriv a) • (kaehlerLift hC ω).base = _
  rw [base_kaehlerLift]
  rfl

/-! ### The module structure over the ring of differential operators -/

/-- The coefficient action `a ↦ a · ∇ⁿ ω`, as an additive map. -/
def diffOpAux (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) (ω : Ω[K⁄C]) (n : ℕ) :
    K →+ Ω[K⁄C] where
  toFun a := a • ((kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] ω)
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b _

/-- **A differential operator acts on Kähler differentials** through the connection. -/
def diffOpSMul (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p : DiffOp K) (ω : Ω[K⁄C]) : Ω[K⁄C] :=
  Finsupp.liftAddHom (diffOpAux hC ω) (DiffOp.toFinsupp p)

theorem diffOpSMul_mono (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (n : ℕ) (a : K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (DiffOp.mono n a) ω = a • ((kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] ω) := by
  rw [diffOpSMul, DiffOp.toFinsupp_mono]
  exact Finsupp.liftAddHom_apply_single (diffOpAux hC ω) n a

@[simp] theorem diffOpSMul_zero_op (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (ω : Ω[K⁄C]) : diffOpSMul hC 0 ω = 0 := by
  rw [diffOpSMul, DiffOp.toFinsupp_zero, map_zero]

theorem diffOpSMul_add_op (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p q : DiffOp K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (p + q) ω = diffOpSMul hC p ω + diffOpSMul hC q ω := by
  rw [diffOpSMul, diffOpSMul, diffOpSMul, DiffOp.toFinsupp_add, map_add]

theorem diffOpSMul_smul (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (a : K) (p : DiffOp K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (a • p) ω = a • diffOpSMul hC p ω := by
  refine DiffOp.induction_linear
    (motive := fun p => diffOpSMul hC (a • p) ω = a • diffOpSMul hC p ω) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [smul_add, diffOpSMul_add_op, diffOpSMul_add_op, hp, hq, smul_add]
  · intro n c
    rw [DiffOp.smul_mono, diffOpSMul_mono, diffOpSMul_mono, mul_smul]

theorem diffOpSMul_dpartial (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p : DiffOp K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (DiffOp.dpartial p) ω = kaehlerConnection hC (diffOpSMul hC p ω) := by
  refine DiffOp.induction_linear
    (motive := fun p => diffOpSMul hC (DiffOp.dpartial p) ω
      = kaehlerConnection hC (diffOpSMul hC p ω)) p ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [DiffOp.dpartial_add, diffOpSMul_add_op, hp, hq, diffOpSMul_add_op, map_add]
  · intro n a
    rw [DiffOp.dpartial_mono, diffOpSMul_add_op, diffOpSMul_mono, diffOpSMul_mono,
      diffOpSMul_mono, kaehlerConnection_smul, Function.iterate_succ_apply']

theorem diffOpSMul_dpartial_iterate (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (n : ℕ) (p : DiffOp K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (DiffOp.dpartial^[n] p) ω
      = (kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] (diffOpSMul hC p ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', diffOpSMul_dpartial, ih]

theorem diffOpSMul_mul (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p q : DiffOp K) (ω : Ω[K⁄C]) :
    diffOpSMul hC (p * q) ω = diffOpSMul hC p (diffOpSMul hC q ω) := by
  refine DiffOp.induction_linear
    (motive := fun p => diffOpSMul hC (p * q) ω = diffOpSMul hC p (diffOpSMul hC q ω))
    p ?_ ?_ ?_
  · rw [DiffOp.zero_mul', diffOpSMul_zero_op, diffOpSMul_zero_op]
  · intro p₁ p₂ h₁ h₂
    rw [DiffOp.add_mul', diffOpSMul_add_op, h₁, h₂, diffOpSMul_add_op]
  · intro n a
    rw [DiffOp.mono_mul, diffOpSMul_smul, diffOpSMul_dpartial_iterate, diffOpSMul_mono]

theorem diffOpSMul_zero (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p : DiffOp K) : diffOpSMul hC p 0 = 0 := by
  refine DiffOp.induction_linear (motive := fun p => diffOpSMul hC p 0 = 0) p ?_ ?_ ?_
  · rw [diffOpSMul_zero_op]
  · intro p q hp hq
    rw [diffOpSMul_add_op, hp, hq, add_zero]
  · intro n a
    rw [diffOpSMul_mono, Function.iterate_fixed (map_zero _), smul_zero]

theorem diffOpSMul_add (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p : DiffOp K) (ω η : Ω[K⁄C]) :
    diffOpSMul hC p (ω + η) = diffOpSMul hC p ω + diffOpSMul hC p η := by
  have hiter : ∀ n : ℕ, (kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] (ω + η)
      = (kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] ω
        + (kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] η := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]
  refine DiffOp.induction_linear
    (motive := fun p => diffOpSMul hC p (ω + η) = diffOpSMul hC p ω + diffOpSMul hC p η)
    p ?_ ?_ ?_
  · rw [diffOpSMul_zero_op, diffOpSMul_zero_op, diffOpSMul_zero_op, add_zero]
  · intro p q hp hq
    rw [diffOpSMul_add_op, diffOpSMul_add_op, diffOpSMul_add_op, hp, hq]
    abel
  · intro n a
    rw [diffOpSMul_mono, diffOpSMul_mono, diffOpSMul_mono, hiter, smul_add]

theorem diffOpSMul_one (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) (ω : Ω[K⁄C]) :
    diffOpSMul hC 1 ω = ω := by
  rw [DiffOp.one_def, diffOpSMul_mono]
  simp

/-- **The Kähler module of a differential ring is a module over its ring of differential
operators**, through the canonical connection. -/
@[reducible] def kaehlerDiffOpModule
    (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0) :
    Module (DiffOp K) (Ω[K⁄C]) where
  smul := diffOpSMul hC
  one_smul := diffOpSMul_one hC
  mul_smul := diffOpSMul_mul hC
  smul_zero := diffOpSMul_zero hC
  smul_add := diffOpSMul_add hC
  add_smul p q ω := diffOpSMul_add_op hC p q ω
  zero_smul := diffOpSMul_zero_op hC

/-- **The connection is unique.**  Any additive endomorphism of `Ω[K⁄C]` sending `d b` to `d (δ b)`
and satisfying the Leibniz law is the canonical connection; so this construction agrees with any
other. -/
theorem kaehlerConnection_unique (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (φ : Ω[K⁄C] →+ Ω[K⁄C])
    (hD : ∀ b : K,
      φ (KaehlerDifferential.D C K b) = KaehlerDifferential.D C K (Differential.deriv b))
    (hsmul : ∀ (a : K) (ω : Ω[K⁄C]), φ (a • ω) = a • φ ω + (Differential.deriv a) • ω)
    (ω : Ω[K⁄C]) : φ ω = kaehlerConnection hC ω := by
  have hmem : ω ∈ (⊤ : Submodule K (Ω[K⁄C])) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [hD b, kaehlerConnection_D]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx => rw [hsmul, hx, kaehlerConnection_smul]

/-- The base ring consists of constants. -/
class IsConstantBase (C K : Type*) [CommRing C] [CommRing K] [Algebra C K] [Differential K] :
    Prop where
  /-- The image of the base is annihilated by the derivation. -/
  deriv_algebraMap : ∀ c : C, Differential.deriv (algebraMap C K c) = 0

instance kaehlerDiffOpModuleInstance [IsConstantBase C K] : Module (DiffOp K) (Ω[K⁄C]) :=
  kaehlerDiffOpModule IsConstantBase.deriv_algebraMap

theorem diffOp_smul_def [IsConstantBase C K] (p : DiffOp K) (ω : Ω[K⁄C]) :
    p • ω = diffOpSMul (IsConstantBase.deriv_algebraMap (C := C) (K := K)) p ω := rfl

instance [IsConstantBase C K] : IsScalarTower K (DiffOp K) (Ω[K⁄C]) :=
  ⟨fun a p ω => by
    rw [diffOp_smul_def, diffOp_smul_def]
    exact diffOpSMul_smul _ a p ω⟩

theorem partial_smul_eq_connection [IsConstantBase C K] (ω : Ω[K⁄C]) :
    (DiffOp.mono 1 1 : DiffOp K) • ω
      = kaehlerConnection (IsConstantBase.deriv_algebraMap (C := C) (K := K)) ω := by
  rw [diffOp_smul_def, diffOpSMul_mono, one_smul]
  rfl

theorem diffOpSMul_eq_sum (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (p : DiffOp K) (ω : Ω[K⁄C]) (T : Finset ℕ) (hT : ∀ n ∉ T, DiffOp.coeff p n = 0) :
    diffOpSMul hC p ω
      = ∑ n ∈ T, (DiffOp.coeff p n) • ((kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] ω) := by
  classical
  have hsub : (DiffOp.toFinsupp p).support ⊆ T := by
    intro n hn
    by_contra hcon
    exact (Finsupp.mem_support_iff.mp hn) (hT n hcon)
  have hval : diffOpSMul hC p ω
      = ∑ n ∈ (DiffOp.toFinsupp p).support,
          (DiffOp.coeff p n) • ((kaehlerConnection hC : Ω[K⁄C] → Ω[K⁄C])^[n] ω) := by
    rw [diffOpSMul, Finsupp.liftAddHom_apply, Finsupp.sum]
    rfl
  rw [hval]
  refine Finset.sum_subset hsub fun n _ hn => ?_
  rw [show DiffOp.coeff p n = 0 from Finsupp.notMem_support_iff.mp hn, zero_smul]

end

end GaloisForLFunctions.HTGeometry
