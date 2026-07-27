import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCupDescent

/-!
# Poisson--zeta assembly for Deninger arithmetic cohomology

This module formalizes the source-independent algebraic assembly behind
`DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`.

Given injective maps

`Hcap --Z--> Hminus` and `P --principal--> D`,

the complex

`R × Hcap --> Hminus × P --> D`

has `H⁰ ≃ R`, `H¹ ≃ Hminus / range Z`, and
`H² ≃ D / range principal`.  It also carries the chain-level endpoint
and middle cup pairings forced by a degree map and an alternating form
on the Poisson quotient.

No Schwartz-space theorem, zeta zero, positivity premise, or Riemann
hypothesis is assumed here.
-/

namespace RHTower

section PoissonZetaAssembly

variable {R Hcap Hminus P D : Type*}
variable [CommRing R]
variable [AddCommGroup Hcap] [Module R Hcap]
variable [AddCommGroup Hminus] [Module R Hminus]
variable [AddCommGroup P] [Module R P]
variable [AddCommGroup D] [Module R D]

/-- Degree-zero differential: the Poisson--zeta map, with no endpoint component. -/
def deningerPoissonZetaD0
    (Z : Hcap →ₗ[R] Hminus) :
    (R × Hcap) →ₗ[R] (Hminus × P) where
  toFun x := (Z x.2, 0)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

/-- Degree-one differential: the principal Arakelov divisor map. -/
def deningerPoissonZetaD1
    (principal : P →ₗ[R] D) :
    (Hminus × P) →ₗ[R] D where
  toFun x := principal x.2
  map_add' x y := by
    simp
  map_smul' c x := by
    simp

@[simp]
theorem deningerPoissonZetaD0_apply
    (Z : Hcap →ₗ[R] Hminus) (x : R × Hcap) :
    deningerPoissonZetaD0 (P := P) Z x = (Z x.2, 0) :=
  rfl

@[simp]
theorem deningerPoissonZetaD1_apply
    (principal : P →ₗ[R] D) (x : Hminus × P) :
    deningerPoissonZetaD1 (Hminus := Hminus) principal x =
      principal x.2 :=
  rfl

/-- The Poisson and endpoint maps form a three-term cochain complex. -/
def deningerPoissonZetaComplex
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    DeningerArithmeticThreeTermComplex
      R (R × Hcap) (Hminus × P) D where
  d0 := deningerPoissonZetaD0 (P := P) Z
  d1 := deningerPoissonZetaD1 (Hminus := Hminus) principal
  d1_comp_d0 := by
    apply LinearMap.ext
    intro x
    simp

/-- Injectivity of `Z` leaves only the constant line in degree zero. -/
theorem deningerPoissonZeta_mem_cycles0_iff
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (hZ : Function.Injective Z)
    (x : R × Hcap) :
    x ∈ (deningerPoissonZetaComplex Z principal).cycles0 ↔
      x.2 = 0 := by
  constructor
  · intro hx
    change (Z x.2, (0 : P)) = 0 at hx
    have hz : Z x.2 = Z 0 := by
      simpa using congrArg Prod.fst hx
    exact hZ hz
  · intro hx
    change (Z x.2, (0 : P)) = 0
    rw [hx, map_zero]
    rfl

/-- The degree-zero cohomology of the assembled complex is the constant line. -/
noncomputable def deningerPoissonZetaH0Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (hZ : Function.Injective Z) :
    (deningerPoissonZetaComplex Z principal).H0 ≃ₗ[R] R where
  toFun x := (x : R × Hcap).1
  invFun a :=
    ⟨(a, 0),
      (deningerPoissonZeta_mem_cycles0_iff Z principal hZ (a, 0)).2 rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact
        (deningerPoissonZeta_mem_cycles0_iff
          Z principal hZ (x : R × Hcap)).1 x.2 |>.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Injectivity of the principal map makes every degree-one cocycle purely generic. -/
theorem deningerPoissonZeta_mem_cycles1_iff
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (hprincipal : Function.Injective principal)
    (x : Hminus × P) :
    x ∈ (deningerPoissonZetaComplex Z principal).cycles1 ↔
      x.2 = 0 := by
  constructor
  · intro hx
    change principal x.2 = 0 at hx
    apply hprincipal
    simpa using hx
  · intro hx
    change principal x.2 = 0
    rw [hx, map_zero]

/-- Degree-one boundaries are exactly `(Z f, 0)`. -/
theorem deningerPoissonZeta_mem_boundaries1_iff
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (x : Hminus × P) :
    x ∈ (deningerPoissonZetaComplex Z principal).boundaries1 ↔
      ∃ f : Hcap, x = (Z f, 0) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.2, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨((0 : R), f), rfl⟩

/-- Projection of degree-one cocycles to the Poisson quotient. -/
def deningerPoissonZetaCycles1ToQuotient
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    (deningerPoissonZetaComplex Z principal).cycles1 →ₗ[R]
      Hminus ⧸ LinearMap.range Z where
  toFun x := (LinearMap.range Z).mkQ (x : Hminus × P).1
  map_add' x y := by
    simp
  map_smul' c x := by
    simp

/-- Degree-one boundaries vanish under projection to `Hminus / range Z`. -/
theorem deningerPoissonZeta_boundaries1_le_quotientKer
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    (deningerPoissonZetaComplex Z principal).boundaries1.comap
        (deningerPoissonZetaComplex Z principal).cycles1.subtype ≤
      LinearMap.ker
        (deningerPoissonZetaCycles1ToQuotient Z principal) := by
  intro x hx
  change (x : Hminus × P) ∈
    (deningerPoissonZetaComplex Z principal).boundaries1 at hx
  rw [deningerPoissonZeta_mem_boundaries1_iff Z principal] at hx
  obtain ⟨f, hf⟩ := hx
  change (LinearMap.range Z).mkQ (x : Hminus × P).1 = 0
  rw [show (x : Hminus × P).1 = Z f by simpa [hf]]
  exact
    (Submodule.Quotient.mk_eq_zero (LinearMap.range Z)).2
      ⟨f, rfl⟩

/-- Canonical map from assembled `H¹` to the Poisson quotient. -/
def deningerPoissonZetaH1ToQuotient
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    (deningerPoissonZetaComplex Z principal).H1 →ₗ[R]
      Hminus ⧸ LinearMap.range Z :=
  ((deningerPoissonZetaComplex Z principal).boundaries1.comap
      (deningerPoissonZetaComplex Z principal).cycles1.subtype).liftQ
    (deningerPoissonZetaCycles1ToQuotient Z principal)
    (deningerPoissonZeta_boundaries1_le_quotientKer Z principal)

@[simp]
theorem deningerPoissonZetaH1ToQuotient_mkQ
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (x : (deningerPoissonZetaComplex Z principal).cycles1) :
    deningerPoissonZetaH1ToQuotient Z principal
        (Submodule.Quotient.mk x) =
      (LinearMap.range Z).mkQ (x : Hminus × P).1 := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ
      ((deningerPoissonZetaComplex Z principal).boundaries1.comap
        (deningerPoissonZetaComplex Z principal).cycles1.subtype)
      (deningerPoissonZetaCycles1ToQuotient Z principal)
      (deningerPoissonZeta_boundaries1_le_quotientKer Z principal)) x

/-- The assembled `H¹` maps injectively to the Poisson quotient. -/
theorem deningerPoissonZetaH1ToQuotient_injective
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (hprincipal : Function.Injective principal) :
    Function.Injective
      (deningerPoissonZetaH1ToQuotient Z principal) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  intro q hq
  let B :=
    (deningerPoissonZetaComplex Z principal).boundaries1.comap
      (deningerPoissonZetaComplex Z principal).cycles1.subtype
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective B q
  rw [deningerPoissonZetaH1ToQuotient_mkQ] at hq
  apply (Submodule.Quotient.mk_eq_zero B).2
  change (x : Hminus × P) ∈
    (deningerPoissonZetaComplex Z principal).boundaries1
  rw [deningerPoissonZeta_mem_boundaries1_iff Z principal]
  have hxP :
      (x : Hminus × P).2 = 0 :=
    (deningerPoissonZeta_mem_cycles1_iff
      Z principal hprincipal (x : Hminus × P)).1 x.2
  have hxH :
      (x : Hminus × P).1 ∈ LinearMap.range Z :=
    (Submodule.Quotient.mk_eq_zero (LinearMap.range Z)).1 hq
  obtain ⟨f, hf⟩ := hxH
  refine ⟨f, ?_⟩
  apply Prod.ext
  · exact hf.symm
  · exact hxP

/-- Every Poisson quotient class is represented by a degree-one cocycle. -/
theorem deningerPoissonZetaH1ToQuotient_surjective
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    Function.Surjective
      (deningerPoissonZetaH1ToQuotient Z principal) := by
  intro q
  obtain ⟨h, rfl⟩ :=
    Submodule.Quotient.mk_surjective (LinearMap.range Z) q
  let x : (deningerPoissonZetaComplex Z principal).cycles1 :=
    ⟨(h, 0), by
      change principal 0 = 0
      rw [map_zero]⟩
  refine
    ⟨Submodule.Quotient.mk x, ?_⟩
  rw [deningerPoissonZetaH1ToQuotient_mkQ]
  rfl

/-- The middle cohomology is exactly Meyer's source quotient algebraically. -/
noncomputable def deningerPoissonZetaH1Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (hprincipal : Function.Injective principal) :
    (deningerPoissonZetaComplex Z principal).H1 ≃ₗ[R]
      Hminus ⧸ LinearMap.range Z :=
  LinearEquiv.ofBijective
    (deningerPoissonZetaH1ToQuotient Z principal)
    ⟨deningerPoissonZetaH1ToQuotient_injective
        Z principal hprincipal,
      deningerPoissonZetaH1ToQuotient_surjective Z principal⟩

/-- Top boundaries are exactly principal Arakelov divisors. -/
theorem deningerPoissonZeta_boundaries2_eq_range
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    (deningerPoissonZetaComplex Z principal).boundaries2 =
      LinearMap.range principal := by
  ext d
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.2, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨((0 : Hminus), p), rfl⟩

/-- Top cohomology is the Arakelov divisor quotient by principal divisors. -/
def deningerPoissonZetaH2Equiv
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D) :
    (deningerPoissonZetaComplex Z principal).H2 ≃ₗ[R]
      D ⧸ LinearMap.range principal :=
  Submodule.quotEquivOfEq
    (deningerPoissonZetaComplex Z principal).boundaries2
    (LinearMap.range principal)
    (deningerPoissonZeta_boundaries2_eq_range Z principal)

/-- Endpoint cup--trace: constant multiplication followed by Arakelov degree. -/
def deningerPoissonZetaPair02
    (degree : D →ₗ[R] R) :
    (R × Hcap) →ₗ[R] D →ₗ[R] R where
  toFun x :=
    { toFun := fun d => x.1 * degree d
      map_add' := by
        intro d e
        simp [mul_add]
      map_smul' := by
        intro c d
        simp [mul_comm, mul_left_comm, mul_assoc] }
  map_add' x y := by
    apply LinearMap.ext
    intro d
    simp [add_mul]
  map_smul' c x := by
    apply LinearMap.ext
    intro d
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- Middle cup--trace ignores the contractible endpoint coordinate. -/
def deningerPoissonZetaPair11
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R) :
    (Hminus × P) →ₗ[R] (Hminus × P) →ₗ[R] R where
  toFun x :=
    { toFun := fun y => psi x.1 y.1
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro c y
        simp }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    simp

@[simp]
theorem deningerPoissonZetaPair02_apply
    (degree : D →ₗ[R] R) (x : R × Hcap) (d : D) :
    deningerPoissonZetaPair02 (Hcap := Hcap) degree x d =
      x.1 * degree d :=
  rfl

@[simp]
theorem deningerPoissonZetaPair11_apply
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (x y : Hminus × P) :
    deningerPoissonZetaPair11 (P := P) psi x y =
      psi x.1 y.1 :=
  rfl

/-- Paugam middle duality and Arakelov degree assemble to a cochain cup pairing. -/
def deningerPoissonZetaCupPairing
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (degree : D →ₗ[R] R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hdegree : degree.comp principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h) :
    DeningerArithmeticThreeTermCupPairing
      (deningerPoissonZetaComplex Z principal) where
  pair02 := deningerPoissonZetaPair02 degree
  pair11 := deningerPoissonZetaPair11 psi
  differential_adjoint := by
    rintro ⟨a, f⟩ ⟨h, p⟩
    change psi (Z f) h + a * degree (principal p) = 0
    have hp := LinearMap.congr_fun hdegree p
    change degree (principal p) = 0 at hp
    rw [hpsiBoundary, hp, mul_zero, add_zero]
  skew := by
    rintro ⟨h, p⟩ ⟨k, q⟩
    exact hpsiSkew h k

/-- Componentwise generator used by the Poisson--zeta flow. -/
def deningerPoissonZetaProductEnd
    {A B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (thetaA : Module.End R A)
    (thetaB : Module.End R B) :
    Module.End R (A × B) where
  toFun x := (thetaA x.1, thetaB x.2)
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp

@[simp]
theorem deningerPoissonZetaProductEnd_apply
    {A B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (thetaA : Module.End R A)
    (thetaB : Module.End R B)
    (x : A × B) :
    deningerPoissonZetaProductEnd thetaA thetaB x =
      (thetaA x.1, thetaB x.2) :=
  rfl

/-- Flow generator on the assembled Poisson--zeta complex. -/
def deningerPoissonZetaFlow
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (thetaP : Module.End R P)
    (thetaD : Module.End R D)
    (hZ :
      Z.comp thetaCap = thetaMinus.comp Z)
    (hprincipal :
      principal.comp thetaP = thetaD.comp principal) :
    DeningerArithmeticThreeTermFlow
      R (R × Hcap) (Hminus × P) D where
  toDeningerArithmeticThreeTermComplex :=
    deningerPoissonZetaComplex Z principal
  theta0 :=
    deningerPoissonZetaProductEnd (0 : Module.End R R) thetaCap
  theta1 :=
    deningerPoissonZetaProductEnd thetaMinus thetaP
  theta2 := thetaD
  theta_commutes_d0 := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun hZ x.2
    · simp [deningerPoissonZetaComplex, deningerPoissonZetaD0]
  theta_commutes_d1 := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hprincipal x.2

/-- Weight-one cup law for the assembled flow. -/
def deningerPoissonZetaWeightOneCup
    (Z : Hcap →ₗ[R] Hminus)
    (principal : P →ₗ[R] D)
    (degree : D →ₗ[R] R)
    (psi : Hminus →ₗ[R] Hminus →ₗ[R] R)
    (hdegree : degree.comp principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew : ∀ h k, psi h k = -psi k h)
    (thetaCap : Module.End R Hcap)
    (thetaMinus : Module.End R Hminus)
    (thetaP : Module.End R P)
    (thetaD : Module.End R D)
    (hZ :
      Z.comp thetaCap = thetaMinus.comp Z)
    (hprincipal :
      principal.comp thetaP = thetaD.comp principal)
    (hdegreeTheta : degree.comp thetaD = degree)
    (hpsiTheta :
      ∀ h k,
        psi (thetaMinus h) k + psi h (thetaMinus k) =
          psi h k) :
    DeningerArithmeticThreeTermWeightOneCup
      (deningerPoissonZetaFlow
        Z principal thetaCap thetaMinus thetaP thetaD hZ hprincipal)
      (deningerPoissonZetaCupPairing
        Z principal degree psi hdegree hpsiBoundary hpsiSkew) where
  endpoint_weight := by
    rintro ⟨a, f⟩ d
    change 0 * degree d + a * degree (thetaD d) = a * degree d
    have hd := LinearMap.congr_fun hdegreeTheta d
    change degree (thetaD d) = degree d at hd
    rw [zero_mul, zero_add, hd]
  middle_weight := by
    rintro ⟨h, p⟩ ⟨k, q⟩
    exact hpsiTheta h k

end PoissonZetaAssembly

end RHTower
