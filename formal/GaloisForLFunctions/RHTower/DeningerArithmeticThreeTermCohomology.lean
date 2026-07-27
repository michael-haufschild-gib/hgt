import Mathlib

/-!
# Three-term arithmetic cohomology

This module defines the source-independent cohomology of a three-term Deninger coefficient
complex

`A⁰ --d⁰--> A¹ --d¹--> A²`

and the endomorphisms induced by a commuting transverse generator `Theta`.

The intended arithmetic instance is the realified, completed derived Milnor--Witt
rational-Witt coefficient complex.  No analytic Xi quotient, zeta-zero set, positivity
premise, or Riemann hypothesis enters these definitions or proofs.
-/

namespace RHTower

section ThreeTermCohomology

variable (R A0 A1 A2 : Type*)
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/-- A three-term cochain complex underlying Deninger arithmetic cohomology. -/
structure DeningerArithmeticThreeTermComplex where
  d0 : A0 →ₗ[R] A1
  d1 : A1 →ₗ[R] A2
  d1_comp_d0 : d1.comp d0 = 0

namespace DeningerArithmeticThreeTermComplex

variable {R A0 A1 A2}
variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)

/-- Degree-zero cocycles. -/
def cycles0 : Submodule R A0 :=
  LinearMap.ker C.d0

/-- Degree-one cocycles. -/
def cycles1 : Submodule R A1 :=
  LinearMap.ker C.d1

/-- Degree-one boundaries. -/
def boundaries1 : Submodule R A1 :=
  LinearMap.range C.d0

/-- Degree-two boundaries. -/
def boundaries2 : Submodule R A2 :=
  LinearMap.range C.d1

/-- Every degree-one boundary is a degree-one cocycle. -/
theorem boundaries1_le_cycles1 :
    C.boundaries1 ≤ C.cycles1 := by
  rintro _ ⟨x, rfl⟩
  have hx := LinearMap.congr_fun C.d1_comp_d0 x
  simpa [cycles1] using hx

/-- Arithmetic `H⁰`: degree-zero cocycles. -/
abbrev H0 : Type _ :=
  C.cycles0

/-- Arithmetic `H¹`: degree-one cocycles modulo degree-one boundaries. -/
abbrev H1 : Type _ :=
  C.cycles1 ⧸ C.boundaries1.comap C.cycles1.subtype

/-- Arithmetic `H²`: degree-two cochains modulo degree-two boundaries. -/
abbrev H2 : Type _ :=
  A2 ⧸ C.boundaries2

/-- A degree-one cocycle represents zero exactly when it is a boundary. -/
theorem H1_mk_eq_zero_iff (x : C.cycles1) :
    (Submodule.Quotient.mk x : C.H1) = 0 ↔
      (x : A1) ∈ C.boundaries1 := by
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- A degree-two cochain represents zero exactly when it is a boundary. -/
theorem H2_mk_eq_zero_iff (x : A2) :
    (Submodule.Quotient.mk x : C.H2) = 0 ↔
      x ∈ C.boundaries2 :=
  Submodule.Quotient.mk_eq_zero C.boundaries2

end DeningerArithmeticThreeTermComplex

/-- A transverse generator commuting with a three-term arithmetic differential. -/
structure DeningerArithmeticThreeTermFlow
    extends DeningerArithmeticThreeTermComplex R A0 A1 A2 where
  theta0 : Module.End R A0
  theta1 : Module.End R A1
  theta2 : Module.End R A2
  theta_commutes_d0 : d0.comp theta0 = theta1.comp d0
  theta_commutes_d1 : d1.comp theta1 = theta2.comp d1

namespace DeningerArithmeticThreeTermFlow

variable {R A0 A1 A2}
variable (F : DeningerArithmeticThreeTermFlow R A0 A1 A2)

/-- The underlying three-term cochain complex. -/
abbrev complex : DeningerArithmeticThreeTermComplex R A0 A1 A2 :=
  F.toDeningerArithmeticThreeTermComplex

/-- `Theta` preserves degree-zero cocycles. -/
def thetaH0 : Module.End R F.complex.H0 where
  toFun x := ⟨F.theta0 x, by
    change F.d0 (F.theta0 (x : A0)) = 0
    have hcomm := LinearMap.congr_fun F.theta_commutes_d0 (x : A0)
    change F.d0 (F.theta0 (x : A0)) =
      F.theta1 (F.d0 (x : A0)) at hcomm
    rw [x.2, map_zero] at hcomm
    exact hcomm⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add F.theta0 x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul F.theta0 c x.1

/-- `Theta` preserves degree-one cocycles. -/
def thetaCycles1 :
    F.complex.cycles1 →ₗ[R] F.complex.cycles1 where
  toFun x := ⟨F.theta1 x, by
    change F.d1 (F.theta1 (x : A1)) = 0
    have hcomm := LinearMap.congr_fun F.theta_commutes_d1 (x : A1)
    change F.d1 (F.theta1 (x : A1)) =
      F.theta2 (F.d1 (x : A1)) at hcomm
    rw [x.2, map_zero] at hcomm
    exact hcomm⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add F.theta1 x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul F.theta1 c x.1

/-- `Theta` preserves the degree-one boundary submodule inside the cocycles. -/
theorem thetaCycles1_mem_boundaries
    (x : F.complex.cycles1)
    (hx : x ∈ F.complex.boundaries1.comap F.complex.cycles1.subtype) :
    F.thetaCycles1 x ∈
      F.complex.boundaries1.comap F.complex.cycles1.subtype := by
  change F.theta1 (x : A1) ∈ F.complex.boundaries1
  change (x : A1) ∈ F.complex.boundaries1 at hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨F.theta0 a, ?_⟩
  have hcomm := LinearMap.congr_fun F.theta_commutes_d0 a
  change F.d0 (F.theta0 a) = F.theta1 (F.d0 a) at hcomm
  rw [hcomm, ha]

/-- The induced transverse generator on arithmetic `H¹`. -/
def thetaH1 : Module.End R F.complex.H1 :=
  Submodule.mapQ
    (F.complex.boundaries1.comap F.complex.cycles1.subtype)
    (F.complex.boundaries1.comap F.complex.cycles1.subtype)
    F.thetaCycles1
    F.thetaCycles1_mem_boundaries

@[simp]
theorem thetaH1_mk (x : F.complex.cycles1) :
    F.thetaH1 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.thetaCycles1 x) :=
  rfl

/-- `Theta` preserves degree-two boundaries. -/
theorem theta2_mem_boundaries
    (x : A2) (hx : x ∈ F.complex.boundaries2) :
    F.theta2 x ∈ F.complex.boundaries2 := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨F.theta1 a, ?_⟩
  have hcomm := LinearMap.congr_fun F.theta_commutes_d1 a
  change F.d1 (F.theta1 a) = F.theta2 (F.d1 a) at hcomm
  rw [hcomm, ha]

/-- The induced transverse generator on arithmetic `H²`. -/
def thetaH2 : Module.End R F.complex.H2 :=
  Submodule.mapQ F.complex.boundaries2 F.complex.boundaries2
    F.theta2 F.theta2_mem_boundaries

@[simp]
theorem thetaH2_mk (x : A2) :
    F.thetaH2 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F.theta2 x) :=
  rfl

end DeningerArithmeticThreeTermFlow

end ThreeTermCohomology

end RHTower
