import GaloisForLFunctions.RHTower.DeningerArithmeticEndpointPurity

/-!
# Cup and Poincare descent for three-term arithmetic cohomology

This module isolates the source-independent quotient argument required by Deninger's
arithmetic cohomology.  A degree-two cochain pairing satisfying residue adjunction and
degree-one skew-symmetry descends to `H⁰ × H²` and `H¹ × H¹`.  The exact cochain radical
criterion is equivalent to separation of the descended middle pairing.

No analytic zeta model, zero set, positivity premise, or Riemann hypothesis occurs here.
-/

namespace RHTower

section ThreeTermCupDescent

variable {R A0 A1 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/-- Chain-level degree-two cup-trace data on a three-term arithmetic complex. -/
structure DeningerArithmeticThreeTermCupPairing
    (C : DeningerArithmeticThreeTermComplex R A0 A1 A2) where
  pair02 : A0 →ₗ[R] A2 →ₗ[R] R
  pair11 : A1 →ₗ[R] A1 →ₗ[R] R
  differential_adjoint :
    ∀ x y, pair11 (C.d0 x) y + pair02 x (C.d1 y) = 0
  skew :
    ∀ x y, pair11 x y = -pair11 y x

namespace DeningerArithmeticThreeTermCupPairing

variable (C : DeningerArithmeticThreeTermComplex R A0 A1 A2)
variable (P : DeningerArithmeticThreeTermCupPairing C)

/-- Degree-two boundaries pair trivially with degree-zero cocycles. -/
theorem boundaries2_le_pair02_ker (x : C.H0) :
    C.boundaries2 ≤ LinearMap.ker (P.pair02 x) := by
  rintro _ ⟨y, rfl⟩
  change P.pair02 (x : A0) (C.d1 y) = 0
  have h := P.differential_adjoint (x : A0) y
  have hx : C.d0 (x : A0) = 0 := x.2
  rw [hx] at h
  simpa only [map_zero, LinearMap.zero_apply, zero_add] using h

/-- The endpoint cup-trace pairing descended in its degree-two variable. -/
def pairH02 (x : C.H0) : C.H2 →ₗ[R] R :=
  C.boundaries2.liftQ (P.pair02 x) (P.boundaries2_le_pair02_ker C x)

@[simp]
theorem pairH02_mkQ (x : C.H0) (z : A2) :
    P.pairH02 C x (C.boundaries2.mkQ z) =
      P.pair02 (x : A0) z := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ C.boundaries2
      (P.pair02 x) (P.boundaries2_le_pair02_ker C x)) z

/-- The fully bilinear endpoint cup-trace pairing on `H⁰ × H²`. -/
def pairH02Linear : C.H0 →ₗ[R] Module.Dual R C.H2 where
  toFun x := P.pairH02 C x
  map_add' x x' := by
    apply LinearMap.ext
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective C.boundaries2 q
    change
      P.pair02 ((x + x' : C.H0) : A0) z =
        P.pair02 (x : A0) z + P.pair02 (x' : A0) z
    simp
  map_smul' r x := by
    apply LinearMap.ext
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective C.boundaries2 q
    change
      P.pair02 ((r • x : C.H0) : A0) z =
        r • P.pair02 (x : A0) z
    simp

@[simp]
theorem pairH02Linear_mkQ (x : C.H0) (z : A2) :
    P.pairH02Linear C x (C.boundaries2.mkQ z) =
      P.pair02 (x : A0) z :=
  P.pairH02_mkQ C x z

/-- Degree-one cup-trace restricted to cocycles in both variables. -/
def pairCycles11 (y : C.cycles1) : C.cycles1 →ₗ[R] R where
  toFun x := P.pair11 (x : A1) (y : A1)
  map_add' x x' := by
    simp
  map_smul' r x := by
    simp

/-- Degree-one boundaries annihilate degree-one cocycles in the left variable. -/
theorem boundaries1_le_pairCycles11_ker (y : C.cycles1) :
    C.boundaries1.comap C.cycles1.subtype ≤
      LinearMap.ker (P.pairCycles11 C y) := by
  intro x hx
  change (x : A1) ∈ C.boundaries1 at hx
  obtain ⟨a, ha⟩ := hx
  change P.pair11 (x : A1) (y : A1) = 0
  have h := P.differential_adjoint a (y : A1)
  rw [y.2, map_zero, add_zero] at h
  rw [← ha]
  exact h

/-- Descend the left degree-one variable through boundaries. -/
def pairH11Left (y : C.cycles1) : C.H1 →ₗ[R] R :=
  (C.boundaries1.comap C.cycles1.subtype).liftQ
    (P.pairCycles11 C y) (P.boundaries1_le_pairCycles11_ker C y)

@[simp]
theorem pairH11Left_mkQ (x y : C.cycles1) :
    P.pairH11Left C y
        ((C.boundaries1.comap C.cycles1.subtype).mkQ x) =
      P.pair11 (x : A1) (y : A1) := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ
      (C.boundaries1.comap C.cycles1.subtype)
      (P.pairCycles11 C y)
      (P.boundaries1_le_pairCycles11_ker C y)) x

/-- A cocycle determines the functional obtained after descending the left variable. -/
def cycles1ToH1Dual :
    C.cycles1 →ₗ[R] Module.Dual R C.H1 where
  toFun y := P.pairH11Left C y
  map_add' y y' := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      Submodule.Quotient.mk_surjective
        (C.boundaries1.comap C.cycles1.subtype) q
    change
      P.pair11 (x : A1) ((y + y' : C.cycles1) : A1) =
        P.pair11 (x : A1) (y : A1) +
          P.pair11 (x : A1) (y' : A1)
    simp
  map_smul' r y := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ :=
      Submodule.Quotient.mk_surjective
        (C.boundaries1.comap C.cycles1.subtype) q
    change
      P.pair11 (x : A1) ((r • y : C.cycles1) : A1) =
        r • P.pair11 (x : A1) (y : A1)
    simp

/-- Skew-symmetry makes boundaries vanish in the remaining degree-one variable. -/
theorem boundaries1_le_cycles1ToH1Dual_ker :
    C.boundaries1.comap C.cycles1.subtype ≤
      LinearMap.ker (P.cycles1ToH1Dual C) := by
  intro y hy
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (C.boundaries1.comap C.cycles1.subtype) q
  change P.pair11 (x : A1) (y : A1) = 0
  rw [P.skew]
  have hzero :=
    P.boundaries1_le_pairCycles11_ker C x hy
  change P.pair11 (y : A1) (x : A1) = 0 at hzero
  rw [hzero, neg_zero]

/-- The fully descended degree-one cup-trace pairing. -/
def pairH11 : C.H1 →ₗ[R] Module.Dual R C.H1 :=
  (C.boundaries1.comap C.cycles1.subtype).liftQ
    (P.cycles1ToH1Dual C) (P.boundaries1_le_cycles1ToH1Dual_ker C)

@[simp]
theorem pairH11_mkQ (y : C.cycles1) :
    P.pairH11 C
        ((C.boundaries1.comap C.cycles1.subtype).mkQ y) =
      P.cycles1ToH1Dual C y := by
  exact LinearMap.congr_fun
    (Submodule.liftQ_mkQ
      (C.boundaries1.comap C.cycles1.subtype)
      (P.cycles1ToH1Dual C)
      (P.boundaries1_le_cycles1ToH1Dual_ker C)) y

@[simp]
theorem pairH11_mkQ_mkQ (x y : C.cycles1) :
    P.pairH11 C
        ((C.boundaries1.comap C.cycles1.subtype).mkQ y)
        ((C.boundaries1.comap C.cycles1.subtype).mkQ x) =
      P.pair11 (x : A1) (y : A1) := by
  rw [P.pairH11_mkQ C]
  exact P.pairH11Left_mkQ C x y

/-- The descended middle pairing remains skew-symmetric. -/
theorem pairH11_skew (x y : C.H1) :
    P.pairH11 C x y = -P.pairH11 C y x := by
  obtain ⟨x', rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (C.boundaries1.comap C.cycles1.subtype) x
  obtain ⟨y', rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (C.boundaries1.comap C.cycles1.subtype) y
  calc
    P.pairH11 C
        ((C.boundaries1.comap C.cycles1.subtype).mkQ x')
        ((C.boundaries1.comap C.cycles1.subtype).mkQ y') =
        P.pair11 (y' : A1) (x' : A1) :=
      P.pairH11_mkQ_mkQ C y' x'
    _ = -P.pair11 (x' : A1) (y' : A1) := P.skew _ _
    _ = -P.pairH11 C
        ((C.boundaries1.comap C.cycles1.subtype).mkQ y')
        ((C.boundaries1.comap C.cycles1.subtype).mkQ x') := by
      rw [P.pairH11_mkQ_mkQ C]

/-- Cochain radical after one variable has been descended. -/
def radical1 : Submodule R C.cycles1 :=
  LinearMap.ker (P.cycles1ToH1Dual C)

/-- Exact radical equality is equivalent to separation of the descended middle pairing. -/
theorem pairH11_separating_iff_radical1_eq_boundaries1 :
    (∀ y : C.H1, (∀ x : C.H1, P.pairH11 C y x = 0) → y = 0) ↔
      P.radical1 C =
        C.boundaries1.comap C.cycles1.subtype := by
  let B := C.boundaries1.comap C.cycles1.subtype
  constructor
  · intro hsep
    apply le_antisymm
    · intro y hy
      apply (Submodule.Quotient.mk_eq_zero B).mp
      apply hsep
      intro x
      change P.cycles1ToH1Dual C y x = 0
      rw [show P.cycles1ToH1Dual C y = 0 from hy]
      rfl
    · simpa [radical1] using P.boundaries1_le_cycles1ToH1Dual_ker C
  · intro hrad y hy
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective B y
    apply (Submodule.Quotient.mk_eq_zero B).mpr
    change y' ∈ C.boundaries1.comap C.cycles1.subtype
    rw [← hrad]
    change P.cycles1ToH1Dual C y' = 0
    apply LinearMap.ext
    intro x
    rw [← P.pairH11_mkQ C y']
    exact hy x

end DeningerArithmeticThreeTermCupPairing

end ThreeTermCupDescent

section ThreeTermCupFlowDescent

variable {R A0 A1 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/-- Chain-level weight-one compatibility between transverse flow and cup-trace. -/
structure DeningerArithmeticThreeTermWeightOneCup
    (F : DeningerArithmeticThreeTermFlow R A0 A1 A2)
    (P : DeningerArithmeticThreeTermCupPairing F.complex) where
  endpoint_weight :
    ∀ x z,
      P.pair02 (F.theta0 x) z + P.pair02 x (F.theta2 z) =
        P.pair02 x z
  middle_weight :
    ∀ x y,
      P.pair11 (F.theta1 x) y + P.pair11 x (F.theta1 y) =
        P.pair11 x y

namespace DeningerArithmeticThreeTermWeightOneCup

variable
  (F : DeningerArithmeticThreeTermFlow R A0 A1 A2)
  (P : DeningerArithmeticThreeTermCupPairing F.complex)
  (W : DeningerArithmeticThreeTermWeightOneCup F P)

/-- The endpoint weight-one law descends to `H⁰ × H²`. -/
theorem endpoint_weight_on_cohomology
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    (x : F.complex.H0) (z : F.complex.H2) :
    P.pairH02Linear F.complex (F.thetaH0 x) z +
        P.pairH02Linear F.complex x (F.thetaH2 z) =
      P.pairH02Linear F.complex x z := by
  obtain ⟨z', rfl⟩ :=
    Submodule.Quotient.mk_surjective F.complex.boundaries2 z
  simp only [DeningerArithmeticThreeTermFlow.thetaH2_mk]
  exact
    DeningerArithmeticThreeTermWeightOneCup.endpoint_weight
      W (x : A0) z'

/-- The middle weight-one law descends to `H¹ × H¹`. -/
theorem middle_weight_on_cohomology
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    (x y : F.complex.H1) :
    P.pairH11 F.complex (F.thetaH1 x) y +
        P.pairH11 F.complex x (F.thetaH1 y) =
      P.pairH11 F.complex x y := by
  let B := F.complex.boundaries1.comap F.complex.cycles1.subtype
  obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective B x
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective B y
  simp only [DeningerArithmeticThreeTermFlow.thetaH1_mk]
  calc
    P.pairH11 F.complex (Submodule.Quotient.mk (F.thetaCycles1 x'))
          (Submodule.Quotient.mk y') +
        P.pairH11 F.complex (Submodule.Quotient.mk x')
          (Submodule.Quotient.mk (F.thetaCycles1 y')) =
        P.pair11 (y' : A1) (F.theta1 (x' : A1)) +
          P.pair11 (F.theta1 (y' : A1)) (x' : A1) := by
      congr 1
    _ = P.pair11 (y' : A1) (x' : A1) := by
      simpa [add_comm] using
        DeningerArithmeticThreeTermWeightOneCup.middle_weight
          W (y' : A1) (x' : A1)
    _ = P.pairH11 F.complex (Submodule.Quotient.mk x')
          (Submodule.Quotient.mk y') :=
      (P.pairH11_mkQ_mkQ F.complex y' x').symm

/--
Trivial `H⁰` flow plus separating endpoint cup-trace forces the top cohomological generator
to be the identity.
-/
theorem thetaH2_eq_id
    (W : DeningerArithmeticThreeTermWeightOneCup F P)
    (htheta0 : F.thetaH0 = 0)
    (hseparating :
      ∀ z : F.complex.H2,
        (∀ x : F.complex.H0, P.pairH02Linear F.complex x z = 0) →
          z = 0) :
    F.thetaH2 = LinearMap.id :=
  deningerTheta2_eq_id_of_theta0_eq_zero_of_endpointPairing
    F.thetaH0 F.thetaH2 (P.pairH02Linear F.complex)
    (DeningerArithmeticThreeTermWeightOneCup.endpoint_weight_on_cohomology
      F P W) htheta0 hseparating

end DeningerArithmeticThreeTermWeightOneCup

end ThreeTermCupFlowDescent

end RHTower
