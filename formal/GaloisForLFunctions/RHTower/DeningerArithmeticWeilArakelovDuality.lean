import GaloisForLFunctions.RHTower.DeningerArithmeticWeilArakelovFiber

/-!
# Weight-complementary duality on Weil--Arakelov fibers

Let a three-term Deninger leafwise complex carry a degree-two Poincare pairing.  If its
transverse generator has weight one for that pairing, then the mapping fibers at weights `n`
and `1 - n` carry a forced degree-three cochain pairing.  This is the chain-level functional
equation behind the Weil--Arakelov specialization.

The proof is pure homological algebra.  It assumes no zeta-zero description, positivity, or
Riemann-hypothesis premise.
-/

namespace RHTower

section WeilArakelovDuality

variable {R A0 A1 A2 : Type*}
variable [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup A1] [Module R A1]
variable [AddCommGroup A2] [Module R A2]

/-- The vertical map `Theta - n` at weight `n`. -/
def deningerWeilArakelovCenteredVertical
    (theta : A0 →ₗ[R] A0) (n : R) :
    A0 →ₗ[R] A0 :=
  theta - n • LinearMap.id

@[simp]
theorem deningerWeilArakelovCenteredVertical_apply
    (theta : A0 →ₗ[R] A0) (n : R) (x : A0) :
    deningerWeilArakelovCenteredVertical theta n x =
      theta x - n • x := by
  rfl

/--
Degree-`0` against degree-`3` pairing on complementary Weil--Arakelov fibers.
-/
def deningerWeilArakelovPair03
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (x : A0) (z : A2) : R :=
  pair02 x z

/--
Degree-`1` against degree-`2` pairing.  The sign is forced by the mapping-fiber differential.
-/
def deningerWeilArakelovPair12
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (x : A1 × A0) (y : A2 × A1) : R :=
  -pair11 x.1 y.2 + pair02 x.2 y.1

/--
Degree-`2` against degree-`1` pairing on complementary Weil--Arakelov fibers.
-/
def deningerWeilArakelovPair21
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (x : A2 × A1) (y : A1 × A0) : R :=
  pair02 y.2 x.1 + pair11 x.2 y.1

/-- Degree-`3` against degree-`0` pairing on complementary fibers. -/
def deningerWeilArakelovPair30
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (z : A2) (x : A0) : R :=
  pair02 x z

/--
Weight one for `Theta` makes `Theta - n` and `Theta - (1 - n)` adjoint with opposite signs
under the endpoint pairing.
-/
theorem deningerWeilArakelov_centered_pair02
    (theta0 : A0 →ₗ[R] A0)
    (theta2 : A2 →ₗ[R] A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (hTheta02 :
      ∀ x z, pair02 (theta0 x) z + pair02 x (theta2 z) = pair02 x z)
    (n : R) (x : A0) (z : A2) :
    pair02 (deningerWeilArakelovCenteredVertical theta0 n x) z +
        pair02 x
          (deningerWeilArakelovCenteredVertical theta2 (1 - n) z) = 0 := by
  simp only [deningerWeilArakelovCenteredVertical_apply, map_sub, map_smul, smul_eq_mul]
  linear_combination hTheta02 x z

/--
Weight one for `Theta` gives the same complementary adjointness law in middle degree.
-/
theorem deningerWeilArakelov_centered_pair11
    (theta1 : A1 →ₗ[R] A1)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (hTheta11 :
      ∀ x y, pair11 (theta1 x) y + pair11 x (theta1 y) = pair11 x y)
    (n : R) (x y : A1) :
    pair11 (deningerWeilArakelovCenteredVertical theta1 n x) y +
        pair11 x
          (deningerWeilArakelovCenteredVertical theta1 (1 - n) y) = 0 := by
  simp only [deningerWeilArakelovCenteredVertical_apply, map_sub, map_smul, smul_eq_mul]
  linear_combination hTheta11 x y

/--
The right-hand differential adjointness follows from left adjointness and skew-symmetry in
degree one.
-/
theorem deningerThreeTermPoincare_d_right
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (hSkew : ∀ x y, pair11 x y = -pair11 y x)
    (hD : ∀ x y, pair11 (d0 x) y + pair02 x (d1 y) = 0)
    (y : A1) (x : A0) :
    pair11 y (d0 x) - pair02 x (d1 y) = 0 := by
  rw [hSkew]
  linear_combination -(hD x y)

/--
Bottom and top differentials are graded-adjoint for the complementary fiber pairing.
-/
theorem deningerWeilArakelov_pair_D0_D2
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (theta0 : A0 →ₗ[R] A0)
    (theta2 : A2 →ₗ[R] A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (hD : ∀ x y, pair11 (d0 x) y + pair02 x (d1 y) = 0)
    (hTheta02 :
      ∀ x z, pair02 (theta0 x) z + pair02 x (theta2 z) = pair02 x z)
    (n : R) (x : A0) (z : A2) (y : A1) :
    deningerWeilArakelovPair12 pair02 pair11
          (deningerWeilArakelovD0 d0
            (deningerWeilArakelovCenteredVertical theta0 n) x)
          (z, y) +
        deningerWeilArakelovPair03 pair02 x
          (deningerWeilArakelovD2 d1
            (deningerWeilArakelovCenteredVertical theta2 (1 - n)) (z, y)) = 0 := by
  simp only [deningerWeilArakelovD0_apply, deningerWeilArakelovD2_apply,
    deningerWeilArakelovPair12, deningerWeilArakelovPair03, map_sub]
  linear_combination
    deningerWeilArakelov_centered_pair02 theta0 theta2 pair02 hTheta02 n x z -
      hD x y

/--
The two middle differentials are graded-adjoint for the complementary fiber pairing.
-/
theorem deningerWeilArakelov_pair_D1_D1
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (theta1 : A1 →ₗ[R] A1)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (hSkew : ∀ x y, pair11 x y = -pair11 y x)
    (hD : ∀ x y, pair11 (d0 x) y + pair02 x (d1 y) = 0)
    (hTheta11 :
      ∀ x y, pair11 (theta1 x) y + pair11 x (theta1 y) = pair11 x y)
    (n : R) (x y : A1) (a b : A0) :
    deningerWeilArakelovPair21 pair02 pair11
          (deningerWeilArakelovD1 d0 d1
            (deningerWeilArakelovCenteredVertical theta1 n) (x, a))
          (y, b) -
        deningerWeilArakelovPair12 pair02 pair11
          (x, a)
          (deningerWeilArakelovD1 d0 d1
            (deningerWeilArakelovCenteredVertical theta1 (1 - n)) (y, b)) = 0 := by
  simp only [deningerWeilArakelovD1_apply, deningerWeilArakelovPair21,
    deningerWeilArakelovPair12, map_sub, neg_sub]
  linear_combination
    deningerWeilArakelov_centered_pair11 theta1 pair11 hTheta11 n x y -
      hD a y -
      deningerThreeTermPoincare_d_right d0 d1 pair02 pair11 hSkew hD x b

/--
Top and bottom differentials are graded-adjoint for the complementary fiber pairing.
-/
theorem deningerWeilArakelov_pair_D2_D0
    (d0 : A0 →ₗ[R] A1)
    (d1 : A1 →ₗ[R] A2)
    (theta0 : A0 →ₗ[R] A0)
    (theta2 : A2 →ₗ[R] A2)
    (pair02 : A0 →ₗ[R] A2 →ₗ[R] R)
    (pair11 : A1 →ₗ[R] A1 →ₗ[R] R)
    (hSkew : ∀ x y, pair11 x y = -pair11 y x)
    (hD : ∀ x y, pair11 (d0 x) y + pair02 x (d1 y) = 0)
    (hTheta02 :
      ∀ x z, pair02 (theta0 x) z + pair02 x (theta2 z) = pair02 x z)
    (n : R) (z : A2) (y : A1) (x : A0) :
    deningerWeilArakelovPair30 pair02
          (deningerWeilArakelovD2 d1
            (deningerWeilArakelovCenteredVertical theta2 n) (z, y))
          x +
        deningerWeilArakelovPair21 pair02 pair11
          (z, y)
          (deningerWeilArakelovD0 d0
            (deningerWeilArakelovCenteredVertical theta0 (1 - n)) x) = 0 := by
  simp only [deningerWeilArakelovD2_apply, deningerWeilArakelovD0_apply,
    deningerWeilArakelovPair30, deningerWeilArakelovPair21, map_sub]
  linear_combination
    deningerWeilArakelov_centered_pair02 theta0 theta2 pair02 hTheta02
        (1 - n) x z +
      deningerThreeTermPoincare_d_right d0 d1 pair02 pair11 hSkew hD y x

end WeilArakelovDuality

end RHTower
