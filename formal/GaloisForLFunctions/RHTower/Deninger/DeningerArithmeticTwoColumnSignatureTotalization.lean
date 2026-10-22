import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticThreeTermCupDescent

/-!
# Two-column Rost--Schmid/signature totalization

This module formalizes the algebraic total complex underlying
`DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`.  Two Rost--Schmid columns in internal
degrees zero and one, together with one archimedean orientation summand in top
degree, produce a three-term cochain complex.

The transverse Deninger flow is not a differential here.  No zeta function,
zero set, spectral premise, positivity premise, or Riemann hypothesis enters.
-/

namespace RHTower

section TwoColumnSignatureTotalization

variable {R G00 G10 G01 G11 S : Type*}
variable [CommRing R]
variable [AddCommGroup G00] [Module R G00]
variable [AddCommGroup G10] [Module R G10]
variable [AddCommGroup G01] [Module R G01]
variable [AddCommGroup G11] [Module R G11]
variable [AddCommGroup S] [Module R S]

/--
Degree-zero total differential.  Its two components are the horizontal
Rost--Schmid residue and the internal coefficient differential.
-/
def deningerTwoColumnSignatureD0
    (horizontal0 : G00 →ₗ[R] G10)
    (vertical0 : G00 →ₗ[R] G01) :
    G00 →ₗ[R] G10 × G01 :=
  horizontal0.prod vertical0

/--
Degree-one total differential.  The first component is the signed
two-column total differential.  The second is the archimedean signature
boundary.
-/
def deningerTwoColumnSignatureD1
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S) :
    G10 × G01 →ₗ[R] G11 × S where
  toFun x :=
    (vertical1 x.1 - horizontal1 x.2,
      signature10 x.1 + signature01 x.2)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    · abel
    · abel
  map_smul' c x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
    · exact (smul_sub c (vertical1 x.1) (horizontal1 x.2)).symm
    · exact (smul_add c (signature10 x.1) (signature01 x.2)).symm

@[simp]
theorem deningerTwoColumnSignatureD0_apply
    (horizontal0 : G00 →ₗ[R] G10)
    (vertical0 : G00 →ₗ[R] G01)
    (a : G00) :
    deningerTwoColumnSignatureD0 horizontal0 vertical0 a =
      (horizontal0 a, vertical0 a) :=
  rfl

@[simp]
theorem deningerTwoColumnSignatureD1_apply
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S)
    (x : G10 × G01) :
    deningerTwoColumnSignatureD1
        horizontal1 vertical1 signature10 signature01 x =
      (vertical1 x.1 - horizontal1 x.2,
        signature10 x.1 + signature01 x.2) :=
  rfl

/--
The total differential squares to zero precisely from commutativity of the
Rost--Schmid square and reciprocity of the two signature boundary components.
-/
theorem deningerTwoColumnSignatureD1_comp_D0
    (horizontal0 : G00 →ₗ[R] G10)
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical0 : G00 →ₗ[R] G01)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S)
    (hSquare :
      vertical1.comp horizontal0 = horizontal1.comp vertical0)
    (hSignature :
      signature10.comp horizontal0 + signature01.comp vertical0 = 0) :
    (deningerTwoColumnSignatureD1
        horizontal1 vertical1 signature10 signature01).comp
      (deningerTwoColumnSignatureD0 horizontal0 vertical0) = 0 := by
  apply LinearMap.ext
  intro a
  ext
  · have ha := LinearMap.congr_fun hSquare a
    change vertical1 (horizontal0 a) - horizontal1 (vertical0 a) = 0
    exact sub_eq_zero.mpr ha
  · have ha := LinearMap.congr_fun hSignature a
    change signature10 (horizontal0 a) + signature01 (vertical0 a) = 0
    simpa using ha

/--
The three-term arithmetic cochain complex associated with a commuting
two-column residue square and an archimedean reciprocity boundary.
-/
def deningerTwoColumnSignatureComplex
    (horizontal0 : G00 →ₗ[R] G10)
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical0 : G00 →ₗ[R] G01)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S)
    (hSquare :
      vertical1.comp horizontal0 = horizontal1.comp vertical0)
    (hSignature :
      signature10.comp horizontal0 + signature01.comp vertical0 = 0) :
    DeningerArithmeticThreeTermComplex
      R G00 (G10 × G01) (G11 × S) where
  d0 := deningerTwoColumnSignatureD0 horizontal0 vertical0
  d1 :=
    deningerTwoColumnSignatureD1
      horizontal1 vertical1 signature10 signature01
  d1_comp_d0 :=
    deningerTwoColumnSignatureD1_comp_D0
      horizontal0 horizontal1 vertical0 vertical1
      signature10 signature01 hSquare hSignature

/--
**A nonzero archimedean `k`-invariant creates no fourth term.**  Adding any further component to
the signature boundary leaves the same three total degrees; only the reciprocity identity of the
degree-one differential changes.
-/
def deningerTwoColumnSignatureComplexKInvariant
    (horizontal0 : G00 →ₗ[R] G10)
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical0 : G00 →ₗ[R] G01)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 kInvariant : G01 →ₗ[R] S)
    (hSquare :
      vertical1.comp horizontal0 = horizontal1.comp vertical0)
    (hSignature :
      signature10.comp horizontal0 + (signature01 + kInvariant).comp vertical0 = 0) :
    DeningerArithmeticThreeTermComplex
      R G00 (G10 × G01) (G11 × S) :=
  deningerTwoColumnSignatureComplex horizontal0 horizontal1 vertical0 vertical1
    signature10 (signature01 + kInvariant) hSquare hSignature

/-- Componentwise endomorphism on a product of coefficient columns. -/
def deningerTwoColumnProductEnd
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
theorem deningerTwoColumnProductEnd_apply
    {A B : Type*}
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    (thetaA : Module.End R A)
    (thetaB : Module.End R B)
    (x : A × B) :
    deningerTwoColumnProductEnd thetaA thetaB x =
      (thetaA x.1, thetaB x.2) :=
  rfl

/--
Componentwise transverse flow on the two-column/signature total complex.
The six commutation identities are exactly the naturality obligations for
the two residue maps, the internal differential, and the real signature
boundary.
-/
def deningerTwoColumnSignatureFlow
    (horizontal0 : G00 →ₗ[R] G10)
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical0 : G00 →ₗ[R] G01)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S)
    (hSquare :
      vertical1.comp horizontal0 = horizontal1.comp vertical0)
    (hSignature :
      signature10.comp horizontal0 + signature01.comp vertical0 = 0)
    (theta00 : Module.End R G00)
    (theta10 : Module.End R G10)
    (theta01 : Module.End R G01)
    (theta11 : Module.End R G11)
    (thetaS : Module.End R S)
    (hHorizontal0 : horizontal0.comp theta00 = theta10.comp horizontal0)
    (hVertical0 : vertical0.comp theta00 = theta01.comp vertical0)
    (hHorizontal1 : horizontal1.comp theta01 = theta11.comp horizontal1)
    (hVertical1 : vertical1.comp theta10 = theta11.comp vertical1)
    (hSignature10 : signature10.comp theta10 = thetaS.comp signature10)
    (hSignature01 : signature01.comp theta01 = thetaS.comp signature01) :
    DeningerArithmeticThreeTermFlow
      R G00 (G10 × G01) (G11 × S) where
  toDeningerArithmeticThreeTermComplex :=
    deningerTwoColumnSignatureComplex
      horizontal0 horizontal1 vertical0 vertical1
      signature10 signature01 hSquare hSignature
  theta0 := theta00
  theta1 := deningerTwoColumnProductEnd theta10 theta01
  theta2 := deningerTwoColumnProductEnd theta11 thetaS
  theta_commutes_d0 := by
    apply LinearMap.ext
    intro a
    ext
    · exact LinearMap.congr_fun hHorizontal0 a
    · exact LinearMap.congr_fun hVertical0 a
  theta_commutes_d1 := by
    apply LinearMap.ext
    rintro ⟨c, b⟩
    ext
    · have hc := LinearMap.congr_fun hVertical1 c
      have hb := LinearMap.congr_fun hHorizontal1 b
      change vertical1 (theta10 c) = theta11 (vertical1 c) at hc
      change horizontal1 (theta01 b) = theta11 (horizontal1 b) at hb
      change
        vertical1 (theta10 c) - horizontal1 (theta01 b) =
          theta11 (vertical1 c - horizontal1 b)
      rw [hc, hb, map_sub]
    · have hc := LinearMap.congr_fun hSignature10 c
      have hb := LinearMap.congr_fun hSignature01 b
      change signature10 (theta10 c) = thetaS (signature10 c) at hc
      change signature01 (theta01 b) = thetaS (signature01 b) at hb
      change
        signature10 (theta10 c) + signature01 (theta01 b) =
          thetaS (signature10 c + signature01 b)
      rw [hc, hb, map_add]

/--
Endpoint cup--trace on the total complex, assembled from the finite-column
top trace and the archimedean signature trace.
-/
def deningerTwoColumnPair02
    (topPair : G00 →ₗ[R] G11 →ₗ[R] R)
    (signaturePair : G00 →ₗ[R] S →ₗ[R] R) :
    G00 →ₗ[R] (G11 × S) →ₗ[R] R where
  toFun a :=
    { toFun := fun z => topPair a z.1 + signaturePair a z.2
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add, map_add]
        abel
      map_smul' := by
        intro c x
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
        exact (smul_add c (topPair a x.1) (signaturePair a x.2)).symm }
  map_add' a a' := by
    apply LinearMap.ext
    intro z
    change
      topPair (a + a') z.1 + signaturePair (a + a') z.2 =
        (topPair a z.1 + signaturePair a z.2) +
          (topPair a' z.1 + signaturePair a' z.2)
    simp only [map_add, LinearMap.add_apply]
    abel
  map_smul' c a := by
    apply LinearMap.ext
    intro z
    simp only [map_smul, LinearMap.smul_apply]
    exact (smul_add c (topPair a z.1) (signaturePair a z.2)).symm

/--
Alternating middle cup--trace on the total complex.  It is the signed cross
pairing between the residue column and the internal degree-one column.
-/
def deningerTwoColumnPair11
    (crossPair : G10 →ₗ[R] G01 →ₗ[R] R) :
    (G10 × G01) →ₗ[R] (G10 × G01) →ₗ[R] R where
  toFun x :=
    { toFun := fun y => crossPair x.1 y.2 - crossPair y.1 x.2
      map_add' := by
        intro y y'
        change
          crossPair x.1 (y + y').2 -
              crossPair (y + y').1 x.2 =
            (crossPair x.1 y.2 - crossPair y.1 x.2) +
              (crossPair x.1 y'.2 - crossPair y'.1 x.2)
        simp only [Prod.fst_add, Prod.snd_add, map_add,
          LinearMap.add_apply]
        abel
      map_smul' := by
        intro c y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul]
        exact (smul_sub c (crossPair x.1 y.2) (crossPair y.1 x.2)).symm }
  map_add' x x' := by
    apply LinearMap.ext
    intro y
    change
      crossPair (x + x').1 y.2 -
          crossPair y.1 (x + x').2 =
        (crossPair x.1 y.2 - crossPair y.1 x.2) +
          (crossPair x'.1 y.2 - crossPair y.1 x'.2)
    simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    abel
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      LinearMap.smul_apply]
    exact (smul_sub c (crossPair x.1 y.2) (crossPair y.1 x.2)).symm

@[simp]
theorem deningerTwoColumnPair02_apply
    (topPair : G00 →ₗ[R] G11 →ₗ[R] R)
    (signaturePair : G00 →ₗ[R] S →ₗ[R] R)
    (a : G00) (z : G11 × S) :
    deningerTwoColumnPair02 topPair signaturePair a z =
      topPair a z.1 + signaturePair a z.2 :=
  rfl

@[simp]
theorem deningerTwoColumnPair11_apply
    (crossPair : G10 →ₗ[R] G01 →ₗ[R] R)
    (x y : G10 × G01) :
    deningerTwoColumnPair11 crossPair x y =
      crossPair x.1 y.2 - crossPair y.1 x.2 :=
  rfl

/--
The two local adjunction identities assemble the endpoint and middle traces
into a chain-level cup pairing on the arithmetic total complex.
-/
def deningerTwoColumnCupPairing
    (horizontal0 : G00 →ₗ[R] G10)
    (horizontal1 : G01 →ₗ[R] G11)
    (vertical0 : G00 →ₗ[R] G01)
    (vertical1 : G10 →ₗ[R] G11)
    (signature10 : G10 →ₗ[R] S)
    (signature01 : G01 →ₗ[R] S)
    (hSquare :
      vertical1.comp horizontal0 = horizontal1.comp vertical0)
    (hSignature :
      signature10.comp horizontal0 + signature01.comp vertical0 = 0)
    (topPair : G00 →ₗ[R] G11 →ₗ[R] R)
    (signaturePair : G00 →ₗ[R] S →ₗ[R] R)
    (crossPair : G10 →ₗ[R] G01 →ₗ[R] R)
    (hAdj10 :
      ∀ a c,
        -crossPair c (vertical0 a) +
            topPair a (vertical1 c) +
            signaturePair a (signature10 c) = 0)
    (hAdj01 :
      ∀ a b,
        crossPair (horizontal0 a) b -
            topPair a (horizontal1 b) +
            signaturePair a (signature01 b) = 0) :
    DeningerArithmeticThreeTermCupPairing
      (deningerTwoColumnSignatureComplex
        horizontal0 horizontal1 vertical0 vertical1
        signature10 signature01 hSquare hSignature) where
  pair02 := deningerTwoColumnPair02 topPair signaturePair
  pair11 := deningerTwoColumnPair11 crossPair
  differential_adjoint := by
    rintro a ⟨c, b⟩
    change
      (crossPair (horizontal0 a) b - crossPair c (vertical0 a)) +
          (topPair a (vertical1 c - horizontal1 b) +
            signaturePair a (signature10 c + signature01 b)) = 0
    simp only [map_sub, map_add]
    have hc := hAdj10 a c
    have hb := hAdj01 a b
    linear_combination hc + hb
  skew := by
    rintro ⟨c, b⟩ ⟨c', b'⟩
    change
      crossPair c b' - crossPair c' b =
        -(crossPair c' b - crossPair c b')
    ring

end TwoColumnSignatureTotalization

end RHTower
