import GaloisForLFunctions.RHTower.EulerSquarefreeWickBinaryGaugeOrientationNoGo

/-!
# Principal-jet gauge collapse for the Euler--Wick binary tower

At a zero of one complex variable there is one cotangent coordinate.  The source-correct action
of a quadratic gauge on its homogeneous jet coordinates is therefore the sign dilation
`X ↦ ±X`.  This module proves that distinct EWQ gauge generators induce exactly the same sign
dilation in every jet degree.  More generally, no map from a Boolean cube of rank at least two to
one binary scalar phase can be faithful.

This is stronger than the auxiliary-tensor no-go: even a direct, dimension-preserving scalar sign
action on the original Xi jet collapses all independent gauge generators to one parity bit.  It
does not exclude nonlinear automorphisms of a truncated local algebra; that larger escape requires
a separate torsion-rigidity argument.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Configuration with exactly one negative binary gauge. -/
def binaryGaugeSingleFlip {I : Type*} [DecidableEq I] (i : I) : I → Bool :=
  fun j => decide (j = i)

@[simp]
theorem binaryGaugeSingleFlip_self {I : Type*} [DecidableEq I] (i : I) :
    binaryGaugeSingleFlip i i = true := by
  simp [binaryGaugeSingleFlip]

@[simp]
theorem binaryGaugeSingleFlip_ne {I : Type*} [DecidableEq I]
    {i j : I} (hij : j ≠ i) :
    binaryGaugeSingleFlip i j = false := by
  simp [binaryGaugeSingleFlip, hij]

theorem binaryGaugeSingleFlip_injective {I : Type*} [DecidableEq I] :
    Function.Injective (binaryGaugeSingleFlip : I → I → Bool) := by
  intro i j hij
  by_contra hne
  have hvalue := congrFun hij i
  simp [binaryGaugeSingleFlip, hne] at hvalue

/-- Every single gauge flip has the same full-interaction scalar character `-1`. -/
theorem orientationWalshCharacter_univ_binaryGaugeSingleFlip
    {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ
      (binaryGaugeSingleFlip i) = -1 := by
  classical
  rw [GaloisForLFunctions.HTGeometry.orientationWalshCharacter]
  rw [Finset.prod_eq_single i]
  · simp [binaryGaugeSingleFlip,
      GaloisForLFunctions.HTGeometry.primeDirichletSign]
  · intro j hj hji
    simp [binaryGaugeSingleFlip, hji,
      GaloisForLFunctions.HTGeometry.primeDirichletSign]
  · simp

/-- The source-correct one-variable sign action on the coefficient model of an order-`m` jet. -/
def binaryGaugePrincipalJetSignAction {I : Type*} [Fintype I]
    {m : ℕ} (x : I → Bool) (A : Fin m → ℂ) (j : Fin m) : ℂ :=
  GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x ^ (j : ℕ) * A j

/-- One-variable jet sign actions factor through the single full-interaction character. -/
theorem binaryGaugePrincipalJetSignAction_eq_of_character_eq
    {I : Type*} [Fintype I] {m : ℕ} {x y : I → Bool}
    (hxy : GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ x =
      GaloisForLFunctions.HTGeometry.orientationWalshCharacter Finset.univ y) :
    binaryGaugePrincipalJetSignAction (m := m) x =
      binaryGaugePrincipalJetSignAction y := by
  funext A j
  simp [binaryGaugePrincipalJetSignAction, hxy]

/-- Distinct quadratic gauge generators induce exactly the same action on every homogeneous
degree of every one-variable local divisor jet. -/
theorem binaryGaugePrincipalJetSignAction_singleFlip_eq
    {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ} (i j : I) :
    binaryGaugePrincipalJetSignAction (m := m) (binaryGaugeSingleFlip i) =
      binaryGaugePrincipalJetSignAction (binaryGaugeSingleFlip j) := by
  apply binaryGaugePrincipalJetSignAction_eq_of_character_eq
  rw [orientationWalshCharacter_univ_binaryGaugeSingleFlip,
    orientationWalshCharacter_univ_binaryGaugeSingleFlip]

/-- At binary rank at least two the direct one-variable jet sign action is not faithful. -/
theorem binaryGaugePrincipalJetSignAction_not_injective
    {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    {i j : I} (hij : i ≠ j) :
    ¬ Function.Injective
      (fun x : I → Bool => binaryGaugePrincipalJetSignAction (m := m) x) := by
  intro hinj
  have hflip : binaryGaugeSingleFlip i = binaryGaugeSingleFlip j :=
    hinj (binaryGaugePrincipalJetSignAction_singleFlip_eq i j)
  exact hij (binaryGaugeSingleFlip_injective hflip)

/-- No scalar binary phase can faithfully encode a gauge cube of rank at least two. -/
theorem binaryGaugeScalarPhase_not_injective
    {I : Type*} [Fintype I] (hI : 2 ≤ Fintype.card I)
    (phase : (I → Bool) → Bool) :
    ¬ Function.Injective phase := by
  intro hphase
  have hcard := Nat.card_le_card_of_injective phase hphase
  have hBool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_bool
  have hIndex : Nat.card I = Fintype.card I := Nat.card_eq_fintype_card
  rw [Nat.card_fun, hBool, hIndex] at hcard
  have hpow : 4 ≤ 2 ^ Fintype.card I := by
    calc
      4 = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ Fintype.card I := Nat.pow_le_pow_right (by omega) hI
  omega

end

end GaloisForLFunctions.RHTower
