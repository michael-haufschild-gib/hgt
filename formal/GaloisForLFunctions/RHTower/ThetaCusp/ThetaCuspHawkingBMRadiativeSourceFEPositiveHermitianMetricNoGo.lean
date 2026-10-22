import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMRadiativeSourceFECoherentCancellationNoGo

/-!
# Positive Hermitian geometry for radiative source-FE transport: no-go

HC89 constructs actual Green-dressed source-functional-equation transport and proves bright
reflected Ward cancellation off the critical line. This module attacks strongest remaining
selection objection: perhaps positivity or Hermiticity forces transport weights to be fixed or
reflection-real and therefore recovers RH.

The actual radiative cocycle lifts to a conjugate-linear involution on every finite Xi packet.
Symmetrizing ordinary finite Hermitian geometry along this involution constructs a positive-
definite Hermitian form for which actual radiative transport is antiunitary. At orbit level,
cocycle modulus itself supplies a strictly positive diagonal weight satisfying exact gain balance.
These structures coexist with HC89's nonzero off-line bright-pair cancellation.

Thus positivity/Hermiticity alone cannot distinguish critical-line copies. Surviving burden is
strictly stronger: derive fixed, source-independent, or reflection-real metric data before
transport, or prove copywise darkness from local dynamics.

`[NEW] [POSITIVE HERMITIAN METRIC] [ANTIUNITARY TRANSPORT] [BRIGHT CANCELLATION] [NO-GO]`
-/

open Complex Real
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Actual Green/source-FE transport lifted to finite Xi packets. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport :
    HBXiPeierlsPacket →ₗ⋆[ℂ] HBXiPeierlsPacket where
  toFun x :=
    hbXiPeierlsWeightedPacket
      (fun q => hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
        (xiZeroCopyReflectEquiv q))
      ((Finsupp.domCongr xiZeroCopyReflectEquiv)
        (hbXiPeierlsPacketConjugation x))
  map_add' x y := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
    ring
  map_smul' c x := by
    ext q
    simp [Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply, smul_eq_mul]
    ring

private theorem hc90_xiZeroCopyReflectEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv.symm q = xiZeroCopyReflectEquiv q := by
  apply xiZeroCopyReflectEquiv.injective
  simp

@[simp]
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_apply
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x q =
      hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
          (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (x (xiZeroCopyReflectEquiv q)) := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport,
    Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    hc90_xiZeroCopyReflectEquiv_symm_apply]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_single
    (q : XiZeroCopy) (c : ℂ) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport
        (Finsupp.single q c) =
      Finsupp.single (xiZeroCopyReflectEquiv q)
        (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q *
          (starRingEnd ℂ) c) := by
  classical
  ext r
  by_cases h : r = xiZeroCopyReflectEquiv q
  · subst r
    simp
  · have hRq : xiZeroCopyReflectEquiv r ≠ q := by
      intro heq
      apply h
      rw [← heq, xiZeroCopyReflectEquiv_apply_apply]
    simp [h, hRq]

/-- Actual radiative packet transport remains an anti-linear involution. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_involutive
    (x : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x) = x := by
  ext q
  simp only [hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_apply,
    xiZeroCopyReflectEquiv_apply_apply, map_mul]
  have hcocycle :=
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive q
  have hcc : (starRingEnd ℂ) ((starRingEnd ℂ) (x q)) = x q := by simp
  rw [hcc, ← mul_assoc, hcocycle, one_mul]

/-- Strictly positive diagonal orbit weight supplied by radiative cocycle modulus. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight
    (q : XiZeroCopy) : ℝ :=
  ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight_pos
    (q : XiZeroCopy) :
    0 < hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight q := by
  exact norm_pos_iff.mpr
    (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero q)

/-- The positive modulus weight exactly compensates radiative FE gain on each orbit. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight_balance
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight
          (xiZeroCopyReflectEquiv q) *
        Complex.normSq
          (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight q := by
  have hinv := congrArg norm
    (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive q)
  have hnorm :
      ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
          (xiZeroCopyReflectEquiv q)‖ *
        ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ = 1 := by
    simpa [norm_mul] using hinv
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight,
    Complex.normSq_eq_norm_sq]
  calc
    ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
        (xiZeroCopyReflectEquiv q)‖ *
          ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ ^ (2 : ℕ) =
      (‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle
          (xiZeroCopyReflectEquiv q)‖ *
        ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖) *
          ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ := by ring
    _ = ‖hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q‖ := by
      rw [hnorm, one_mul]

def hbXiPeierlsFiniteHermitianEnergy (x : HBXiPeierlsPacket) : ℝ :=
  ∑ q ∈ x.support, Complex.normSq (x q)

theorem hbXiPeierlsFiniteHermitianEnergy_nonneg (x : HBXiPeierlsPacket) : 0 ≤ hbXiPeierlsFiniteHermitianEnergy x := by
  exact Finset.sum_nonneg fun q _ => Complex.normSq_nonneg (x q)

theorem hbXiPeierlsFiniteHermitianEnergy_eq_zero_iff (x : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianEnergy x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro h
    have hall : ∀ q ∈ x.support, Complex.normSq (x q) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ => Complex.normSq_nonneg (x q))).mp h
    ext q
    by_cases hq : q ∈ x.support
    · exact Complex.normSq_eq_zero.mp (hall q hq)
    · rw [Finsupp.mem_support_iff] at hq
      exact not_ne_iff.mp hq
  · intro h
    subst x
    simp [hbXiPeierlsFiniteHermitianEnergy]

def hbXiPeierlsFiniteHermitianForm (x y : HBXiPeierlsPacket) : ℂ :=
  hbXiPeierlsDot (hbXiPeierlsPacketConjugation x) y

theorem hbXiPeierlsDot_packetConjugation_hc90 (x y : HBXiPeierlsPacket) :
    hbXiPeierlsDot (hbXiPeierlsPacketConjugation x)
        (hbXiPeierlsPacketConjugation y) =
      (starRingEnd ℂ) (hbXiPeierlsDot x y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [hbXiPeierlsDot]
  | add f g hf hg =>
      rw [map_add, hbXiPeierlsDot_add_left, hf, hg,
        hbXiPeierlsDot_add_left, map_add]
  | single q c =>
      rw [hbXiPeierlsPacketConjugation_single,
        hbXiPeierlsDot_single, hbXiPeierlsDot_single,
        hbXiPeierlsPacketConjugation_apply, map_mul]

theorem hbXiPeierlsFiniteHermitianForm_conj_symm (x y : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm y x = (starRingEnd ℂ) (hbXiPeierlsFiniteHermitianForm x y) := by
  rw [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot_comm]
  have hcc : hbXiPeierlsPacketConjugation
      (hbXiPeierlsPacketConjugation x) = x := by
    ext q
    simp
  calc
    hbXiPeierlsDot x (hbXiPeierlsPacketConjugation y) =
        hbXiPeierlsDot
          (hbXiPeierlsPacketConjugation (hbXiPeierlsPacketConjugation x))
          (hbXiPeierlsPacketConjugation y) := by rw [hcc]
    _ = (starRingEnd ℂ)
        (hbXiPeierlsDot (hbXiPeierlsPacketConjugation x) y) :=
      hbXiPeierlsDot_packetConjugation_hc90 (hbXiPeierlsPacketConjugation x) y

theorem hbXiPeierlsFiniteHermitianForm_self (x : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm x x = (hbXiPeierlsFiniteHermitianEnergy x : ℂ) := by
  classical
  have hsupp : (hbXiPeierlsPacketConjugation x).support = x.support := by
    ext q
    simp [Finsupp.mem_support_iff]
  rw [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot, Finsupp.linearCombination_apply]
  change (∑ q ∈ (hbXiPeierlsPacketConjugation x).support,
      (starRingEnd ℂ) (x q) * x q) = (hbXiPeierlsFiniteHermitianEnergy x : ℂ)
  rw [hsupp]
  simp only [← Complex.normSq_eq_conj_mul_self, hbXiPeierlsFiniteHermitianEnergy]
  norm_cast

theorem hbXiPeierlsFiniteHermitianForm_add_left
    (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm (x + y) z =
      hbXiPeierlsFiniteHermitianForm x z +
        hbXiPeierlsFiniteHermitianForm y z := by
  simp [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot_add_left]

theorem hbXiPeierlsFiniteHermitianForm_smul_left
    (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm (c • x) y =
      (starRingEnd ℂ) c * hbXiPeierlsFiniteHermitianForm x y := by
  simp [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot_smul_left]

theorem hbXiPeierlsFiniteHermitianForm_add_right
    (x y z : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm x (y + z) =
      hbXiPeierlsFiniteHermitianForm x y +
        hbXiPeierlsFiniteHermitianForm x z := by
  simp [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot_add_right]

theorem hbXiPeierlsFiniteHermitianForm_smul_right
    (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPeierlsFiniteHermitianForm x (c • y) =
      c * hbXiPeierlsFiniteHermitianForm x y := by
  simp [hbXiPeierlsFiniteHermitianForm, hbXiPeierlsDot_smul_right]

/-- Canonical positive Hermitian form obtained by symmetrizing along actual radiative transport. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm
    (x y : HBXiPeierlsPacket) : ℂ :=
  hbXiPeierlsFiniteHermitianForm x y +
    hbXiPeierlsFiniteHermitianForm
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y)
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)

/-- Real quadratic energy underlying the radiative Hermitian form. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy
    (x : HBXiPeierlsPacket) : ℝ :=
  hbXiPeierlsFiniteHermitianEnergy x +
    hbXiPeierlsFiniteHermitianEnergy (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_add_left
    (x y z : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm (x + y) z =
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x z +
        hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm y z := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPeierlsFiniteHermitianForm_add_left,
    hbXiPeierlsFiniteHermitianForm_add_right]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_smul_left
    (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm (c • x) y =
      (starRingEnd ℂ) c *
        hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPeierlsFiniteHermitianForm_smul_left,
    hbXiPeierlsFiniteHermitianForm_smul_right]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_add_right
    (x y z : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x (y + z) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y +
        hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x z := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPeierlsFiniteHermitianForm_add_left,
    hbXiPeierlsFiniteHermitianForm_add_right]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_smul_right
    (c : ℂ) (x y : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x (c • y) =
      c * hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y := by
  simp [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPeierlsFiniteHermitianForm_smul_left,
    hbXiPeierlsFiniteHermitianForm_smul_right]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_conj_symm
    (x y : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm y x =
      (starRingEnd ℂ)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y) := by
  calc
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm y x =
        (starRingEnd ℂ) (hbXiPeierlsFiniteHermitianForm x y) +
          (starRingEnd ℂ)
            (hbXiPeierlsFiniteHermitianForm
              (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y)
              (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)) := by
      rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
        hbXiPeierlsFiniteHermitianForm_conj_symm x y,
        hbXiPeierlsFiniteHermitianForm_conj_symm
          (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y)
          (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)]
    _ = (starRingEnd ℂ)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y) := by
      rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm, map_add]

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_self
    (x : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x x =
      (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x : ℂ) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy,
    hbXiPeierlsFiniteHermitianForm_self, hbXiPeierlsFiniteHermitianForm_self]
  norm_cast

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_nonneg
    (x : HBXiPeierlsPacket) :
    0 ≤ hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x := by
  exact add_nonneg (hbXiPeierlsFiniteHermitianEnergy_nonneg x)
    (hbXiPeierlsFiniteHermitianEnergy_nonneg
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x))

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_eq_zero_iff
    (x : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx : hbXiPeierlsFiniteHermitianEnergy x = 0 := by
      have hxnonneg := hbXiPeierlsFiniteHermitianEnergy_nonneg x
      have hTnonneg := hbXiPeierlsFiniteHermitianEnergy_nonneg
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)
      rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy] at h
      linarith
    exact (hbXiPeierlsFiniteHermitianEnergy_eq_zero_iff x).mp hx
  · intro hx
    subst x
    simp [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy, hbXiPeierlsFiniteHermitianEnergy]

/-- Actual Green/source-FE packet transport is antiunitary for the symmetrized Hermitian form. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_transport
    (x y : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y) =
      (starRingEnd ℂ)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_involutive,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_involutive,
    map_add]
  rw [hbXiPeierlsFiniteHermitianForm_conj_symm x y,
    hbXiPeierlsFiniteHermitianForm_conj_symm
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y)
      (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)]
  ring

theorem hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_transport
    (x : HBXiPeierlsPacket) :
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy,
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_involutive]
  ring

/-- Closed certificate that positive Hermitian geometry and bright off-line cancellation coexist. -/
def HBXiPhaseSensitiveUnitRadiativeSourceFEPositiveHermitianBrightCancellation : Prop :=
  HBXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation ∧
  (∀ x : HBXiPeierlsPacket,
    hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x) = x ∧
    0 ≤ hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x ∧
    (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x = 0 ↔ x = 0) ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x) ∧
  (∀ c : ℂ, ∀ x y z : HBXiPeierlsPacket,
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm (x + y) z =
        hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x z +
          hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm y z ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm (c • x) y =
        (starRingEnd ℂ) c *
          hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x (y + z) =
        hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y +
          hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x z ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x (c • y) =
      c * hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y) ∧
  (∀ x y : HBXiPeierlsPacket,
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm y x =
      (starRingEnd ℂ)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y) ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x x =
      (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy x : ℂ) ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport x)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport y) =
      (starRingEnd ℂ)
        (hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm x y)) ∧
  (∀ q : XiZeroCopy,
    0 < hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight q ∧
    hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight
          (xiZeroCopyReflectEquiv q) *
        Complex.normSq
          (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) =
      hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight q)

/-- **[POSITIVE-METRIC NO-GO]** Actual radiative source-FE transport admits positive-definite
antiunitary packet geometry and positive diagonal orbit weights while HC89 bright cancellation
persists. Positivity/Hermiticity alone therefore cannot select the critical line. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveHermitianBrightCancellation :
    HBXiPhaseSensitiveUnitRadiativeSourceFEPositiveHermitianBrightCancellation := by
  refine ⟨hbXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨
      hbXiPhaseSensitiveUnitRadiativeSourceFEPacketTransport_involutive x,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_nonneg x,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_eq_zero_iff x,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianEnergy_transport x⟩
  · intro c x y z
    exact ⟨
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_add_left x y z,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_smul_left c x y,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_add_right x y z,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_smul_right c x y⟩
  · intro x y
    exact ⟨
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_conj_symm x y,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_self x,
      hbXiPhaseSensitiveUnitRadiativeSourceFEHermitianForm_transport x y⟩
  · intro q
    exact ⟨
      hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight_pos q,
      hbXiPhaseSensitiveUnitRadiativeSourceFEPositiveOrbitWeight_balance q⟩

end

end RHTower
