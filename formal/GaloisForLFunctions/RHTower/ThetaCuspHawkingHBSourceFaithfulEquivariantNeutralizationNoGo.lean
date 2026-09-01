import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBSourceRealSwapEquivariantPartialResponseNoGo

/-!
# Source-faithful equivariant neutralization cannot repair the HB charged sector

The source-real HB survivor left by the invariant-reporter no-go could try to retain the
charged-sector swap in the dynamics while adding an oriented reporter, or could interpret equality
of the two response outputs as neutral-sector localization. This module closes both possibilities
for the actual charged double-KMS vectors.

The visible/partner overlap is exactly the square of the one-mode geometric Hellinger affinity.
The vectors themselves agree exactly at zero horizon charge. For an arbitrary time-dependent,
nonlinear, norm-unbounded partial response history, injectivity of one time slice therefore makes
output neutralization equivalent to zero charge. Off wall there is an exhaustive dichotomy:
either the outputs collapse and the time slice is noninjective, or one ordered occupation-coordinate
linear reporter distinguishes them.

The collapse branch is nonselective. A full-domain constant-zero equivariant history neutralizes
the pair at the first step for every charge and is necessarily noninjective off wall. Consequently,
universal neutralization by injective source-real responses is equivalent to RH itself. Reporter-only
orientation and nonfaithful output equality cannot supply the missing source-faithful neutral-sector
producer.

The positive survivor is sharp: a viable HB producer must derive actual charge annihilation or put
oriented information in the response domain/evolution while retaining a separately specified source
fidelity law.

`[NEW ROUTE-SPECIFIC CONSEQUENCE] [HB ROUTE-CLASS KILL] [CHARGED DOUBLE KMS]
[SOURCE FIDELITY] [NONLINEAR] [PARTIAL DOMAIN] [LEAN-PROVED]`
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Exact overlap invariant of the actual charged thermofield pair. The two charge factors swap,
so their tensor overlap is the square of the geometric Hellinger affinity. -/
theorem inner_thetaCuspHawkingPrimeVisibleChargedDoubleKMS_partner_eq_affinity_sq
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    inner ℂ
        (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p)
        (thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p) =
      ((geometricHellingerAffinity
        (thetaCuspHawkingPrimeVisibleKMSRatio r p)
        (thetaCuspHawkingPrimePartnerKMSRatio r p) : ℝ) : ℂ) ^ 2 := by
  rw [thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity,
    thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity,
    inner_lpTensorProductVector,
    inner_geometricOccupationHalfDensity,
    inner_geometricOccupationHalfDensity]
  have hsym :
      geometricHellingerAffinity
          (thetaCuspHawkingPrimePartnerKMSRatio r p)
          (thetaCuspHawkingPrimeVisibleKMSRatio r p) =
        geometricHellingerAffinity
          (thetaCuspHawkingPrimeVisibleKMSRatio r p)
          (thetaCuspHawkingPrimePartnerKMSRatio r p) := by
    simp [geometricHellingerAffinity, mul_comm]
  rw [hsym]
  ring

/-- Actual visible and reflected charged thermofield vectors agree exactly in the neutral sector. -/
theorem thetaCuspHawkingPrimeVisibleChargedDoubleKMS_eq_partner_iff_horizonCharge_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p =
        thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p ↔
      thetaCuspHawkingBackreactionHorizonCharge r = 0 := by
  constructor
  · intro hvec
    apply
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
        r p).1
    intro k l
    rw [hvec]
  · intro hcharge
    have hratio :=
      (thetaCuspHawkingPrimeKMSRatio_eq_iff_horizonCharge_zero r p).2 hcharge
    apply lp.ext
    funext i
    rcases i with ⟨k, l⟩
    simp only [thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity,
      thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity,
      lpTensorProductVector_apply, geometricOccupationHalfDensity_apply]
    rw [hratio]

/-- Time-`n` equality of the actual visible and partner response outputs. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.NeutralizesAt
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    (n : ℕ) : Prop :=
  ((R.evolve n R.visibleState : R.domain) :
      ThetaCuspHawkingChargedDoubleKMSCarrier) =
    ((R.evolve n (R.swapOnDomain R.visibleState) : R.domain) :
      ThetaCuspHawkingChargedDoubleKMSCarrier)

/-- Ordered occupation-coordinate evaluation. Choosing `(k,l)` rather than `(l,k)` supplies the
minimal complex-linear charged-sector orientation. -/
def thetaCuspHawkingChargedDoubleKMSOrientedCoordinateReporter
    (i : ℕ × ℕ) :
    ThetaCuspHawkingChargedDoubleKMSCarrier →ₗ[ℂ] ℂ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Some ordered occupation-coordinate linear reporter distinguishes the two outputs. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.SeparatesByOrientedCoordinateAt
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    (n : ℕ) : Prop :=
  ∃ i : ℕ × ℕ,
    thetaCuspHawkingChargedDoubleKMSOrientedCoordinateReporter i
        ((R.evolve n R.visibleState : R.domain) :
          ThetaCuspHawkingChargedDoubleKMSCarrier) ≠
      thetaCuspHawkingChargedDoubleKMSOrientedCoordinateReporter i
        ((R.evolve n (R.swapOnDomain R.visibleState) : R.domain) :
          ThetaCuspHawkingChargedDoubleKMSCarrier)

/-- **Sharp source-fidelity law.** If a response time slice is injective, equality of its actual
visible/partner outputs is exactly neutral horizon charge. -/
theorem ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.neutralizesAt_iff_horizonCharge_zero_of_injective
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    (n : ℕ) (hinj : Function.Injective (R.evolve n)) :
    R.NeutralizesAt n ↔ thetaCuspHawkingBackreactionHorizonCharge r = 0 := by
  constructor
  · intro hneutral
    have hinput : R.visibleState = R.swapOnDomain R.visibleState :=
      hinj (Subtype.ext hneutral)
    apply
      (thetaCuspHawkingPrimeVisibleChargedDoubleKMS_eq_partner_iff_horizonCharge_zero
        r p).1
    calc
      thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p =
          (R.visibleState : ThetaCuspHawkingChargedDoubleKMSCarrier) := rfl
      _ = (R.swapOnDomain R.visibleState :
          ThetaCuspHawkingChargedDoubleKMSCarrier) := congrArg Subtype.val hinput
      _ = thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p :=
        R.swap_visibleState_eq_partner
  · intro hcharge
    have hvec :=
      (thetaCuspHawkingPrimeVisibleChargedDoubleKMS_eq_partner_iff_horizonCharge_zero
        r p).2 hcharge
    have hinput : R.visibleState = R.swapOnDomain R.visibleState := by
      apply Subtype.ext
      calc
        (R.visibleState : ThetaCuspHawkingChargedDoubleKMSCarrier) =
            thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p := rfl
        _ = thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p := hvec
        _ = (R.swapOnDomain R.visibleState :
            ThetaCuspHawkingChargedDoubleKMSCarrier) :=
          R.swap_visibleState_eq_partner.symm
    exact congrArg (fun x : R.domain =>
      ((R.evolve n x : R.domain) :
        ThetaCuspHawkingChargedDoubleKMSCarrier)) hinput

/-- **Faithful-or-erasing dichotomy.** Off wall, each response time either collapses the actual
pair by losing injectivity or leaves a distinction visible to one ordered coordinate reporter. -/
theorem ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.collapse_loses_injectivity_or_orientedCoordinate_separates
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    (hcharge : thetaCuspHawkingBackreactionHorizonCharge r ≠ 0)
    (n : ℕ) :
    (R.NeutralizesAt n ∧ ¬ Function.Injective (R.evolve n)) ∨
      R.SeparatesByOrientedCoordinateAt n := by
  by_cases hneutral : R.NeutralizesAt n
  · left
    refine ⟨hneutral, ?_⟩
    intro hinj
    exact hcharge ((R.neutralizesAt_iff_horizonCharge_zero_of_injective n hinj).1 hneutral)
  · right
    rw [ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.SeparatesByOrientedCoordinateAt]
    by_contra hsep
    push Not at hsep
    apply hneutral
    apply lp.ext
    funext i
    exact hsep i

/-- Full-domain constant eraser. It respects the charged-sector swap but discards every source. -/
def thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p where
  domain := Set.univ
  visible_mem := Set.mem_univ _
  domain_swap := fun {_} _ => Set.mem_univ _
  step := fun _ _ => ⟨0, Set.mem_univ _⟩
  step_swap := by
    intro n x
    simp

/-- The constant eraser neutralizes every actual charged pair after one step. -/
theorem thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory_neutralizesAt_one
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) :
    (thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).NeutralizesAt 1 := by
  rfl

/-- At nonzero charge, the constant eraser's neutralization necessarily loses source fidelity. -/
theorem thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory_not_injective_of_charge_ne_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes)
    (hcharge : thetaCuspHawkingBackreactionHorizonCharge r ≠ 0) :
    ¬ Function.Injective
      ((thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).evolve 1) := by
  intro hinj
  have hzero :=
    ((thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).neutralizesAt_iff_horizonCharge_zero_of_injective 1 hinj).1
      (thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory_neutralizesAt_one r p)
  exact hcharge hzero

/-- Universal neutralization by every injective source-real response. -/
def D4HBEveryInjectiveSwapEquivariantResponseNeutralizes : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes)
      (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) (n : ℕ),
    Function.Injective (R.evolve n) → R.NeutralizesAt n

/-- Universal source-faithful equivariant neutralization is exactly RH, not a weaker physical
producer premise. The time-zero identity slice already retains the complete charge obstruction. -/
theorem d4HBEveryInjectiveSwapEquivariantResponseNeutralizes_iff_riemannHypothesis :
    D4HBEveryInjectiveSwapEquivariantResponseNeutralizes ↔ RiemannHypothesis := by
  constructor
  · intro hneutral
    apply
      (thetaCuspHawkingChargedDoubleKMSOccupationAligned_iff_riemannHypothesis).1
    intro r p
    apply
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
        r p).2
    have hzero := hneutral r p
      (thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p) 0 (by
        change Function.Injective id
        exact Function.injective_id)
    exact
      ((thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).neutralizesAt_iff_horizonCharge_zero_of_injective 0 (by
          change Function.Injective id
          exact Function.injective_id)).1 hzero
  · intro hRH r p R n hinj
    have halign :=
      (thetaCuspHawkingChargedDoubleKMSOccupationAligned_iff_riemannHypothesis).2
        hRH r p
    have hcharge :=
      (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
        r p).1 halign
    exact (R.neutralizesAt_iff_horizonCharge_zero_of_injective n hinj).2 hcharge

/-- Closed certificate for the HB source-faithful swap-equivariant neutralization route class. -/
def D4HBSourceFaithfulSwapEquivariantNeutralizationRouteKilled : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes),
    inner ℂ
        (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p)
        (thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p) =
      ((geometricHellingerAffinity
        (thetaCuspHawkingPrimeVisibleKMSRatio r p)
        (thetaCuspHawkingPrimePartnerKMSRatio r p) : ℝ) : ℂ) ^ 2 ∧
    (thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p =
        thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p ↔
      thetaCuspHawkingBackreactionHorizonCharge r = 0) ∧
    (∀ (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) (n : ℕ),
      Function.Injective (R.evolve n) →
        (R.NeutralizesAt n ↔ thetaCuspHawkingBackreactionHorizonCharge r = 0)) ∧
    (thetaCuspHawkingBackreactionHorizonCharge r ≠ 0 →
      ∀ (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) (n : ℕ),
        (R.NeutralizesAt n ∧ ¬ Function.Injective (R.evolve n)) ∨
          R.SeparatesByOrientedCoordinateAt n) ∧
    (thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).NeutralizesAt 1 ∧
    (thetaCuspHawkingBackreactionHorizonCharge r ≠ 0 →
      ¬ Function.Injective
        ((thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory r p).evolve 1))

/-- **[HB ROUTE-CLASS KILL]** Injective swap-equivariant dynamics preserve the exact charged
distinction; output collapse is noninjective source erasure and is available at every charge. -/
theorem d4HBSourceFaithfulSwapEquivariantNeutralizationRouteKilled :
    D4HBSourceFaithfulSwapEquivariantNeutralizationRouteKilled := by
  intro r p
  exact ⟨
    inner_thetaCuspHawkingPrimeVisibleChargedDoubleKMS_partner_eq_affinity_sq r p,
    thetaCuspHawkingPrimeVisibleChargedDoubleKMS_eq_partner_iff_horizonCharge_zero r p,
    fun R n hinj => R.neutralizesAt_iff_horizonCharge_zero_of_injective n hinj,
    fun hcharge R n => R.collapse_loses_injectivity_or_orientedCoordinate_separates hcharge n,
    thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory_neutralizesAt_one r p,
    thetaCuspHawkingPrimeSwapInvariantZeroResponseHistory_not_injective_of_charge_ne_zero r p⟩

end

end RHTower
