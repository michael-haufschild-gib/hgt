import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingModularSuperselectionChargedUnitaryBypassNoGo

/-!
# Source-real swap-equivariant HB responses cannot select the neutral sector

The remaining Hartle--Hawking producer asks the real theta source to exclude the charged
double-KMS bypass and force occupation-aligned visible/reflected marginals.  The corpus already
constructs the exact charged thermofield vectors and a unitary sector swap carrying the visible
vector to its reflected partner.

This module closes the entire producer class in which source reality is represented only by that
swap symmetry.  A response history may be time-dependent, nonlinear, norm-unbounded, and defined
on an arbitrary partial domain.  If the domain and every response step preserve the swap, then
the complete histories remain swap-related.  Every swap-invariant reporter therefore has exactly
the same value on both histories at every time.  No continuity, linearity, differentiability,
finite-energy, Fock, or Schatten premise is used.

At nonzero Hawking charge, the same actual pair is not occupation-aligned.  Hence a source-real,
swap-equivariant history cannot supply the missing neutral-sector localization.  The sharp
positive survivor is an oriented source datum: domain, evolution, or reporter must break the
charged-sector swap.  Combined with the existing aligned-double-KMS endpoint, such an additional
symmetry-breaking law remains the only arrow from this construction to RH.

`[NEW] [HB ROUTE-CLASS KILL] [CHARGED DOUBLE KMS] [PARTIAL DOMAIN]
[NONLINEAR] [TIME-DEPENDENT] [SOURCE REALITY] [LEAN-PROVED]`
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Hilbert carrier of the actual charged double-KMS theta states. -/
abbrev ThetaCuspHawkingChargedDoubleKMSCarrier :=
  lp (fun _ : ℕ × ℕ => ℂ) 2

/-- A time-dependent, possibly nonlinear and norm-unbounded response history on a
swap-invariant partial domain containing the actual visible charged theta state. -/
structure ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory
    (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes) where
  domain : Set ThetaCuspHawkingChargedDoubleKMSCarrier
  visible_mem : thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p ∈ domain
  domain_swap : ∀ {x}, x ∈ domain →
    thetaCuspHawkingChargedDoubleKMSSwapUnitary x ∈ domain
  step : ℕ → domain → domain
  step_swap : ∀ n (x : domain),
    thetaCuspHawkingChargedDoubleKMSSwapUnitary (step n x :
      ThetaCuspHawkingChargedDoubleKMSCarrier) =
      (step n ⟨thetaCuspHawkingChargedDoubleKMSSwapUnitary x,
        domain_swap x.property⟩ : ThetaCuspHawkingChargedDoubleKMSCarrier)

/-- Charged-sector swap restricted to the invariant response domain. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.swapOnDomain
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) :
    R.domain → R.domain := fun x =>
  ⟨thetaCuspHawkingChargedDoubleKMSSwapUnitary x,
    R.domain_swap x.property⟩

/-- Non-autonomous response evolution.  Step `n` acts after the first `n` steps. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.evolve
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) :
    ℕ → R.domain → R.domain
  | 0 => id
  | n + 1 => fun x => R.step n (R.evolve n x)

/-- Actual visible charged theta state as an element of the partial response domain. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.visibleState
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) : R.domain :=
  ⟨thetaCuspHawkingPrimeVisibleChargedDoubleKMSHalfDensity r p, R.visible_mem⟩

/-- The domain swap of the visible state is literally the corpus's reflected partner state. -/
theorem ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.swap_visibleState_eq_partner
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) :
    (R.swapOnDomain R.visibleState : ThetaCuspHawkingChargedDoubleKMSCarrier) =
      thetaCuspHawkingPrimePartnerChargedDoubleKMSHalfDensity r p := by
  exact thetaCuspHawkingChargedDoubleKMSSwapUnitary_visible_eq_partner r p

/-- Every time-dependent partial response history preserves the exact swap relation. -/
theorem ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.swap_evolve
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    (x : R.domain) (n : ℕ) :
    thetaCuspHawkingChargedDoubleKMSSwapUnitary
        ((R.evolve n x : R.domain) : ThetaCuspHawkingChargedDoubleKMSCarrier) =
      ((R.evolve n (R.swapOnDomain x) : R.domain) :
        ThetaCuspHawkingChargedDoubleKMSCarrier) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change thetaCuspHawkingChargedDoubleKMSSwapUnitary
          (R.step n (R.evolve n x) : ThetaCuspHawkingChargedDoubleKMSCarrier) =
        (R.step n (R.evolve n (R.swapOnDomain x)) :
          ThetaCuspHawkingChargedDoubleKMSCarrier)
      rw [R.step_swap]
      have hsub :
          R.swapOnDomain (R.evolve n x) =
            R.evolve n (R.swapOnDomain x) := Subtype.ext ih
      exact congrArg (fun y : R.domain =>
        (R.step n y : ThetaCuspHawkingChargedDoubleKMSCarrier)) hsub

/-- Every swap-invariant reporter is blind along every time-dependent equivariant partial
response history, for an arbitrary target type and with no regularity assumptions. -/
theorem
    ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.invariantReporter_evolve_eq
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p)
    {A : Type*} (reporter : ThetaCuspHawkingChargedDoubleKMSCarrier → A)
    (hreporter : ∀ x,
      reporter (thetaCuspHawkingChargedDoubleKMSSwapUnitary x) = reporter x)
    (n : ℕ) :
    reporter ((R.evolve n (R.swapOnDomain R.visibleState) : R.domain) :
        ThetaCuspHawkingChargedDoubleKMSCarrier) =
      reporter ((R.evolve n R.visibleState : R.domain) :
        ThetaCuspHawkingChargedDoubleKMSCarrier) := by
  rw [← R.swap_evolve R.visibleState n]
  exact hreporter _

/-- Proposed source-real selector: a swap-invariant scalar reporter separates the actual visible
and reflected response histories at some time. -/
def ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.SeparatesByInvariantReporter
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) : Prop :=
  ∃ (reporter : ThetaCuspHawkingChargedDoubleKMSCarrier → ℂ),
    (∀ x, reporter (thetaCuspHawkingChargedDoubleKMSSwapUnitary x) = reporter x) ∧
    ∃ n,
      reporter ((R.evolve n (R.swapOnDomain R.visibleState) : R.domain) :
          ThetaCuspHawkingChargedDoubleKMSCarrier) ≠
        reporter ((R.evolve n R.visibleState : R.domain) :
          ThetaCuspHawkingChargedDoubleKMSCarrier)

/-- No invariant reporter separates the two charged histories. -/
theorem
    ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory.not_separatesByInvariantReporter
    {r : ThetaCuspHawkingBackreactionResonantMode} {p : Nat.Primes}
    (R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p) :
    ¬ R.SeparatesByInvariantReporter := by
  rintro ⟨reporter, hreporter, n, hne⟩
  exact hne (R.invariantReporter_evolve_eq reporter hreporter n)

/-- Closed HB route class: at nonzero charge the actual charged pair is not occupation-aligned,
while every swap-equivariant partial response history remains invisible to every invariant
reporter. -/
def D4HBSourceRealSwapEquivariantNeutralSectorRouteKilled : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (p : Nat.Primes),
    thetaCuspHawkingBackreactionHorizonCharge r ≠ 0 →
      ¬ ThetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned r p ∧
      ∀ R : ThetaCuspHawkingPrimeSwapInvariantPartialResponseHistory r p,
        ¬ R.SeparatesByInvariantReporter

/-- Premise-free certificate killing source-real, swap-equivariant neutral-sector localization as
the missing HB producer. -/
theorem d4HBSourceRealSwapEquivariantNeutralSectorRouteKilled :
    D4HBSourceRealSwapEquivariantNeutralSectorRouteKilled := by
  intro r p hcharge
  exact ⟨
    (thetaCuspHawkingPrimeChargedDoubleKMSOccupationAligned_iff_horizonCharge_zero
      r p).not.mpr hcharge,
    fun R => R.not_separatesByInvariantReporter⟩

end

end RHTower
