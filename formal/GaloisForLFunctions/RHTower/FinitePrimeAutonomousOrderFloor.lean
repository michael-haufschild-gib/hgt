import GaloisForLFunctions.HTGeometry.AutonomousCarrierRegularity
import GaloisForLFunctions.HTGeometry.AutonomousFlowFrequencyRankStrict
import GaloisForLFunctions.HTGeometry.CarrierDivisorObservable
import GaloisForLFunctions.HTGeometry.PrimePhaseBudgetRank
import GaloisForLFunctions.RHTower.PrimeLogPhaseBudget

open Module Set Complex
open scoped BoundedContinuousFunction

/-!
# Finite-prime autonomous order floors

This module composes prime-log independence with established carrier frequency-rank laws.
General regular strip and divisor-observable forms give the closed bound pi'(N) <= 2n.
For the explicit finite-phase autonomous model, the sharper existing phase-rank theorem gives the
strict card floor pi'(N) < 2n, hence pi'(N) / 2 + 1 <= n.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Any additive subgroup containing the finite prime-log packet has at least prime-counting rank. -/
theorem primeCounting_le_rank_addSubgroup_of_primeLog_mem
    {N : ℕ} (H : AddSubgroup ℝ)
    (hH : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈ H) :
    (Nat.primeCounting' N : Cardinal) ≤ Module.rank ℤ H := by
  classical
  have hindep : LinearIndependent ℤ
      (fun p : (N.primesBelow : Finset ℕ) =>
        (⟨Real.log (p : ℕ), hH (p : ℕ) p.2⟩ : H)) := by
    refine LinearIndependent.of_comp H.subtype.toIntLinearMap ?_
    have hcomp : (H.subtype.toIntLinearMap ∘
        fun p : (N.primesBelow : Finset ℕ) =>
          (⟨Real.log (p : ℕ), hH (p : ℕ) p.2⟩ : H)) =
        fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ) := by
      funext p
      rfl
    rw [hcomp]
    exact primeLog_primesBelow_linearIndependent N
  have hcard := hindep.cardinal_le_rank
  have hmk : Cardinal.mk ((N.primesBelow : Finset ℕ) : Type) =
      (Nat.primeCounting' N : Cardinal) := by
    rw [Cardinal.mk_fintype, Fintype.card_coe, Nat.primesBelow_card_eq_primeCounting']
  rwa [hmk] at hcard

/-- Finite-prime consequence of the regular autonomous strip frequency-rank law. -/
theorem primeCounting_le_two_mul_of_strip_differential_equation
    {F : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * I))
    {n N : ℕ} (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      StripAnnihilator σ R F n Q → Q.natDegree ≠ 0)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' N ≤ 2 * n := by
  have hlower := primeCounting_le_rank_addSubgroup_of_primeLog_mem
    (AddSubgroup.closure (bohrSpectrum (fun x => f x))) hprime
  have hupper := rank_bohrSpectrum_le_of_strip_differential_equation
    hR hF hap hf hn hex horder
  have hchain : (Nat.primeCounting' N : Cardinal) ≤ ((n * 2 : ℕ) : Cardinal) :=
    hlower.trans hupper
  have hnat : Nat.primeCounting' N ≤ n * 2 := by exact_mod_cast hchain
  simpa [mul_comm] using hnat

/-- Divisor-observable finite-prime consequence of the autonomous strip rank law. -/
theorem primeCounting_le_two_mul_of_divisor_stripAnnihilator
    {F : ℂ → ℂ} {σ R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * I))
    (hfne : ∃ s : ℝ, f s ≠ 0)
    {n N : ℕ} (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      StripAnnihilator σ R F n Q → Q.natDegree ≠ 0)
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ))
    (hKU : tsupport φ ⊆ verticalStrip σ (r + ρ))
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum
        (fun t : ℝ => HTGeometry.divisorPairing
          (fun z => F (z + (t : ℂ) * I)) φ))) :
    Nat.primeCounting' N ≤ 2 * n := by
  have hlower := primeCounting_le_rank_addSubgroup_of_primeLog_mem
    (AddSubgroup.closure (bohrSpectrum
      (fun t : ℝ => HTGeometry.divisorPairing
        (fun z => F (z + (t : ℂ) * I)) φ))) hprime
  have hupper := rank_bohrSpectrum_divisor_le_of_stripAnnihilator
    hr hρ hrρ hF hap hf hfne hn hex horder hφ hKc hKU
  have hchain : (Nat.primeCounting' N : Cardinal) ≤ ((n * 2 : ℕ) : Cardinal) :=
    hlower.trans hupper
  have hnat : Nat.primeCounting' N ≤ n * 2 := by exact_mod_cast hchain
  simpa [mul_comm] using hnat

/-- Prime-log independence plus locally unique autonomous carrier transport gives the strict
ambient real-dimension floor. -/
theorem primeCounting_lt_of_local_ambient_transport
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {d N : ℕ} (hd : 0 < d)
    (J : BohrHull f → EuclideanSpace ℝ (Fin d))
    (hJcont : Continuous J) (hJinj : Function.Injective J)
    (htransport : HasLocalAmbientCarrierTransport f J)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' N < d := by
  have hfap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit htb
  have hfreq : ∀ p : (N.primesBelow : Finset ℕ),
      IsBohrHullFrequency f (Real.log (p : ℕ)) := fun p =>
    (closure_bohrSpectrum_le_bohrHullFrequencies hfap) (hprime (p : ℕ) p.2)
  have hlt := independent_family_card_lt_of_local_ambient_transport hf htb
    (HTGeometry.primeLog_primesBelow_linearIndependent_rat N) hfreq hd
    J hJcont hJinj htransport
  rwa [Fintype.card_coe, Nat.primesBelow_card_eq_primeCounting'] at hlt

/-- An order-`n` complex autonomous state has real dimension `2n`; locally unique carrier
transport therefore forces the strict half-prime-count order floor. -/
theorem primeCounting_lt_two_mul_of_local_autonomous_carrier
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (J : BohrHull f → EuclideanSpace ℝ (Fin (n * 2)))
    (hJcont : Continuous J) (hJinj : Function.Injective J)
    (htransport : HasLocalAmbientCarrierTransport f J)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' N < 2 * n := by
  have hlt := primeCounting_lt_of_local_ambient_transport hf htb
    (d := n * 2) (by positivity) J hJcont hJinj htransport hprime
  simpa [mul_comm] using hlt

/-- Exact carrier-level encoding of a regular locally unique autonomous complex state of order
`n`: the compact phase carrier embeds in its `2n` real jet coordinates and every time translation
extends locally to an injective continuous ambient evolution map. -/
def HasRegularLocallyUniqueAutonomousCarrier (f : ℝ →ᵇ ℂ) (n : ℕ) : Prop :=
  ∃ J : BohrHull f → EuclideanSpace ℝ (Fin (n * 2)),
    Continuous J ∧ Function.Injective J ∧ HasLocalAmbientCarrierTransport f J

/-- Strict finite-prime order law for a regular locally unique autonomous carrier. -/
theorem primeCounting_lt_two_mul_of_regular_locallyUnique_autonomousCarrier
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' N < 2 * n := by
  obtain ⟨J, hJcont, hJinj, htransport⟩ := haut
  exact primeCounting_lt_two_mul_of_local_autonomous_carrier
    hf htb hn J hJcont hJinj htransport hprime

/-- Divisor/observable form: prime phases retained by any continuous carrier observable obey the
same strict order floor, because an observable cannot create carrier frequencies. -/
theorem primeCounting_lt_two_mul_of_regular_locallyUnique_autonomousCarrier_observable
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (Psi : BohrHull f → ℂ) (hPsi : Continuous Psi)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Psi (bohrIota f t)))) :
    Nat.primeCounting' N < 2 * n := by
  have hsub : AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Psi (bohrIota f t))) ≤
      bohrHullFrequencies f :=
    AddSubgroup.closure_le _ |>.mpr
      (bohrSpectrum_observable_subset_bohrHullFrequencies hf htb Psi hPsi)
  obtain ⟨J, hJcont, hJinj, htransport⟩ := haut
  have hfreq : ∀ p : (N.primesBelow : Finset ℕ),
      IsBohrHullFrequency f (Real.log (p : ℕ)) := fun p =>
    hsub (hprime (p : ℕ) p.2)
  have hlt := independent_family_card_lt_of_local_ambient_transport hf htb
    (HTGeometry.primeLog_primesBelow_linearIndependent_rat N) hfreq (by positivity)
    J hJcont hJinj htransport
  rw [Fintype.card_coe, Nat.primesBelow_card_eq_primeCounting'] at hlt
  simpa [mul_comm] using hlt

/-- Exact integral floor corresponding to the strict regular-autonomous carrier law. -/
theorem primeCounting_half_add_one_le_of_regular_locallyUnique_autonomousCarrier
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (hprime : ∀ p ∈ N.primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' N / 2 + 1 ≤ n := by
  have hlt := primeCounting_lt_two_mul_of_regular_locallyUnique_autonomousCarrier
    hf htb hn haut hprime
  omega

/-- Inclusive cutoff form of the card: `(N + 1).primesBelow` is exactly the family of primes
`p ≤ N`, so its cardinal is `Nat.primeCounting' (N + 1)`. -/
theorem primeCounting_succ_lt_two_mul_of_regular_locallyUnique_autonomousCarrier
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (hprime : ∀ p ∈ (N + 1).primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' (N + 1) < 2 * n :=
  primeCounting_lt_two_mul_of_regular_locallyUnique_autonomousCarrier
    hf htb hn haut hprime

/-- Inclusive-cutoff divisor/observable form. -/
theorem primeCounting_succ_lt_two_mul_of_regular_locallyUnique_autonomousCarrier_observable
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (Psi : BohrHull f → ℂ) (hPsi : Continuous Psi)
    (hprime : ∀ p ∈ (N + 1).primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Psi (bohrIota f t)))) :
    Nat.primeCounting' (N + 1) < 2 * n :=
  primeCounting_lt_two_mul_of_regular_locallyUnique_autonomousCarrier_observable
    hf htb hn haut Psi hPsi hprime

/-- Inclusive-cutoff integral floor `n ≥ floor(π(N)/2) + 1`. -/
theorem primeCounting_succ_half_add_one_le_of_regular_locallyUnique_autonomousCarrier
    {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {n N : ℕ} (hn : 0 < n)
    (haut : HasRegularLocallyUniqueAutonomousCarrier f n)
    (hprime : ∀ p ∈ (N + 1).primesBelow, Real.log (p : ℕ) ∈
      AddSubgroup.closure (bohrSpectrum (fun x => f x))) :
    Nat.primeCounting' (N + 1) / 2 + 1 ≤ n := by
  have hlt := primeCounting_succ_lt_two_mul_of_regular_locallyUnique_autonomousCarrier
    hf htb hn haut hprime
  omega

/-- In the explicit finite-phase model, the existing order-sharp law gives the card's strict floor. -/
theorem primeCounting_lt_two_mul_of_realAutonomousAnnihilator_of_primeLog_mem
    {d : Type} [Fintype d] [DecidableEq d] {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j)
    (hindep : HTGeometry.RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (HTGeometry.polyannulus ρ))
    {n N : ℕ} (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      HTGeometry.RealAutonomousAnnihilator (HTGeometry.phaseFunction omega F) n P)
    (hΓ : ∀ p ∈ N.primesBelow,
      (Real.log (p : ℕ) : ℝ) ∈
        bohrFrequencyModule (HTGeometry.realPhaseFunction omega F)) :
    Nat.primeCounting' N < 2 * n := by
  have hle := HTGeometry.primeCounting_le_of_realAutonomousAnnihilator_of_primeLog_mem
    hρ hindep hF hex hΓ
  exact hle.trans_lt (by omega)

/-- Integer form of the strict half-prime-count order floor. -/
theorem primeCounting_half_add_one_le_of_lt_two_mul
    {N n : ℕ} (h : Nat.primeCounting' N < 2 * n) :
    Nat.primeCounting' N / 2 + 1 ≤ n := by
  omega

end

end GaloisForLFunctions
