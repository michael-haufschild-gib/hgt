import GaloisForLFunctions.RHTower.ArithmeticResonanceCofinalTemperedness
import GaloisForLFunctions.RHTower.CCMFirstClockAsymptoticBohrLaw
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# Arithmetic asymptotic-hull temperedness

The literal first CCM clock has a compact recurrent asymptote exactly when every occupied Xi mode
is tempered under genuine completed Euler--Gamma shell evolution.  This is a source-to-spectrum
bridge: the recurrence premise contains no divisor-location statement, while its conclusion is
uniform over divisor copies, prime clocks, and nonzero polarizations.

The negated law has one common quantitative witness.  If recurrence fails, a single Xi
multiplicity-copy escapes every finite-shell positive-energy ceiling at every prime and for every
nonzero polarization.  The offending copy does not depend on prime or coefficient.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

private theorem riemannHypothesis_of_allXiZeroCopies_re_eq_half
    (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi_zero_re_eq_half]
  intro ρ hρ
  let supportPoint : XiDivisorSupport :=
    ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
  have hpos := xi_divisor_pos_on_support supportPoint
  have hcopy : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (supportPoint : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨supportPoint, ⟨0, hcopy⟩⟩
  simpa [q, supportPoint] using h q

/-- Asymptotic recurrence of the literal first clock is exactly cofinal temperedness of every
occupied Xi mode, at every prime clock and every nonzero polarization. -/
theorem ccmFirstClockSourceRecurrence_iff_allXiModesCofinallyTempered :
    CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic ↔
      ∀ (q : XiZeroCopy) (p : Nat.Primes) {c : ℂ}, c ≠ 0 →
        CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget
          p (q.1 : ℂ) c := by
  constructor
  · intro hrec q p c hc
    have hRH :=
      riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic hrec
    have hs := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
    exact
      (completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
        p hs.1 hs.2 hc).2
        (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro htemp
    apply ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_of_rh
    apply riemannHypothesis_of_allXiZeroCopies_re_eq_half
    intro q
    have hs := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
    exact
      (completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
        (default : Nat.Primes) hs.1 hs.2 one_ne_zero).1
        (htemp q (default : Nat.Primes) one_ne_zero)

/-- Failure of source recurrence has a prime-persistent local witness: one fixed occupied Xi mode
escapes every positive finite-shell energy ceiling at every prime and for every nonzero
polarization. -/
theorem not_ccmFirstClockSourceRecurrence_iff_exists_primePersistentXiModeShellEnergyEscape :
    ¬ CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic ↔
      ∃ q : XiZeroCopy,
        ∀ (p : Nat.Primes) {c : ℂ}, c ≠ 0 → ∀ B : ℝ,
          ∃ n : ℕ, ∀ᶠ K : ℕ in atTop,
            B < sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
              (completeResolutionPrimePeeledCumulativeReflectedSecondCartierJet
                p K n (q.1 : ℂ) c) := by
  constructor
  · intro hnrec
    have hnRH : ¬ RiemannHypothesis := by
      intro hRH
      exact hnrec
        (ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic_of_rh hRH)
    have hoff : ∃ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 := by
      by_contra hnone
      push Not at hnone
      apply hnRH
      exact riemannHypothesis_of_allXiZeroCopies_re_eq_half hnone
    obtain ⟨q, hq⟩ := hoff
    refine ⟨q, fun p c hc B => ?_⟩
    have hs := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)
    have hnotBudget :
        ¬ CompleteResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget
          p (q.1 : ℂ) c := by
      intro hbudget
      exact hq
        ((completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff_re_eq_half
          p hs.1 hs.2 hc).1 hbudget)
    have hnotOrbit :
        ¬ SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
          ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1 : ℂ))) c := by
      intro horbit
      exact hnotBudget
        ((completeResolutionPrimePeeledCumulativeReflectedSecondCartierCofinalBudget_iff
          p hs.1 hs.2).2 horbit)
    have hlarge :
        ∃ n : ℕ, B + 1 <
          sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
            (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
              ((p.1 : ℂ) ^ ((1 / 2 : ℂ) - (q.1 : ℂ))) c n) := by
      by_contra hnone
      push Not at hnone
      exact hnotOrbit ⟨B + 1, hnone⟩
    obtain ⟨n, hn⟩ := hlarge
    have hlim :=
      tendsto_completeResolutionPrimePeeledCumulativeReflectedSecondCartierEnergy
        p hs.1 hs.2 n (c := c)
    obtain ⟨K₀, hK₀⟩ := (Metric.tendsto_atTop.mp hlim) 1 zero_lt_one
    refine ⟨n, ?_⟩
    filter_upwards [eventually_ge_atTop K₀] with K hK
    have hnear := hK₀ K hK
    rw [Real.dist_eq] at hnear
    linarith [(abs_lt.mp hnear).1]
  · rintro ⟨q, hescape⟩ hrec
    have htemp :=
      ccmFirstClockSourceRecurrence_iff_allXiModesCofinallyTempered.mp hrec
    obtain ⟨C, hC⟩ := htemp q (default : Nat.Primes) one_ne_zero
    obtain ⟨n, hn⟩ := hescape (default : Nat.Primes) one_ne_zero C
    have hfalse : ∀ᶠ K : ℕ in atTop, False := by
      filter_upwards [hn, hC n] with K hgt hle
      exact (not_lt_of_ge hle) hgt
    obtain ⟨_, hbad⟩ := hfalse.exists
    exact hbad

end

end RHTower
