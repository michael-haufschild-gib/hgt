import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewBohrCoefficients
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Asymptotic Bohr Torelli law for the literal first CCM clock

Any continuous Bohr almost-periodic asymptote of the aperture-scaled published source is unique.
Its existence forces RH, identifies it with the explicit critical Xi screw series, and makes each
nonzero Bohr coefficient a quantized divisor measurement:

`a_P(λ) = -N(|λ|)/λ²`,

where `N(|λ|)` is the exact number of Xi divisor copies at absolute ordinate `|λ|`.  Thus the
literal source asymptote recovers the full multiplicity-bearing absolute Xi spectrum, without
simplicity or rational-independence assumptions.  This is a Torelli theorem conditional only on
the source-side asymptote hypothesis; that hypothesis is already equivalent to RH.
-/

open Complex Filter Set Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

namespace RHTower

noncomputable section

/-- Divisor copies at the unsigned real frequency `|λ|`. -/
def xiAbsoluteOrdinateFiber (lam : ℝ) : Set XiZeroCopy :=
  {q | xiRealSpectralPoint q = lam ∨ -xiRealSpectralPoint q = lam}

theorem mem_xiAbsoluteOrdinateFiber_iff_abs
    (q : XiZeroCopy) (lam : ℝ) :
    q ∈ xiAbsoluteOrdinateFiber lam ↔
      |xiRealSpectralPoint q| = |lam| := by
  rw [xiAbsoluteOrdinateFiber, Set.mem_setOf_eq, abs_eq_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem finite_xiAbsoluteOrdinateFiber_of_rh
    (hRH : RiemannHypothesis) (lam : ℝ) :
    (xiAbsoluteOrdinateFiber lam).Finite := by
  apply ((finite_xiSpectralPoint_fiber (lam : ℂ)).union
    (finite_xiSpectralPoint_fiber ((-lam : ℝ) : ℂ))).subset
  intro q hq
  change xiRealSpectralPoint q = lam ∨ -xiRealSpectralPoint q = lam at hq
  rcases hq with hq | hq
  · left
    change xiSpectralPoint q = (lam : ℂ)
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH q, hq]
  · right
    change xiSpectralPoint q = ((-lam : ℝ) : ℂ)
    rw [xiSpectralPoint_eq_ofReal_of_rh hRH q]
    congr 1
    linarith

/-- Exact multiplicity-copy count at unsigned ordinate `|λ|`, under RH. -/
def xiAbsoluteOrdinateMultiplicity
    (hRH : RiemannHypothesis) (lam : ℝ) : ℕ :=
  (finite_xiAbsoluteOrdinateFiber_of_rh hRH lam).toFinset.card

/-- Every source asymptote is the explicit critical Xi screw model. -/
theorem ccmFirstClockAsymptoticBohrModel_eq_explicitScrew
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (nhds 0)) :
    P = fun L => 2 * xiCriticalScrewSeries L := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
      ⟨P, hPc, hPa, hP⟩
  apply asymptoticBohrModel_unique hPc hPa
    (continuous_const.mul (xiCriticalScrewSeries_continuous_of_rh hRH))
    (by
      have hcont := xiCriticalScrewSeries_continuous_of_rh hRH
      have hap := xiCriticalScrewSeries_isBohrAlmostPeriodic_of_rh hRH
      have hadd := isBohrAlmostPeriodic_add hcont hap hcont hap
      change IsBohrAlmostPeriodic (fun t => 2 * xiCriticalScrewSeries t)
      simpa only [two_mul] using hadd)
    hP
    (ccmFirstClockScaledSource_sub_explicitScrew_tendsto_zero_of_rh hRH)

theorem bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_tsum
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (nhds 0))
    (lam : ℝ) :
    bohrCoefficient (fun L => (P L : ℂ)) lam =
      2 * ∑' q : XiZeroCopy,
        screwAtomBohrCoefficient (xiCriticalScrewWeight q)
          (xiRealSpectralPoint q) lam := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
      ⟨P, hPc, hPa, hP⟩
  have hmodel := ccmFirstClockAsymptoticBohrModel_eq_explicitScrew hPc hPa hP
  rw [hmodel]
  have hfun :
      (fun L : ℝ => ((2 * xiCriticalScrewSeries L : ℝ) : ℂ)) =
        fun L : ℝ => (2 : ℂ) * (xiCriticalScrewSeries L : ℂ) := by
    funext L
    push_cast
    ring
  rw [hfun, bohrCoefficient_const_mul]
  · unfold xiCriticalScrewSeries
    rw [bohrCoefficient_complex_screwSeries
      xiCriticalScrewWeight_nonneg
      (summable_xiCriticalScrewWeight_of_rh hRH)]
  · exact Complex.continuous_ofReal.comp
      (xiCriticalScrewSeries_continuous_of_rh hRH)
  · exact isBohrAlmostPeriodic_ofReal
      (xiCriticalScrewSeries_isBohrAlmostPeriodic_of_rh hRH)

theorem bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_fiberMass
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (nhds 0))
    {lam : ℝ} (hlam : lam ≠ 0) :
    bohrCoefficient (fun L => (P L : ℂ)) lam =
      ∑' q : XiZeroCopy,
        if xiRealSpectralPoint q = lam ∨ -xiRealSpectralPoint q = lam
        then -((1 / lam ^ (2 : ℕ) : ℝ) : ℂ) else 0 := by
  classical
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
      ⟨P, hPc, hPa, hP⟩
  rw [bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_tsum hPc hPa hP lam,
    ← tsum_mul_left]
  apply tsum_congr
  intro q
  have hwne : xiRealSpectralPoint q ≠ 0 := xiRealSpectralPoint_ne_zero hRH q
  rw [xiCriticalScrewWeight]
  unfold screwAtomBohrCoefficient
  simp only [if_neg (Ne.symm hlam)]
  by_cases hp : xiRealSpectralPoint q = lam
  · have hn : -xiRealSpectralPoint q ≠ lam := by
      rw [hp]
      intro h
      apply hlam
      linarith
    rw [if_pos hp, if_neg hn, if_pos (Or.inl hp)]
    push_cast
    rw [hp]
    ring
  · by_cases hn : -xiRealSpectralPoint q = lam
    · rw [if_neg hp, if_pos hn, if_pos (Or.inr hn)]
      have homega : xiRealSpectralPoint q = -lam := by linarith
      rw [homega]
      push_cast
      ring
    · rw [if_neg hp, if_neg hn, if_neg (not_or_intro hp hn)]
      ring

/-- Quantized Torelli law: every nonzero coefficient is `-N(|λ|)/λ²`. -/
theorem bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_multiplicity
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (nhds 0))
    {lam : ℝ} (hlam : lam ≠ 0) :
    bohrCoefficient (fun L => (P L : ℂ)) lam =
      -(xiAbsoluteOrdinateMultiplicity
          (riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
          ⟨P, hPc, hPa, hP⟩) lam : ℂ) / (lam : ℂ) ^ (2 : ℕ) := by
  classical
  let hRH : RiemannHypothesis :=
    riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
      ⟨P, hPc, hPa, hP⟩
  rw [bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_fiberMass
    hPc hPa hP hlam]
  let S : Finset XiZeroCopy :=
    (finite_xiAbsoluteOrdinateFiber_of_rh hRH lam).toFinset
  rw [tsum_eq_sum (s := S)]
  · calc
      ∑ q ∈ S, (if xiRealSpectralPoint q = lam ∨
          -xiRealSpectralPoint q = lam
          then -((1 / lam ^ (2 : ℕ) : ℝ) : ℂ) else 0) =
          ∑ _q ∈ S, -((1 / lam ^ (2 : ℕ) : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [if_pos]
            have hmem : q ∈ xiAbsoluteOrdinateFiber lam := by
              simpa only [S, Set.Finite.mem_toFinset] using hq
            simpa only [xiAbsoluteOrdinateFiber, Set.mem_setOf_eq] using hmem
      _ = -(xiAbsoluteOrdinateMultiplicity hRH lam : ℂ) / (lam : ℂ) ^ (2 : ℕ) := by
        unfold xiAbsoluteOrdinateMultiplicity
        dsimp only [S]
        push_cast
        simp
        ring
  · intro q hq
    rw [if_neg]
    intro hmem
    apply hq
    have hset : q ∈ xiAbsoluteOrdinateFiber lam := by
      simpa only [xiAbsoluteOrdinateFiber, Set.mem_setOf_eq] using hmem
    simpa only [S, Set.Finite.mem_toFinset] using hset

/-- Multiplying a nonzero Bohr coefficient by `-λ²` recovers the exact number of divisor
copies at the absolute ordinate `|λ|`. -/
theorem ccmFirstClockAsymptoticBohrModel_recovers_absoluteMultiplicity
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockScaledPublishedSource L - P L) atTop (nhds 0))
    {lam : ℝ} (hlam : lam ≠ 0) :
    -((lam : ℂ) ^ (2 : ℕ)) * bohrCoefficient (fun L => (P L : ℂ)) lam =
      (xiAbsoluteOrdinateMultiplicity
        (riemannHypothesis_of_ccmFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic
          ⟨P, hPc, hPa, hP⟩) lam : ℂ) := by
  rw [bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_multiplicity
    hPc hPa hP hlam]
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  field_simp [hlamC]

end
end RHTower
