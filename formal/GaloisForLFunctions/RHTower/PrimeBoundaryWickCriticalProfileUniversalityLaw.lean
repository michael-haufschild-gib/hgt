import GaloisForLFunctions.RHTower.PrimeBoundaryDickmanWick
import GaloisForLFunctions.RHTower.PrimeClockCriticalProfile

/-!
# Prime-boundary Wick critical-profile universality law

The finite Dickman/Wick cumulant on the real axis is exactly radial prime-clock energy at half the
coordinate.  Independently, prime-clock energy at horizontal scale `c / log N` converges to one
universal nonlinear profile.  Therefore the Wick cumulant at scale `2c / log N` has the same
profile, both for fixed and moving scaled coordinates.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- **Fixed prime-boundary Wick critical-profile law.**  The finite prime-boundary cumulant at
real critical coordinate `2c/log N` converges to the complexification of the universal prime-clock
profile. -/
theorem tendsto_primeBoundaryWickCumulant_critical_profile (c : ℝ) :
    Tendsto (fun N : ℕ =>
      primeBoundaryWickCumulant N (((2 * c / Real.log N : ℝ) : ℂ)))
      atTop (𝓝 (primeClockUniversalProfile c : ℂ)) := by
  have hreal := tendsto_primeClockCutoffEnergy_critical_profile c
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine hcomplex.congr' ?_
  filter_upwards with N
  change (primeClockCutoffEnergy N (c / Real.log N) : ℂ) =
    primeBoundaryWickCumulant N (((2 * c / Real.log N : ℝ) : ℂ))
  rw [primeBoundaryWickCumulant_ofReal]
  congr 1
  ring_nf

/-- **Moving prime-boundary Wick critical-profile law.**  Any moving scaled coordinate `cN`
converging to `c` produces the same Wick-cumulant crossover at real coordinate
`2 cN(N) / log N`. -/
theorem tendsto_primeBoundaryWickCumulant_critical_profile_of_tendsto
    {cN : ℕ → ℝ} {c : ℝ} (hcN : Tendsto cN atTop (𝓝 c)) :
    Tendsto (fun N : ℕ =>
      primeBoundaryWickCumulant N (((2 * cN N / Real.log N : ℝ) : ℂ)))
      atTop (𝓝 (primeClockUniversalProfile c : ℂ)) := by
  have hreal := tendsto_primeClockCutoffEnergy_critical_profile_of_tendsto cN c hcN
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  refine hcomplex.congr' ?_
  filter_upwards with N
  change (primeClockCutoffEnergy N (cN N / Real.log N) : ℂ) =
    primeBoundaryWickCumulant N (((2 * cN N / Real.log N : ℝ) : ℂ))
  rw [primeBoundaryWickCumulant_ofReal]
  congr 1
  ring_nf

end

end RHTower
