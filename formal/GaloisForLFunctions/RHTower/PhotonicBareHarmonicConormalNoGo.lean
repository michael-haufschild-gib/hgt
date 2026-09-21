import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization

/-!
# Bare helical harmonic cannot produce the PTR conormal ladder

## PTR proof-chain position

The literal rotating material supplies one nonzero prime helical coefficient,
`photonicPrimeConstitutiveHarmonic p`.  The required PTR target is instead the
spectral family `e ↦ p^(1/2-s)^(-e)`.  This file proves that no boundary law
which sees only that one instantaneous coefficient can output the target for
every spectral label: it would give one fixed family both on and off the
critical line, although the former is moderate and the latter is not.

Thus the missing rotating temporal-Maxwell boundary map must retain
spectral/temporal matching or an equivalent nonlocal datum.  This does not
rule out such a map; it rules out identifying the bare material harmonic
itself with the full conormal amplitude law.
-/

namespace RHTower

/-- A putative conormal boundary law which observes only the instantaneous
prime helical coefficient and is claimed to reproduce every spectral target. -/
def PhotonicBareHarmonicOnlyConormalLaw (p : Nat.Primes) : Prop :=
  ∃ amplitude : ℂ → (ℤ → ℂ),
    ∀ s : ℂ, amplitude (photonicPrimeConstitutiveHarmonic p) =
      photonicPrimePCMConormalSideband p s

/-- No spectral-label-blind function of the bare helical coefficient can be
the PTR conormal amplitude law. -/
theorem not_photonicBareHarmonicOnlyConormalLaw (p : Nat.Primes) :
    ¬ PhotonicBareHarmonicOnlyConormalLaw p := by
  rintro ⟨amplitude, htarget⟩
  have hmoderate : bilateralModerate
      (amplitude (photonicPrimeConstitutiveHarmonic p)) := by
    rw [htarget ((1 / 2 : ℝ) : ℂ)]
    apply (bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half p _).mpr
    norm_num
  have hzero : bilateralModerate (photonicPrimePCMConormalSideband p 0) := by
    rw [← htarget 0]
    exact hmoderate
  have hcritical :=
    (bilateralModerate_photonicPrimePCMConormalSideband_iff_re_eq_half p 0).mp hzero
  norm_num at hcritical

end RHTower
