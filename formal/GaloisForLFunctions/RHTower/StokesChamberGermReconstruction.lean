import GaloisForLFunctions.RHTower.SourceHorizontalStokesCoenergySharpPrimeAsymptotic
import GaloisForLFunctions.HTGeometry.PoissonBooleanTransferGerm

/-!
# Stokes-chamber reconstruction from the reflected boundary germ

In the complementary Stokes chamber the reflected parameter is `t = (1-s)/2`.  The directed
Poisson–Boolean boundary germ of the reflected prime packet recovers the ordered rate pair, hence
`t`, hence `s = 1 - 2t`; substituting into the sharp prime–valuation coenergy law gives the
reconstructed exponent `2 + 2(1-2t)e` and coefficient `√2 t (e+1)^{-2}`.
-/

open Filter Topology Real GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- The reflected parameter of the complementary Stokes chamber. -/
def stokesReflectionParameter (s : ℝ) : ℝ := (1 - s) / 2

theorem stokesReflectionParameter_pos {s : ℝ} (hs1 : s < 1) :
    0 < stokesReflectionParameter s := by
  rw [stokesReflectionParameter]
  linarith

theorem stokesReflectionParameter_lt_half {s : ℝ} (hs : 0 < s) :
    stokesReflectionParameter s < 1 / 2 := by
  rw [stokesReflectionParameter]
  linarith

theorem one_sub_two_mul_stokesReflectionParameter (s : ℝ) :
    1 - 2 * stokesReflectionParameter s = s := by
  rw [stokesReflectionParameter]
  ring

/-- **The Stokes chamber parameter is reconstructed from the reflected rate pair** (ULF-FTGM-1, (5.3)
in the chamber `t = (1-s)/2`). -/
theorem stokesChamber_recovery (p : Nat.Primes) (s : ℝ) :
    1 - 2 * (1 / (2 * Real.log (p : ℝ)) *
        Real.log ((Real.exp ((reflectedSourceRate p (stokesReflectionParameter s) : ℝ)) - 1) /
          (Real.exp ((reflectedSourceRate p (-stokesReflectionParameter s) : ℝ)) - 1))) = s := by
  rw [reflectedSourceRate_recovery, one_sub_two_mul_stokesReflectionParameter]

/-- **Fourth-organ Stokes reconstruction** (ULF-FTGM-1, (5.4)–`(5.5)`).  Written in the reflected
parameter, the sharp prime–valuation coenergy law has exponent `2 + 2(1-2t)e` and coefficient
`√2 t (e+1)^{-2}`. -/
theorem isEquivalent_stokesCoenergy_reflected {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) (e : ℕ) :
    Asymptotics.IsEquivalent cofinite
      (fun p : Nat.Primes =>
        sourceHorizontalStokesConditionedInformationTerm (1 - 2 * t) (p, e))
      (fun p : Nat.Primes => Real.sqrt 2 * t / (((e : ℝ) + 1) ^ 2) *
        (p : ℝ) ^ (-2 - 2 * (1 - 2 * t) * (e : ℝ))) := by
  have hs : (0 : ℝ) < 1 - 2 * t := by linarith
  have hs1 : (1 : ℝ) - 2 * t < 1 := by linarith
  have hcoeff : (1 - (1 - 2 * t)) / (Real.sqrt 2 * (((e : ℝ) + 1) ^ 2))
      = Real.sqrt 2 * t / (((e : ℝ) + 1) ^ 2) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2' : Real.sqrt 2 ≠ 0 := by positivity
    have he : ((e : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    nlinarith [h2]
  have := isEquivalent_stokesCoenergy_sharp hs hs1 e
  rwa [hcoeff] at this

end

end RHTower.HedenmalmThetaSource
