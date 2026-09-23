import GaloisForLFunctions.RHTower.MobiusDivisorInclusiveGcdGramNoGo

/-!
# Superquadraticity of the positive gcd completion

The literal late-prime mass already diverges after linear normalization.  The
finite lower bound from `MobiusDivisorInclusiveGcdGramNoGo` transports that
fact into the all-channel positive gcd completion.  Hence this completion is
not a quadratic-scale signed-cancellation controller.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- The inclusive gcd completion is superquadratic along literal late-prime cutoffs. -/
theorem tendsto_mobiusDivisorInclusiveGcdGram_div_quadratic_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorInclusiveGcdGram (4 * N) /
      ((4 * N : ℕ) : ℝ) ^ (2 : ℕ)) atTop atTop := by
  have hmass := tendsto_mobiusDivisorLatePrimeMass_div_atTop
  have hsource := hmass.const_mul_atTop (show (0 : ℝ) < 2 / 5 by norm_num)
  apply tendsto_atTop_mono' _ _ hsource
  filter_upwards [hmass.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with N hratio hN
  have hfour : ((4 * N : ℕ) : ℝ) = 4 * (N : ℝ) := by norm_num
  have hMpos : 0 < ((4 * N : ℕ) : ℝ) := by positivity
  have hratio' : 1 ≤ mobiusDivisorLatePrimeMass (4 * N) /
      ((4 * N : ℕ) : ℝ) := by simpa [hfour] using hratio
  have hMle : ((4 * N : ℕ) : ℝ) ≤ mobiusDivisorLatePrimeMass (4 * N) :=
    by simpa using (le_div_iff₀ hMpos).mp hratio'
  have hmass0 : 0 ≤ mobiusDivisorLatePrimeMass (4 * N) := by
    unfold mobiusDivisorLatePrimeMass
    exact sum_nonneg fun _ _ => divisorUnsignedDilationChannel_nonneg _ _
  have hprod : (2 / 5 : ℝ) * mobiusDivisorLatePrimeMass (4 * N) *
      ((4 * N : ℕ) : ℝ) ≤ mobiusDivisorInclusiveGcdGram (4 * N) := by
    have hmul := mul_le_mul_of_nonneg_left hMle hmass0
    have hscale := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ 2 / 5 by norm_num)
    calc
      (2 / 5 : ℝ) * mobiusDivisorLatePrimeMass (4 * N) * ((4 * N : ℕ) : ℝ) =
          (2 / 5 : ℝ) *
            (mobiusDivisorLatePrimeMass (4 * N) * ((4 * N : ℕ) : ℝ)) := by ring
      _ ≤ (2 / 5 : ℝ) *
          (mobiusDivisorLatePrimeMass (4 * N) * mobiusDivisorLatePrimeMass (4 * N)) := hscale
      _ = (2 / 5 : ℝ) * (mobiusDivisorLatePrimeMass (4 * N)) ^ (2 : ℕ) := by ring
      _ ≤ mobiusDivisorInclusiveGcdGram (4 * N) :=
        two_fifths_late_prime_mass_sq_le_inclusiveGcdGram N hN
  have hdiv : (2 / 5 : ℝ) *
      (mobiusDivisorLatePrimeMass (4 * N) / ((4 * N : ℕ) : ℝ)) ≤
        mobiusDivisorInclusiveGcdGram (4 * N) / ((4 * N : ℕ) : ℝ) ^ (2 : ℕ) := by
    calc
      (2 / 5 : ℝ) *
          (mobiusDivisorLatePrimeMass (4 * N) / ((4 * N : ℕ) : ℝ)) =
          ((2 / 5 : ℝ) * mobiusDivisorLatePrimeMass (4 * N) *
            ((4 * N : ℕ) : ℝ)) / ((4 * N : ℕ) : ℝ) ^ (2 : ℕ) := by
            field_simp
      _ ≤ mobiusDivisorInclusiveGcdGram (4 * N) / ((4 * N : ℕ) : ℝ) ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right hprod (by positivity)
  simpa [hfour] using hdiv

end RHTower
