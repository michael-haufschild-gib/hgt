import GaloisForLFunctions.HTGeometry.CoppoSSH
import GaloisForLFunctions.RHTower.WindingDivisor

/-!
# Dimerized hopping as a corpus winding observer

The two positive-hopping SSH phases from arXiv:2503.11928 are realized by
explicit zero-free loops. Swapping the bonds preserves all squared Bloch
energies while changing their winding, so scalar band data loses orientation.
-/

open Complex
open GaloisForLFunctions.HTGeometry
namespace RHTower

/-- The intercell-dominant loop winds once, for every constructed hopping ratio. -/
theorem coppoSSH_topological_winding (a : ℝ) :
    windingNumber (coppoSSHOffDiagonal (coppoSSHRatio a) 1) 0 (2 * Real.pi) = 1 := by
  have hin : ‖(0 : ℂ) - (coppoSSHRatio a : ℂ)‖ < (1 : ℝ) := by
    simpa [abs_of_pos (coppoSSHRatio_pos a)] using coppoSSHRatio_lt_one a
  change windingNumber (fun theta : ℝ => (coppoSSHRatio a : ℂ) +
    1 * Complex.exp ((theta : ℂ) * I)) 0 (2 * Real.pi) = 1
  simpa only [Complex.ofReal_one, one_mul, mul_one, sub_zero, mul_comm] using
    (windingNumber_linear_enclosing (c := (coppoSSHRatio a : ℂ)) (ρ := 0) (r := 1)
      zero_lt_one hin)

/-- The intracell-dominant loop lies in a logarithm chart and has zero winding. -/
theorem coppoSSH_trivial_winding (a : ℝ) :
    windingNumber (coppoSSHOffDiagonal 1 (coppoSSHRatio a)) 0 (2 * Real.pi) = 0 := by
  apply windingNumber_eq_zero_of_ball1
  · change Continuous (fun theta : ℝ => (1 : ℂ) +
      (coppoSSHRatio a : ℂ) * Complex.exp ((theta : ℂ) * I))
    fun_prop
  · dsimp [coppoSSHOffDiagonal, unitBlochFactor]
    rw [zero_mul, Complex.exp_zero]
    rw [show (((2 * Real.pi : ℝ) : ℂ) * I) = 2 * (Real.pi : ℂ) * I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  · intro theta
    have heq : coppoSSHOffDiagonal 1 (coppoSSHRatio a) theta - 1 =
        (coppoSSHRatio a : ℂ) * unitBlochFactor theta := by
      simp [coppoSSHOffDiagonal]
    rw [heq, norm_mul, norm_unitBlochFactor, mul_one]
    simpa [abs_of_pos (coppoSSHRatio_pos a)] using coppoSSHRatio_lt_one a

/-- The topological distinction is invisible to the complete scalar squared-band function. -/
theorem coppoSSH_swapped_bands_equal (a theta : ℝ) :
    coppoSSHGapSq (coppoSSHRatio a) 1 theta =
      coppoSSHGapSq 1 (coppoSSHRatio a) theta := by
  dsimp [coppoSSHGapSq]; ring

/-- An unconditional pair with identical squared bands and different winding observers. -/
theorem coppoSSH_band_winding_separation (a : ℝ) :
    (∀ theta, coppoSSHGapSq (coppoSSHRatio a) 1 theta =
      coppoSSHGapSq 1 (coppoSSHRatio a) theta) ∧
    windingNumber (coppoSSHOffDiagonal (coppoSSHRatio a) 1) 0 (2 * Real.pi) = 1 ∧
    windingNumber (coppoSSHOffDiagonal 1 (coppoSSHRatio a)) 0 (2 * Real.pi) = 0 :=
  ⟨coppoSSH_swapped_bands_equal a, coppoSSH_topological_winding a, coppoSSH_trivial_winding a⟩

/-- The existing long-range hopping ratio has a topological dimerized realization. -/
theorem coppoSSH_longRange_winding (a : ℝ) :
    windingNumber (coppoSSHOffDiagonal (strictLongRangeRatio a) 1) 0 (2 * Real.pi) = 1 := by
  rw [← coppoSSHRatio_longRange]
  exact coppoSSH_topological_winding _

end RHTower
