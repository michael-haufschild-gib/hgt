import GaloisForLFunctions.HTGeometry.ModulusProfileHypertranscendence
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# One Newton profile carries both a DA and an HT entire function

The exponential and the phase-randomized series with the same coefficient magnitudes `1/n!` have
identical Taylor moduli, hence identical maximum-term functions, logarithmic Newton envelopes,
active indices and plateau widths — while one is differentially algebraic and the other is
hypertranscendental.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The factorial modulus profile. -/
def factorialProfile (n : ℕ) : ℝ := 1 / (n.factorial : ℝ)

theorem factorialProfile_pos (n : ℕ) : 0 < factorialProfile n := by
  rw [factorialProfile]
  positivity

theorem factorialProfile_ne_zero (n : ℕ) : factorialProfile n ≠ 0 :=
  ne_of_gt (factorialProfile_pos n)

theorem support_factorialProfile : {n : ℕ | factorialProfile n ≠ 0} = Set.univ := by
  ext n
  simp [factorialProfile_ne_zero n]

theorem infinite_support_factorialProfile : {n : ℕ | factorialProfile n ≠ 0}.Infinite := by
  rw [support_factorialProfile]
  exact Set.infinite_univ

theorem factorialProfile_bounded :
    ∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n, |factorialProfile n| * r ^ n ≤ C := by
  intro r _
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop r
  obtain ⟨C, hC⟩ := hlim.bddAbove_range
  refine ⟨C, fun n => ?_⟩
  have hval : |factorialProfile n| * r ^ n = r ^ n / (n.factorial : ℝ) := by
    rw [factorialProfile, abs_of_pos (by positivity)]
    field_simp
  rw [hval]
  exact hC ⟨n, rfl⟩

/-- The hypertranscendental member of the factorial profile. -/
def factorialProfileHT : ℂ → ℂ := modulusProfileFunction factorialProfile

theorem norm_taylorPS_factorialProfileHT (n : ℕ) :
    ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS factorialProfileHT)‖
      = 1 / (n.factorial : ℝ) := by
  rw [factorialProfileHT, norm_taylorPS_modulusProfileFunction factorialProfile_bounded,
    factorialProfile, abs_of_pos (by positivity)]

theorem hypertranscendental_factorialProfileHT :
    GaloisForLFunctions.Hypertranscendental factorialProfileHT :=
  hypertranscendental_modulusProfileFunction factorialProfile_bounded
    infinite_support_factorialProfile

/-- The exponential has the same Taylor moduli. -/
theorem norm_taylorPS_cexp (n : ℕ) :
    ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)‖
      = 1 / (n.factorial : ℝ) := by
  have hiter : ∀ k : ℕ, iteratedDeriv k Complex.exp = Complex.exp := by
    intro k
    induction k with
    | zero => simp [iteratedDeriv_zero]
    | succ k ih => rw [iteratedDeriv_succ, ih, Complex.deriv_exp]
  rw [GaloisForLFunctions.coeff_taylorPS, hiter n]
  rw [Complex.exp_zero, norm_div, norm_one]
  simp

/-- **One modulus profile, two differential natures.**  The exponential and the phase-randomized
factorial series have the same Taylor coefficient magnitudes, one is differentially algebraic and
the other is hypertranscendental. -/
theorem factorial_profile_carries_DA_and_HT :
    (∀ n : ℕ, ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)‖
        = ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS factorialProfileHT)‖)
      ∧ GaloisForLFunctions.DifferentiallyAlgebraic Complex.exp
      ∧ GaloisForLFunctions.Hypertranscendental factorialProfileHT := by
  refine ⟨fun n => ?_, GaloisForLFunctions.differentiallyAlgebraic_exp,
    hypertranscendental_factorialProfileHT⟩
  rw [norm_taylorPS_cexp, norm_taylorPS_factorialProfileHT]

end

end GaloisForLFunctions.HTGeometry
