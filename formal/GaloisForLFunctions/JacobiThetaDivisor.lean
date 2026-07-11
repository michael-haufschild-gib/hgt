/-
# The half-period divisor of the Jacobi theta function

For the convention

`Theta(z,tau) = sum_n exp(2*pi*i*n*z + pi*i*n^2*tau)`,

the basic zero is the odd half-period `(1+tau)/2`.  The proof below uses only the exact evenness,
periodicity, and quasiperiodicity constraints already formalized in mathlib; it does not appeal to
a product expansion or to a numerical estimate.
-/
import GaloisForLFunctions.MeromorphicTheta

namespace GaloisForLFunctions

noncomputable section

/-- The distinguished odd half-period for the theta convention used by `jacobiTheta₂`. -/
def thetaHalfPeriod (τ : ℂ) : ℂ := (1 + τ) / 2

/-- The derivative of theta at its distinguished half-period.  Its nonvanishing is exactly the
simplicity of the basic theta divisor. -/
def thetaHalfPeriodDerivative (τ : ℂ) : ℂ :=
  jacobiTheta₂' (thetaHalfPeriod τ) τ

/-- The quasiperiodic multiplier at the reflected half-period is exactly `-1`. -/
theorem thetaHalfPeriod_quasiFactor (τ : ℂ) :
    Complex.exp
      (-Real.pi * Complex.I *
        (τ + 2 * (-thetaHalfPeriod τ + 1))) = -1 := by
  have harg : τ + 2 * (-thetaHalfPeriod τ + 1) = 1 := by
    rw [thetaHalfPeriod]
    ring
  rw [harg]
  norm_num [Complex.exp_neg_pi_mul_I]

/-- **Odd half-period zero.** The Jacobi theta function vanishes at `(1+τ)/2`.
This is forced by the three constraints `Theta(-z)=Theta(z)`, `Theta(z+1)=Theta(z)`, and the
`τ`-quasiperiodicity: at the half-period they identify `Theta` with its own negative. -/
theorem jacobiTheta₂_thetaHalfPeriod_eq_zero (τ : ℂ) :
    jacobiTheta₂ (thetaHalfPeriod τ) τ = 0 := by
  have hcoord : thetaHalfPeriod τ = (-thetaHalfPeriod τ + 1) + τ := by
    rw [thetaHalfPeriod]
    ring
  have hneg : jacobiTheta₂ (thetaHalfPeriod τ) τ =
      -jacobiTheta₂ (thetaHalfPeriod τ) τ := by
    calc
      jacobiTheta₂ (thetaHalfPeriod τ) τ =
          jacobiTheta₂ ((-thetaHalfPeriod τ + 1) + τ) τ :=
        congrArg (fun z : ℂ ↦ jacobiTheta₂ z τ) hcoord
      _ = Complex.exp
            (-Real.pi * Complex.I * (τ + 2 * (-thetaHalfPeriod τ + 1))) *
            jacobiTheta₂ (-thetaHalfPeriod τ + 1) τ :=
          jacobiTheta₂_add_left' (-thetaHalfPeriod τ + 1) τ
      _ = -jacobiTheta₂ (thetaHalfPeriod τ) τ := by
          rw [thetaHalfPeriod_quasiFactor, neg_one_mul,
            jacobiTheta₂_add_left, jacobiTheta₂_neg_left]
  exact CharZero.eq_neg_self_iff.mp hneg

/-- A theta zero propagates through every integral multiple of the quasiperiod `τ`.  The backward
step is legitimate because the exponential quasiperiod multiplier never vanishes. -/
theorem jacobiTheta₂_eq_zero_add_int_mul_tau {z τ : ℂ}
    (hz : jacobiTheta₂ z τ = 0) (n : ℤ) :
    jacobiTheta₂ (z + (n : ℂ) * τ) τ = 0 := by
  induction n using Int.induction_on with
  | zero => simpa using hz
  | succ n ih =>
      have harg : z + (((n : ℤ) + 1 : ℤ) : ℂ) * τ =
          (z + ((n : ℤ) : ℂ) * τ) + τ := by
        push_cast
        ring
      rw [harg, jacobiTheta₂_add_left', ih, mul_zero]
  | pred n ih =>
      let w : ℂ := z + ((-(n : ℤ) - 1 : ℤ) : ℂ) * τ
      have harg : w + τ = z + ((-(n : ℤ) : ℤ) : ℂ) * τ := by
        dsimp [w]
        push_cast
        ring
      have hstep := jacobiTheta₂_add_left' w τ
      rw [harg, ih] at hstep
      have hprod :
          Complex.exp (-Real.pi * Complex.I * (τ + 2 * w)) * jacobiTheta₂ w τ = 0 :=
        hstep.symm
      exact (mul_eq_zero.mp hprod).resolve_left (Complex.exp_ne_zero _)

/-- A theta zero propagates through every integral period. -/
theorem jacobiTheta₂_eq_zero_add_int {z τ : ℂ}
    (hz : jacobiTheta₂ z τ = 0) (m : ℤ) :
    jacobiTheta₂ (z + (m : ℂ)) τ = 0 := by
  have hper : Function.Periodic (fun w : ℂ ↦ jacobiTheta₂ w τ) 1 :=
    fun w ↦ jacobiTheta₂_add_left w τ
  have hm := hper.int_mul m z
  simpa only [Int.cast_ofNat, mul_one] using hm.trans hz

/-- **Full odd-half-period zero orbit.** Every translate of `(1+τ)/2` by the lattice
`ℤ + τℤ` is a zero of `jacobiTheta₂`. -/
theorem jacobiTheta₂_thetaHalfPeriod_add_lattice_eq_zero
    (τ : ℂ) (m n : ℤ) :
    jacobiTheta₂ (thetaHalfPeriod τ + (m : ℂ) + (n : ℂ) * τ) τ = 0 := by
  have hn := jacobiTheta₂_eq_zero_add_int_mul_tau
    (jacobiTheta₂_thetaHalfPeriod_eq_zero τ) n
  have hm := jacobiTheta₂_eq_zero_add_int hn m
  convert hm using 2
  ring

/-- Shifting the modular parameter by one is equivalent to shifting the elliptic variable by one
half, for the `z`-derivative of theta. -/
theorem jacobiTheta₂'_add_right_one (z τ : ℂ) :
    jacobiTheta₂' z (τ + 1) = jacobiTheta₂' (z + 1 / 2) τ := by
  unfold jacobiTheta₂' jacobiTheta₂'_term jacobiTheta₂_term
  refine tsum_congr fun n ↦ ?_
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, n ^ 2 - n = 2 * k := by
    obtain ⟨m, hm⟩ := Int.even_mul_succ_self (n - 1)
    exact ⟨m, by linear_combination hm⟩
  have hcast : (n : ℂ) ^ 2 - (n : ℂ) = 2 * (k : ℂ) := by
    exact_mod_cast hk
  refine ⟨k, ?_⟩
  linear_combination (Real.pi * Complex.I) * hcast

/-- The half-period derivative is invariant under `τ ↦ τ+1`. -/
theorem thetaHalfPeriodDerivative_add_one (τ : ℂ) :
    thetaHalfPeriodDerivative (τ + 1) = thetaHalfPeriodDerivative τ := by
  rw [thetaHalfPeriodDerivative, thetaHalfPeriodDerivative,
    jacobiTheta₂'_add_right_one]
  have harg : thetaHalfPeriod (τ + 1) + 1 / 2 = thetaHalfPeriod τ + 1 := by
    simp only [thetaHalfPeriod]
    ring
  rw [harg, jacobiTheta₂'_add_left]

end

end GaloisForLFunctions
