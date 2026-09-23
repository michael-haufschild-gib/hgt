import GaloisForLFunctions.RHTower.LiEvenCrossCriticalAbelBoundaryNoGo

/-!
# LI Cayley square defect and critical prime sign wall

The corpus identity behind the even-Li square is exposed over `ℝ`: every critical common-reversal
density is exactly one half of a first-kind Chebyshev square defect and therefore lies in
`[0,1/2]`. This is the strongest positive survivor of the critical Abel boundary no-go.

The zeroth mode nevertheless has a Fourier sign wall at `|ξ| = 2`. At prime frequencies its
signed literal von Mangoldt leg is exactly `(π/2)(Λ(n)/n)(1-log(n)/2)`, is eventually nonpositive,
and is not summable. Hence neither pointwise density positivity, Fourier coefficient positivity,
nor ordinary signed summation can produce LI's completed cross capital. Prime, polar, and Gamma
terms must remain coupled in one Abel/Hadamard finite part.

Corpus provenance: `LiArithmeticProgressionSquareSourceCriterion` supplies the Chebyshev norm
identity; `LiEvenCrossCriticalAbelBoundaryNoGo` supplies the exact density/Fourier law and harmonic
absolute-divergence wall. RH passport remains the existing chain from completed cross-capital
nonnegativity to even Li positivity and RH.
-/

open Polynomial Real

namespace RHTower

noncomputable section

/-- Real Chebyshev norm identity used by every even-Li mode. -/
theorem chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq_real (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)) ^ (2 : ℕ) +
      (1 - X ^ (2 : ℕ)) * (Polynomial.Chebyshev.U ℝ (n : ℤ)) ^ (2 : ℕ) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.cast_succ]
      rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring]
      rw [Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U ℝ (n : ℤ),
        Polynomial.Chebyshev.U_eq_X_mul_U_add_T ℝ (n : ℤ)]
      linear_combination (norm := ring_nf) ih

/-- Every critical LI cross density is half of one Chebyshev square defect. -/
theorem liCriticalEvenCrossCauchyDensity_eq_chebyshevSquareDefect
    (n : ℕ) (x : ℝ) :
    liCriticalEvenCrossCauchyDensity n x =
      (1 - (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval
        (liCriticalCayleyCoordinate x) ^ (2 : ℕ)) / 2 := by
  rw [liCriticalEvenCrossCauchyDensity_eq_squareDefect]
  have hnorm := congrArg
    (fun P : Polynomial ℝ => P.eval (liCriticalCayleyCoordinate x))
    (chebyshevT_sq_add_one_sub_X_sq_mul_chebyshevU_sq_real n)
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X] at hnorm
  rw [liEvenCrossLeftPolynomial]
  linarith

/-- Uniform all-mode upper wall forced by the exact square defect. -/
theorem liCriticalEvenCrossCauchyDensity_le_half (n : ℕ) (x : ℝ) :
    liCriticalEvenCrossCauchyDensity n x ≤ 1 / 2 := by
  rw [liCriticalEvenCrossCauchyDensity_eq_chebyshevSquareDefect]
  nlinarith [sq_nonneg ((Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).eval
    (liCriticalCayleyCoordinate x))]

/-- Closed all-mode range classification of the critical LI density. -/
theorem liCriticalEvenCrossCauchyDensity_mem_unitHalf (n : ℕ) (x : ℝ) :
    liCriticalEvenCrossCauchyDensity n x ∈ Set.Icc 0 (1 / 2) :=
  ⟨liCriticalEvenCrossCauchyDensity_nonneg n x,
    liCriticalEvenCrossCauchyDensity_le_half n x⟩

/-- Real Fourier profile of the zeroth LI cross mode. -/
theorem routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re (ξ : ℝ) :
    (routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) ξ).re =
      Real.pi / 2 * Real.exp (-|ξ| / 2) * (1 - |ξ| / 2) := by
  have h := congrArg Complex.re
    (routeUFourierIntegral_liCriticalFirstCrossCauchyDensity ξ)
  norm_num at h
  rw [show -((|ξ| : ℝ) : ℂ) / 2 = ((-|ξ| / 2 : ℝ) : ℂ) by
    push_cast
    ring, Complex.exp_ofReal_re] at h
  exact h

/-- Exact high-frequency sign wall: negativity starts precisely beyond frequency two. -/
theorem routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re_neg_iff
    (ξ : ℝ) :
    (routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) ξ).re < 0 ↔ 2 < |ξ| := by
  rw [routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re]
  have hpos : 0 < Real.pi / 2 * Real.exp (-|ξ| / 2) := by positivity
  constructor <;> intro h <;> nlinarith

/-- Exact Fourier nodal wall of the zeroth LI cross mode. -/
theorem routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re_eq_zero_iff
    (ξ : ℝ) :
    (routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) ξ).re = 0 ↔ |ξ| = 2 := by
  rw [routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re]
  have hpos : 0 < Real.pi / 2 * Real.exp (-|ξ| / 2) := by positivity
  constructor <;> intro h <;> nlinarith

/-- Normalized signed harmonic von Mangoldt weight at the critical LI boundary. -/
def liCriticalFirstCrossPrimeSignedWeight (n : ℕ) : ℝ :=
  finiteVonMangoldtRealWeight n * (1 - Real.log n / 2)

/-- Literal signed prime leg formed from the Fourier profile at `log n`. -/
def liCriticalFirstCrossPrimeLegSignedWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (routeUFourierIntegral (fun x : ℝ =>
      (liCriticalFirstCrossCauchyDensity x : ℂ)) (Real.log n)).re

private theorem exp_neg_log_nat_div_two_div_sqrt
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-Real.log (n : ℝ) / 2) / Real.sqrt n = 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    have hsq : Real.exp (Real.log (n : ℝ) / 2) ^ (2 : ℕ) = n := by
      rw [← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (Real.log (n : ℝ) / 2) = Real.log n by
          push_cast
          ring]
      exact Real.exp_log hnR
    calc
      Real.sqrt (n : ℝ) = Real.sqrt (Real.exp (Real.log n / 2) ^ (2 : ℕ)) := by rw [hsq]
      _ = Real.exp (Real.log n / 2) := Real.sqrt_sq (Real.exp_pos _).le
  rw [hsqrt, ← Real.exp_sub]
  rw [show -Real.log (n : ℝ) / 2 - Real.log n / 2 = -Real.log n by ring]
  rw [Real.exp_neg, Real.exp_log hnR]
  simp [one_div]

/-- Exact reduction of the literal signed prime leg to its harmonic boundary weight. -/
theorem liCriticalFirstCrossPrimeLegSignedWeight_eq (n : ℕ) :
    liCriticalFirstCrossPrimeLegSignedWeight n =
      Real.pi / 2 * liCriticalFirstCrossPrimeSignedWeight n := by
  rcases n with _ | n
  · simp [liCriticalFirstCrossPrimeLegSignedWeight,
      liCriticalFirstCrossPrimeSignedWeight, finiteVonMangoldtRealWeight]
  · have hn : 0 < n + 1 := by omega
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    rw [liCriticalFirstCrossPrimeLegSignedWeight,
      routeUFourierIntegral_liCriticalFirstCrossCauchyDensity_re,
      abs_of_nonneg hlog, liCriticalFirstCrossPrimeSignedWeight,
      finiteVonMangoldtRealWeight]
    have hratio := exp_neg_log_nat_div_two_div_sqrt hn
    push_cast at hratio ⊢
    calc
      ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1) *
          (Real.pi / 2 * Real.exp (-Real.log (n + 1) / 2) *
            (1 - Real.log (n + 1) / 2)) =
          Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) *
              (Real.exp (-Real.log (n + 1) / 2) / Real.sqrt (n + 1))) *
            (1 - Real.log (n + 1) / 2) := by ring
      _ = Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) / (n + 1)) *
            (1 - Real.log (n + 1) / 2) := by rw [hratio]; ring
      _ = Real.pi / 2 *
            (ArithmeticFunction.vonMangoldt (n + 1) / (n + 1) *
              (1 - Real.log (n + 1) / 2)) := by ring

/-- The critical signed prime boundary has a cofinal nonpositive tail. -/
theorem liCriticalFirstCrossPrimeSignedWeight_eventually_nonpos :
    ∀ᶠ n : ℕ in Filter.atTop,
      liCriticalFirstCrossPrimeSignedWeight n ≤ 0 := by
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 2)
  filter_upwards [hlog] with n hn
  exact mul_nonpos_of_nonneg_of_nonpos
    (finiteVonMangoldtRealWeight_nonneg n) (by linarith)

/-- Absolute value of the signed boundary is the previously classified absolute wall. -/
theorem abs_liCriticalFirstCrossPrimeSignedWeight (n : ℕ) :
    |liCriticalFirstCrossPrimeSignedWeight n| =
      liCriticalFirstCrossPrimeAbsoluteWeight n := by
  rw [liCriticalFirstCrossPrimeSignedWeight,
    liCriticalFirstCrossPrimeAbsoluteWeight, abs_mul,
    abs_of_nonneg (finiteVonMangoldtRealWeight_nonneg n)]

/-- The normalized signed critical prime boundary does not converge as an ordinary series. -/
theorem not_summable_liCriticalFirstCrossPrimeSignedWeight :
    ¬ Summable liCriticalFirstCrossPrimeSignedWeight := by
  intro hsum
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    liCriticalFirstCrossPrimeSignedWeight_eventually_nonpos
  have hshift : Summable (fun k : ℕ =>
      liCriticalFirstCrossPrimeSignedWeight (k + N)) := by
    exact hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hshiftAbs : Summable (fun k : ℕ =>
      liCriticalFirstCrossPrimeAbsoluteWeight (k + N)) := by
    refine hshift.neg.congr (fun k => ?_)
    rw [← abs_liCriticalFirstCrossPrimeSignedWeight]
    exact (abs_of_nonpos (hN (k + N) (by omega))).symm
  exact not_summable_liCriticalFirstCrossPrimeAbsoluteWeight
    ((summable_nat_add_iff N).mp hshiftAbs)

/-- The literal signed zeroth-mode prime leg is not summable. -/
theorem not_summable_liCriticalFirstCrossPrimeLegSignedWeight :
    ¬ Summable liCriticalFirstCrossPrimeLegSignedWeight := by
  intro hsum
  have hscaled : Summable (fun n : ℕ =>
      Real.pi / 2 * liCriticalFirstCrossPrimeSignedWeight n) :=
    hsum.congr (fun n => liCriticalFirstCrossPrimeLegSignedWeight_eq n)
  have hrecover := hscaled.mul_left (2 / Real.pi)
  have : Summable liCriticalFirstCrossPrimeSignedWeight := by
    exact hrecover.congr (fun n => by field_simp [Real.pi_ne_zero])
  exact not_summable_liCriticalFirstCrossPrimeSignedWeight this

end

end RHTower
