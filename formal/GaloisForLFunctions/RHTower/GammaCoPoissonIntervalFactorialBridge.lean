import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Gamma factorial conormal as the co-Poisson interval cell

The complete factorial-tail Gamma conormal has generating function

`C(z) = ∑ n, z^n / (n+1)!`.

For a logarithmic interval of length `L`, its pairing with the raw exponential
jet is exactly the confluent co-Poisson divided-difference cell. Thus the
Gamma Taylor conormal and the compact-log-support Burnol interval source are
one local object, not parallel analogies.

This file proves the local source comparison. It does not perform the
all-prime Möbius condensation, construct the Gamma/co-Poisson/Sonin exact
couple, or land an Xi conormal.
-/

open Complex

namespace RHTower

noncomputable section

/-- Complex generating function of the complete factorial-tail Gamma
conormal. -/
def gammaFactorialComplexCompression (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((n + 1).factorial : ℂ)

/-- The factorial-tail generating function is the entire divided exponential
increment, in a form valid also at `z = 0`. -/
theorem mul_gammaFactorialComplexCompression
    (z : ℂ) :
    z * gammaFactorialComplexCompression z = Complex.exp z - 1 := by
  let e : ℕ → ℂ := fun n => z ^ n / (n.factorial : ℂ)
  have hexp : HasSum e (Complex.exp z) := by
    simpa [e, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp z)
  have htail : HasSum (fun n => e (n + 1)) (Complex.exp z - 1) := by
    have h := (hasSum_nat_add_iff' (f := e) 1).mpr hexp
    simpa [e] using h
  have hterm :
      (fun n : ℕ =>
        z * (z ^ n / ((n + 1).factorial : ℂ))) =
        fun n : ℕ => e (n + 1) := by
    funext n
    dsimp [e]
    rw [Nat.factorial_succ]
    push_cast
    ring_nf
  rw [← hterm] at htail
  simpa [gammaFactorialComplexCompression, tsum_mul_left] using htail.tsum_eq

/-- The literal Gamma/co-Poisson interval cell. With `L = log p`, this is

`p^(w-1/2) log(p) C((z-w) log(p))`.

The exponential convention avoids branch ambiguity for complex powers. -/
def gammaCoPoissonIntervalCell (L z w : ℂ) : ℂ :=
  Complex.exp ((w - 1 / 2) * L) * L *
    gammaFactorialComplexCompression ((z - w) * L)

/-- **Factorial-conormal/interval boundary law.** Applying the spectral
boundary `z-w` to the Gamma factorial cell gives the difference of the two
endpoint characters. -/
theorem spectralBoundary_mul_gammaCoPoissonIntervalCell
    (L z w : ℂ) :
    (z - w) * gammaCoPoissonIntervalCell L z w =
      Complex.exp ((z - 1 / 2) * L) -
        Complex.exp ((w - 1 / 2) * L) := by
  calc
    (z - w) * gammaCoPoissonIntervalCell L z w =
        Complex.exp ((w - 1 / 2) * L) *
          (((z - w) * L) *
            gammaFactorialComplexCompression ((z - w) * L)) := by
      simp only [gammaCoPoissonIntervalCell]
      ring
    _ = Complex.exp ((w - 1 / 2) * L) *
          (Complex.exp ((z - w) * L) - 1) := by
      rw [mul_gammaFactorialComplexCompression]
    _ = Complex.exp ((z - 1 / 2) * L) -
          Complex.exp ((w - 1 / 2) * L) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      ring_nf

/-- Off the spectral diagonal, the factorial cell is exactly the usual
co-Poisson divided difference. -/
theorem gammaCoPoissonIntervalCell_eq_dividedDifference
    (L z w : ℂ) (hzw : z ≠ w) :
    gammaCoPoissonIntervalCell L z w =
      (Complex.exp ((z - 1 / 2) * L) -
        Complex.exp ((w - 1 / 2) * L)) / (z - w) := by
  apply (eq_div_iff (sub_ne_zero.mpr hzw)).2
  rw [mul_comm]
  exact spectralBoundary_mul_gammaCoPoissonIntervalCell L z w

/-- On confluence, the same entire cell is the logarithmic tangent character.
For `L = log p`, its value is `p^(w-1/2) log p`. -/
@[simp] theorem gammaCoPoissonIntervalCell_self
    (L w : ℂ) :
    gammaCoPoissonIntervalCell L w w =
      Complex.exp ((w - 1 / 2) * L) * L := by
  have hzero : gammaFactorialComplexCompression 0 = 1 := by
    rw [gammaFactorialComplexCompression]
    calc
      (∑' n : ℕ, (0 : ℂ) ^ n / ((n + 1).factorial : ℂ)) =
          (0 : ℂ) ^ 0 / ((0 + 1).factorial : ℂ) := by
        apply tsum_eq_single 0
        intro b hb
        simp [zero_pow hb]
      _ = 1 := by simp
  simp [gammaCoPoissonIntervalCell, hzero]

/-- **Logarithmic-interval concatenation law.**  The factorial/co-Poisson
cell is a relative character cocycle for addition of logarithmic actions.
After setting `L₁ = log m` and `L₂ = log n`, this is the multiplicative
source law for the action `mn`.

The identity remains valid on spectral confluence, where the divided
difference becomes the logarithmic tangent character. -/
theorem gammaCoPoissonIntervalCell_add
    (L₁ L₂ z w : ℂ) :
    gammaCoPoissonIntervalCell (L₁ + L₂) z w =
      Complex.exp ((z - 1 / 2) * L₁) *
          gammaCoPoissonIntervalCell L₂ z w +
        gammaCoPoissonIntervalCell L₁ z w *
          Complex.exp ((w - 1 / 2) * L₂) := by
  by_cases hzw : z = w
  · subst z
    simp only [gammaCoPoissonIntervalCell_self]
    rw [show (w - 1 / 2) * (L₁ + L₂) =
        (w - 1 / 2) * L₁ + (w - 1 / 2) * L₂ by ring,
      Complex.exp_add]
    ring
  · rw [gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hzw,
      gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hzw,
      gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hzw]
    rw [show (z - 1 / 2) * (L₁ + L₂) =
        (z - 1 / 2) * L₁ + (z - 1 / 2) * L₂ by ring,
      show (w - 1 / 2) * (L₁ + L₂) =
        (w - 1 / 2) * L₁ + (w - 1 / 2) * L₂ by ring,
      Complex.exp_add, Complex.exp_add]
    field_simp [sub_ne_zero.mpr hzw]
    ring

/-- The factorial/co-Poisson cell is the removable divided slope of one
exponential character, up to the fixed half-density factor. -/
theorem gammaCoPoissonIntervalCell_eq_dslope
    (L z w : ℂ) :
    gammaCoPoissonIntervalCell L z w =
      Complex.exp (-(L / 2)) *
        dslope (fun u : ℂ => Complex.exp (L * u)) w z := by
  by_cases hzw : z = w
  · subst z
    rw [gammaCoPoissonIntervalCell_self, dslope_same,
      ← iteratedDeriv_one,
      GaloisForLFunctions.iteratedDeriv_exp_linear]
    rw [show (w - 1 / 2) * L = -(L / 2) + L * w by ring,
      Complex.exp_add]
    ring
  · rw [gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hzw,
      dslope_of_ne _ hzw, slope_def_module]
    simp only [smul_eq_mul]
    rw [show (z - 1 / 2) * L = -(L / 2) + L * z by ring,
      show (w - 1 / 2) * L = -(L / 2) + L * w by ring,
      Complex.exp_add, Complex.exp_add]
    field_simp [sub_ne_zero.mpr hzw]

/-- **Complete local multiplicity-jet law.**  Every spectral conormal order
of the factorial/co-Poisson interval survives at confluence with its exact
factorial coefficient. -/
theorem iteratedDeriv_gammaCoPoissonIntervalCell_self
    (L w : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z =>
      gammaCoPoissonIntervalCell L z w) w =
      Complex.exp ((w - 1 / 2) * L) *
        L ^ (k + 1) / (k + 1 : ℂ) := by
  rw [show (fun z =>
      gammaCoPoissonIntervalCell L z w) =
        fun z =>
          Complex.exp (-(L / 2)) *
            dslope (fun u : ℂ => Complex.exp (L * u)) w z by
      funext z
      exact gammaCoPoissonIntervalCell_eq_dslope L z w]
  rw [iteratedDeriv_const_mul_field]
  have hanalytic :
      AnalyticAt ℂ (fun u : ℂ => Complex.exp (L * u)) w :=
    (analyticAt_const.mul analyticAt_id).cexp
  rw [HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div
      hanalytic k,
    GaloisForLFunctions.iteratedDeriv_exp_linear]
  rw [show (w - 1 / 2) * L = -(L / 2) + L * w by ring,
    Complex.exp_add]
  ring

/-- No finite multiplicity jet is killed by the local factorial receiver at
a nonzero logarithmic action. -/
theorem iteratedDeriv_gammaCoPoissonIntervalCell_self_ne_zero
    {L w : ℂ} (hL : L ≠ 0) (k : ℕ) :
    iteratedDeriv k (fun z =>
      gammaCoPoissonIntervalCell L z w) w ≠ 0 := by
  rw [iteratedDeriv_gammaCoPoissonIntervalCell_self]
  exact div_ne_zero
    (mul_ne_zero (Complex.exp_ne_zero _)
      (pow_ne_zero (k + 1) hL))
    (by exact_mod_cast (Nat.succ_ne_zero k))

end

end RHTower
