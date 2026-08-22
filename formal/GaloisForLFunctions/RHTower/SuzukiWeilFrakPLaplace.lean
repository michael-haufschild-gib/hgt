import GaloisForLFunctions.RHTower.SuzukiWeilFrakP
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener
import GaloisForLFunctions.RHTower.WeightedLaplaceShift
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure

/-!
# The Laplace transform of Suzuki's function `𝔓_t`

Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3), proves
Proposition 3.1 (`𝔓_t = P_t`) by applying Weil's explicit formula to the non-smooth, non-compactly
supported test function `φ_{z,t}`.  This module instead computes the **Laplace transform of `𝔓_t`
in `t`** in closed form; the companion module `SuzukiWeilZeroSeries` does the same for the Xi-zero
series `P_t`, and the two closed forms are literally the same object.  That reduces Proposition 3.1
to the corpus's already-owned regularized-Cauchy explicit formula plus Laplace determinacy, and
avoids re-deriving an explicit formula for Suzuki's test class.

Equation (1.6) is split into five blocks

```text
suzukiFrakPPolar, suzukiFrakPZeta, suzukiFrakPPrime, suzukiFrakPDigamma, suzukiFrakPLerch
```

whose Laplace transforms are computed separately, with `s_σ = σ + 1/2` and `s_z = 1/2 - iz`:

```text
polar          →  [1/s_σ + 1/(s_σ-1) - 1/s_z - 1/(s_z-1)] / (σ(σ+iz))
zeta           →  -(ζ'/ζ)(s_z) / (σ(σ+iz))
prime          →  +(ζ'/ζ)(s_σ) / (σ(σ+iz))
digamma+Lerch  →  [ψ(s_σ/2) - ψ(s_z/2)] / (2σ(σ+iz))
```

and the capstone `integral_suzukiFrakP_laplace` assembles them into

```text
∫_0^∞ 𝔓_t(z) e^{-σt} dt
  = ((ζ'/ζ + (log archFactor)')(s_σ) - (ζ'/ζ + (log archFactor)')(s_z)) / (σ(σ+iz)).
```

The prime block is handled through its ray decomposition `suzukiPrimeRayTerm`, whose `n`-th Laplace
mass carries the factor `n^{-σ}`; summing gives the von Mangoldt Dirichlet series at `σ + 1/2`, i.e.
`-(ζ'/ζ)(σ+1/2)`.  The Lerch block is handled through `suzukiLerchRayTerm` and the two partial
fractions `1/((n+w)(n+a)) = (a-w)^{-1}[(n+w)^{-1} - (n+a)^{-1}]` with `a = 1/4 + σ/2`.

Everything here is unconditional.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## A general exponential-ray Laplace transform -/

theorem integrableOn_cexp_sub_one_mul_laplace {c : ℂ} {σ : ℝ} (hc : c.re < σ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => (Complex.exp (c * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hsplit : ∀ t : ℝ,
      (Complex.exp (c * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ)))
        = Complex.exp (-(((σ : ℂ) - c) * (t : ℂ))) - Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
    intro t
    rw [show -(((σ : ℂ) - c) * (t : ℂ)) = c * (t : ℂ) + -((σ : ℂ) * (t : ℂ)) by ring,
      Complex.exp_add]
    ring
  have h1 : IntegrableOn (fun t : ℝ => Complex.exp (-(((σ : ℂ) - c) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
    refine integrableOn_Ioi_cexp_neg_mul ?_
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
    refine integrableOn_Ioi_cexp_neg_mul ?_
    simpa using hσ
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun t => ?_)
  exact (hsplit t).symm

/-- The Laplace transform of an exponential ray minus its base value. -/
theorem integral_cexp_sub_one_mul_laplace {c : ℂ} {σ : ℝ} (hc : c.re < σ) (hσ : 0 < σ) :
    (∫ t in Ioi (0 : ℝ),
        (Complex.exp (c * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ((σ : ℂ) - c)⁻¹ - ((σ : ℂ))⁻¹ := by
  have hre1 : 0 < (((σ : ℂ)) - c).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hre2 : 0 < ((σ : ℂ)).re := by simpa using hσ
  have h1 : IntegrableOn (fun t : ℝ => Complex.exp (-(((σ : ℂ) - c) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := integrableOn_Ioi_cexp_neg_mul hre1
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := integrableOn_Ioi_cexp_neg_mul hre2
  have hsplit : ∀ t : ℝ,
      (Complex.exp (c * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ)))
        = Complex.exp (-(((σ : ℂ) - c) * (t : ℂ))) - Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
    intro t
    rw [show -(((σ : ℂ) - c) * (t : ℂ)) = c * (t : ℂ) + -((σ : ℂ) * (t : ℂ)) by ring,
      Complex.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hsplit t),
    MeasureTheory.integral_sub h1 h2, integral_Ioi_cexp_neg_mul hre1,
    integral_Ioi_cexp_neg_mul hre2]


/-! ## The five blocks of `𝔓_t` -/

/-- The two elementary polar blocks of Suzuki eq. (1.6). -/
def suzukiFrakPPolar (t : ℝ) (z : ℂ) : ℂ :=
  4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)
    + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)

/-- The continued prime-carrier block of Suzuki eq. (1.6). -/
def suzukiFrakPZeta (t : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) * logDeriv riemannZeta (1 / 2 - I * z)

/-- The finite prime-power block of Suzuki eq. (1.6). -/
def suzukiFrakPPrime (t : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
    (screwPrimeWeight n : ℂ) *
      ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z))

/-- The digamma block of Suzuki eq. (1.6); it does not depend on `t`. -/
def suzukiFrakPDigamma (z : ℂ) : ℂ :=
  -((Complex.digamma (1 / 4 - I * z / 2) - Complex.digamma (1 / 4)) / (2 * I * z))

/-- The Lerch block of Suzuki eq. (1.6). -/
def suzukiFrakPLerch (t : ℝ) (z : ℂ) : ℂ :=
  -((Real.exp (-(t / 2)) : ℂ) * suzukiLerchDiff t (1 / 4 - I * z / 2) / (2 * I * z))

theorem suzukiFrakP_eq_blocks (t : ℝ) (z : ℂ) :
    suzukiFrakP t z = suzukiFrakPPolar t z + suzukiFrakPZeta t z + suzukiFrakPPrime t z
      + suzukiFrakPDigamma z + suzukiFrakPLerch t z := by
  rw [suzukiFrakP, suzukiFrakPPolar, suzukiFrakPZeta, suzukiFrakPPrime,
    suzukiFrakPDigamma, suzukiFrakPLerch]
  ring

/-! ## Laplace transform of the polar block -/

theorem ofReal_exp_half (a t : ℝ) :
    ((Real.exp (a * t) : ℝ) : ℂ) = Complex.exp (((a : ℂ)) * (t : ℂ)) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

theorem integrableOn_suzukiFrakPPolar_laplace {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h1 := integrableOn_cexp_sub_one_mul_laplace (c := ((1 / 2 : ℝ) : ℂ)) (σ := σ)
    (by simpa using hσ) hσ0
  have h2 := integrableOn_cexp_sub_one_mul_laplace (c := ((-1 / 2 : ℝ) : ℂ)) (σ := σ)
    (by simp; linarith) hσ0
  refine ((h1.const_mul (4 / (1 + 2 * I * z))).add
    (h2.const_mul (4 / (1 - 2 * I * z)))).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, suzukiFrakPPolar]
  have e1 : ((Real.exp (t / 2) : ℝ) : ℂ) = Complex.exp (((1 / 2 : ℝ) : ℂ) * (t : ℂ)) := by
    have := ofReal_exp_half (1 / 2) t
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring] at this
    simpa using this
  have e2 : ((Real.exp (-(t / 2)) : ℝ) : ℂ) = Complex.exp (((-1 / 2 : ℝ) : ℂ) * (t : ℂ)) := by
    have := ofReal_exp_half (-1 / 2) t
    rw [show (-1 / 2 : ℝ) * t = -(t / 2) by ring] at this
    simpa using this
  rw [e1, e2]
  ring

theorem integral_suzukiFrakPPolar_laplace {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = 4 / (1 + 2 * I * z) * (((σ : ℂ) - 1 / 2)⁻¹ - ((σ : ℂ))⁻¹)
        + 4 / (1 - 2 * I * z) * (((σ : ℂ) + 1 / 2)⁻¹ - ((σ : ℂ))⁻¹) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hc1 : (((1 / 2 : ℝ) : ℂ)).re < σ := by simpa using hσ
  have hc2 : (((-1 / 2 : ℝ) : ℂ)).re < σ := by simp; linarith
  have h1 := integrableOn_cexp_sub_one_mul_laplace hc1 hσ0
  have h2 := integrableOn_cexp_sub_one_mul_laplace hc2 hσ0
  have hcongr : ∀ t : ℝ, suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
      = 4 / (1 + 2 * I * z) *
          ((Complex.exp (((1 / 2 : ℝ) : ℂ) * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        + 4 / (1 - 2 * I * z) *
          ((Complex.exp (((-1 / 2 : ℝ) : ℂ) * (t : ℂ)) - 1)
            * Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
    intro t
    rw [suzukiFrakPPolar]
    have e1 : ((Real.exp (t / 2) : ℝ) : ℂ) = Complex.exp (((1 / 2 : ℝ) : ℂ) * (t : ℂ)) := by
      have := ofReal_exp_half (1 / 2) t
      rw [show (1 / 2 : ℝ) * t = t / 2 by ring] at this
      simpa using this
    have e2 : ((Real.exp (-(t / 2)) : ℝ) : ℂ) = Complex.exp (((-1 / 2 : ℝ) : ℂ) * (t : ℂ)) := by
      have := ofReal_exp_half (-1 / 2) t
      rw [show (-1 / 2 : ℝ) * t = -(t / 2) by ring] at this
      simpa using this
    rw [e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t),
    MeasureTheory.integral_add (h1.const_mul _) (h2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_cexp_sub_one_mul_laplace hc1 hσ0, integral_cexp_sub_one_mul_laplace hc2 hσ0]
  norm_num


/-! ## Laplace transform of the continued prime-carrier and digamma blocks -/

theorem re_neg_I_mul (z : ℂ) : (-(I * z)).re = z.im := by
  simp [Complex.mul_re]

theorem integrableOn_suzukiFrakPZeta_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz : z.im < σ) :
    IntegrableOn (fun t : ℝ => suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hc : (-(I * z)).re < σ := by rw [re_neg_I_mul]; exact hz
  have h1 := integrableOn_cexp_sub_one_mul_laplace hc hσ
  refine (h1.const_mul (logDeriv riemannZeta (1 / 2 - I * z) / (I * z))).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [suzukiFrakPZeta]
  rw [show -(I * z) * (t : ℂ) = -(I * z * (t : ℂ)) by ring]
  ring

theorem integral_suzukiFrakPZeta_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz : z.im < σ) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = logDeriv riemannZeta (1 / 2 - I * z) / (I * z) *
          (((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) := by
  have hc : (-(I * z)).re < σ := by rw [re_neg_I_mul]; exact hz
  have hcongr : ∀ t : ℝ, suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
      = logDeriv riemannZeta (1 / 2 - I * z) / (I * z) *
          ((Complex.exp (-(I * z) * (t : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
    intro t
    simp only [suzukiFrakPZeta]
    rw [show -(I * z) * (t : ℂ) = -(I * z * (t : ℂ)) by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t),
    MeasureTheory.integral_const_mul, integral_cexp_sub_one_mul_laplace hc hσ]
  congr 2
  ring

theorem integrableOn_suzukiFrakPDigamma_laplace {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume :=
  (integrableOn_Ioi_cexp_neg_mul (by simpa using hσ)).const_mul _

theorem integral_suzukiFrakPDigamma_laplace {σ : ℝ} (hσ : 0 < σ) (z : ℂ) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = suzukiFrakPDigamma z * ((σ : ℂ))⁻¹ := by
  rw [MeasureTheory.integral_const_mul, integral_Ioi_cexp_neg_mul (by simpa using hσ)]


/-! ## Laplace transform of the finite prime-power block -/

/-- One prime-power ray of Suzuki's finite block, extended by zero to the left of its atom. -/
def suzukiPrimeRayTerm (z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  if Real.log n ≤ t then
    (screwPrimeWeight n : ℂ) *
      ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z))
  else 0

theorem screwPrimeWeight_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : screwPrimeWeight n = 0 := by
  interval_cases n <;> simp [screwPrimeWeight]

/-- The finite block is the everywhere-convergent ray sum. -/
theorem suzukiFrakPPrime_eq_tsum (t : ℝ) (z : ℂ) :
    suzukiFrakPPrime t z = ∑' n : ℕ, suzukiPrimeRayTerm z n t := by
  have hzero : ∀ n ∉ Finset.Icc 2 ⌊Real.exp t⌋₊, suzukiPrimeRayTerm z n t = 0 := by
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with h | h
    · rw [suzukiPrimeRayTerm]
      split_ifs
      · rw [screwPrimeWeight_eq_zero_of_lt_two h]
        simp
      · rfl
    · rw [suzukiPrimeRayTerm, if_neg]
      intro hle
      have hn1 : 1 ≤ n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hle' : (n : ℝ) ≤ Real.exp t := by
        rw [← Real.exp_log hnpos]
        exact Real.exp_le_exp.mpr hle
      have hfl : n ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by exact_mod_cast hle')
      omega
  have hsum : (∑' n : ℕ, suzukiPrimeRayTerm z n t)
      = ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, suzukiPrimeRayTerm z n t := tsum_eq_sum hzero
  rw [hsum, suzukiFrakPPrime]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hle : (n : ℝ) ≤ Real.exp t := by
    calc (n : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hn.2
      _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
  have hlog : Real.log n ≤ t := by
    rw [← Real.log_exp t]
    exact Real.log_le_log hnpos hle
  rw [suzukiPrimeRayTerm, if_pos hlog]

/-- Real part of the ray exponent. -/
theorem re_neg_I_mul_ofReal (z : ℂ) (w : ℝ) : (-(I * z * (w : ℂ))).re = w * z.im := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Norm bound for one prime-power Laplace ray. -/
theorem norm_suzukiPrimeRayTerm_laplace_le (σ : ℝ) (z : ℂ) (n : ℕ) (t : ℝ) :
    ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖
      ≤ (|screwPrimeWeight n| / ‖z‖) *
          (Real.exp (-(Real.log n * z.im)) * Real.exp (-((σ - z.im) * t))
            + Real.exp (-(σ * t))) := by
  have hMnn : (0 : ℝ) ≤ (|screwPrimeWeight n| / ‖z‖) *
      (Real.exp (-(Real.log n * z.im)) * Real.exp (-((σ - z.im) * t))
        + Real.exp (-(σ * t))) := by positivity
  have hcast : ((t : ℂ) - ((Real.log n : ℝ) : ℂ)) = (((t - Real.log n : ℝ)) : ℂ) := by
    push_cast; ring
  rw [suzukiPrimeRayTerm]
  split_ifs with hif
  · rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hIz : ‖I * z‖ = ‖z‖ := by rw [norm_mul, norm_I, one_mul]
      have hexpσ : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      have hexpz : ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ))))‖
          = Real.exp ((t - Real.log n) * z.im) := by
        rw [hcast, Complex.norm_exp, re_neg_I_mul_ofReal]
      have hb : ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1‖
          ≤ Real.exp ((t - Real.log n) * z.im) + 1 := by
        calc ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1‖
            ≤ ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ))))‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
          _ = Real.exp ((t - Real.log n) * z.im) + 1 := by rw [hexpz, norm_one]
      have hsplit : Real.exp ((t - Real.log n) * z.im) * Real.exp (-(σ * t))
          = Real.exp (-(Real.log n * z.im)) * Real.exp (-((σ - z.im) * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [norm_mul, norm_mul, norm_div, hIz, hexpσ, Complex.norm_real, Real.norm_eq_abs]
      calc |screwPrimeWeight n| *
            (‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1‖ / ‖z‖)
              * Real.exp (-(σ * t))
          ≤ |screwPrimeWeight n| *
              ((Real.exp ((t - Real.log n) * z.im) + 1) / ‖z‖) * Real.exp (-(σ * t)) := by
            gcongr
        _ = (|screwPrimeWeight n| / ‖z‖) *
              (Real.exp ((t - Real.log n) * z.im) * Real.exp (-(σ * t))
                + Real.exp (-(σ * t))) := by ring
        _ = (|screwPrimeWeight n| / ‖z‖) *
              (Real.exp (-(Real.log n * z.im)) * Real.exp (-((σ - z.im) * t))
                + Real.exp (-(σ * t))) := by rw [hsplit]
  · simpa using hMnn

theorem integrableOn_suzukiPrimeRayTerm_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz : z.im < σ)
    (n : ℕ) :
    IntegrableOn (fun t : ℝ => suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hσz : (0 : ℝ) < σ - z.im := by linarith
  have hI1 : IntegrableOn (fun t : ℝ => Real.exp (-((σ - z.im) * t))) (Ioi (0 : ℝ)) volume := by
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hσz).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  have hI2 : IntegrableOn (fun t : ℝ => Real.exp (-(σ * t))) (Ioi (0 : ℝ)) volume := by
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hσ).congr (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  have hmaj : IntegrableOn (fun t : ℝ => (|screwPrimeWeight n| / ‖z‖) *
      (Real.exp (-(Real.log n * z.im)) * Real.exp (-((σ - z.im) * t))
        + Real.exp (-(σ * t)))) (Ioi (0 : ℝ)) volume :=
    Integrable.const_mul ((hI1.const_mul _).add hI2) _
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hcont : Continuous (fun t : ℝ =>
        (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1) / (I * z)) *
          Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by fun_prop
    have hind : (fun t : ℝ => suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        = Set.indicator (Ici (Real.log n)) (fun t : ℝ =>
            (screwPrimeWeight n : ℂ) *
              ((Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1) / (I * z)) *
              Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
      funext t
      rw [suzukiPrimeRayTerm, Set.indicator_apply]
      by_cases h : Real.log n ≤ t
      · rw [if_pos h, if_pos (by exact h)]
      · rw [if_neg h, if_neg (by simpa using h), zero_mul]
    rw [hind]
    exact (hcont.aestronglyMeasurable.indicator measurableSet_Ici).restrict
  refine MeasureTheory.Integrable.mono' hmaj hmeas
    (Filter.Eventually.of_forall fun t => norm_suzukiPrimeRayTerm_laplace_le σ z n t)

/-- The Laplace integrand of one prime ray is an indicator of a continuous function. -/
theorem suzukiPrimeRayTerm_laplace_eq_indicator (σ : ℝ) (z : ℂ) (n : ℕ) :
    (fun t : ℝ => suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = Set.indicator (Ici (Real.log n)) (fun t : ℝ =>
          (screwPrimeWeight n : ℂ) *
            ((Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1) / (I * z)) *
            Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
  funext t
  rw [suzukiPrimeRayTerm, Set.indicator_apply]
  by_cases h : Real.log n ≤ t
  · rw [if_pos h, if_pos (by exact h)]
  · rw [if_neg h, if_neg (by simpa using h), zero_mul]

/-- Exact Laplace transform of one prime-power ray. -/
theorem integral_suzukiPrimeRayTerm_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz : z.im < σ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (screwPrimeWeight n : ℂ) * Complex.exp (-((σ : ℂ) * ((Real.log n : ℝ) : ℂ))) / (I * z) *
          (((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) := by
  have hc : (-(I * z)).re < σ := by rw [re_neg_I_mul]; exact hz
  rcases lt_or_ge n 2 with hn | hn
  · have hw : screwPrimeWeight n = 0 := screwPrimeWeight_eq_zero_of_lt_two hn
    have hzero : ∀ t : ℝ, suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))) = 0 := by
      intro t
      rw [suzukiPrimeRayTerm]
      split_ifs <;> simp [hw]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hzero t)]
    simp [hw]
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hcpos : (0 : ℝ) < Real.log n := Real.log_pos hn1
    set c : ℝ := Real.log n with hcdef
    set G : ℝ → ℂ := fun t : ℝ =>
      (screwPrimeWeight n : ℂ) *
        ((Complex.exp (-(I * z * ((t : ℂ) - ((c : ℝ) : ℂ)))) - 1) / (I * z)) *
        Complex.exp (-((σ : ℂ) * (t : ℂ))) with hG
    have hstep1 : (∫ t in Ioi (0 : ℝ), suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        = ∫ t in Ioi (0 : ℝ) ∩ Ici c, G t := by
      rw [suzukiPrimeRayTerm_laplace_eq_indicator σ z n]
      exact MeasureTheory.setIntegral_indicator measurableSet_Ici
    have hinter : Ioi (0 : ℝ) ∩ Ici c = Ici c := by
      refine Set.inter_eq_right.mpr fun x hx => ?_
      exact lt_of_lt_of_le hcpos hx
    have hstep2 : (∫ t in Ici c, G t) = ∫ t in Ioi c, G t :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    have hstep3 : (∫ y in Ioi (0 : ℝ), G (y + c)) = ∫ x in Ioi c, G x := by
      have h := setIntegral_Ioi_comp_add_right G c c
      rwa [sub_self] at h
    have hstep4 : ∀ y : ℝ, G (y + c)
        = (screwPrimeWeight n : ℂ) * Complex.exp (-((σ : ℂ) * ((c : ℝ) : ℂ))) / (I * z) *
            ((Complex.exp (-(I * z) * (y : ℂ)) - 1) * Complex.exp (-((σ : ℂ) * (y : ℂ)))) := by
      intro y
      rw [hG]
      simp only
      have e1 : (((y + c : ℝ)) : ℂ) - ((c : ℝ) : ℂ) = ((y : ℝ) : ℂ) := by push_cast; ring
      rw [e1]
      have e2 : -((σ : ℂ) * (((y + c : ℝ)) : ℂ))
          = -((σ : ℂ) * ((c : ℝ) : ℂ)) + -((σ : ℂ) * ((y : ℝ) : ℂ)) := by push_cast; ring
      rw [e2, Complex.exp_add, show -(I * z) * (y : ℂ) = -(I * z * (y : ℂ)) by ring]
      ring
    rw [hstep1, hinter, hstep2, ← hstep3,
      setIntegral_congr_fun measurableSet_Ioi (fun y _ => hstep4 y),
      MeasureTheory.integral_const_mul, integral_cexp_sub_one_mul_laplace hc hσ]
    congr 2
    ring

/-- The `n`-independent Laplace mass of one prime ray. -/
def suzukiRayNormConst (σ : ℝ) (z : ℂ) : ℝ :=
  ∫ y in Ioi (0 : ℝ),
    ‖(Complex.exp (-(I * z * (y : ℂ))) - 1) / (I * z) * Complex.exp (-((σ : ℂ) * (y : ℂ)))‖

/-- Exact Laplace mass of one prime-power ray: the atom contributes only the factor `n^{-σ}`. -/
theorem integral_norm_suzukiPrimeRayTerm_laplace_eq (σ : ℝ) (z : ℂ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
      = |screwPrimeWeight n| * Real.exp (-(σ * Real.log n)) * suzukiRayNormConst σ z := by
  rcases lt_or_ge n 2 with hn | hn
  · have hw : screwPrimeWeight n = 0 := screwPrimeWeight_eq_zero_of_lt_two hn
    have hzero : ∀ t : ℝ, ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = 0 := by
      intro t
      rw [suzukiPrimeRayTerm]
      split_ifs <;> simp [hw]
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hzero t)]
    simp [hw]
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hcpos : (0 : ℝ) < Real.log n := Real.log_pos hn1
    set c : ℝ := Real.log n with hcdef
    set G : ℝ → ℝ := fun t : ℝ =>
      ‖(screwPrimeWeight n : ℂ) *
        ((Complex.exp (-(I * z * ((t : ℂ) - ((c : ℝ) : ℂ)))) - 1) / (I * z)) *
        Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ with hG
    have hstep1 :
        (∫ t in Ioi (0 : ℝ), ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
          = ∫ t in Ioi (0 : ℝ) ∩ Ici c, G t := by
      have hfun : (fun t : ℝ => ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
          = Set.indicator (Ici c) G := by
        funext t
        rw [congrFun (suzukiPrimeRayTerm_laplace_eq_indicator σ z n) t, ← hcdef, hG]
        by_cases h : c ≤ t
        · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h), Set.indicator_of_mem (Set.mem_Ici.mpr h)]
        · rw [Set.indicator_of_notMem (by simpa using h),
            Set.indicator_of_notMem (by simpa using h), norm_zero]
      rw [hfun]
      exact MeasureTheory.setIntegral_indicator measurableSet_Ici
    have hinter : Ioi (0 : ℝ) ∩ Ici c = Ici c :=
      Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le hcpos hx
    have hstep2 : (∫ t in Ici c, G t) = ∫ t in Ioi c, G t :=
      MeasureTheory.integral_Ici_eq_integral_Ioi
    have hstep3 : (∫ y in Ioi (0 : ℝ), G (y + c)) = ∫ x in Ioi c, G x := by
      have h := setIntegral_Ioi_comp_add_right G c c
      rwa [sub_self] at h
    have hstep4 : ∀ y : ℝ, G (y + c)
        = |screwPrimeWeight n| * Real.exp (-(σ * c)) *
            ‖(Complex.exp (-(I * z * (y : ℂ))) - 1) / (I * z) *
              Complex.exp (-((σ : ℂ) * (y : ℂ)))‖ := by
      intro y
      rw [hG]
      simp only
      have e1 : (((y + c : ℝ)) : ℂ) - ((c : ℝ) : ℂ) = ((y : ℝ) : ℂ) := by push_cast; ring
      rw [e1]
      have e2 : -((σ : ℂ) * (((y + c : ℝ)) : ℂ))
          = -((σ : ℂ) * ((y : ℝ) : ℂ)) + -((σ : ℂ) * ((c : ℝ) : ℂ)) := by push_cast; ring
      rw [e2, Complex.exp_add]
      have e3 : ‖Complex.exp (-((σ : ℂ) * ((c : ℝ) : ℂ)))‖ = Real.exp (-(σ * c)) := by
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re]
      rw [show (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((y : ℝ) : ℂ))) - 1) / (I * z)) *
          (Complex.exp (-((σ : ℂ) * ((y : ℝ) : ℂ))) * Complex.exp (-((σ : ℂ) * ((c : ℝ) : ℂ))))
          = (screwPrimeWeight n : ℂ) * Complex.exp (-((σ : ℂ) * ((c : ℝ) : ℂ))) *
            ((Complex.exp (-(I * z * ((y : ℝ) : ℂ))) - 1) / (I * z) *
              Complex.exp (-((σ : ℂ) * ((y : ℝ) : ℂ)))) by ring]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, e3]
    rw [hstep1, hinter, hstep2, ← hstep3,
      setIntegral_congr_fun measurableSet_Ioi (fun y _ => hstep4 y),
      MeasureTheory.integral_const_mul]
    rw [suzukiRayNormConst]

/-! ## The prime block as a Dirichlet series -/

/-- Suzuki's prime weight against the Laplace atom is the von Mangoldt Dirichlet coefficient. -/
theorem screwPrimeWeight_mul_exp_eq (σ : ℝ) (n : ℕ) :
    screwPrimeWeight n * Real.exp (-(σ * Real.log n))
      = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(σ + 1 / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [screwPrimeWeight]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hexp : Real.exp (-(σ * Real.log n)) = (n : ℝ) ^ (-σ) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [screwPrimeWeight, hexp, hsqrt, div_eq_mul_inv, ← Real.rpow_neg hnpos.le,
      mul_assoc, ← Real.rpow_add hnpos]
    congr 2
    ring

theorem screwPrimeWeight_nonneg (n : ℕ) : 0 ≤ screwPrimeWeight n := by
  rw [screwPrimeWeight]
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem summable_screwPrimeWeight_exp {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun n : ℕ => |screwPrimeWeight n| * Real.exp (-(σ * Real.log n))) := by
  have h := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (σ := σ + 1 / 2) (by linarith)
  refine h.congr fun n => ?_
  rw [← screwPrimeWeight_mul_exp_eq σ n, abs_of_nonneg (screwPrimeWeight_nonneg n)]

theorem ofReal_tsum_screwPrimeWeight_exp {σ : ℝ} (hσ : 1 / 2 < σ) :
    ((∑' n : ℕ, screwPrimeWeight n * Real.exp (-(σ * Real.log n)) : ℝ) : ℂ)
      = -logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ) := by
  have h := GaloisForLFunctions.HTGeometry.ofReal_tsum_vonMangoldt_eq
    (σ := σ + 1 / 2) (by linarith)
  rw [tsum_congr (fun n => screwPrimeWeight_mul_exp_eq σ n), h, logDeriv_apply]
  ring

theorem summable_integral_norm_suzukiPrimeRay {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    Summable (fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖) := by
  refine ((summable_screwPrimeWeight_exp hσ).mul_right (suzukiRayNormConst σ z)).congr fun n => ?_
  exact (integral_norm_suzukiPrimeRayTerm_laplace_eq σ z n).symm

theorem ofReal_tsum_screwPrimeWeight_cexp {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' n : ℕ, (screwPrimeWeight n : ℂ) *
        Complex.exp (-((σ : ℂ) * ((Real.log n : ℝ) : ℂ))))
      = -logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ) := by
  rw [← ofReal_tsum_screwPrimeWeight_exp hσ, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring

/-- **Laplace transform of Suzuki's finite prime block.** -/
theorem integral_suzukiFrakPPrime_laplace {σ : ℝ} (hσ : 1 / 2 < σ) {z : ℂ} (hz : z.im < σ) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = -logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ) / (I * z) *
          (((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun (n : ℕ) (t : ℝ) =>
        suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun n => integrableOn_suzukiPrimeRayTerm_laplace hσ0 hz n)
      (summable_integral_norm_suzukiPrimeRay hσ z)
  have hpt : ∀ t : ℝ,
      (∑' n : ℕ, suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        = suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
    intro t
    rw [tsum_mul_right, ← suzukiFrakPPrime_eq_tsum]
  have hterm : ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        = ((screwPrimeWeight n : ℂ) * Complex.exp (-((σ : ℂ) * ((Real.log n : ℝ) : ℂ)))) *
            ((((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) / (I * z)) := by
    intro n
    rw [integral_suzukiPrimeRayTerm_laplace hσ0 hz n]
    ring
  calc (∫ t in Ioi (0 : ℝ), suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ∫ t in Ioi (0 : ℝ),
          ∑' n : ℕ, suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))) :=
        (setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t).symm
    _ = ∑' n : ℕ,
          ∫ t in Ioi (0 : ℝ), suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))) :=
        h.symm
    _ = ∑' n : ℕ, ((screwPrimeWeight n : ℂ) *
          Complex.exp (-((σ : ℂ) * ((Real.log n : ℝ) : ℂ)))) *
            ((((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) / (I * z)) := tsum_congr hterm
    _ = (∑' n : ℕ, (screwPrimeWeight n : ℂ) *
          Complex.exp (-((σ : ℂ) * ((Real.log n : ℝ) : ℂ)))) *
            ((((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) / (I * z)) := tsum_mul_right
    _ = -logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ) / (I * z) *
          (((σ : ℂ) + I * z)⁻¹ - ((σ : ℂ))⁻¹) := by
        rw [ofReal_tsum_screwPrimeWeight_cexp hσ]
        ring

/-! ## Laplace transform of the Lerch block -/

/-- One archimedean Lerch ray of Suzuki eq. (1.6), with the `e^{-t/2}` prefactor absorbed. -/
def suzukiLerchRayTerm (w : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (-((2 * n + 1 / 2) * t)) : ℂ) * (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)

theorem suzukiFrakPLerch_eq (t : ℝ) (z : ℂ) :
    suzukiFrakPLerch t z
      = -((∑' n : ℕ, suzukiLerchRayTerm (1 / 4 - I * z / 2) n t) / (2 * I * z)) := by
  rw [suzukiFrakPLerch, suzukiLerchDiff, ← tsum_mul_left]
  congr 2
  refine tsum_congr fun n => ?_
  rw [suzukiLerchDiffTerm, suzukiLerchRayTerm, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem integrableOn_suzukiLerchRayTerm_laplace {σ : ℝ} (hσ : 0 < σ) (w : ℂ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have hrate : (0 : ℝ) < 2 * n + 1 / 2 + σ := by positivity
  have hre : 0 < ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ)).re := by simpa using hrate
  refine ((integrableOn_Ioi_cexp_neg_mul hre).const_mul
    (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [suzukiLerchRayTerm, Complex.ofReal_exp]
  rw [show -((((2 * (n : ℝ) + 1 / 2 + σ : ℝ)) : ℂ) * (t : ℂ))
      = ((-((2 * (n : ℝ) + 1 / 2) * t) : ℝ) : ℂ) + -((σ : ℂ) * (t : ℂ)) by push_cast; ring]
  rw [Complex.exp_add]
  ring

/-- Exact Laplace transform of one Lerch ray. -/
theorem integral_suzukiLerchRayTerm_laplace {σ : ℝ} (hσ : 0 < σ) (w : ℂ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) * ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ))⁻¹ := by
  have hrate : (0 : ℝ) < 2 * n + 1 / 2 + σ := by positivity
  have hre : 0 < ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ)).re := by simpa using hrate
  have hcongr : ∀ t : ℝ, suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))
      = (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) *
          Complex.exp (-((((2 * (n : ℝ) + 1 / 2 + σ : ℝ)) : ℂ) * (t : ℂ))) := by
    intro t
    rw [suzukiLerchRayTerm, Complex.ofReal_exp]
    rw [show -((((2 * (n : ℝ) + 1 / 2 + σ : ℝ)) : ℂ) * (t : ℂ))
        = ((-((2 * (n : ℝ) + 1 / 2) * t) : ℝ) : ℂ) + -((σ : ℂ) * (t : ℂ)) by push_cast; ring]
    rw [Complex.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t),
    MeasureTheory.integral_const_mul, integral_Ioi_cexp_neg_mul hre]

theorem summable_lerchCoeff {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => ((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) := by
  refine (summable_suzukiLerchDiffTerm (t := 0) le_rfl hw).congr fun n => ?_
  rw [suzukiLerchDiffTerm]
  simp

theorem integral_norm_suzukiLerchRayTerm_laplace_eq {σ : ℝ} (hσ : 0 < σ) (w : ℂ) (n : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
      = ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ * (2 * n + 1 / 2 + σ)⁻¹ := by
  have hrate : (0 : ℝ) < 2 * n + 1 / 2 + σ := by positivity
  have hcongr : ∀ t : ℝ, ‖suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖
      = ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ * Real.exp (-((2 * n + 1 / 2 + σ) * t)) := by
    intro t
    rw [suzukiLerchRayTerm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have h2 : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [h2, show -((2 * (n : ℝ) + 1 / 2 + σ) * t)
      = -((2 * (n : ℝ) + 1 / 2) * t) + -(σ * t) by ring, Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcongr t),
    MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_mul hrate]
  simp only [one_div]

theorem summable_integral_norm_suzukiLerchRay {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖) := by
  have hnorm : Summable (fun n : ℕ => ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖) :=
    summable_norm_iff.mpr (summable_lerchCoeff hw)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hnorm.mul_right σ⁻¹)
  · exact MeasureTheory.integral_nonneg fun t => norm_nonneg _
  · rw [integral_norm_suzukiLerchRayTerm_laplace_eq hσ w n]
    have hrate : (0 : ℝ) < 2 * n + 1 / 2 + σ := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_le_inv₀ hrate hσ]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **Laplace transform of Suzuki's Lerch block, before partial fractions.** -/
theorem integral_suzukiFrakPLerch_laplace_tsum {σ : ℝ} (hσ : 0 < σ) {z : ℂ}
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = -((∑' n : ℕ, (((n : ℂ) + (1 / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) *
            ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ))⁻¹) / (2 * I * z)) := by
  set w : ℂ := 1 / 4 - I * z / 2 with hwdef
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun (n : ℕ) (t : ℝ) => suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun n => integrableOn_suzukiLerchRayTerm_laplace hσ w n)
      (summable_integral_norm_suzukiLerchRay hσ hw)
  have hpt : ∀ t : ℝ, suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
      = -((∑' n : ℕ, suzukiLerchRayTerm w n t * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          / (2 * I * z)) := by
    intro t
    rw [suzukiFrakPLerch_eq, ← hwdef, tsum_mul_right]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)]
  rw [MeasureTheory.integral_neg, MeasureTheory.integral_div, ← h]
  congr 2
  exact tsum_congr fun n => integral_suzukiLerchRayTerm_laplace hσ w n

/-- **Partial-fraction evaluation of the Lerch Laplace sum.** -/
theorem tsum_lerchRayLaplace_eq {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz : z.im < σ)
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    (∑' n : ℕ, (((n : ℂ) + (1 / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) *
        ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ))⁻¹)
      = (Complex.digamma ((1 : ℂ) / 4 + (σ : ℂ) / 2)
            - Complex.digamma ((1 : ℂ) / 4 - I * z / 2)) / ((σ : ℂ) + I * z)
        - (Complex.digamma ((1 : ℂ) / 4 + (σ : ℂ) / 2)
            - Complex.digamma ((1 : ℂ) / 4)) / (σ : ℂ) := by
  set w : ℂ := 1 / 4 - I * z / 2 with hwdef
  set a : ℂ := (1 : ℂ) / 4 + (σ : ℂ) / 2 with hadef
  have hare : (0 : ℝ) < a.re := by
    rw [hadef]
    simp only [Complex.add_re, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    linarith
  have hqre : (0 : ℝ) < ((1 : ℂ) / 4).re := by norm_num
  have h1 := hasSum_digamma_sub hw hare
  have h2 := hasSum_digamma_sub hqre hare
  have hσC : ((σ : ℂ)) ≠ 0 := by simpa using ne_of_gt hσ
  have hsum : ((σ : ℂ)) + I * z ≠ 0 := by
    intro h
    have hre : (((σ : ℂ)) + I * z).re = σ - z.im := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub]
      ring
    rw [h] at hre
    simp at hre
    linarith
  have hcomb := (h1.div_const ((σ : ℂ) + I * z)).sub (h2.div_const ((σ : ℂ)))
  have hterm : ∀ n : ℕ,
      (1 / (w + (n : ℂ)) - 1 / (a + (n : ℂ))) / ((σ : ℂ) + I * z)
        - (1 / ((1 : ℂ) / 4 + (n : ℂ)) - 1 / (a + (n : ℂ))) / ((σ : ℂ))
      = (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) * ((((2 * n + 1 / 2 + σ : ℝ)) : ℂ))⁻¹ := by
    intro n
    have hwn : (n : ℂ) + w ≠ 0 := nat_add_ne_zero_of_re_pos hw n
    have han : (n : ℂ) + a ≠ 0 := nat_add_ne_zero_of_re_pos hare n
    have hqn : (n : ℂ) + 1 / 4 ≠ 0 := nat_add_quarter_ne_zero n
    have hrate : ((((2 * (n : ℝ) + 1 / 2 + σ : ℝ)) : ℂ)) = 2 * ((n : ℂ) + a) := by
      rw [hadef]; push_cast; ring
    have haw : a - w = ((σ : ℂ) + I * z) / 2 := by rw [hadef, hwdef]; ring
    have haq : a - (1 : ℂ) / 4 = (σ : ℂ) / 2 := by rw [hadef]; ring
    have haw' : ((n : ℂ) + a) - ((n : ℂ) + w) = ((σ : ℂ) + I * z) / 2 := by
      rw [hadef, hwdef]; ring
    have haq' : ((n : ℂ) + a) - ((n : ℂ) + 1 / 4) = (σ : ℂ) / 2 := by
      rw [hadef]; ring
    have hX : 1 / ((n : ℂ) + w) - 1 / ((n : ℂ) + a)
        = ((σ : ℂ) + I * z) * ((2 : ℂ)⁻¹ * (((n : ℂ) + w) * ((n : ℂ) + a))⁻¹) := by
      rw [one_div ((n : ℂ) + w), one_div ((n : ℂ) + a), inv_sub_inv hwn han, haw']
      ring
    have hY : 1 / ((n : ℂ) + 1 / 4) - 1 / ((n : ℂ) + a)
        = (σ : ℂ) * ((2 : ℂ)⁻¹ * (((n : ℂ) + 1 / 4) * ((n : ℂ) + a))⁻¹) := by
      rw [one_div ((n : ℂ) + 1 / 4), one_div ((n : ℂ) + a), inv_sub_inv hqn han, haq']
      ring
    rw [hrate, show w + (n : ℂ) = (n : ℂ) + w by ring, show a + (n : ℂ) = (n : ℂ) + a by ring,
      show (1 : ℂ) / 4 + (n : ℂ) = (n : ℂ) + 1 / 4 by ring, hX, hY,
      mul_div_cancel_left₀ _ hsum, mul_div_cancel_left₀ _ hσC]
    simp only [mul_inv]
    ring
  have := hcomb.tsum_eq
  rw [tsum_congr hterm] at this
  exact this

/-! ## Integrability of the prime and Lerch blocks -/

theorem screwPrimeWeight_le_log {n : ℕ} (hn : 1 ≤ n) : screwPrimeWeight n ≤ Real.log n := by
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  calc screwPrimeWeight n = ArithmeticFunction.vonMangoldt n / Real.sqrt n := rfl
    _ ≤ ArithmeticFunction.vonMangoldt n / 1 :=
        div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg one_pos h1
    _ = ArithmeticFunction.vonMangoldt n := by ring
    _ ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log

theorem sum_screwPrimeWeight_le {t : ℝ} (ht : 0 ≤ t) :
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) ≤ Real.exp t * t := by
  have hcard : ∀ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n ≤ t := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hle : (n : ℝ) ≤ Real.exp t := by
      calc (n : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hn.2
        _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
    have hlog : Real.log n ≤ t := by
      rw [← Real.log_exp t]
      exact Real.log_le_log hnpos hle
    exact (screwPrimeWeight_le_log hn1).trans hlog
  calc (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n)
      ≤ ∑ _n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, t := Finset.sum_le_sum hcard
    _ = (Finset.Icc 2 ⌊Real.exp t⌋₊).card * t := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp t * t := by
        have hc : ((Finset.Icc 2 ⌊Real.exp t⌋₊).card : ℝ) ≤ Real.exp t := by
          rw [Nat.card_Icc]
          have h1 : ((⌊Real.exp t⌋₊ + 1 - 2 : ℕ) : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by
            have : (⌊Real.exp t⌋₊ + 1 - 2) ≤ ⌊Real.exp t⌋₊ := by omega
            exact_mod_cast this
          exact h1.trans (Nat.floor_le (Real.exp_pos t).le)
        exact mul_le_mul_of_nonneg_right hc ht

theorem norm_suzukiFrakPPrime_le {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ‖suzukiFrakPPrime t z‖
      ≤ Real.exp t * t * (Real.exp (t * max z.im 0) + 1) / ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp [suzukiFrakPPrime]
  · have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hterm : ∀ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
        ‖(screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z))‖
          ≤ screwPrimeWeight n * ((Real.exp (t * max z.im 0) + 1) / ‖z‖) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : 1 ≤ n := by omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hle : (n : ℝ) ≤ Real.exp t := by
        calc (n : ℝ) ≤ (⌊Real.exp t⌋₊ : ℝ) := by exact_mod_cast hn.2
          _ ≤ Real.exp t := Nat.floor_le (Real.exp_pos t).le
      have hlog : Real.log n ≤ t := by
        rw [← Real.log_exp t]
        exact Real.log_le_log hnpos hle
      have hlognn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hcast : ((t : ℂ) - ((Real.log n : ℝ) : ℂ)) = (((t - Real.log n : ℝ)) : ℂ) := by
        push_cast; ring
      have hexpz : ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ))))‖
          = Real.exp ((t - Real.log n) * z.im) := by
        rw [hcast, Complex.norm_exp, re_neg_I_mul_ofReal]
      have hbnd : Real.exp ((t - Real.log n) * z.im) ≤ Real.exp (t * max z.im 0) := by
        apply Real.exp_le_exp.mpr
        rcases le_total 0 z.im with him | him
        · have : max z.im 0 = z.im := max_eq_left him
          rw [this]
          nlinarith
        · have : max z.im 0 = 0 := max_eq_right him
          rw [this, mul_zero]
          nlinarith
      rw [norm_mul, norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (screwPrimeWeight_nonneg n)]
      refine mul_le_mul_of_nonneg_left ?_ (screwPrimeWeight_nonneg n)
      rw [div_le_div_iff_of_pos_right hzpos]
      calc ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1‖
          ≤ ‖Complex.exp (-(I * z * ((t : ℂ) - ((Real.log n : ℝ) : ℂ))))‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ Real.exp (t * max z.im 0) + 1 := by rw [hexpz, norm_one]; linarith
    calc ‖suzukiFrakPPrime t z‖
        ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
            ‖(screwPrimeWeight n : ℂ) *
              ((Complex.exp (-(I * z * ((t : ℂ) - (Real.log n : ℂ)))) - 1) / (I * z))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊,
            screwPrimeWeight n * ((Real.exp (t * max z.im 0) + 1) / ‖z‖) :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, screwPrimeWeight n) *
            ((Real.exp (t * max z.im 0) + 1) / ‖z‖) := by rw [← Finset.sum_mul]
      _ ≤ (Real.exp t * t) * ((Real.exp (t * max z.im 0) + 1) / ‖z‖) := by
          refine mul_le_mul_of_nonneg_right (sum_screwPrimeWeight_le ht) ?_
          positivity
      _ = Real.exp t * t * (Real.exp (t * max z.im 0) + 1) / ‖z‖ := by ring

theorem measurable_suzukiFrakPPrime_laplace (σ : ℝ) (z : ℂ) :
    Measurable (fun t : ℝ => suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
  have hfun : (fun t : ℝ => suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = fun t : ℝ => ∑' n : ℕ, suzukiPrimeRayTerm z n t * Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
    funext t
    rw [tsum_mul_right, ← suzukiFrakPPrime_eq_tsum]
  rw [hfun]
  refine Measurable.tsum fun n => ?_
  rw [suzukiPrimeRayTerm_laplace_eq_indicator σ z n]
  refine Measurable.indicator ?_ measurableSet_Ici
  fun_prop

theorem integrableOn_suzukiFrakPPrime_laplace {σ : ℝ} (z : ℂ) (hσ : 1 + max z.im 0 < σ) :
    IntegrableOn (fun t : ℝ => suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  set m : ℝ := max z.im 0 with hm
  have hmnn : (0 : ℝ) ≤ m := le_max_right _ _
  set a : ℝ := σ - 1 - m with ha
  have hapos : (0 : ℝ) < a := by rw [ha]; linarith
  have hmaj : IntegrableOn (fun t : ℝ => 4 / (a * ‖z‖) * Real.exp (-((a / 2) * t)))
      (Ioi (0 : ℝ)) volume := by
    refine Integrable.const_mul ?_ _
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) (by positivity : (0 : ℝ) < a / 2)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  refine MeasureTheory.Integrable.mono' hmaj
    (measurable_suzukiFrakPPrime_laplace σ z).aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have htnn : (0 : ℝ) ≤ t := le_of_lt ht
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hexpσ : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [norm_mul, hexpσ]
  have h1 : ‖suzukiFrakPPrime t z‖ * Real.exp (-(σ * t))
      ≤ (Real.exp t * t * (Real.exp (t * m) + 1) / ‖z‖) * Real.exp (-(σ * t)) := by
    exact mul_le_mul_of_nonneg_right (norm_suzukiFrakPPrime_le htnn z) (Real.exp_pos _).le
  refine h1.trans ?_
  have hone : (1 : ℝ) ≤ Real.exp (t * m) := Real.one_le_exp (by positivity)
  have h2 : Real.exp t * t * (Real.exp (t * m) + 1) / ‖z‖ * Real.exp (-(σ * t))
      ≤ 2 * t / ‖z‖ * Real.exp (-(a * t)) := by
    rcases eq_or_lt_of_le hznn with hz0 | hzpos
    · rw [← hz0]
      simp
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hzpos]
      have hsplit : Real.exp t * Real.exp (t * m) * Real.exp (-(σ * t)) = Real.exp (-(a * t)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [ha]
        ring
      nlinarith [Real.exp_pos (-(σ * t)), Real.exp_pos t, Real.exp_pos (t * m), hsplit,
        mul_nonneg (mul_nonneg (Real.exp_pos t).le htnn) (Real.exp_pos (-(σ*t))).le]
  refine h2.trans ?_
  have hlin : t ≤ 2 / a * Real.exp (a / 2 * t) := by
    calc t = 2 / a * (a / 2 * t) := by field_simp
      _ ≤ 2 / a * Real.exp (a / 2 * t) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.add_one_le_exp (a / 2 * t)]
  have h3 : 2 * t / ‖z‖ * Real.exp (-(a * t)) ≤ 4 / (a * ‖z‖) * Real.exp (-(a / 2 * t)) := by
    rcases eq_or_lt_of_le hznn with hz0 | hzpos
    · rw [← hz0]
      simp
    · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ hzpos (by positivity)]
      have hfac : Real.exp (-(a * t)) = Real.exp (-(a / 2 * t)) * Real.exp (-(a / 2 * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hmul : 2 * t * Real.exp (-(a / 2 * t)) ≤ 4 / a := by
        have hpos : (0:ℝ) < Real.exp (a / 2 * t) := Real.exp_pos _
        have hinv : Real.exp (-(a / 2 * t)) = (Real.exp (a / 2 * t))⁻¹ := by
          rw [Real.exp_neg]
        rw [hinv]
        rw [mul_inv_le_iff₀ hpos]
        have h4 : (4 : ℝ) / a * Real.exp (a / 2 * t) = 2 * (2 / a * Real.exp (a / 2 * t)) := by
          ring
        rw [h4]
        linarith [hlin]
      rw [hfac]
      calc 2 * t * (Real.exp (-(a / 2 * t)) * Real.exp (-(a / 2 * t))) * (a * ‖z‖)
          = (a * ‖z‖ * Real.exp (-(a / 2 * t))) * (2 * t * Real.exp (-(a / 2 * t))) := by ring
        _ ≤ (a * ‖z‖ * Real.exp (-(a / 2 * t))) * (4 / a) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
        _ = 4 * Real.exp (-(a / 2 * t)) * ‖z‖ := by
            field_simp
  exact h3.trans_eq (by ring_nf)

theorem norm_suzukiLerchDiff_le {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.re) :
    ‖suzukiLerchDiff t w‖ ≤ ∑' n : ℕ, ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ := by
  have hs1 : Summable (fun n : ℕ => ‖suzukiLerchDiffTerm t w n‖) :=
    summable_norm_iff.mpr (summable_suzukiLerchDiffTerm ht hw)
  have hs2 : Summable (fun n : ℕ => ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖) :=
    summable_norm_iff.mpr (summable_lerchCoeff hw)
  rw [suzukiLerchDiff]
  refine (norm_tsum_le_tsum_norm hs1).trans (Summable.tsum_le_tsum (fun n => ?_) hs1 hs2)
  rw [suzukiLerchDiffTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]
  have hle : Real.exp (-(2 * (n : ℝ) * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : (0 : ℝ) ≤ 2 * (n : ℝ) * t := by positivity
    linarith
  nlinarith [norm_nonneg (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)]

theorem measurable_suzukiFrakPLerch_laplace (σ : ℝ) (z : ℂ) :
    Measurable (fun t : ℝ => suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
  have hmeas : Measurable (fun t : ℝ => suzukiLerchDiff t (1 / 4 - I * z / 2)) := by
    rw [show (fun t : ℝ => suzukiLerchDiff t (1 / 4 - I * z / 2))
        = fun t : ℝ => ∑' n : ℕ, suzukiLerchDiffTerm t (1 / 4 - I * z / 2) n from rfl]
    refine Measurable.tsum fun n => ?_
    rw [show (fun t : ℝ => suzukiLerchDiffTerm t (1 / 4 - I * z / 2) n)
        = fun t : ℝ => (Real.exp (-(2 * (n : ℝ) * t)) : ℂ) *
          (((n : ℂ) + (1 / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹) from rfl]
    fun_prop
  rw [show (fun t : ℝ => suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = fun t : ℝ => -((Real.exp (-(t / 2)) : ℂ) * suzukiLerchDiff t (1 / 4 - I * z / 2)
        / (2 * I * z)) * Complex.exp (-((σ : ℂ) * (t : ℂ))) from rfl]
  fun_prop

theorem integrableOn_suzukiFrakPLerch_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ}
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    IntegrableOn (fun t : ℝ => suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  set C : ℝ := ∑' n : ℕ, ‖((n : ℂ) + (1 / 4 - I * z / 2))⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ with hC
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hC]
    exact tsum_nonneg fun n => norm_nonneg _
  have hmaj : IntegrableOn (fun t : ℝ => C / (2 * ‖z‖) * Real.exp (-(σ * t)))
      (Ioi (0 : ℝ)) volume := by
    refine Integrable.const_mul ?_ _
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hσ).congr (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  refine MeasureTheory.Integrable.mono' hmaj
    (measurable_suzukiFrakPLerch_laplace σ z).aestronglyMeasurable.restrict ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have htnn : (0 : ℝ) ≤ t := le_of_lt ht
  have hexpσ : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hhalf : ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hden : ‖(2 : ℂ) * I * z‖ = 2 * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_I, mul_one]
    simp
  rw [norm_mul, hexpσ, suzukiFrakPLerch, norm_neg, norm_div, norm_mul, hden]
  have hbound : ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)‖ * ‖suzukiLerchDiff t (1 / 4 - I * z / 2)‖
      ≤ C := by
    calc ‖((Real.exp (-(t / 2)) : ℝ) : ℂ)‖ * ‖suzukiLerchDiff t (1 / 4 - I * z / 2)‖
        ≤ 1 * C := by
          refine mul_le_mul hhalf (norm_suzukiLerchDiff_le htnn hw) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hznn : (0 : ℝ) ≤ 2 * ‖z‖ := by positivity
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact div_le_div_of_nonneg_right hbound hznn

/-! ## The two archimedean blocks combined -/

theorem integral_suzukiFrakPArch_laplace {σ : ℝ} (hσ : 0 < σ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : z.im < σ) (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      + (∫ t in Ioi (0 : ℝ), suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (Complex.digamma ((1 : ℂ) / 4 + (σ : ℂ) / 2)
          - Complex.digamma ((1 : ℂ) / 4 - I * z / 2)) / (2 * (σ : ℂ) * ((σ : ℂ) + I * z)) := by
  have hσC : ((σ : ℂ)) ≠ 0 := by simpa using ne_of_gt hσ
  have hIz : I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hsum : ((σ : ℂ)) + I * z ≠ 0 := by
    intro h
    have hre : (((σ : ℂ)) + I * z).re = σ - z.im := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub]
      ring
    rw [h] at hre
    simp at hre
    linarith
  rw [integral_suzukiFrakPDigamma_laplace hσ z, integral_suzukiFrakPLerch_laplace_tsum hσ hw,
    tsum_lerchRayLaplace_eq hσ hz hw, suzukiFrakPDigamma]
  field_simp
  ring

/-! ## The full Laplace transform of `𝔓_t` -/

/-- **Laplace transform of Suzuki eq. (1.6).** -/
theorem integral_suzukiFrakP_laplace {σ : ℝ} {z : ℂ} (hz0 : z ≠ 0)
    (hσ1 : 1 / 2 < σ) (hσ2 : 1 + max z.im 0 < σ) (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re)
    (hs0 : (1 : ℂ) / 2 - I * z ≠ 0) (hs1 : (1 : ℂ) / 2 - I * z ≠ 1) :
    (∫ t in Ioi (0 : ℝ), suzukiFrakP t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (logDeriv riemannZeta (((σ + 1 / 2 : ℝ)) : ℂ)
          + logDeriv archFactor (((σ + 1 / 2 : ℝ)) : ℂ)
          - logDeriv riemannZeta ((1 : ℂ) / 2 - I * z)
          - logDeriv archFactor ((1 : ℂ) / 2 - I * z)) / ((σ : ℂ) * ((σ : ℂ) + I * z)) := by
  have hmnn : (0 : ℝ) ≤ max z.im 0 := le_max_right _ _
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hz : z.im < σ := lt_of_le_of_lt (le_max_left _ _) (by linarith)
  have hσC : ((σ : ℂ)) ≠ 0 := by simpa using ne_of_gt hσ0
  have hIz : I * z ≠ 0 := mul_ne_zero Complex.I_ne_zero hz0
  have hsum : ((σ : ℂ)) + I * z ≠ 0 := by
    intro h
    have hre : (((σ : ℂ)) + I * z).re = σ - z.im := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub]
      ring
    rw [h] at hre
    simp at hre
    linarith
  -- split the integral into the five blocks
  have hI1 := integrableOn_suzukiFrakPPolar_laplace hσ1 z
  have hI2 := integrableOn_suzukiFrakPZeta_laplace hσ0 hz
  have hI3 := integrableOn_suzukiFrakPPrime_laplace z hσ2
  have hI4 := integrableOn_suzukiFrakPDigamma_laplace hσ0 z
  have hI5 := integrableOn_suzukiFrakPLerch_laplace hσ0 hw
  have hsplit : (∫ t in Ioi (0 : ℝ), suzukiFrakP t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (∫ t in Ioi (0 : ℝ), suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        + (∫ t in Ioi (0 : ℝ), suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        + (∫ t in Ioi (0 : ℝ), suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        + ((∫ t in Ioi (0 : ℝ), suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          + (∫ t in Ioi (0 : ℝ), suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))) := by
    have e : ∀ t : ℝ, suzukiFrakP t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
        = (suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          + (suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
      intro t
      rw [suzukiFrakP_eq_blocks]
      ring
    have h12 : (∫ t in Ioi (0 : ℝ), (suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
          + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))))
        = (∫ t in Ioi (0 : ℝ), suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          + ∫ t in Ioi (0 : ℝ), suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) :=
      MeasureTheory.integral_add hI1 hI2
    have h123 : (∫ t in Ioi (0 : ℝ), (suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
          + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
          + suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))))
        = (∫ t in Ioi (0 : ℝ), (suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))))
          + ∫ t in Ioi (0 : ℝ), suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) :=
      MeasureTheory.integral_add (hI1.add hI2) hI3
    have h45 : (∫ t in Ioi (0 : ℝ), (suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
          + suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))))
        = (∫ t in Ioi (0 : ℝ), suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          + ∫ t in Ioi (0 : ℝ), suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) :=
      MeasureTheory.integral_add hI4 hI5
    have htot : (∫ t in Ioi (0 : ℝ),
          ((suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
          + (suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))))
        = (∫ t in Ioi (0 : ℝ), (suzukiFrakPPolar t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPZeta t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPPrime t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))))
          + ∫ t in Ioi (0 : ℝ), (suzukiFrakPDigamma z * Complex.exp (-((σ : ℂ) * (t : ℂ)))
            + suzukiFrakPLerch t z * Complex.exp (-((σ : ℂ) * (t : ℂ)))) :=
      MeasureTheory.integral_add ((hI1.add hI2).add hI3) (hI4.add hI5)
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => e t), htot, h123, h12, h45]
  rw [hsplit, integral_suzukiFrakPPolar_laplace hσ1 z, integral_suzukiFrakPZeta_laplace hσ0 hz,
    integral_suzukiFrakPPrime_laplace hσ1 hz, integral_suzukiFrakPArch_laplace hσ0 hz0 hz hw]
  -- expand the two archimedean logarithmic derivatives
  have hsσre : (0 : ℝ) < ((((σ + 1 / 2 : ℝ)) : ℂ)).re := by simpa using (by linarith : (0:ℝ) < σ + 1/2)
  have hsσ0 : (((σ + 1 / 2 : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    intro h
    linarith
  have hsσ1 : (((σ + 1 / 2 : ℝ)) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hszre : (0 : ℝ) < ((1 : ℂ) / 2 - I * z).re := by
    have hwre : ((1 : ℂ) / 4 - I * z / 2).re = 1 / 4 + z.im / 2 := by
      simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im]
      norm_num
      ring
    rw [hwre] at hw
    have hzre : ((1 : ℂ) / 2 - I * z).re = 1 / 2 + z.im := by
      simp only [Complex.sub_re, Complex.div_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im]
      norm_num
    rw [hzre]
    linarith
  rw [logDeriv_archFactor_closed hsσre hsσ0 hsσ1, logDeriv_archFactor_closed hszre hs0 hs1,
    GaloisForLFunctions.gammaRealLogConnection, GaloisForLFunctions.gammaRealLogConnection]
  have hhalfσ : (((σ + 1 / 2 : ℝ)) : ℂ) / 2 = (1 : ℂ) / 4 + (σ : ℂ) / 2 := by push_cast; ring
  have hhalfz : ((1 : ℂ) / 2 - I * z) / 2 = (1 : ℂ) / 4 - I * z / 2 := by ring
  rw [hhalfσ, hhalfz]
  have hp1 : (1 : ℂ) + 2 * I * z ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h / 2
  have hp2 : (1 : ℂ) - 2 * I * z ≠ 0 := by
    intro h
    apply hs0
    linear_combination h / 2
  have hq1 : ((σ : ℂ)) - 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hq2 : ((σ : ℂ)) + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hcastσ : (((σ + 1 / 2 : ℝ)) : ℂ) = (σ : ℂ) + 1 / 2 := by push_cast; ring
  rw [hcastσ]
  have hp3 : (1 : ℂ) / 2 + I * z ≠ 0 := by
    intro h
    apply hp1
    linear_combination 2 * h
  have e1 : (σ : ℂ) + 1 / 2 - 1 = (σ : ℂ) - 1 / 2 := by ring
  have e2 : (1 : ℂ) / 2 - I * z - 1 = -((1 : ℂ) / 2 + I * z) := by ring
  rw [e1, e2]
  simp only [show (2 : ℂ) * I * z = 2 * (I * z) from by ring]
  have hu1 : (1 : ℂ) + 2 * (I * z) ≠ 0 := by
    intro h
    exact hp1 (by linear_combination h)
  have hu2 : (1 : ℂ) - 2 * (I * z) ≠ 0 := by
    intro h
    exact hp2 (by linear_combination h)
  have hq1' : (-1 : ℂ) + (σ : ℂ) * 2 ≠ 0 := by
    intro h
    exact hq1 (by linear_combination h / 2)
  have hq2' : (1 : ℂ) + (σ : ℂ) * 2 ≠ 0 := by
    intro h
    exact hq2 (by linear_combination h / 2)
  set u : ℂ := I * z with hu
  have hA : (2 : ℂ) * (σ : ℂ) - 1 ≠ 0 := by
    intro h
    exact hq1 (by linear_combination h / 2)
  have hB : (2 : ℂ) * (σ : ℂ) + 1 ≠ 0 := by
    intro h
    exact hq2 (by linear_combination h / 2)
  have hd1 : ((σ : ℂ) - 1 / 2)⁻¹ - ((σ : ℂ))⁻¹ = 1 / ((σ : ℂ) * (2 * (σ : ℂ) - 1)) := by
    rw [inv_sub_inv hq1 hσC, div_eq_div_iff (mul_ne_zero hq1 hσC) (mul_ne_zero hσC hA)]
    ring
  have hd2 : ((σ : ℂ) + 1 / 2)⁻¹ - ((σ : ℂ))⁻¹ = -(1 / ((σ : ℂ) * (2 * (σ : ℂ) + 1))) := by
    rw [inv_sub_inv hq2 hσC, neg_div', div_eq_div_iff (mul_ne_zero hq2 hσC)
      (mul_ne_zero hσC hB)]
    ring
  have hd3 : ((σ : ℂ) + u)⁻¹ - ((σ : ℂ))⁻¹ = -(u / ((σ : ℂ) * ((σ : ℂ) + u))) := by
    rw [inv_sub_inv hsum hσC, neg_div', div_eq_div_iff (mul_ne_zero hsum hσC)
      (mul_ne_zero hσC hsum)]
    ring
  rw [hd1, hd2, hd3]
  field_simp [hA, hB]
  ring

end
end RHTower
