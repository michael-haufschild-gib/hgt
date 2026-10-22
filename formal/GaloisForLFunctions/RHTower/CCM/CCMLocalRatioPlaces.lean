import GaloisForLFunctions.RHTower.CCM.CCMLocalRatioAnomaly
import GaloisForLFunctions.RHTower.CCM.CCMCoherentSquareExclusion
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The critical-line local ratio at a finite place, and its covariance charge

The local ratio of a prime `p` restricted to the critical line is

```text
u_p(t) = (1 - r_p e^(i L_p t))/(1 - r_p e^(-i L_p t)),   r_p = p^(-1/2), L_p = log p,
```

a unimodular multiplier with `u_p(0) = 1` and `u_p'(0) = -i b_p`, `b_p = 2 log p/(sqrt p - 1)`.

* `primeLocalRatio`, `primeLocalRatio_zero`, `hasDerivAt_primeLocalRatio` — the multiplier and its
  first jet, for an arbitrary radius `|r| < 1`.
* `primeRadius`, `primeRatioCharge`, `primeRatio` — the arithmetic instance.  Both are extended by the
  trivial value at `p <= 1`, so that the multiplier family is defined and equal to one at *every*
  index; this is what lets the generic anomaly theorems apply with no side conditions.
* `primeRatioCharge_pos`, `two_div_le_primeRatioCharge` — positivity and the harmonic lower bound
  `b_p >= 2/p`, from `log x >= 1 - 1/x`.
* `tendsto_primeCovarianceAnomaly_div_sq` — the quadratic jet of the prime-only anomaly, negative and
  equal to `-((sum b)^(2 : ℕ) - sum b^(2 : ℕ))/2 = -sum_(p<q) b_p b_q`.
* `tendsto_primeOffDiagCharge_atTop` — the cofinal divergence: the charge is unbounded along the
  exhaustion of the primes, because `sum 1/p` diverges while `sum 1/p^(2 : ℕ)` converges.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset Filter Topology

/-! ## The local ratio of a place -/

/-- The critical-line local ratio with radius `r` and frequency `L`. -/
def primeLocalRatio (r L : ℝ) (t : ℝ) : ℂ :=
  (1 - (r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I))
    / (1 - (r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)))

theorem norm_exp_neg_ofReal_mul_I (x : ℝ) : ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := by
  rw [show -((x : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) * Complex.I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-x)

theorem primeLocalRatio_den_ne_zero {r : ℝ} (hr : |r| < 1) (L t : ℝ) :
    (1 - (r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I))) ≠ 0 := by
  intro hc
  have hz : (r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)) = 1 := by
    linear_combination -hc
  have hnorm : ‖(r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I))‖ = |r| := by
    rw [norm_mul, norm_exp_neg_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hz, norm_one] at hnorm
  exact absurd hnorm.symm (ne_of_lt hr)

theorem primeLocalRatio_num_ne_zero {r : ℝ} (hr : |r| < 1) (L t : ℝ) :
    (1 - (r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
  intro hc
  have hz : (r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I) = 1 := by
    linear_combination -hc
  have hnorm : ‖(r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I)‖ = |r| := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hz, norm_one] at hnorm
  exact absurd hnorm.symm (ne_of_lt hr)

theorem primeLocalRatio_zero {r : ℝ} (hr : |r| < 1) (L : ℝ) : primeLocalRatio r L 0 = 1 := by
  have hne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
    have := primeLocalRatio_den_ne_zero hr L 0
    simpa using this
  rw [primeLocalRatio]
  norm_num
  exact hne

/-- The linear phase and its derivative at the seam. -/
theorem hasDerivAt_linPhase (L : ℝ) :
    HasDerivAt (fun t : ℝ => ((L * t : ℝ) : ℂ) * Complex.I) ((L : ℂ) * Complex.I) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => L * t) L 0 := by
    simpa only [mul_one, id_eq] using HasDerivAt.const_mul L (hasDerivAt_id (0 : ℝ))
  exact HasDerivAt.mul_const (HasDerivAt.ofReal_comp h0) Complex.I

/-- The exponential factor and its derivative at the seam. -/
theorem hasDerivAt_expFreq (L : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (((L * t : ℝ) : ℂ) * Complex.I))
      ((L : ℂ) * Complex.I) 0 := by
  have h2 := HasDerivAt.cexp (hasDerivAt_linPhase L)
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at h2
  exact h2

theorem hasDerivAt_expFreq_neg (L : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)))
      (-((L : ℂ) * Complex.I)) 0 := by
  have h := hasDerivAt_expFreq (-L)
  have hfun : (fun t : ℝ => Complex.exp ((((-L) * t : ℝ) : ℂ) * Complex.I))
      = fun t : ℝ => Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)) := by
    funext t
    congr 1
    push_cast
    ring
  rw [hfun] at h
  have hval : ((-L : ℝ) : ℂ) * Complex.I = -((L : ℂ) * Complex.I) := by push_cast; ring
  rw [hval] at h
  exact h

/-- **Equation (2).**  The first jet of the local ratio at the seam is purely imaginary, with
magnitude `2 r L/(1 - r)`. -/
theorem hasDerivAt_primeLocalRatio {r : ℝ} (hr : |r| < 1) (L : ℝ) :
    HasDerivAt (primeLocalRatio r L) (-Complex.I * ((2 * r * L / (1 - r) : ℝ) : ℂ)) 0 := by
  have hrne : ((1 : ℂ) - (r : ℂ)) ≠ 0 := by
    have := primeLocalRatio_den_ne_zero hr L 0
    simpa using this
  have hA : HasDerivAt (fun t : ℝ => 1 - (r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I))
      (-((r : ℂ) * ((L : ℂ) * Complex.I))) 0 :=
    HasDerivAt.const_sub 1 (HasDerivAt.const_mul (r : ℂ) (hasDerivAt_expFreq L))
  have hB : HasDerivAt (fun t : ℝ => 1 - (r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)))
      (-((r : ℂ) * -((L : ℂ) * Complex.I))) 0 :=
    HasDerivAt.const_sub 1 (HasDerivAt.const_mul (r : ℂ) (hasDerivAt_expFreq_neg L))
  have hden := primeLocalRatio_den_ne_zero hr L 0
  have hdiv := HasDerivAt.div hA hB hden
  have hval : ((-((r : ℂ) * ((L : ℂ) * Complex.I))
        * (1 - (r : ℂ) * Complex.exp (-(((L * (0 : ℝ) : ℝ) : ℂ) * Complex.I)))
      - (1 - (r : ℂ) * Complex.exp (((L * (0 : ℝ) : ℝ) : ℂ) * Complex.I))
        * (-((r : ℂ) * -((L : ℂ) * Complex.I))))
      / (1 - (r : ℂ) * Complex.exp (-(((L * (0 : ℝ) : ℝ) : ℂ) * Complex.I))) ^ 2)
      = -Complex.I * ((2 * r * L / (1 - r) : ℝ) : ℂ) := by
    norm_num
    field_simp
    ring
  rw [hval] at hdiv
  exact hdiv

/-! ## The arithmetic instance -/

/-- The critical-line radius of the place `p`, extended by zero below `2`. -/
def primeRadius (p : ℕ) : ℝ := if 1 < p then 1 / Real.sqrt p else 0

/-- The first-jet magnitude `b_p = 2 log p/(sqrt p - 1)`, extended by zero below `2`. -/
def primeRatioCharge (p : ℕ) : ℝ := if 1 < p then 2 * Real.log p / (Real.sqrt p - 1) else 0

/-- The critical-line local ratio of the place `p`. -/
def primeRatio (p : ℕ) : ℝ → ℂ := primeLocalRatio (primeRadius p) (Real.log p)

theorem one_lt_sqrt_of_two_le {p : ℕ} (hp : 2 ≤ p) : 1 < Real.sqrt p := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : Real.sqrt 1 < Real.sqrt p := by
    refine Real.sqrt_lt_sqrt (by norm_num) ?_
    linarith
  simpa using h1

theorem abs_primeRadius_lt_one (p : ℕ) : |primeRadius p| < 1 := by
  rw [primeRadius]
  split_ifs with h
  · have hp : 2 ≤ p := by omega
    have hs : 1 < Real.sqrt p := one_lt_sqrt_of_two_le hp
    rw [abs_of_nonneg (by positivity)]
    rw [div_lt_one (by linarith)]
    linarith
  · simp

theorem primeRatio_zero (p : ℕ) : primeRatio p 0 = 1 :=
  primeLocalRatio_zero (abs_primeRadius_lt_one p) _

/-- The first jet of the arithmetic local ratio. -/
theorem hasDerivAt_primeRatio (p : ℕ) :
    HasDerivAt (primeRatio p) (-Complex.I * ((primeRatioCharge p : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_primeLocalRatio (abs_primeRadius_lt_one p) (Real.log p)
  have hcharge : 2 * primeRadius p * Real.log p / (1 - primeRadius p) = primeRatioCharge p := by
    rw [primeRadius, primeRatioCharge]
    split_ifs with hp
    · have hp2 : 2 ≤ p := by omega
      have hs : 1 < Real.sqrt p := one_lt_sqrt_of_two_le hp2
      have hs0 : (0 : ℝ) < Real.sqrt p := by linarith
      field_simp
    · norm_num
  rw [hcharge] at h
  exact h

/-! ## Positivity and the harmonic lower bound -/

theorem primeRatioCharge_pos {p : ℕ} (hp : 2 ≤ p) : 0 < primeRatioCharge p := by
  have hlt : 1 < p := by omega
  have hs : 1 < Real.sqrt p := one_lt_sqrt_of_two_le hp
  have hlog : 0 < Real.log p := by
    refine Real.log_pos ?_
    exact_mod_cast hlt
  rw [primeRatioCharge, if_pos hlt]
  positivity

/-- **Equation (12).**  The harmonic lower bound `b_p >= 2/p`, from `log x >= 1 - 1/x`. -/
theorem two_div_le_primeRatioCharge {p : ℕ} (hp : 2 ≤ p) :
    2 / (p : ℝ) ≤ primeRatioCharge p := by
  have hlt : 1 < p := by omega
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hs : 1 < Real.sqrt p := one_lt_sqrt_of_two_le hp
  have hsq : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hppos.le
  -- `log x ≥ 1 - 1/x` at `x = p`
  have hlog : 1 - 1 / (p : ℝ) ≤ Real.log p := by
    have h := Real.log_le_sub_one_of_pos (x := 1 / (p : ℝ)) (by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt hppos), Real.log_one] at h
    linarith
  rw [primeRatioCharge, if_pos hlt, le_div_iff₀ (by linarith)]
  have hkey : 2 / (p : ℝ) * (Real.sqrt p - 1) ≤ 2 * (1 - 1 / (p : ℝ)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hppos]
    have h1 : 2 * (1 - 1 / (p : ℝ)) * (p : ℝ) = 2 * ((p : ℝ) - 1) := by
      field_simp
    rw [h1]
    nlinarith [hs, hsq]
  calc 2 / (p : ℝ) * (Real.sqrt p - 1) ≤ 2 * (1 - 1 / (p : ℝ)) := hkey
    _ ≤ 2 * Real.log p := by linarith

/-! ## The prime-only anomaly and its curvature -/

theorem sum_primeRatioCharge_cast (F : Finset ℕ) :
    (∑ p ∈ F, -Complex.I * ((primeRatioCharge p : ℝ) : ℂ))
      = -Complex.I * (((∑ p ∈ F, primeRatioCharge p : ℝ)) : ℂ) := by
  rw [Complex.ofReal_sum, Finset.mul_sum]

/-- **Equations (9)–(11) at the finite places.**  The quadratic jet of the prime-only covariance
anomaly is the negative of half the off-diagonal charge.  Since every `b_p` is positive, the jet is
strictly negative as soon as two places are present. -/
theorem tendsto_primeCovarianceAnomaly_div_sq (F : Finset ℕ) :
    Tendsto (fun t : ℝ => covarianceAnomaly F primeRatio t / (t : ℂ) ^ 2) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((((∑ p ∈ F, primeRatioCharge p) ^ 2
        - ∑ p ∈ F, primeRatioCharge p ^ 2) / 2 : ℝ) : ℂ))) := by
  have h := tendsto_covarianceAnomaly_div_sq (u := primeRatio)
    (c := fun p => -Complex.I * ((primeRatioCharge p : ℝ) : ℂ))
    (fun p => primeRatio_zero p) (fun p => hasDerivAt_primeRatio p) F
  have hval : (((∑ p ∈ F, -Complex.I * ((primeRatioCharge p : ℝ) : ℂ)) ^ 2
        - ∑ p ∈ F, (-Complex.I * ((primeRatioCharge p : ℝ) : ℂ)) ^ 2) / 2)
      = -((((∑ p ∈ F, primeRatioCharge p) ^ 2
        - ∑ p ∈ F, primeRatioCharge p ^ 2) / 2 : ℝ) : ℂ) := by
    rw [sum_primeRatioCharge_cast F]
    have hsq : ∀ p : ℕ, (-Complex.I * ((primeRatioCharge p : ℝ) : ℂ)) ^ 2
        = -(((primeRatioCharge p ^ 2 : ℝ)) : ℂ) := by
      intro p
      push_cast
      rw [neg_mul, neg_pow, mul_pow, Complex.I_sq]
      ring
    rw [Finset.sum_congr rfl fun p _ => hsq p, Finset.sum_neg_distrib, ← Complex.ofReal_sum]
    push_cast
    have hI : (-Complex.I) ^ 2 = -1 := by
      rw [neg_pow, Complex.I_sq]
      norm_num
    rw [mul_pow, hI]
    ring
  rw [hval] at h
  exact h

/-- The explicit pairwise curvature contribution of two places. -/
theorem primeRatioCharge_mul {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    primeRatioCharge p * primeRatioCharge q
      = 4 * (Real.log p * Real.log q) / ((Real.sqrt p - 1) * (Real.sqrt q - 1)) := by
  have hsp : 1 < Real.sqrt p := one_lt_sqrt_of_two_le hp
  have hsq : 1 < Real.sqrt q := one_lt_sqrt_of_two_le hq
  rw [primeRatioCharge, primeRatioCharge, if_pos (by omega : 1 < p), if_pos (by omega : 1 < q)]
  field_simp
  ring

/-- **Equation (11).**  The curvature of the prime-only anomaly, as an off-diagonal sum. -/
theorem primeQuadraticCharge_eq_sum_offDiag (F : Finset ℕ) :
    (∑ p ∈ F, primeRatioCharge p) ^ 2 - ∑ p ∈ F, primeRatioCharge p ^ 2
      = ∑ x ∈ F.offDiag, primeRatioCharge x.1 * primeRatioCharge x.2 :=
  offDiagCharge_eq_sum_offDiag F primeRatioCharge

/-! ## Cofinal divergence -/

theorem summable_inv_sq : Summable fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have h : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine h.congr fun n => ?_
  rw [inv_pow, one_div]

/-- **Equations (13)–(14).**  Along the exhaustion of the primes the off-diagonal charge diverges:
`b_p >= 2/p`, `sum 1/p` diverges, and `sum 1/p^(2 : ℕ)` converges. -/
theorem tendsto_primeOffDiagCharge_atTop :
    Tendsto (fun N : ℕ => ∑ x ∈ ((Finset.range N).filter Nat.Prime).offDiag,
      primeRatioCharge x.1 * primeRatioCharge x.2) atTop atTop := by
  classical
  set S : ℝ := ∑' n : ℕ, ((n : ℝ)⁻¹) ^ 2 with hSdef
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ)⁻¹) ^ 2 := fun n => sq_nonneg _
  have hbound : ∀ N : ℕ, 4 * ((primeReciprocalSum N) ^ 2 - S)
      ≤ ∑ x ∈ ((Finset.range N).filter Nat.Prime).offDiag,
          primeRatioCharge x.1 * primeRatioCharge x.2 := by
    intro N
    set F : Finset ℕ := (Finset.range N).filter Nat.Prime with hFdef
    have hprime : ∀ p ∈ F, 2 ≤ p := by
      intro p hp
      rw [hFdef, Finset.mem_filter] at hp
      exact hp.2.two_le
    -- the harmonic comparison, termwise on the off-diagonal
    have hcomp : ∑ x ∈ F.offDiag, (2 / (x.1 : ℝ)) * (2 / (x.2 : ℝ))
        ≤ ∑ x ∈ F.offDiag, primeRatioCharge x.1 * primeRatioCharge x.2 := by
      refine sum_offDiag_le_sum_offDiag (b := fun p : ℕ => 2 / (p : ℝ))
        (b' := primeRatioCharge) ?_
      intro v hv w hw _
      have hv2 := hprime v hv
      have hw2 := hprime w hw
      have hvpos : (0 : ℝ) < 2 / (v : ℝ) := by
        have : (2 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv2
        positivity
      have hwpos : (0 : ℝ) < 2 / (w : ℝ) := by
        have : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw2
        positivity
      exact mul_le_mul (two_div_le_primeRatioCharge hv2) (two_div_le_primeRatioCharge hw2)
        hwpos.le (le_trans hvpos.le (two_div_le_primeRatioCharge hv2))
    -- evaluate the harmonic off-diagonal charge
    have hharm : ∑ x ∈ F.offDiag, (2 / (x.1 : ℝ)) * (2 / (x.2 : ℝ))
        = (∑ p ∈ F, 2 / (p : ℝ)) ^ 2 - ∑ p ∈ F, (2 / (p : ℝ)) ^ 2 :=
      (offDiagCharge_eq_sum_offDiag F fun p => 2 / (p : ℝ)).symm
    have hsum1 : (∑ p ∈ F, 2 / (p : ℝ)) = 2 * primeReciprocalSum N := by
      rw [primeReciprocalSum, hFdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [inv_eq_one_div]; ring
    have hsum2 : (∑ p ∈ F, (2 / (p : ℝ)) ^ 2) = 4 * ∑ p ∈ F, ((p : ℝ)⁻¹) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by rw [div_pow, inv_pow]; ring
    have htail : (∑ p ∈ F, ((p : ℝ)⁻¹) ^ 2) ≤ S := by
      rw [hSdef]
      exact summable_inv_sq.sum_le_tsum F fun n _ => hnn n
    calc 4 * ((primeReciprocalSum N) ^ 2 - S)
        ≤ 4 * ((primeReciprocalSum N) ^ 2 - ∑ p ∈ F, ((p : ℝ)⁻¹) ^ 2) := by
          have := htail
          nlinarith
      _ = (∑ p ∈ F, 2 / (p : ℝ)) ^ 2 - ∑ p ∈ F, (2 / (p : ℝ)) ^ 2 := by
          rw [hsum1, hsum2]
          ring
      _ = ∑ x ∈ F.offDiag, (2 / (x.1 : ℝ)) * (2 / (x.2 : ℝ)) := hharm.symm
      _ ≤ ∑ x ∈ F.offDiag, primeRatioCharge x.1 * primeRatioCharge x.2 := hcomp
  have hdiv : Tendsto (fun N : ℕ => 4 * ((primeReciprocalSum N) ^ 2 - S)) atTop atTop := by
    have hsq : Tendsto (fun N : ℕ => (primeReciprocalSum N) ^ 2) atTop atTop := by
      have h := tendsto_primeReciprocalSum_atTop.atTop_mul_atTop₀
        tendsto_primeReciprocalSum_atTop
      refine h.congr fun N => ?_
      rw [sq]
    have hshift : Tendsto (fun N : ℕ => primeReciprocalSum N ^ 2 - S) atTop atTop := by
      have h := Filter.tendsto_atTop_add_const_right atTop (-S) hsq
      exact h.congr fun N => by ring
    exact Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4) hshift
  exact tendsto_atTop_mono hbound hdiv

end GaloisForLFunctions.RHTower

end
