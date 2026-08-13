import GaloisForLFunctions.RHTower.EulerHellingerDyadicSignSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The sewing cost is a dyadic annulus of the Euler–Gamma quadrant current

The prime-power segments `t ↦ (t, k log p - t)`, weighted by `1/k` and restricted to `p < N`, carry
the finite Euler–Gamma quadrant current.  Pairing a function on the quadrant against it,

```text
⟨F⟩_N = ∑_{p<N} ∑_{k≥1} (1/k) ∫_0^{k log p} F(t, k log p - t) dt,
```

gives two exact evaluations.  Against the exponential the pairing is the divided difference of the
Euler logarithm,

```text
⟨e^{-zt-wu}⟩_N = (P_N(z) - P_N(w)) / (w - z),
```

and consequently the reflected Hellinger sewing cost is the dyadic annulus

```text
L_N(c) = 4c [ ⟨e^{-(1-2c)t-(1+2c)u}⟩_N - ⟨e^{-(1-c)t-(1+c)u}⟩_N ]
       = ⟨ 4c e^{-(t+u)} ( cosh(2c(t-u)) - cosh(c(t-u)) ) ⟩_N .
```

The second form is manifestly signed: on a segment `t + u` is constant, so the integrand reduces to
the dyadic sinh step of the prime-power series, which is positive for positive drift.  The essential
sewing cost is therefore a positive dyadic annulus cut from the quadrant current, not an unspecified
multiplier.
-/

open MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-! ## Two segment integrals -/

/-- The exponential segment integral is a divided difference. -/
theorem integral_segment_exp {z w : ℝ} (hzw : w - z ≠ 0) (Λ : ℝ) :
    (∫ t in (0:ℝ)..Λ, Real.exp (-(z * t) - w * (Λ - t)))
      = (Real.exp (-(z * Λ)) - Real.exp (-(w * Λ))) / (w - z) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) Λ,
      HasDerivAt (fun x : ℝ => Real.exp (-(z * x) - w * (Λ - x)) / (w - z))
        (Real.exp (-(z * t) - w * (Λ - t))) t := by
    intro t _
    have hinner : HasDerivAt (fun x : ℝ => -(z * x) - w * (Λ - x)) (w - z) t := by
      have haffine : (fun x : ℝ => -(z * x) - w * (Λ - x)) = fun x : ℝ => (w - z) * x - w * Λ := by
        funext x
        ring
      rw [haffine]
      simpa using ((hasDerivAt_id t).const_mul (w - z)).sub_const (w * Λ)
    have hexp := (Real.hasDerivAt_exp (-(z * t) - w * (Λ - t))).comp t hinner
    have := hexp.div_const (w - z)
    rw [mul_comm] at this
    have heq : (w - z) * Real.exp (-(z * t) - w * (Λ - t)) / (w - z)
        = Real.exp (-(z * t) - w * (Λ - t)) := by
      field_simp
    rwa [heq] at this
  have hcont : ContinuousOn (fun t : ℝ => Real.exp (-(z * t) - w * (Λ - t))) (Set.uIcc 0 Λ) := by
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [mul_zero, sub_zero, neg_zero, zero_sub]
  rw [div_sub_div_same]
  congr 1
  ring_nf

/-- The symmetric cosine-hyperbolic segment integral. -/
theorem integral_segment_cosh {a : ℝ} (ha : a ≠ 0) (Λ : ℝ) :
    (∫ t in (0:ℝ)..Λ, Real.cosh (a * (2 * t - Λ))) = Real.sinh (a * Λ) / a := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) Λ,
      HasDerivAt (fun x : ℝ => Real.sinh (a * (2 * x - Λ)) / (2 * a))
        (Real.cosh (a * (2 * t - Λ))) t := by
    intro t _
    have hinner : HasDerivAt (fun x : ℝ => a * (2 * x - Λ)) (2 * a) t := by
      have h1 : HasDerivAt (fun x : ℝ => 2 * x - Λ) (2 : ℝ) t := by
        simpa using ((hasDerivAt_id t).const_mul (2:ℝ)).sub_const Λ
      simpa [mul_comm] using h1.const_mul a
    have hsinh := (Real.hasDerivAt_sinh (a * (2 * t - Λ))).comp t hinner
    have hdiv := hsinh.div_const (2 * a)
    have heq : Real.cosh (a * (2 * t - Λ)) * (2 * a) / (2 * a)
        = Real.cosh (a * (2 * t - Λ)) := by
      field_simp
    rwa [heq] at hdiv
  have hcont : ContinuousOn (fun t : ℝ => Real.cosh (a * (2 * t - Λ))) (Set.uIcc 0 Λ) := by
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have hsymm : Real.sinh (a * (2 * 0 - Λ)) = -Real.sinh (a * Λ) := by
    have : a * (2 * 0 - Λ) = -(a * Λ) := by ring
    rw [this, Real.sinh_neg]
  have hend : a * (2 * Λ - Λ) = a * Λ := by ring
  rw [hend, hsymm]
  field_simp
  ring

/-! ## The quadrant pairing -/

/-- The pairing of a quadrant function against the finite Euler–Gamma prime-power segment
current. -/
def eulerQuadrantPairing (F : ℝ → ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N, ∑' k : ℕ, (1 / ((k : ℝ) + 1)) *
    ∫ t in (0:ℝ)..(((k : ℝ) + 1) * Real.log (p : ℝ)),
      F t ((((k : ℝ) + 1) * Real.log (p : ℝ)) - t)

/-- The two-variable Laplace transform of the quadrant current. -/
def eulerQuadrantLaplace (z w : ℝ) (N : ℕ) : ℝ :=
  eulerQuadrantPairing (fun t u => Real.exp (-(z * t) - w * u)) N

/-! ## The Laplace transform is the divided difference of the Euler logarithm -/

/-- A prime power in exponential coordinates. -/
theorem exp_neg_mul_log_eq_rpow {p : ℕ} (hp : p.Prime) (σ m : ℝ) :
    Real.exp (-(σ * (m * Real.log (p : ℝ)))) = (p : ℝ) ^ (-σ * m) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hp0]
  congr 1
  ring

/-- **The Laplace transform of the quadrant current.**  It is the divided difference of the finite
Euler logarithm. -/
theorem eulerQuadrantLaplace_eq {z w : ℝ} (hz : 0 < z) (hw : 0 < w) (hzw : w - z ≠ 0) (N : ℕ) :
    eulerQuadrantLaplace z w N
      = (primeEulerLogBelow z N - primeEulerLogBelow w N) / (w - z) := by
  rw [eulerQuadrantLaplace, eulerQuadrantPairing,
    primeEulerLogBelow_eq_sum hz N, primeEulerLogBelow_eq_sum hw N,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hzsum := hasSum_neg_log_one_sub_rpow hprime hz
  have hwsum := hasSum_neg_log_one_sub_rpow hprime hw
  have hterm : ∀ k : ℕ,
      (1 / ((k : ℝ) + 1)) *
          ∫ t in (0:ℝ)..(((k : ℝ) + 1) * Real.log (p : ℝ)),
            Real.exp (-(z * t) - w * ((((k : ℝ) + 1) * Real.log (p : ℝ)) - t))
        = (((p : ℝ) ^ (-z)) ^ (k + 1) / ((k : ℝ) + 1)
            - ((p : ℝ) ^ (-w)) ^ (k + 1) / ((k : ℝ) + 1)) / (w - z) := by
    intro k
    rw [integral_segment_exp hzw]
    rw [exp_neg_mul_log_eq_rpow hprime z ((k : ℝ) + 1),
      exp_neg_mul_log_eq_rpow hprime w ((k : ℝ) + 1),
      pow_rpow_neg_eq z k, pow_rpow_neg_eq w k]
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [tsum_congr hterm, tsum_div_const, (hzsum.sub hwsum).tsum_eq]

/-! ## The dyadic annulus form -/

/-- **The sewing cost is the dyadic annulus of the quadrant current.** -/
theorem logReflectedSewingBelow_eq_laplace_annulus {c : ℝ} (hc : |c| < 1 / 2) (hc0 : c ≠ 0)
    (N : ℕ) :
    logReflectedSewingBelow c N
      = 4 * c * (eulerQuadrantLaplace (1 - 2 * c) (1 + 2 * c) N
          - eulerQuadrantLaplace (1 - c) (1 + c) N) := by
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hc
  have h1 : (0 : ℝ) < 1 - 2 * c := by linarith
  have h2 : (0 : ℝ) < 1 + 2 * c := by linarith
  have h3 : (0 : ℝ) < 1 - c := by linarith
  have h4 : (0 : ℝ) < 1 + c := by linarith
  have hd1 : (1 + 2 * c) - (1 - 2 * c) ≠ 0 := by
    intro h
    exact hc0 (by linarith)
  have hd2 : (1 + c) - (1 - c) ≠ 0 := by
    intro h
    exact hc0 (by linarith)
  rw [eulerQuadrantLaplace_eq h1 h2 hd1 N, eulerQuadrantLaplace_eq h3 h4 hd2 N,
    logReflectedSewingBelow_eq hc]
  field_simp
  ring

/-! ## The positive `cosh` form -/

/-- **The manifestly signed annulus representation.**  On a segment `t + u` is constant, so the
integrand collapses to the dyadic sinh step of the prime-power series. -/
theorem logReflectedSewingBelow_eq_cosh_pairing {c : ℝ} (hc : |c| < 1 / 2) (hc0 : c ≠ 0) (N : ℕ) :
    logReflectedSewingBelow c N
      = eulerQuadrantPairing (fun t u => 4 * c * Real.exp (-(t + u)) *
          (Real.cosh (2 * c * (t - u)) - Real.cosh (c * (t - u)))) N := by
  rw [logReflectedSewingBelow_eq_sum_localSewingLog hc N, eulerQuadrantPairing]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
  have hseries := hasSum_localSewingLog hprime hc
  refine (hseries.tsum_eq).symm.trans (tsum_congr fun k => ?_)
  set Λ : ℝ := ((k : ℝ) + 1) * Real.log (p : ℝ) with hΛ
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hinteg : (∫ t in (0:ℝ)..Λ, 4 * c * Real.exp (-(t + (Λ - t))) *
        (Real.cosh (2 * c * (t - (Λ - t))) - Real.cosh (c * (t - (Λ - t)))))
      = 4 * c * Real.exp (-Λ) *
        (Real.sinh (2 * c * Λ) / (2 * c) - Real.sinh (c * Λ) / c) := by
    have hrw : ∀ t : ℝ, 4 * c * Real.exp (-(t + (Λ - t))) *
          (Real.cosh (2 * c * (t - (Λ - t))) - Real.cosh (c * (t - (Λ - t))))
        = (4 * c * Real.exp (-Λ)) *
          (Real.cosh (2 * c * (2 * t - Λ)) - Real.cosh (c * (2 * t - Λ))) := by
      intro t
      have e1 : -(t + (Λ - t)) = -Λ := by ring
      have e2 : t - (Λ - t) = 2 * t - Λ := by ring
      rw [e1, e2]
    rw [intervalIntegral.integral_congr (g := fun t => (4 * c * Real.exp (-Λ)) *
      (Real.cosh (2 * c * (2 * t - Λ)) - Real.cosh (c * (2 * t - Λ)))) (fun t _ => hrw t)]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub
        ((Continuous.intervalIntegrable (by fun_prop) _ _))
        ((Continuous.intervalIntegrable (by fun_prop) _ _)),
      integral_segment_cosh (by simpa using mul_ne_zero (two_ne_zero) hc0) Λ,
      integral_segment_cosh hc0 Λ]
  rw [hinteg]
  have hexp : Real.exp (-Λ) = (p : ℝ) ^ (-((k : ℝ) + 1)) := by
    rw [hΛ]
    have : -(((k : ℝ) + 1) * Real.log (p : ℝ)) = -(1 * (((k : ℝ) + 1) * Real.log (p : ℝ))) := by
      ring
    rw [this, exp_neg_mul_log_eq_rpow hprime 1 ((k : ℝ) + 1)]
    congr 1
    ring
  have hL2 : 2 * c * Λ = 2 * (c * ((k : ℝ) + 1) * Real.log (p : ℝ)) := by
    rw [hΛ]; ring
  have hL1 : c * Λ = c * ((k : ℝ) + 1) * Real.log (p : ℝ) := by
    rw [hΛ]; ring
  rw [hexp, hL2, hL1]
  field_simp
  ring

end

end RHTower
