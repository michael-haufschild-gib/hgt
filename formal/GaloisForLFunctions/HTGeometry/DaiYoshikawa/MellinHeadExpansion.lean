import GaloisForLFunctions.HTGeometry.DaiYoshikawa.MellinSplit

/-!
# Subtracting the two-term expansion from the head

The last algebraic step in continuing a spectral zeta function past `Re s = 1` is to subtract the
small-time expansion from the head Mellin integral:

```text
∫_0^1 (Θ(t) − h) t^{s−1} dt
  = ∫_0^1 (Θ(t) − a₀/t − a₁) t^{s−1} dt + a₀/(s−1) + (a₁ − h)/s .
```

The two explicit terms carry the poles at `s = 1` and `s = 0`.  This file proves the additivity of
the head Mellin integral and the resulting expansion, completing the identity used in
`SpectralZetaDerivative`.
-/

open MeasureTheory Set Filter Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The head Mellin integral is additive. -/
theorem mellinHead_add {g₁ g₂ : ℝ → ℂ} {s : ℂ}
    (h₁ : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • g₁ t) (Ioc (0 : ℝ) 1) volume)
    (h₂ : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • g₂ t) (Ioc (0 : ℝ) 1) volume) :
    mellinHead (fun t => g₁ t + g₂ t) s = mellinHead g₁ s + mellinHead g₂ s := by
  rw [mellinHead_eq_setIntegral, mellinHead_eq_setIntegral, mellinHead_eq_setIntegral,
    ← MeasureTheory.integral_add h₁ h₂]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  show (t : ℂ) ^ (s - 1) • (g₁ t + g₂ t)
    = (t : ℂ) ^ (s - 1) • g₁ t + (t : ℂ) ^ (s - 1) • g₂ t
  rw [smul_add]

/-- The head Mellin integral is homogeneous. -/
theorem mellinHead_const_mul (c : ℂ) (g : ℝ → ℂ) (s : ℂ) :
    mellinHead (fun t => c * g t) s = c * mellinHead g s := by
  rw [mellinHead_eq_setIntegral, mellinHead_eq_setIntegral, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  show (t : ℂ) ^ (s - 1) • (c * g t) = c * ((t : ℂ) ^ (s - 1) • g t)
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- The `t^{-1}` term is integrable against `t^{s-1}` on `(0,1]` for `Re s > 1`. -/
theorem integrableOn_head_cpow_neg_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-1 : ℂ)))
      (Ioc (0 : ℝ) 1) volume := by
  have hre : 0 < s.re + ((-1 : ℂ)).re := by
    simp only [Complex.neg_re, Complex.one_re]
    linarith
  have hconv : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1)
        • Set.indicator (Ioc (0 : ℝ) 1) (fun u : ℝ => (u : ℂ) ^ (-1 : ℂ)) t)
      (Ioi (0 : ℝ)) volume := (hasMellin_cpow_Ioc (-1 : ℂ) hre).1
  have hsub := hconv.mono_set (fun t (ht : t ∈ Ioc (0 : ℝ) 1) => ht.1)
  refine hsub.congr_fun (fun t ht => ?_) measurableSet_Ioc
  show (t : ℂ) ^ (s - 1)
      • Set.indicator (Ioc (0 : ℝ) 1) (fun u : ℝ => (u : ℂ) ^ (-1 : ℂ)) t
    = (t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-1 : ℂ))
  rw [Set.indicator_of_mem ht]

/-- The constant term is integrable against `t^{s-1}` on `(0,1]` for `Re s > 0`. -/
theorem integrableOn_head_one {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (1 : ℂ)) (Ioc (0 : ℝ) 1) volume := by
  have hconv : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1)
        • Set.indicator (Ioc (0 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) t)
      (Ioi (0 : ℝ)) volume := (hasMellin_one_Ioc hs).1
  have hsub := hconv.mono_set (fun t (ht : t ∈ Ioc (0 : ℝ) 1) => ht.1)
  refine hsub.congr_fun (fun t ht => ?_) measurableSet_Ioc
  show (t : ℂ) ^ (s - 1) • Set.indicator (Ioc (0 : ℝ) 1) (fun _ : ℝ => (1 : ℂ)) t
    = (t : ℂ) ^ (s - 1) • (1 : ℂ)
  rw [Set.indicator_of_mem ht]

/-- **The head expansion.**

`∫_0^1 g(t) t^{s−1} dt = ∫_0^1 (g(t) − a₀ t^{-1} − a₁) t^{s−1} dt + a₀/(s−1) + a₁/s`
for `Re s > 1`. -/
theorem mellinHead_eq_regularized_add {g : ℝ → ℂ} {a₀ a₁ : ℂ} {s : ℂ} (hs : 1 < s.re)
    (hreg : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (g t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁))
      (Ioc (0 : ℝ) 1) volume) :
    mellinHead g s
      = mellinHead (fun t => g t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁) s + a₀ / (s - 1) + a₁ / s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hpole : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ))) (Ioc (0 : ℝ) 1) volume := by
    have h : IntegrableOn (fun t : ℝ => a₀ * ((t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-1 : ℂ))))
        (Ioc (0 : ℝ) 1) volume := (integrableOn_head_cpow_neg_one hs).const_mul a₀
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
    show a₀ * ((t : ℂ) ^ (s - 1) • ((t : ℂ) ^ (-1 : ℂ)))
      = (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ))
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have hconst : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • a₁) (Ioc (0 : ℝ) 1) volume := by
    have h : IntegrableOn (fun t : ℝ => a₁ * ((t : ℂ) ^ (s - 1) • (1 : ℂ)))
        (Ioc (0 : ℝ) 1) volume := (integrableOn_head_one hs0).const_mul a₁
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
    show a₁ * ((t : ℂ) ^ (s - 1) • (1 : ℂ)) = (t : ℂ) ^ (s - 1) • a₁
    rw [smul_eq_mul, smul_eq_mul]
    ring
  have hadd2 : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ) + a₁))
      (Ioc (0 : ℝ) 1) volume := by
    have h : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ))
        + (t : ℂ) ^ (s - 1) • a₁) (Ioc (0 : ℝ) 1) volume := hpole.add hconst
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioc
    show (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ)) + (t : ℂ) ^ (s - 1) • a₁
      = (t : ℂ) ^ (s - 1) • (a₀ * (t : ℂ) ^ (-1 : ℂ) + a₁)
    rw [smul_add]
  have hsplit1 : mellinHead g s
      = mellinHead (fun t => (g t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁)
          + (a₀ * (t : ℂ) ^ (-1 : ℂ) + a₁)) s := by
    refine congrArg (fun f => mellinHead f s) ?_
    funext t
    ring
  rw [hsplit1, mellinHead_add hreg hadd2, mellinHead_add hpole hconst]
  have hpoleval : mellinHead (fun t : ℝ => a₀ * (t : ℂ) ^ (-1 : ℂ)) s = a₀ / (s - 1) := by
    rw [mellinHead_const_mul, mellinHead_cpow_neg_one hs]
    ring
  have hconstval : mellinHead (fun _ : ℝ => a₁) s = a₁ / s := by
    have h : mellinHead (fun t : ℝ => a₁ * (1 : ℂ)) s
        = a₁ * mellinHead (fun _ : ℝ => (1 : ℂ)) s := mellinHead_const_mul a₁ _ s
    simp only [mul_one] at h
    rw [h, mellinHead_one hs0]
    ring
  rw [hpoleval, hconstval]
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
