import GaloisForLFunctions.RHTower.EulerMascheroniExponentialIntegral

/-!
# The regularized logarithm of a determinant from a heat trace

Section 3.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), uses the zeta-regularized determinant only through the explicit
formula (3.3): if the heat trace `Θ(t) = Tr e^{−tΔ}` has the small-time expansion
`Θ(t) = a₀/t + a₁ + O(t)` and approaches the dimension `h` of the kernel exponentially fast, then

```text
log det' Δ⁻¹ = ∫_0^(1 : ℕ) (Θ(t) − a₀/t − a₁) dt/t + ∫_1^∞ (Θ(t) − h) dt/t − Γ'(1)(a₀ − h) .
```

Both integrals converge under exactly those two hypotheses, which is proved here.

The structural point exploited throughout Section 3 of the paper is that the regularizing constants
`a₀`, `a₁`, `h` are *the same* for the trivial bundle and for a bundle that is flat near the nodes,
so they cancel in the difference and

```text
log τ(X_s, 𝒪) − log τ(X_s, L) = ∫_0^(1 : ℕ) (Θ₁ − Θ₂) dt/t + ∫_1^∞ (Θ₁ − Θ₂) dt/t ,
```

with no regularization left.  That cancellation is the second theorem below, and it is what turns
(3.19) into a statement purely about the difference of two heat kernels.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The small-time regularized part of the heat-trace integral. -/
noncomputable def torsionHead (Θ : ℝ → ℝ) (a₀ a₁ : ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, (Θ t - a₀ / t - a₁) / t

/-- The large-time part of the heat-trace integral. -/
noncomputable def torsionTail (Θ : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ t in Ioi (1 : ℝ), (Θ t - h) / t

/-- The zeta-regularized logarithm of the determinant, in the form (3.3) of Dai–Yoshikawa.
`Γ'(1) = −γ`, so the correction term is `+ γ (a₀ − h)`. -/
noncomputable def logTorsion (Θ : ℝ → ℝ) (a₀ a₁ h : ℝ) : ℝ :=
  torsionHead Θ a₀ a₁ + torsionTail Θ h + Real.eulerMascheroniConstant * (a₀ - h)

/-! ## Convergence -/

/-- **The small-time integral converges.**  The two-term expansion `Θ(t) = a₀/t + a₁ + O(t)` makes
the regularized integrand bounded on `(0,1]`. -/
theorem integrableOn_torsionHead_integrand {Θ : ℝ → ℝ} {a₀ a₁ C : ℝ}
    (hΘ : Measurable Θ)
    (hbd : ∀ t ∈ Ioc (0 : ℝ) 1, |Θ t - a₀ / t - a₁| ≤ C * t) :
    IntegrableOn (fun t => (Θ t - a₀ / t - a₁) / t) (Ioc (0 : ℝ) 1) volume := by
  have hmeas : Measurable fun t => (Θ t - a₀ / t - a₁) / t :=
    ((hΘ.sub (measurable_const.div measurable_id)).sub measurable_const).div measurable_id
  refine Measure.integrableOn_of_bounded (M := C) (measure_Ioc_lt_top).ne
    hmeas.aestronglyMeasurable ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    filter_upwards with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    exact hbd t ht

/-- **The large-time integral converges.**  Exponential approach of the heat trace to the dimension
of the kernel makes the integrand exponentially small. -/
theorem integrableOn_torsionTail_integrand {Θ : ℝ → ℝ} {h C c : ℝ} (hc : 0 < c)
    (hΘ : Measurable Θ)
    (hbd : ∀ t ∈ Ioi (1 : ℝ), |Θ t - h| ≤ C * Real.exp (-c * t)) :
    IntegrableOn (fun t => (Θ t - h) / t) (Ioi (1 : ℝ)) volume := by
  have hmeas : AEStronglyMeasurable (fun t => (Θ t - h) / t) (volume.restrict (Ioi (1 : ℝ))) :=
    ((hΘ.sub measurable_const).div measurable_id).aestronglyMeasurable
  have hmaj : IntegrableOn (fun t => C * Real.exp (-c * t)) (Ioi (1 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi 1 hc).const_mul C
  refine hmaj.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards with t ht
  have ht1 : (1 : ℝ) < t := ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
  refine le_trans (div_le_self (abs_nonneg _) ht1.le) (hbd t ht)

/-! ## The regularization cancels in differences -/

/-- **The regularizing constants cancel.**

Two heat traces with the same small-time expansion and the same kernel dimension have a difference
of regularized log-determinants given by a single unregularized integral of the difference of the
traces.  This is (3.19) of Dai–Yoshikawa: the ratio of the two analytic torsions is
`∫_0^∞ (k_s − K^{L_s}) dt/t`, with no subtractions. -/
theorem logTorsion_sub_logTorsion {Θ₁ Θ₂ : ℝ → ℝ} {a₀ a₁ h : ℝ}
    (h₁head : IntegrableOn (fun t => (Θ₁ t - a₀ / t - a₁) / t) (Ioc (0 : ℝ) 1) volume)
    (h₂head : IntegrableOn (fun t => (Θ₂ t - a₀ / t - a₁) / t) (Ioc (0 : ℝ) 1) volume)
    (h₁tail : IntegrableOn (fun t => (Θ₁ t - h) / t) (Ioi (1 : ℝ)) volume)
    (h₂tail : IntegrableOn (fun t => (Θ₂ t - h) / t) (Ioi (1 : ℝ)) volume) :
    logTorsion Θ₁ a₀ a₁ h - logTorsion Θ₂ a₀ a₁ h
      = (∫ t in Ioc (0 : ℝ) 1, (Θ₁ t - Θ₂ t) / t)
        + ∫ t in Ioi (1 : ℝ), (Θ₁ t - Θ₂ t) / t := by
  have hhead : torsionHead Θ₁ a₀ a₁ - torsionHead Θ₂ a₀ a₁
      = ∫ t in Ioc (0 : ℝ) 1, (Θ₁ t - Θ₂ t) / t := by
    rw [torsionHead, torsionHead, ← MeasureTheory.integral_sub h₁head h₂head]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    ring
  have htail : torsionTail Θ₁ h - torsionTail Θ₂ h
      = ∫ t in Ioi (1 : ℝ), (Θ₁ t - Θ₂ t) / t := by
    rw [torsionTail, torsionTail, ← MeasureTheory.integral_sub h₁tail h₂tail]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [logTorsion, logTorsion, ← hhead, ← htail]
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
