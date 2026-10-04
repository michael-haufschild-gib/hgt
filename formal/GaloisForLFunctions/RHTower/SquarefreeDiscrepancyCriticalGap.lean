import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyMellin
import GaloisForLFunctions.RHTower.ZetaRealSignature
import GaloisForLFunctions.RHTower.ZetaRealTraceDiscCount

/-!
# Signed and absolute squarefree-discrepancy responses

The response of the literal squarefree discrepancy to each real power strictly below
one half is strictly below one and tends to one at the critical exponent. On the fixed
interval between the reciprocal density and two, the discrepancy is strictly negative.
Retaining that interval gives a uniform positive gap between absolute and signed
responses, so the absolute response exceeds one near the critical exponent.

These statements concern the exact discrepancy integrals. They do not assert a bound
for an arbitrary dilation operator or for the signed Liouville source.
-/

open Filter Topology MeasureTheory Set Asymptotics Complex
open scoped BigOperators
namespace RHTower.SquarefreeDiscrepancy
noncomputable section

/-- Real part of the discrepancy response on the real axis. -/
def realResponse (a : ℝ) : ℝ := (response (a : ℂ)).re

/-- Response obtained by replacing the literal discrepancy with its absolute value. -/
def absoluteResponse (a : ℝ) : ℝ :=
  a / Sieve.squarefreeDensity * ∫ x in Ioi (1 : ℝ), |error x| * x ^ (a - 2)

private theorem rho_pos : 0 < Sieve.squarefreeDensity := by
  rw [Sieve.squarefreeDensity_eq]
  positivity

/-- The complex response is the cast of the literal real discrepancy integral. -/
theorem response_ofReal_eq (a : ℝ) :
    response (a : ℂ) =
      ((a / Sieve.squarefreeDensity * ∫ x in Ioi (1 : ℝ), error x * x ^ (a - 2) : ℝ) : ℂ) := by
  rw [response, moment_eq_integral]
  have hi : (∫ x in Ioi (1 : ℝ), (error x : ℂ) * (x : ℂ)^(-((1-(a:ℂ))+1))) =
      ((∫ x in Ioi (1 : ℝ), error x * x^(a-2) : ℝ) : ℂ) := by
    trans ∫ x in Ioi (1 : ℝ), ((error x*x^(a-2) : ℝ) : ℂ)
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (show 0 ≤ x by change 1 < x at hx; linarith)]
      congr 2
      push_cast
      ring
    · exact integral_ofReal
  rw [hi]
  push_cast
  rfl

/-- Exact real signed integral defining the real-axis response. -/
theorem realResponse_eq (a : ℝ) :
    realResponse a = a / Sieve.squarefreeDensity *
      ∫ x in Ioi (1 : ℝ), error x * x^(a-2) := by
  simp only [realResponse, response_ofReal_eq, Complex.ofReal_re]

/-- Every strictly subcritical positive real mode has a positive deficit from one. -/
theorem realResponse_lt_one {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    realResponse a < 1 := by
  obtain ⟨z, hz, hζ⟩ := riemannZeta_real_strip_neg
    (show 0 < 1-a by linarith) (show 1-a < 1 by linarith)
  have hz2 := riemannZeta_two_mul_eq_ofReal (σ := 1-a) (by linarith)
  have hp := eulerPositiveTotal_two_mul_pos (σ := 1-a) (by linarith)
  have hr := response_eq (a := (a : ℂ)) (by simpa using ha0) (by simpa using ha)
  have hζ' : riemannZeta (1-(a : ℂ)) = (z : ℂ) := by simpa using hζ
  have hz2' : riemannZeta (2*(1-(a : ℂ))) = (eulerPositiveTotal (2*(1-a)) : ℂ) := by
    simpa using hz2
  rw [hζ', hz2'] at hr
  have hreal : realResponse a =
      1 + a*z / (Sieve.squarefreeDensity*(1-a)*eulerPositiveTotal (2*(1-a))) := by
    rw [realResponse, hr]
    norm_cast
  rw [hreal]
  have hden : 0 < Sieve.squarefreeDensity*(1-a)*eulerPositiveTotal (2*(1-a)) :=
    mul_pos (mul_pos rho_pos (by linarith)) hp
  have hneg : a*z / (Sieve.squarefreeDensity*(1-a)*eulerPositiveTotal (2*(1-a))) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha0 hz) hden
  linarith

private def regularResponse (a : ℝ) : ℂ :=
  1 + (a : ℂ)*riemannZeta (1-(a : ℂ))*(1-2*(a : ℂ)) /
    ((Sieve.squarefreeDensity : ℂ)*(1-(a : ℂ))*zetaResidueUnit (2*(1-(a : ℂ))))

private theorem response_eq_regular {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    response (a : ℂ) = regularResponse a := by
  have hn0 : (1-2*(a : ℂ)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, two_mul, Complex.add_re, Complex.ofReal_re,
      Complex.zero_re] at hr
    linarith
  have harg : 2*(1-(a : ℂ)) ≠ 1 := by
    intro h
    apply hn0
    linear_combination h
  rw [response_eq (by simpa using ha0) (by simpa using ha), regularResponse,
    zetaResidueUnit, Function.update_of_ne harg]
  rw [show 2*(1-(a : ℂ))-1 = 1-2*(a : ℂ) by ring]
  congr 1
  rw [show (Sieve.squarefreeDensity : ℂ)*(1-(a : ℂ))*
      ((1-2*(a : ℂ))*riemannZeta (2*(1-(a : ℂ)))) =
      ((Sieve.squarefreeDensity : ℂ)*(1-(a : ℂ))*riemannZeta (2*(1-(a : ℂ))))*
      (1-2*(a : ℂ)) by ring]
  exact (mul_div_mul_right _ _ hn0).symm

private theorem continuousAt_regular_half : ContinuousAt regularResponse (1/2) := by
  have ha : ContinuousAt (fun a : ℝ => (a : ℂ)) (1/2) := Complex.continuous_ofReal.continuousAt
  have hb : ContinuousAt (fun a : ℝ => (1 : ℂ) - (a : ℂ)) (1/2) :=
    continuousAt_const.sub ha
  have hz0 : ContinuousAt riemannZeta (1-((1/2 : ℝ) : ℂ)) :=
    (differentiableAt_riemannZeta (by norm_num : (1-((1/2 : ℝ) : ℂ)) ≠ 1)).continuousAt
  have hz : ContinuousAt (fun a : ℝ => riemannZeta (1-(a : ℂ))) (1/2) := hz0.comp (f := fun a : ℝ => (1 : ℂ)-(a : ℂ)) hb
  have hu : ContinuousAt (fun a : ℝ => zetaResidueUnit (2*(1-(a : ℂ)))) (1/2) :=
    (analyticAt_zetaResidueUnit _).continuousAt.comp
      (f := fun a : ℝ => (2 : ℂ)*(1-(a : ℂ))) (continuousAt_const.mul hb)
  have hrho : (Sieve.squarefreeDensity : ℂ) ≠ 0 := by exact_mod_cast rho_pos.ne'
  have hden : (Sieve.squarefreeDensity : ℂ)*(1-((1/2 : ℝ) : ℂ))*
      zetaResidueUnit (2*(1-((1/2 : ℝ) : ℂ))) ≠ 0 := by
    norm_num [mul_ne_zero_iff, hrho]
  exact continuousAt_const.add (((ha.mul hz).mul
    (continuousAt_const.sub (continuousAt_const.mul ha))).div
      ((continuousAt_const.mul hb).mul hu) hden)

/-- The signed subcritical moments approach one from the critical left side. -/
theorem tendsto_response_half :
    Tendsto (fun a : ℝ => response (a : ℂ)) (𝓝[<] (1/2 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hval : regularResponse (1/2) = 1 := by norm_num [regularResponse]
  have ht : Tendsto regularResponse (𝓝[<] (1/2 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [hval] using continuousAt_regular_half.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [((eventually_gt_nhds (show (0 : ℝ) < 1/2 by norm_num)).filter_mono
    nhdsWithin_le_nhds), self_mem_nhdsWithin] with a ha0 ha
  exact (response_eq_regular ha0 ha).symm

/-- Real-axis form of the critical Abelian limit. -/
theorem tendsto_realResponse_half :
    Tendsto realResponse (𝓝[<] (1/2 : ℝ)) (𝓝 (1 : ℝ)) := by
  change Tendsto (fun a : ℝ => (response (a : ℂ)).re) _ _
  simpa only [Complex.one_re, Function.comp_def] using
    (Complex.continuous_re.tendsto (1 : ℂ)).comp tendsto_response_half

/-- Absolute integrability of each strictly subcritical real signed moment. -/
theorem integrable_real_moment {a : ℝ} (ha : a < 1/2) :
    IntegrableOn (fun x : ℝ => error x * x^(a-2)) (Ioi 1) := by
  have hs : 1/2 < (1-(a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  have hi := Complex.reCLM.integrable_comp (integrable_moment hs)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hp : (x : ℂ)^(-((1-(a : ℂ))+1)) = ((x^(a-2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (show 0 ≤ x by change 1 < x at hx; linarith)]
    congr 1
    push_cast
    ring
  rw [hp, ← Complex.ofReal_mul]
  rfl

/-- Integrability of the absolute comparison moment. -/
theorem integrable_absolute_moment {a : ℝ} (ha : a < 1/2) :
    IntegrableOn (fun x : ℝ => |error x| * x^(a-2)) (Ioi 1) := by
  apply (integrable_real_moment ha).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (Real.rpow_nonneg (show 0 ≤ x by change 1 < x at hx; linarith) _)]

private theorem exists_negative_interval :
    ∃ u v c : ℝ, 1 < u ∧ u < v ∧ v < 2 ∧ 0 < c ∧
      ∀ x ∈ Icc u v, error x ≤ -c := by
  have hρ1 : Sieve.squarefreeDensity < 1 := by
    rw [Sieve.squarefreeDensity_eq]
    apply (div_lt_one (by positivity)).2
    nlinarith [Real.pi_gt_three]
  have hinv : 1 / Sieve.squarefreeDensity < 2 := by
    rw [Sieve.squarefreeDensity_eq]
    convert pi_sq_div_six_lt_two using 1
    field_simp
  have hone : 1 < 1 / Sieve.squarefreeDensity :=
    (lt_div_iff₀ rho_pos).2 (by simpa using hρ1)
  obtain ⟨u, hu, hu2⟩ := exists_between hinv
  obtain ⟨v, huv, hv2⟩ := exists_between hu2
  have hu1 : 1 < u := hone.trans hu
  have hc : 0 < Sieve.squarefreeDensity*u-1 := by
    have := (div_lt_iff₀ rho_pos).1 hu
    nlinarith
  refine ⟨u, v, Sieve.squarefreeDensity*u-1, hu1, huv, hv2, hc, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := hu1.le.trans hx.1
  have hx2 : x < 2 := hx.2.trans_lt hv2
  have hfloor : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).2 (by constructor; exact_mod_cast hx1; norm_num; exact hx2)
  have hcount : count x = 1 := by simp [count, hfloor]
  rw [error, hcount]
  nlinarith [mul_le_mul_of_nonneg_left hx.1 rho_pos.le]

private theorem integrable_gap {a : ℝ} (ha : a < 1/2) :
    IntegrableOn (fun x : ℝ => (|error x|-error x)*x^(a-2)) (Ioi 1) := by
  convert (integrable_absolute_moment ha).sub (integrable_real_moment ha) using 1
  ext x
  simp only [Pi.sub_apply]
  ring

/-- A fixed negative counting interval forces a uniform positive cost for discarding signs. -/
theorem exists_uniform_absolute_gap :
    ∃ η : ℝ, 0 < η ∧ ∀ a : ℝ, 1/4 ≤ a → a < 1/2 →
      realResponse a + η ≤ absoluteResponse a := by
  obtain ⟨u, v, c, hu, huv, hv, hc, herror⟩ := exists_negative_interval
  let d : ℝ := (v-u)*(c/2)
  have hd : 0 < d := mul_pos (sub_pos.mpr huv) (half_pos hc)
  refine ⟨d/(4*Sieve.squarefreeDensity), div_pos hd (mul_pos (by norm_num) rho_pos), ?_⟩
  intro a ha0 ha
  have ha0' : 0 ≤ a := by linarith
  have hi := integrable_gap ha
  have hsub : Icc u v ⊆ Ioi (1 : ℝ) := fun x hx => hu.trans_le hx.1
  have hpos : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ (|error x|-error x)*x^(a-2) := by
    intro x hx
    exact mul_nonneg (sub_nonneg.mpr (le_abs_self _))
      (Real.rpow_nonneg (by change 1 < x at hx; linarith) _)
  have hlocal : ∀ x ∈ Icc u v, c/2 ≤ (|error x|-error x)*x^(a-2) := by
    intro x hx
    have hx1 : 1 ≤ x := hu.le.trans hx.1
    have hx2 : x ≤ 2 := hx.2.trans hv.le
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx1
    have he := herror x hx
    have hn : error x < 0 := lt_of_le_of_lt he (neg_neg_of_pos hc)
    rw [abs_of_neg hn]
    have hw1 : (1/4 : ℝ) ≤ x^(-2 : ℝ) := by
      have hw := Real.rpow_le_rpow_of_nonpos hx0 hx2 (by norm_num : (-2 : ℝ) ≤ 0)
      norm_num [Real.rpow_neg, Real.rpow_natCast] at hw ⊢
      exact hw
    have hw2 : x^(-2 : ℝ) ≤ x^(a-2) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hmul := mul_le_mul_of_nonneg_right (show 2*c ≤ -error x-error x by linarith)
      (show 0 ≤ x^(a-2) from Real.rpow_nonneg hx0.le _)
    nlinarith [mul_le_mul_of_nonneg_left (hw1.trans hw2) (show 0 ≤ 2*c by linarith)]
  have hIlocal : d ≤ ∫ x in Icc u v, (|error x|-error x)*x^(a-2) := by
    have h := setIntegral_mono_on (f := fun _ : ℝ => c/2)
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) :
        IntegrableOn (fun _ : ℝ => c/2) (Icc u v))
      (hi.mono_set hsub) measurableSet_Icc hlocal
    simpa only [setIntegral_const, Real.volume_real_Icc_of_le huv.le, smul_eq_mul, d] using h
  have hI : d ≤ ∫ x in Ioi (1 : ℝ), (|error x|-error x)*x^(a-2) := by
    apply hIlocal.trans (setIntegral_mono_set hi ?_ (Filter.Eventually.of_forall hsub))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpos x hx
  have hdiff : absoluteResponse a-realResponse a = a/Sieve.squarefreeDensity *
      ∫ x in Ioi (1 : ℝ), (|error x|-error x)*x^(a-2) := by
    rw [absoluteResponse, realResponse_eq]
    simp_rw [sub_mul]
    rw [integral_sub (integrable_absolute_moment ha) (integrable_real_moment ha)]
    ring
  have hcoef : (1/4 : ℝ)/Sieve.squarefreeDensity ≤ a/Sieve.squarefreeDensity :=
    div_le_div_of_nonneg_right ha0 rho_pos.le
  have hbound := mul_le_mul_of_nonneg_left hI (div_nonneg ha0' rho_pos.le)
  have hlower := mul_le_mul_of_nonneg_right hcoef hd.le
  rw [← hdiff] at hbound
  have halg : (1/4 : ℝ)/Sieve.squarefreeDensity*d = d/(4*Sieve.squarefreeDensity) := by ring
  rw [halg] at hlower
  linarith

/-- The absolute comparison multiplier exceeds one throughout a critical left neighborhood. -/
theorem eventually_one_lt_absoluteResponse :
    ∀ᶠ a : ℝ in 𝓝[<] (1/2 : ℝ), 1 < absoluteResponse a := by
  obtain ⟨η, hη, hgap⟩ := exists_uniform_absolute_gap
  have ht := tendsto_realResponse_half.eventually (eventually_gt_nhds (show 1-η/2 < 1 by linarith))
  filter_upwards [ht, (eventually_gt_nhds (show (1/4 : ℝ) < 1/2 by norm_num)).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with a hq ha0 ha
  have := hgap a ha0.le ha
  linarith

end
end RHTower.SquarefreeDiscrepancy
