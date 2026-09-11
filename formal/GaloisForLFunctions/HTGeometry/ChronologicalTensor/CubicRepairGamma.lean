import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRepairLimit

/-!
# The explicit finite Gamma/power-sum response

The finite normalization defect of rank `k` has kernel `b_k = C_k - H_k` with
`C_k(t) = ∫_0^k e^{-xt} dx` and `H_k(t) = Σ_{n=1}^k e^{-nt}`. On the strip `0 < Re s < 1` its
Mellin transform is

  `R_k(s) = Γ(s) (k^(1-s)/(1-s) - Σ_{n=1}^k n^(-s))`.

The discrete part is a finite sum of scaled Gamma integrals. The continuum reference is the same
Gamma integral integrated in its parameter, which is one application of Fubini justified by the
Tonelli bound `∫_0^k x^(-Re s) dx < ∞`.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section
open Set MeasureTheory

/-! ### The scaled Gamma integral -/

theorem cpow_ofReal_ne_zero {r : ℝ} (hr : 0 < r) (y : ℂ) : (r:ℂ) ^ y ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]
  intro h
  exact absurd h.1 (by exact_mod_cast ne_of_gt hr)

theorem one_div_cpow_ofReal {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((1:ℂ)/(r:ℂ)) ^ s = (r:ℂ) ^ (-s) := by
  rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Ne.symm Real.pi_ne_zero), Complex.cpow_neg]

theorem ofReal_exp_neg_mul (r t : ℝ) :
    ((Real.exp (-(r*t)) : ℝ) : ℂ) = Complex.exp (-((r:ℂ)*(t:ℂ))) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The value of the scaled Gamma integral. -/
theorem integral_cpow_mul_exp_scaled {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) * ((Real.exp (-(r*t)) : ℝ) : ℂ)
      = Complex.Gamma s * (r:ℂ)^(-s) := by
  have heq : (fun t : ℝ => (t:ℂ)^(s-1) * ((Real.exp (-(r*t)) : ℝ) : ℂ))
      = fun t : ℝ => (t:ℂ)^(s-1) * Complex.exp (-((r:ℂ)*(t:ℂ))) := by
    funext t
    rw [ofReal_exp_neg_mul]
  rw [heq, Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr, one_div_cpow_ofReal hr]
  ring

/-- Integrability of the scaled Gamma integrand. -/
theorem integrableOn_cpow_mul_exp_scaled {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1) * ((Real.exp (-(r*t)) : ℝ) : ℂ)) (Ioi 0) := by
  have hbase := Complex.GammaIntegral_convergent hs
  have hscaled : IntegrableOn
      (fun x : ℝ => ((Real.exp (-(r*x)) : ℝ) : ℂ) * ((r*x : ℝ):ℂ)^(s-1)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ) * (x:ℂ)^(s-1)) 0 hr).mpr (by simpa using hbase)
    simpa using h
  have hfac : ∀ x ∈ Ioi (0:ℝ),
      ((Real.exp (-(r*x)) : ℝ) : ℂ) * ((r*x : ℝ):ℂ)^(s-1)
        = (r:ℂ)^(s-1) * ((x:ℂ)^(s-1) * ((Real.exp (-(r*x)) : ℝ) : ℂ)) := by
    intro x hx
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (le_of_lt hx)]
    ring
  have hscaled2 : IntegrableOn
      (fun x : ℝ => (r:ℂ)^(s-1) * ((x:ℂ)^(s-1) * ((Real.exp (-(r*x)) : ℝ) : ℂ))) (Ioi 0) :=
    hscaled.congr (Filter.eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi) hfac)
  have h3 := hscaled2.const_mul ((r:ℂ)^(s-1))⁻¹
  refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
  show ((r:ℂ)^(s-1))⁻¹ * ((r:ℂ)^(s-1) * ((x:ℂ)^(s-1) * ((Real.exp (-(r*x)) : ℝ) : ℂ)))
      = (x:ℂ)^(s-1) * ((Real.exp (-(r*x)) : ℝ) : ℂ)
  rw [← mul_assoc, inv_mul_cancel₀ (cpow_ofReal_ne_zero hr _), one_mul]

/-! ### The discrete part -/

/-- The Mellin transform of the finite discrete heat. -/
theorem integral_cpow_mul_finiteHeat (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) *
        ((∑ n ∈ Finset.range k, Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ)
      = Complex.Gamma s * ∑ n ∈ Finset.range k, ((n+1:ℕ):ℂ)^(-s) := by
  have hsplit : (fun t : ℝ => (t:ℂ)^(s-1) *
      ((∑ n ∈ Finset.range k, Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ))
      = fun t : ℝ => ∑ n ∈ Finset.range k,
          (t:ℂ)^(s-1) * ((Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ) := by
    funext t
    push_cast
    rw [Finset.mul_sum]
  rw [hsplit, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
    rw [integral_cpow_mul_exp_scaled hs hn]
    norm_cast
  · intro n _
    have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
    exact integrableOn_cpow_mul_exp_scaled hs hn

/-! ### The continuum reference -/

theorem norm_cpow_mul_exp {s : ℂ} {t x : ℝ} (ht : 0 < t) :
    ‖(t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ))‖ = t^(s.re-1) * Real.exp (-(t*x)) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

theorem integrableOn_rpow_mul_one_sub_exp {k σ : ℝ} (hk : 0 < k) (h0 : 0 < σ) (h1 : σ < 1) :
    IntegrableOn (fun t : ℝ => t^(σ-2) * (1 - Real.exp (-(k*t)))) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t^(σ-2) * (1 - Real.exp (-(k*t)))) (Ioi 0) := by
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (ne_of_gt ht))
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)).symm
  rw [hsplit, integrableOn_union]
  constructor
  · refine Integrable.mono' (g := fun t : ℝ => k * t^(σ-1)) ?_
      ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    · exact ((intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1:ℝ) < σ-1)).1).const_mul k
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hb : 1 - Real.exp (-(k*t)) ≤ k*t := by
        have := Real.add_one_le_exp (-(k*t))
        linarith
      have hb0 : 0 ≤ 1 - Real.exp (-(k*t)) := by
        have := Real.exp_le_one_iff.mpr (by nlinarith : -(k*t) ≤ 0)
        linarith
      have hp : (0:ℝ) < t^(σ-2) := Real.rpow_pos_of_pos ht0 _
      have hmul : t^(σ-2) * t = t^(σ-1) := by
        rw [show (σ-1) = (σ-2) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc t^(σ-2) * (1 - Real.exp (-(k*t))) ≤ t^(σ-2) * (k*t) := by
            exact mul_le_mul_of_nonneg_left hb hp.le
        _ = k * t^(σ-1) := by rw [← hmul]; ring
  · refine Integrable.mono' (g := fun t : ℝ => t^(σ-2)) ?_
      ((hcont.mono (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    · exact integrableOn_Ioi_rpow_of_lt (by linarith : σ-2 < -1) (by norm_num)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := lt_trans (by norm_num) ht
      have hb1 : 1 - Real.exp (-(k*t)) ≤ 1 := by
        have := Real.exp_pos (-(k*t))
        linarith
      have hb0 : 0 ≤ 1 - Real.exp (-(k*t)) := by
        have := Real.exp_le_one_iff.mpr (by nlinarith : -(k*t) ≤ 0)
        linarith
      have hp : (0:ℝ) < t^(σ-2) := Real.rpow_pos_of_pos ht0 _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith

/-- The finite continuum reference is a complex exponential interval integral. -/
theorem ofReal_finiteContinuousHeat (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ((cubicFiniteContinuousHeat k t : ℝ) : ℂ)
      = ∫ x in Ioc (0:ℝ) (k:ℝ), Complex.exp (-(t:ℂ)*(x:ℂ)) := by
  have htc : (-(t:ℂ)) ≠ 0 := neg_ne_zero.mpr (by exact_mod_cast ne_of_gt ht)
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ (k:ℝ))]
  rw [show (fun x : ℝ => Complex.exp (-(t:ℂ)*(x:ℂ))) = fun x : ℝ => Complex.exp ((-(t:ℂ))*(x:ℂ))
    from rfl, integral_exp_mul_complex htc, cubicFiniteContinuousHeat_eq k ht]
  have hne : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  rw [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp]
  push_cast
  field_simp
  simp only [mul_zero, neg_zero, Complex.exp_zero]
  ring

theorem integrableOn_cpow_mul_finiteContinuousHeat (k : ℕ) (hk : 0 < k) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^(s-1) * ((cubicFiniteContinuousHeat k t : ℝ) : ℂ))
      (Ioi 0) := by
  have hkr : (0:ℝ) < (k:ℝ) := by positivity
  refine Integrable.mono'
    (g := fun t : ℝ => t^(s.re-2) * (1 - Real.exp (-((k:ℝ)*t))))
    (integrableOn_rpow_mul_one_sub_exp hkr hs0 hs1) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (fun t ht => ((Complex.continuousAt_ofReal_cpow_const t (s-1)
      (Or.inr (ne_of_gt ht))).continuousWithinAt)) ?_
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.congr ?_ (fun t ht => (cubicFiniteContinuousHeat_eq k ht))
    exact ContinuousOn.div (by fun_prop) continuousOn_id (fun t ht => ne_of_gt ht)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht0 : (0:ℝ) < t := ht
    have htne : t ≠ 0 := ne_of_gt ht0
    have hval : cubicFiniteContinuousHeat k t = (1 - Real.exp (-((k:ℝ)*t)))/t := by
      rw [cubicFiniteContinuousHeat_eq k ht0]
      simp only [neg_mul]
    have hb0 : 0 ≤ 1 - Real.exp (-((k:ℝ)*t)) := by
      have := Real.exp_le_one_iff.mpr (by nlinarith : -((k:ℝ)*t) ≤ 0)
      linarith
    have h1 : t ^ (s.re - 2) * t = t ^ (s.re - 1) := by
      have h := (Real.rpow_add ht0 (s.re - 2) 1).symm
      rw [Real.rpow_one] at h
      rw [h]
      congr 1
      ring
    refine le_of_eq ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
      hval, abs_of_nonneg (div_nonneg hb0 ht0.le), Complex.sub_re, Complex.one_re, ← h1]
    field_simp

/-- The product integrability justifying the Fubini swap. -/
theorem integrable_uncurry_cpow_exp (k : ℕ) (hk : 0 < k) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    Integrable (Function.uncurry fun t x : ℝ => (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) (k:ℝ)))) := by
  have hkr : (0:ℝ) < (k:ℝ) := by positivity
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun t x : ℝ => (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) (k:ℝ)))) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioc)
    refine ContinuousOn.mul ?_ (by fun_prop)
    intro p hp
    exact ((Complex.continuousAt_ofReal_cpow_const p.1 (s-1)
      (Or.inr (ne_of_gt hp.1))).comp continuousAt_fst).continuousWithinAt
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    exact (by fun_prop : Continuous
      (fun x : ℝ => (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ)))).integrableOn_Ioc
  · have heq : ∀ t ∈ Ioi (0:ℝ),
        t^(s.re-2) * (1 - Real.exp (-((k:ℝ)*t)))
          = ∫ x in Ioc (0:ℝ) (k:ℝ), ‖(t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ))‖ := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => norm_cpow_mul_exp ht0),
        integral_const_mul]
      have hc : ∫ x in Ioc (0:ℝ) (k:ℝ), Real.exp (-(t*x)) = cubicFiniteContinuousHeat k t := by
        rw [cubicFiniteContinuousHeat, intervalIntegral.integral_of_le (le_of_lt hkr)]
        exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => by rw [neg_mul])
      have htne : t ≠ 0 := ne_of_gt ht0
      have hval : cubicFiniteContinuousHeat k t = (1 - Real.exp (-((k:ℝ)*t)))/t := by
        rw [cubicFiniteContinuousHeat_eq k ht0]
        simp only [neg_mul]
      have h1 : t ^ (s.re - 2) * t = t ^ (s.re - 1) := by
        have h := (Real.rpow_add ht0 (s.re - 2) 1).symm
        rw [Real.rpow_one] at h
        rw [h]
        congr 1
        ring
      rw [hc, hval, ← h1]
      field_simp
    exact (integrableOn_rpow_mul_one_sub_exp hkr hs0 hs1).congr
      (Filter.eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi) heq)

/-- The Mellin transform of the finite continuum reference. -/
theorem integral_cpow_mul_finiteRef (k : ℕ) (hk : 0 < k) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    ∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) * ((cubicFiniteContinuousHeat k t : ℝ) : ℂ)
      = Complex.Gamma s * ((k:ℂ)^(1-s)/(1-s)) := by
  have hkr : (0:ℝ) < (k:ℝ) := by positivity
  have hs1' : (1:ℂ) - s ≠ 0 := by
    intro h
    have hse : s = 1 := by linear_combination -h
    rw [hse] at hs1
    simp at hs1
  have hstep : ∀ t ∈ Ioi (0:ℝ),
      (t:ℂ)^(s-1) * ((cubicFiniteContinuousHeat k t : ℝ) : ℂ)
        = ∫ x in Ioc (0:ℝ) (k:ℝ), (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ)) := by
    intro t ht
    rw [ofReal_finiteContinuousHeat k ht, integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hstep,
    MeasureTheory.integral_integral_swap (integrable_uncurry_cpow_exp k hk hs0 hs1)]
  have hinner : ∀ x ∈ Ioc (0:ℝ) (k:ℝ),
      (∫ t in Ioi (0:ℝ), (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ)))
        = Complex.Gamma s * (x:ℂ)^(-s) := by
    intro x hx
    have hcast : ∀ t : ℝ, (t:ℂ)^(s-1) * Complex.exp (-(t:ℂ)*(x:ℂ))
        = (t:ℂ)^(s-1) * ((Real.exp (-(x*t)) : ℝ) : ℂ) := by
      intro t
      rw [ofReal_exp_neg_mul]
      ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcast t)]
    exact integral_cpow_mul_exp_scaled hs0 hx.1
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, integral_const_mul,
    ← intervalIntegral.integral_of_le (le_of_lt hkr),
    integral_cpow (Or.inl (by simpa using hs1 : (-1:ℝ) < (-s).re)),
    show (-s) + 1 = 1 - s by ring, Complex.ofReal_zero, Complex.zero_cpow hs1']
  simp

/-! ### The capstone -/

/-- **The explicit finite Gamma/power-sum response.** On the strip `0 < Re s < 1` the Mellin
transform of the rank-`k` finite normalization defect is
`Γ(s) (k^(1-s)/(1-s) - Σ_{n=1}^k n^(-s))`. -/
theorem cubicFiniteKernel_mellin_gamma (k : ℕ) (hk : 0 < k) {s : ℂ}
    (hs : s ∈ fusionMellinStrip) :
    mellin (cubicFiniteKernel k) s
      = Complex.Gamma s *
        ((k:ℂ)^(1-s)/(1-s) - ∑ n ∈ Finset.range k, ((n+1:ℕ):ℂ)^(-s)) := by
  have hA := integrableOn_cpow_mul_finiteContinuousHeat k hk hs.1 hs.2
  have hB : IntegrableOn (fun t : ℝ => ∑ n ∈ Finset.range k,
      (t:ℂ)^(s-1) * ((Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ)) (Ioi 0) :=
    integrable_finsetSum _ (fun n _ =>
      integrableOn_cpow_mul_exp_scaled hs.1 (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ)))
  have hid : ∀ t ∈ Ioi (0:ℝ), (t:ℂ)^(s-1) • cubicFiniteKernel k t
      = (t:ℂ)^(s-1) * ((cubicFiniteContinuousHeat k t : ℝ) : ℂ)
        - ∑ n ∈ Finset.range k, (t:ℂ)^(s-1) * ((Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have hh : cubicFiniteHeat k (Real.log t)
        = ∑ n ∈ Finset.range k, Real.exp (-(((n+1:ℕ):ℝ)*t)) := by
      rw [cubicFiniteHeat_partialSum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [cubicCuspModeHeat_eq, Real.exp_log ht0]
      congr 1
      ring
    simp only [cubicFiniteKernel, if_pos ht0, smul_eq_mul, hh, Complex.ofReal_sub,
      Complex.ofReal_sum, mul_sub, Finset.mul_sum]
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hid, integral_sub hA hB,
    integral_cpow_mul_finiteRef k hk hs.1 hs.2]
  have hsum : ∫ t in Ioi (0:ℝ), ∑ n ∈ Finset.range k,
      (t:ℂ)^(s-1) * ((Real.exp (-(((n+1:ℕ):ℝ)*t)) : ℝ) : ℂ)
      = Complex.Gamma s * ∑ n ∈ Finset.range k, ((n+1:ℕ):ℂ)^(-s) := by
    rw [integral_finsetSum _ (fun n _ =>
      integrableOn_cpow_mul_exp_scaled hs.1 (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ))), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [integral_cpow_mul_exp_scaled hs.1 (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ))]
    norm_cast
  rw [hsum]
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
