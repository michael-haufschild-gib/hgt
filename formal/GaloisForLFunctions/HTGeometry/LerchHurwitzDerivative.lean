import GaloisForLFunctions.HTGeometry.BinetLogGamma

/-!
# Lerch's formula for the derivative of the Hurwitz zeta function at `s = 0`

The spectral zeta function of the shifted number operator, `ζ_H(s,a) = ∑_{n ≥ 0} (n+a)^{-s}`, is
continued to a neighbourhood of `s = 0` by second-order Euler–Maclaurin:

```text
ζ_H(s,a) = a^{1-s}/(s-1) + a^{-s}/2 − s(s+1) ∫_0^∞ P₂(x)(x+a)^{-s-2} dx.
```

Its derivative at `s = 0` is Lerch's formula

```text
ζ_H'(0,a) = log Γ(a) − (1/2) log (2π),
```

equivalently `Γ(a)·exp(−ζ_H'(0,a)) = √(2π)`: the ζ-regularized determinant of `N + a` is the
*reciprocal* of `Γ(a)` up to `√(2π)`.  Only continuity of the Euler–Maclaurin integral at `s = 0` is
needed, because the factor `s(s+1)` already vanishes there.
-/

open Filter Real MeasureTheory Set Complex
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Shifted power integrability -/

theorem hasDerivAt_shift_rpow {a q x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => (y + a) ^ q) (q * (x + a) ^ (q - 1)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have hout : HasDerivAt (fun t : ℝ => t ^ q) (q * (x + a) ^ (q - 1)) (x + a) :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt h))
  have := hout.comp x hb
  have hfun : ((fun t : ℝ => t ^ q) ∘ fun y : ℝ => y + a) = fun y : ℝ => (y + a) ^ q := rfl
  rw [hfun] at this
  exact this.congr_deriv (by ring)

theorem integrableOn_Ioi_shift_rpow_neg {a p : ℝ} (ha : 0 < a) (hp : 1 < p) :
    IntegrableOn (fun x : ℝ => (x + a) ^ (-p)) (Ioi (0 : ℝ)) := by
  have hp0 : (0 : ℝ) < p - 1 := by linarith
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg
    (g := fun x : ℝ => -((x + a) ^ (1 - p) / (p - 1))) (l := 0) ?_ ?_ ?_ ?_
  · have hcont : ContinuousAt (fun x : ℝ => -((x + a) ^ (1 - p) / (p - 1))) 0 := by
      refine ContinuousAt.neg (ContinuousAt.div ?_ continuousAt_const (by linarith))
      exact (Real.continuousAt_rpow_const _ _ (Or.inl (by simpa using ne_of_gt ha))).comp
        (by fun_prop)
    exact hcont.continuousWithinAt
  · intro x hx
    have hxa : (0 : ℝ) < x + a := by
      have : (0 : ℝ) < x := hx
      linarith
    have hd := (hasDerivAt_shift_rpow (a := a) (q := 1 - p) hxa).div_const (p - 1)
    refine (hd.neg).congr_deriv ?_
    have hexp : (1 : ℝ) - p - 1 = -p := by ring
    rw [hexp]
    field_simp
    ring
  · intro x hx
    have hxa : (0 : ℝ) < x + a := by
      have : (0 : ℝ) < x := hx
      linarith
    positivity
  · have hbase : Tendsto (fun x : ℝ => x + a) atTop atTop :=
      tendsto_atTop_add_const_right _ a tendsto_id
    have hrpow : Tendsto (fun t : ℝ => t ^ (-(p - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hp0
    have hcomp : Tendsto (fun x : ℝ => (x + a) ^ (-(p - 1))) atTop (𝓝 0) := hrpow.comp hbase
    have hfin : Tendsto (fun x : ℝ => -((x + a) ^ (-(p - 1)) / (p - 1))) atTop (𝓝 (-(0 / (p - 1)))) :=
      (hcomp.div_const (p - 1)).neg
    rw [zero_div, neg_zero] at hfin
    refine hfin.congr fun x => ?_
    congr 2
    ring

/-! ## The Euler–Maclaurin kernel -/

/-- The Euler–Maclaurin kernel `∫_0^∞ P₂(x)(x+a)^{-s-2} dx`. -/
def emKernel (a : ℝ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)

theorem norm_shiftCpow {a x : ℝ} (h : 0 < x + a) (s : ℂ) :
    ‖((x + a : ℝ) : ℂ) ^ (-s - 2)‖ = (x + a) ^ (-s.re - 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h]
  congr 1

/-- The uniform dominating bound on a strip around `s = 0`. -/
theorem norm_emKernel_integrand_le {a : ℝ} (ha : 0 < a) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1 / 2) {x : ℝ} (hx : 0 < x) :
    ‖((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)‖
      ≤ (1 / 8) * max 1 a⁻¹ * (x + a) ^ (-(3 / 2 : ℝ)) := by
  have hxa : (0 : ℝ) < x + a := by linarith
  have hax : a ≤ x + a := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_shiftCpow hxa]
  have hsplit : (x + a) ^ (-s.re - 2)
      = (x + a) ^ (-(3 / 2 : ℝ)) * (x + a) ^ (-s.re - 1 / 2) := by
    rw [← Real.rpow_add hxa]
    congr 1
    ring
  have hexp : -s.re - 1 / 2 ≤ 0 := by linarith
  have hexp' : -(1 : ℝ) ≤ -s.re - 1 / 2 := by linarith
  have hmono : (x + a) ^ (-s.re - 1 / 2) ≤ a ^ (-s.re - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos ha hax hexp
  have hbound : a ^ (-s.re - 1 / 2) ≤ max 1 a⁻¹ := by
    rcases le_or_gt 1 a with hge | hlt
    · refine le_trans ?_ (le_max_left 1 a⁻¹)
      calc a ^ (-s.re - 1 / 2) ≤ a ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hge hexp
        _ = 1 := Real.rpow_zero a
    · refine le_trans ?_ (le_max_right 1 a⁻¹)
      have hinv : a ^ (-(1 : ℝ)) = a⁻¹ := by
        rw [Real.rpow_neg_one]
      rw [← hinv]
      exact Real.rpow_le_rpow_of_exponent_ge ha hlt.le hexp'
  have hker := abs_bernoulliHalfPer_le x
  have hpos1 : (0 : ℝ) < (x + a) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hxa _
  have hstep : (x + a) ^ (-s.re - 2) ≤ (x + a) ^ (-(3 / 2 : ℝ)) * max 1 a⁻¹ := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (le_trans hmono hbound) hpos1.le
  calc |bernoulliHalfPer x| * (x + a) ^ (-s.re - 2)
      ≤ (1 / 8) * ((x + a) ^ (-(3 / 2 : ℝ)) * max 1 a⁻¹) := by
        refine mul_le_mul hker hstep (Real.rpow_nonneg hxa.le _) (by norm_num)
    _ = (1 / 8) * max 1 a⁻¹ * (x + a) ^ (-(3 / 2 : ℝ)) := by ring

theorem aestronglyMeasurable_emKernel_integrand {a : ℝ} (ha : 0 < a) (s : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · exact (Complex.measurable_ofReal.comp measurable_bernoulliHalfPer).aestronglyMeasurable
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.cpow_const (by fun_prop) ?_
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    exact Or.inl (by simpa using (by linarith : (0 : ℝ) < y + a))

theorem integrableOn_emKernel_integrand {a : ℝ} (ha : 0 < a) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1 / 2) :
    IntegrableOn
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2))
      (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn
      (fun x : ℝ => (1 / 8) * max 1 a⁻¹ * (x + a) ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_shift_rpow_neg ha (by norm_num)).const_mul _
  refine Integrable.mono hdom (aestronglyMeasurable_emKernel_integrand ha s) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hxa : (0 : ℝ) < x + a := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_emKernel_integrand_le ha h1 h2 hx0

/-- The Euler–Maclaurin kernel is continuous at `s = 0`. -/
theorem continuousAt_emKernel_zero {a : ℝ} (ha : 0 < a) :
    ContinuousAt (emKernel a) 0 := by
  have hball : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 := by
    have hcont : ContinuousAt Complex.re 0 := Complex.continuous_re.continuousAt
    have h1 : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), s.re < 1 / 2 := by
      refine hcont.eventually_lt_const ?_
      norm_num
    have h2 : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -(1 / 2 : ℝ) < s.re := by
      refine hcont.eventually_const_lt ?_
      norm_num
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs2.le, hs1.le⟩
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun x : ℝ => (1 / 8) * max 1 a⁻¹ * (x + a) ^ (-(3 / 2 : ℝ))) ?_ ?_ ?_ ?_
  · filter_upwards [hball] with s _
    exact aestronglyMeasurable_emKernel_integrand ha s
  · filter_upwards [hball] with s hs
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact norm_emKernel_integrand_le ha hs.1 hs.2 hx
  · exact (integrableOn_Ioi_shift_rpow_neg ha (by norm_num)).const_mul _
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hxa : (0 : ℝ) < x + a := by linarith
    refine ContinuousAt.mul continuousAt_const ?_
    have hbase : ((x + a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hxa)
    exact ContinuousAt.const_cpow (by fun_prop) (Or.inl hbase)

/-! ## The Euler–Maclaurin continuation and its derivative at `s = 0` -/

/-- The Euler–Maclaurin continuation of the spectral zeta function `∑_{n ≥ 0} (n+a)^{-s}`. -/
def hurwitzZetaEM (a : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (1 - s) / (s - 1) + (a : ℂ) ^ (-s) / 2 - s * (s + 1) * emKernel a s

theorem emKernel_zero {a : ℝ} (ha : 0 < a) : emKernel a 0 = ((binetKernel a : ℝ) : ℂ) := by
  rw [emKernel, binetKernel, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := hx
  have hxa : (0 : ℝ) < x + a := by linarith
  have hexp : (-(0 : ℂ) - 2) = (((-2 : ℝ) : ℝ) : ℂ) := by norm_num
  have hpow : ((x + a : ℝ) : ℂ) ^ (((-2 : ℝ) : ℝ) : ℂ) = (((x + a) ^ (-2 : ℝ) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow hxa.le (-2 : ℝ)).symm
  have hrpow : (x + a) ^ (-2 : ℝ) = 1 / (x + a) ^ 2 := by
    rw [Real.rpow_neg hxa.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [hexp, hpow, hrpow]
  push_cast
  ring

theorem hasDerivAt_hurwitzZetaEM_zero {a : ℝ} (ha : 0 < a) :
    HasDerivAt (hurwitzZetaEM a)
      (((a * Real.log a - a - Real.log a / 2 - binetKernel a : ℝ) : ℂ)) 0 := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hlog : Complex.log ((a : ℝ) : ℂ) = ((Real.log a : ℝ) : ℂ) := (Complex.ofReal_log ha.le).symm
  -- first summand
  have hu : HasDerivAt (fun s : ℂ => (a : ℂ) ^ (1 - s))
      (-(((a * Real.log a : ℝ) : ℂ))) 0 := by
    have hb : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hd := hb.const_cpow (c := (a : ℂ)) (Or.inl hane)
    refine hd.congr_deriv ?_
    rw [hlog]
    simp only [sub_zero, Complex.cpow_one]
    push_cast
    ring
  have hv : HasDerivAt (fun s : ℂ => s - 1) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).sub_const 1
  have hvne : ((0 : ℂ) - 1) ≠ 0 := by norm_num
  have hA : HasDerivAt (fun s : ℂ => (a : ℂ) ^ (1 - s) / (s - 1))
      (((a * Real.log a - a : ℝ) : ℂ)) 0 := by
    have hd := hu.div hv hvne
    refine hd.congr_deriv ?_
    simp only [sub_zero, Complex.cpow_one]
    push_cast
    ring
  -- second summand
  have hB : HasDerivAt (fun s : ℂ => (a : ℂ) ^ (-s) / 2)
      ((-(((Real.log a : ℝ) : ℂ)) / 2)) 0 := by
    have hb : HasDerivAt (fun s : ℂ => -s) (-1) 0 := by
      have h := (hasDerivAt_id (0 : ℂ)).neg
      have hf : (-(id : ℂ → ℂ)) = fun s : ℂ => -s := by
        funext s
        simp [Pi.neg_apply]
      rw [hf] at h
      exact h
    have hd := (hb.const_cpow (c := (a : ℂ)) (Or.inl hane)).div_const 2
    refine hd.congr_deriv ?_
    rw [hlog]
    simp only [neg_zero, Complex.cpow_zero]
    ring
  -- third summand
  have hC : HasDerivAt (fun s : ℂ => s * (s + 1) * emKernel a s) (emKernel a 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hbase : Tendsto (fun s : ℂ => (s + 1) * emKernel a s) (𝓝 (0 : ℂ))
        (𝓝 (((0 : ℂ) + 1) * emKernel a 0)) :=
      ((continuousAt_id.add continuousAt_const).mul (continuousAt_emKernel_zero ha))
    rw [zero_add, one_mul] at hbase
    have hnhds : Tendsto (fun s : ℂ => (s + 1) * emKernel a s) (𝓝[≠] (0 : ℂ))
        (𝓝 (emKernel a 0)) := hbase.mono_left nhdsWithin_le_nhds
    refine hnhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    rw [slope_def_field]
    field_simp
    ring
  have hsum := (hA.add hB).sub hC
  have hfun : (((fun s : ℂ => (a : ℂ) ^ (1 - s) / (s - 1)) + fun s : ℂ => (a : ℂ) ^ (-s) / 2)
      - fun s : ℂ => s * (s + 1) * emKernel a s) = hurwitzZetaEM a := by
    funext s
    simp [hurwitzZetaEM, Pi.sub_apply, Pi.add_apply]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [emKernel_zero ha]
  push_cast
  ring

/-- **Lerch's formula.**  The `s`-derivative at `0` of the spectral zeta function of `N + a` is
`log Γ(a) − (1/2) log (2π)`. -/
theorem hasDerivAt_hurwitzZetaEM_zero_lerch {a : ℝ} (ha : 0 < a) :
    HasDerivAt (hurwitzZetaEM a)
      (((Real.log (Real.Gamma a) - Real.log (2 * π) / 2 : ℝ) : ℂ)) 0 := by
  have hd := hasDerivAt_hurwitzZetaEM_zero ha
  have hbinet := log_Gamma_eq_binet ha
  have heq : (a * Real.log a - a - Real.log a / 2 - binetKernel a : ℝ)
      = Real.log (Real.Gamma a) - Real.log (2 * π) / 2 := by
    rw [hbinet]
    ring
  rw [heq] at hd
  exact hd

theorem deriv_hurwitzZetaEM_zero {a : ℝ} (ha : 0 < a) :
    deriv (hurwitzZetaEM a) 0 = ((Real.log (Real.Gamma a) - Real.log (2 * π) / 2 : ℝ) : ℂ) :=
  (hasDerivAt_hurwitzZetaEM_zero_lerch ha).deriv

/-! ## The Euler–Maclaurin function is the Hurwitz zeta function -/

theorem hasDerivAt_shiftCpow {a : ℝ} (c : ℂ) {x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => ((y + a : ℝ) : ℂ) ^ c) (c * ((x + a : ℝ) : ℂ) ^ (c - 1)) x := by
  have hb : HasDerivAt (fun y : ℝ => ((y + a : ℝ) : ℂ)) 1 x := by
    have hreal : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
    simpa using hreal.ofReal_comp
  have hmem : ((x + a : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using h)
  have hout : HasDerivAt (fun z : ℂ => z ^ c) (c * ((x + a : ℝ) : ℂ) ^ (c - 1) * 1)
      ((x + a : ℝ) : ℂ) := (hasDerivAt_id ((x + a : ℝ) : ℂ)).cpow_const hmem
  have hcomp := hout.comp x hb
  have hfun : ((fun z : ℂ => z ^ c) ∘ fun y : ℝ => ((y + a : ℝ) : ℂ))
      = fun y : ℝ => ((y + a : ℝ) : ℂ) ^ c := rfl
  rw [hfun] at hcomp
  exact hcomp.congr_deriv (by ring)

theorem continuousOn_shiftCpow {a : ℝ} (ha : 0 < a) (c : ℂ) :
    ContinuousOn (fun y : ℝ => ((y + a : ℝ) : ℂ) ^ c) (Ici (0 : ℝ)) := by
  refine ContinuousOn.cpow_const (by fun_prop) ?_
  intro y hy
  have hy0 : (0 : ℝ) ≤ y := hy
  exact Or.inl (by simpa using (by linarith : (0 : ℝ) < y + a))

theorem integral_shiftCpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), ((x + a : ℝ) : ℂ) ^ (-s))
      = ((((N : ℝ) + a : ℝ) : ℂ) ^ (1 - s) - ((a : ℝ) : ℂ) ^ (1 - s)) / (1 - s) := by
  have hle : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) ((N : ℝ)),
      HasDerivAt (fun y : ℝ => ((y + a : ℝ) : ℂ) ^ (1 - s) / (1 - s))
        (((x + a : ℝ) : ℂ) ^ (-s)) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have hxa : (0 : ℝ) < x + a := by linarith [hx.1]
    have hd := (hasDerivAt_shiftCpow (a := a) (1 - s) hxa).div_const (1 - s)
    refine hd.congr_deriv ?_
    have hexp : (1 : ℂ) - s - 1 = -s := by ring
    rw [hexp]
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => ((x + a : ℝ) : ℂ) ^ (-s)) volume 0 ((N : ℝ)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    exact (continuousOn_shiftCpow ha (-s)).mono (fun x hx => le_trans hx.1 le_rfl)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  push_cast
  rw [div_sub_div_same, zero_add]

theorem sum_shiftCpow_eq {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + a : ℝ) : ℂ) ^ (-s))
      = ((((N : ℝ) + a : ℝ) : ℂ) ^ (1 - s) - ((a : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + (((a : ℝ) : ℂ) ^ (-s) + ((((N : ℝ) + a : ℝ) : ℂ)) ^ (-s)) / 2
        - s * (s + 1) *
          ∫ x in (0 : ℝ)..(N : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2) := by
  have hpos : ∀ x ∈ Ici (0 : ℝ), 0 < x + a := by
    intro x hx
    have : (0 : ℝ) ≤ x := hx
    linarith
  have hem := euler_maclaurin_second_order (f := fun y : ℝ => ((y + a : ℝ) : ℂ) ^ (-s))
    (f' := fun y : ℝ => -s * ((y + a : ℝ) : ℂ) ^ (-s - 1))
    (f'' := fun y : ℝ => s * (s + 1) * ((y + a : ℝ) : ℂ) ^ (-s - 2)) N
    (fun x hx => by
      have hd := hasDerivAt_shiftCpow (a := a) (-s) (hpos x hx)
      exact hd.congr_deriv (by ring))
    (fun x hx => by
      have hd := (hasDerivAt_shiftCpow (a := a) (-s - 1) (hpos x hx)).const_mul (-s)
      refine hd.congr_deriv ?_
      have hexp : -s - 1 - 1 = -s - 2 := by ring
      rw [hexp]
      ring)
    (by
      refine ContinuousOn.mul continuousOn_const ?_
      exact continuousOn_shiftCpow ha (-s - 2))
  rw [integral_shiftCpow ha hs N] at hem
  have hker : (∫ x in (0 : ℝ)..(N : ℝ),
      ((bernoulliHalfPer x : ℝ) : ℂ) * (s * (s + 1) * ((x + a : ℝ) : ℂ) ^ (-s - 2)))
      = s * (s + 1) * ∫ x in (0 : ℝ)..(N : ℝ),
        ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hker] at hem
  rw [hem]
  push_cast
  ring

/-! ## Identification with the convergent series -/

theorem norm_emKernel_integrand_le' {a : ℝ} (ha : 0 < a) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) {x : ℝ} (hx : 0 < x) :
    ‖((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)‖
      ≤ (1 / 8) * a ^ (-s.re - 1 / 2) * (x + a) ^ (-(3 / 2 : ℝ)) := by
  have hxa : (0 : ℝ) < x + a := by linarith
  have hax : a ≤ x + a := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_shiftCpow hxa]
  have hsplit : (x + a) ^ (-s.re - 2)
      = (x + a) ^ (-(3 / 2 : ℝ)) * (x + a) ^ (-s.re - 1 / 2) := by
    rw [← Real.rpow_add hxa]
    congr 1
    ring
  have hexp : -s.re - 1 / 2 ≤ 0 := by linarith
  have hmono : (x + a) ^ (-s.re - 1 / 2) ≤ a ^ (-s.re - 1 / 2) :=
    Real.rpow_le_rpow_of_nonpos ha hax hexp
  have hker := abs_bernoulliHalfPer_le x
  have hpos1 : (0 : ℝ) < (x + a) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hxa _
  have hstep : (x + a) ^ (-s.re - 2) ≤ (x + a) ^ (-(3 / 2 : ℝ)) * a ^ (-s.re - 1 / 2) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hmono hpos1.le
  calc |bernoulliHalfPer x| * (x + a) ^ (-s.re - 2)
      ≤ (1 / 8) * ((x + a) ^ (-(3 / 2 : ℝ)) * a ^ (-s.re - 1 / 2)) :=
        mul_le_mul hker hstep (Real.rpow_nonneg hxa.le _) (by norm_num)
    _ = (1 / 8) * a ^ (-s.re - 1 / 2) * (x + a) ^ (-(3 / 2 : ℝ)) := by ring

theorem integrableOn_emKernel_integrand' {a : ℝ} (ha : 0 < a) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) :
    IntegrableOn
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2))
      (Ioi (0 : ℝ)) := by
  have hdom : IntegrableOn
      (fun x : ℝ => (1 / 8) * a ^ (-s.re - 1 / 2) * (x + a) ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_shift_rpow_neg ha (by norm_num)).const_mul _
  refine Integrable.mono hdom (aestronglyMeasurable_emKernel_integrand ha s) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hcst : (0 : ℝ) ≤ a ^ (-s.re - 1 / 2) := Real.rpow_nonneg ha.le _
  have hxa : (0 : ℝ) < x + a := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_emKernel_integrand_le' ha h1 hx0

theorem tendsto_emKernelTrunc {a : ℝ} (ha : 0 < a) {s : ℂ} (h1 : -(1 / 2 : ℝ) ≤ s.re) :
    Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
        ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2))
      atTop (𝓝 (emKernel a s)) :=
  MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
    (integrableOn_emKernel_integrand' ha h1) tendsto_natCast_atTop_atTop

theorem tendsto_shiftCpow_atTop {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => ((((N : ℝ) + a : ℝ)) : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ N : ℕ, ‖((((N : ℝ) + a : ℝ)) : ℂ) ^ w‖ = ((N : ℝ) + a) ^ w.re := by
    intro N
    have hpos : (0 : ℝ) < (N : ℝ) + a := by
      have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    exact Complex.norm_cpow_eq_rpow_re_of_pos hpos w
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) + a) atTop atTop :=
    tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop
  have hrpow : Tendsto (fun t : ℝ => t ^ (-(-w.re))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hcomp : Tendsto (fun N : ℕ => ((N : ℝ) + a) ^ (-(-w.re))) atTop (𝓝 0) := hrpow.comp hbase
  refine hcomp.congr fun N => ?_
  rw [neg_neg, hnorm N]

theorem summable_shiftCpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n : ℝ) + a : ℝ) : ℂ) ^ (-s)) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + a := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-s).re = -s.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by linarith)

/-- **The Euler–Maclaurin function is the Hurwitz zeta function.**  On `Re s > 1` it equals the
convergent spectral series `∑_{n ≥ 0} (n+a)^{-s}`. -/
theorem hurwitzZetaEM_eq_tsum {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZetaEM a s = ∑' n : ℕ, (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hsum := summable_shiftCpow ha hs
  have hpartial : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
      (((m : ℝ) + a : ℝ) : ℂ) ^ (-s)) atTop (𝓝 (∑' n : ℕ, (((n : ℝ) + a : ℝ) : ℂ) ^ (-s))) := by
    have hbase := hsum.hasSum.tendsto_sum_nat
    exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim1 : Tendsto (fun N : ℕ => ((((N : ℝ) + a : ℝ) : ℂ)) ^ (1 - s)) atTop (𝓝 0) :=
    tendsto_shiftCpow_atTop ha (by simp; linarith)
  have hlim2 : Tendsto (fun N : ℕ => ((((N : ℝ) + a : ℝ) : ℂ)) ^ (-s)) atTop (𝓝 0) :=
    tendsto_shiftCpow_atTop ha (by simp; linarith)
  have hlim3 := tendsto_emKernelTrunc ha (s := s) (by linarith)
  have hrhs : Tendsto (fun N : ℕ => ((((N : ℝ) + a : ℝ) : ℂ) ^ (1 - s) - ((a : ℝ) : ℂ) ^ (1 - s))
      / (1 - s) + (((a : ℝ) : ℂ) ^ (-s) + ((((N : ℝ) + a : ℝ) : ℂ)) ^ (-s)) / 2
      - s * (s + 1) * ∫ x in (0 : ℝ)..(N : ℝ),
        ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2)) atTop
      (𝓝 (((0 : ℂ) - ((a : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + (((a : ℝ) : ℂ) ^ (-s) + 0) / 2 - s * (s + 1) * emKernel a s)) := by
    refine Tendsto.sub (Tendsto.add ?_ ?_) ?_
    · exact (hlim1.sub tendsto_const_nhds).div_const _
    · exact (tendsto_const_nhds.add hlim2).div_const _
    · exact tendsto_const_nhds.mul hlim3
  have heq : ∀ N : ℕ, (∑ m ∈ Finset.range (N + 1), (((m : ℝ) + a : ℝ) : ℂ) ^ (-s))
      = ((((N : ℝ) + a : ℝ) : ℂ) ^ (1 - s) - ((a : ℝ) : ℂ) ^ (1 - s)) / (1 - s)
        + (((a : ℝ) : ℂ) ^ (-s) + ((((N : ℝ) + a : ℝ) : ℂ)) ^ (-s)) / 2
        - s * (s + 1) * ∫ x in (0 : ℝ)..(N : ℝ),
          ((bernoulliHalfPer x : ℝ) : ℂ) * ((x + a : ℝ) : ℂ) ^ (-s - 2) :=
    fun N => sum_shiftCpow_eq ha hs1 N
  have hfinal := tendsto_nhds_unique (hpartial.congr heq) hrhs
  rw [hfinal]
  simp only [hurwitzZetaEM]
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-! ## The ζ-regularized determinant of `N + a` -/

/-- Lerch's value: the `s`-derivative at `0` of the spectral zeta function of `N + a`. -/
def hurwitzDerivZero (a : ℝ) : ℝ := Real.log (Real.Gamma a) - Real.log (2 * π) / 2

theorem deriv_hurwitzZetaEM_zero_eq {a : ℝ} (ha : 0 < a) :
    deriv (hurwitzZetaEM a) 0 = ((hurwitzDerivZero a : ℝ) : ℂ) :=
  deriv_hurwitzZetaEM_zero ha

/-- The ζ-regularized determinant `det_ζ(N + a) = exp(−ζ_H'(0,a))`. -/
def zetaRegDet (a : ℝ) : ℝ := Real.exp (-(hurwitzDerivZero a))

/-- **The regularized determinant is the reciprocal of `Γ` up to `√(2π)`.** -/
theorem zetaRegDet_eq {a : ℝ} (ha : 0 < a) :
    zetaRegDet a = Real.sqrt (2 * π) / Real.Gamma a := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [zetaRegDet, hurwitzDerivZero, neg_sub, Real.exp_sub, Real.exp_log hΓ]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h2π]
  congr 1
  ring

/-- **`Γ(a)·det_ζ(N+a) = √(2π)`** — the one-sided regularized ladder identity. -/
theorem Gamma_mul_zetaRegDet {a : ℝ} (ha : 0 < a) :
    Real.Gamma a * zetaRegDet a = Real.sqrt (2 * π) := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  rw [zetaRegDet_eq ha]
  field_simp

/-- **The archimedean Euler factor is an inverse regularized determinant.**
`Γ_ℝ(s) = π^{-s/2}·√(2π)·det_ζ(N + s/2)^{-1}`. -/
theorem Gammaℝ_mul_zetaRegDet {s : ℝ} (hs : 0 < s) :
    Complex.Gammaℝ (s : ℂ) * ((zetaRegDet (s / 2) : ℝ) : ℂ)
      = ((π : ℝ) : ℂ) ^ (-(s : ℂ) / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have hs2 : (0 : ℝ) < s / 2 := by linarith
  have hΓ : Complex.Gamma ((s : ℂ) / 2) = ((Real.Gamma (s / 2) : ℝ) : ℂ) := by
    rw [show ((s : ℂ) / 2) = (((s / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
  rw [Complex.Gammaℝ_def, hΓ, mul_assoc, ← Complex.ofReal_mul, Gamma_mul_zetaRegDet hs2]

end

end GaloisForLFunctions.HTGeometry
