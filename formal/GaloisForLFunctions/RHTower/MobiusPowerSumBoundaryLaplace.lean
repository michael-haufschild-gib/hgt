import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovTransform

/-!
# The Laplace transform of the shifted power-sum boundary vector

`mobius-signed-coisometry-schur-transfer-law.md`, equations `(14)` and `(17)`:

```text
a_omega(t) = e^{-(1+omega)t} sum_{m <= e^t} m^omega ,
L a_omega(z) = zeta(1+z)/(1+omega+z) ,        Re z > 0 .
```

The proof is Tonelli on the divisor atoms: each integer `m` contributes the causal exponential
supported on `t >= log m`, whose Laplace integral is `m^{-(1+omega+z)}/(1+omega+z)`; multiplying by
the weight `m^omega` and summing gives `zeta(1+z)/(1+omega+z)`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace RHTower

/-- The power weight of the shifted power-sum, with the empty index removed. -/
def powerSumWeight (omega : ℝ) (m : ℕ) : ℝ := if m = 0 then 0 else (m : ℝ) ^ omega

theorem powerSumWeight_nonneg (omega : ℝ) (m : ℕ) : 0 ≤ powerSumWeight omega m := by
  rw [powerSumWeight]
  split_ifs with h
  · exact le_rfl
  · positivity

theorem powerSumWeight_of_pos {omega : ℝ} {m : ℕ} (hm : 0 < m) :
    powerSumWeight omega m = (m : ℝ) ^ omega := by
  rw [powerSumWeight, if_neg hm.ne']

/-- Card `(14)`: the exterior-normalized power-sum boundary vector. -/
def powerSumBoundary (omega t : ℝ) : ℝ :=
  Real.exp (-(1 + omega) * t) * ∑ m ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (m : ℝ) ^ omega

/-- The `m`-th causal atom of the Laplace integrand. -/
def powerSumAtom (omega : ℝ) (z : ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  Set.indicator (Set.Ici (Real.log m))
    (fun v : ℝ => (powerSumWeight omega m : ℂ) *
      Complex.exp (-((1 + (omega : ℂ) + z) * (v : ℂ)))) t

theorem powerSumAtom_zero (omega : ℝ) (z : ℂ) (t : ℝ) : powerSumAtom omega z 0 t = 0 := by
  rw [powerSumAtom]
  by_cases h : t ∈ Set.Ici (Real.log (0 : ℕ))
  · rw [Set.indicator_of_mem h]
    simp [powerSumWeight]
  · rw [Set.indicator_of_notMem h]

/-! ### The Laplace integral of a single atom -/

/-- Integrating a causal indicator against the positive ray drops the ambient cutoff. -/
private theorem setIntegral_Ioi_indicator_Ici
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 ≤ L) (f : ℝ → E) (hf : IntegrableOn f (Ioi L) volume) :
    (∫ t in Ioi (0 : ℝ), Set.indicator (Set.Ici L) f t) = ∫ t in Ioi L, f t := by
  have hae : (fun t : ℝ => Set.indicator (Set.Ici L) f t)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t : ℝ => Set.indicator (Set.Ioi L) f t := by
    have hnull : volume.restrict (Ioi (0 : ℝ)) ({L} : Set ℝ) = 0 := by
      rw [Measure.restrict_apply₀' measurableSet_Ioi.nullMeasurableSet]
      exact measure_mono_null Set.inter_subset_left (by simp)
    refine (ae_iff).mpr ?_
    refine measure_mono_null ?_ hnull
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    by_contra hne
    apply ht
    rcases lt_trichotomy t L with h | h | h
    · rw [Set.indicator_of_notMem (by simpa using h.not_ge),
        Set.indicator_of_notMem (by simpa using h.not_gt)]
    · exact absurd (by simpa using h) hne
    · rw [Set.indicator_of_mem (by simpa using h.le), Set.indicator_of_mem (by simpa using h)]
  have hvanish : ∀ v : ℝ, v ≤ L → Set.indicator (Set.Ioi L) f v = 0 := by
    intro v hv
    exact Set.indicator_of_notMem (by simpa using hv.not_gt) _
  have hintOn : IntegrableOn (fun t : ℝ => Set.indicator (Set.Ioi L) f t) (Ioi L) volume := by
    refine hf.congr_fun ?_ measurableSet_Ioi
    intro v hv
    exact (Set.indicator_of_mem (f := f) hv).symm
  calc (∫ t in Ioi (0 : ℝ), Set.indicator (Set.Ici L) f t)
      = ∫ t in Ioi (0 : ℝ), Set.indicator (Set.Ioi L) f t := integral_congr_ae hae
    _ = ∫ t in Ioi L, Set.indicator (Set.Ioi L) f t :=
        GaloisForLFunctions.RHTower.setIntegral_Ioi_of_vanishing hL hvanish hintOn
    _ = ∫ t in Ioi L, f t := by
        refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
        exact Set.indicator_of_mem hv _

/-- The real shifted exponential Laplace integral. -/
private theorem integral_Ioi_exp_neg_mul_shift {c : ℝ} (hc : 0 < c) (L : ℝ) :
    (∫ t in Ioi L, Real.exp (-(c * t))) = Real.exp (-(c * L)) / c := by
  rw [← GaloisForLFunctions.RHTower.integral_Ioi_translate L
    (fun t : ℝ => Real.exp (-(c * t)))]
  have hsplit : ∀ u : ℝ, Real.exp (-(c * (L + u))) = Real.exp (-(c * L)) * Real.exp (-(c * u)) := by
    intro u
    rw [← Real.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit u), integral_const_mul,
    GaloisForLFunctions.RHTower.integral_Ioi_exp_neg_mul hc]
  field_simp

private theorem integrableOn_Ioi_exp_neg_mul_shift {c : ℝ} (hc : 0 < c) (L : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ioi L) volume := by
  have h := exp_neg_integrableOn_Ioi L hc
  refine h.congr_fun ?_ measurableSet_Ioi
  intro v _
  simp only []
  ring_nf


/-! ### The Laplace integral of a single atom -/

private theorem re_shift (omega : ℝ) (z : ℂ) :
    ((1 : ℂ) + (omega : ℂ) + z).re = 1 + omega + z.re := by simp

theorem integrableOn_powerSumAtom
    {omega : ℝ} {z : ℂ} (homega : 0 ≤ omega) (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (powerSumAtom omega z m) (Ioi (0 : ℝ)) volume := by
  have hb : 0 < ((1 : ℂ) + (omega : ℂ) + z).re := by
    rw [re_shift]; linarith
  have hg : IntegrableOn
      (fun v : ℝ => (powerSumWeight omega m : ℂ) *
        Complex.exp (-(((1 : ℂ) + (omega : ℂ) + z) * (v : ℂ)))) (Ioi (0 : ℝ)) volume :=
    (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul hb).const_mul _
  exact hg.indicator measurableSet_Ici

/-- The exact norm integral of one atom. -/
theorem integral_norm_powerSumAtom
    {omega : ℝ} {z : ℂ} (homega : 0 ≤ omega) (hz : 0 < z.re) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖powerSumAtom omega z m t‖)
      = (m : ℝ) ^ (-(1 + z.re)) / (1 + omega + z.re) := by
  set c : ℝ := 1 + omega + z.re with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hnormpt : ∀ t : ℝ, ‖powerSumAtom omega z m t‖ =
      Set.indicator (Set.Ici (Real.log m))
        (fun v : ℝ => powerSumWeight omega m * Real.exp (-(c * v))) t := by
    intro t
    rw [powerSumAtom, norm_indicator_eq_indicator_norm]
    by_cases hmem : t ∈ Set.Ici (Real.log m)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (powerSumWeight_nonneg omega m), Complex.norm_exp]
      congr 1
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, re_shift, hc]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : ∀ t : ℝ, ‖powerSumAtom omega z 0 t‖ = 0 := by
      intro t; rw [powerSumAtom_zero, norm_zero]
    simp only [this, integral_zero]
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), zero_div]
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hint : IntegrableOn (fun v : ℝ => powerSumWeight omega m * Real.exp (-(c * v)))
        (Ioi (Real.log m)) volume :=
      (integrableOn_Ioi_exp_neg_mul_shift hcpos (Real.log m)).const_mul _
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hnormpt t),
      setIntegral_Ioi_indicator_Ici hlog _ hint, integral_const_mul,
      integral_Ioi_exp_neg_mul_shift hcpos]
    rw [powerSumWeight_of_pos hm]
    have hexp : Real.exp (-(c * Real.log m)) = (m : ℝ) ^ (-c) := by
      rw [Real.rpow_def_of_pos hmpos]
      congr 1
      ring
    rw [hexp, ← mul_div_assoc, ← Real.rpow_add hmpos]
    congr 2
    rw [hc]; ring

theorem summable_integral_norm_powerSumAtom
    {omega : ℝ} {z : ℂ} (homega : 0 ≤ omega) (hz : 0 < z.re) :
    Summable (fun m : ℕ => ∫ t in Ioi (0 : ℝ), ‖powerSumAtom omega z m t‖) := by
  have hbase : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + z.re))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine (hbase.div_const (1 + omega + z.re)).congr fun m => ?_
  exact (integral_norm_powerSumAtom homega hz m).symm

/-- The exact Laplace integral of one atom. -/
theorem integral_powerSumAtom
    {omega : ℝ} {z : ℂ} (homega : 0 ≤ omega) (hz : 0 < z.re) (m : ℕ) :
    (∫ t in Ioi (0 : ℝ), powerSumAtom omega z m t)
      = (m : ℂ) ^ (-(1 + z)) / (1 + (omega : ℂ) + z) := by
  have hb : 0 < ((1 : ℂ) + (omega : ℂ) + z).re := by rw [re_shift]; linarith
  have hbne : (1 : ℂ) + (omega : ℂ) + z ≠ 0 := by
    intro h; rw [h] at hb; simp at hb
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hzero : ∀ t : ℝ, powerSumAtom omega z 0 t = 0 := powerSumAtom_zero omega z
    simp only [hzero, integral_zero]
    have hne : -((1 : ℂ) + z) ≠ 0 := by
      intro h
      have : (1 : ℂ) + z = 0 := by linear_combination -h
      have hre := congrArg Complex.re this
      simp at hre
      linarith
    rw [Nat.cast_zero, Complex.zero_cpow hne, zero_div]
  · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hint : IntegrableOn
        (fun v : ℝ => (powerSumWeight omega m : ℂ) *
          Complex.exp (-(((1 : ℂ) + (omega : ℂ) + z) * (v : ℂ)))) (Ioi (Real.log m)) volume :=
      (GaloisForLFunctions.RHTower.integrableOn_Ioi_cexp_neg_mul_shift hb hlog).const_mul _
    simp only [powerSumAtom]
    rw [setIntegral_Ioi_indicator_Ici hlog _ hint, integral_const_mul,
      GaloisForLFunctions.RHTower.integral_Ioi_cexp_neg_mul_shift hb]
    have hcpow : Complex.exp (-(((1 : ℂ) + (omega : ℂ) + z) * ((Real.log m : ℝ) : ℂ)))
        = (m : ℂ) ^ (-((1 : ℂ) + (omega : ℂ) + z)) := by
      rw [Complex.cpow_def_of_ne_zero hmne]
      congr 1
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (le_of_lt hmpos)]
      push_cast
      ring
    have hweight : ((powerSumWeight omega m : ℝ) : ℂ) = (m : ℂ) ^ ((omega : ℂ)) := by
      rw [powerSumWeight_of_pos hm, ← Complex.ofReal_natCast,
        Complex.ofReal_cpow (le_of_lt hmpos)]
    rw [hcpow, hweight, ← mul_div_assoc, ← Complex.cpow_add _ _ hmne]
    congr 2
    ring


/-! ### The pointwise atomic decomposition and the transform -/

/-- **Pointwise decomposition.**  On the causal ray the Laplace integrand of the power-sum boundary
vector is the sum of its divisor atoms. -/
theorem tsum_powerSumAtom (omega : ℝ) (z : ℂ) (t : ℝ) :
    (∑' m : ℕ, powerSumAtom omega z m t)
      = (powerSumBoundary omega t : ℂ) * Complex.exp (-(z * (t : ℂ))) := by
  have hexp : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hsupport : ∀ m : ℕ, m ∉ Finset.Icc 1 ⌊Real.exp t⌋₊ → powerSumAtom omega z m t = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0; exact powerSumAtom_zero omega z t
    · have hgt : ⌊Real.exp t⌋₊ < m := by
        rw [Finset.mem_Icc] at hm
        push Not at hm
        exact hm hm0
      have hlt : Real.exp t < (m : ℝ) := (Nat.floor_lt hexp.le).mp hgt
      have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
      have hlog : t < Real.log m := (Real.lt_log_iff_exp_lt hmpos).mpr hlt
      exact Set.indicator_of_notMem (by simpa using hlog.not_ge) _
  rw [tsum_eq_sum hsupport]
  have hval : ∀ m ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
      powerSumAtom omega z m t =
        (((m : ℝ) ^ omega : ℝ) : ℂ) *
          Complex.exp (-(((1 : ℂ) + (omega : ℂ) + z) * (t : ℂ))) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmpos : 0 < m := hm.1
    have hmle : (m : ℝ) ≤ Real.exp t := le_trans (by exact_mod_cast hm.2) (Nat.floor_le hexp.le)
    have hlog : Real.log m ≤ t := (Real.log_le_iff_le_exp (by exact_mod_cast hmpos)).mpr hmle
    rw [powerSumAtom, Set.indicator_of_mem (by simpa using hlog), powerSumWeight_of_pos hmpos]
  rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
  rw [powerSumBoundary, Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  have hAB : Complex.exp (-(1 + (omega : ℂ)) * (t : ℂ)) * Complex.exp (-(z * (t : ℂ)))
      = Complex.exp (-(((1 : ℂ) + (omega : ℂ) + z) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  linear_combination
    (-(∑ i ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (((i : ℝ) ^ omega : ℝ) : ℂ))) * hAB

/-- **Card `(17)`.**  The causal Laplace transform of the shifted power-sum boundary vector. -/
theorem causalLaplace_powerSumBoundary
    {omega : ℝ} {z : ℂ} (homega : 0 ≤ omega) (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), (powerSumBoundary omega t : ℂ) * Complex.exp (-(z * (t : ℂ))))
      = riemannZeta (1 + z) / (1 + (omega : ℂ) + z) := by
  have hbne : (1 : ℂ) + (omega : ℂ) + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [re_shift] at hre
    simp at hre
    linarith
  have hzre : 1 < ((1 : ℂ) + z).re := by simp; linarith
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun m : ℕ => powerSumAtom omega z m)
    (fun m => integrableOn_powerSumAtom homega hz m)
    (summable_integral_norm_powerSumAtom homega hz)
  have hpt : (∫ t in Ioi (0 : ℝ), ∑' m : ℕ, powerSumAtom omega z m t)
      = ∫ t in Ioi (0 : ℝ), (powerSumBoundary omega t : ℂ) * Complex.exp (-(z * (t : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact tsum_powerSumAtom omega z t
  rw [← hpt, ← hswap]
  rw [show (∑' m : ℕ, ∫ t in Ioi (0 : ℝ), powerSumAtom omega z m t)
      = ∑' m : ℕ, (m : ℂ) ^ (-(1 + z)) / (1 + (omega : ℂ) + z) from
    tsum_congr (integral_powerSumAtom homega hz)]
  rw [tsum_div_const]
  congr 1
  rw [zeta_eq_tsum_one_div_nat_cpow hzre]
  refine tsum_congr fun n => ?_
  rw [Complex.cpow_neg, one_div]

end RHTower
