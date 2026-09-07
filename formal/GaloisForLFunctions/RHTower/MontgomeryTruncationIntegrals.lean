import GaloisForLFunctions.RHTower.MontgomeryZeroSumWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Elementary integrals for the truncation of Montgomery's pair form

Real-variable estimates used to compare `∫_0^T |S(x,t)|² dt` with `∫_ℝ |S_T(x,t)|² dt`:

* on `[0, T]`, `∫ (1/(1+(T−t)) + 1/(1+t)) dt = 2 log(1+T)`;
* on `(a, ∞)` (and mirrored on `(−∞, a]`), a non-negative function bounded by
  `K ((A + log(1+|t−a|))/(1+|t−a|))²` is integrable with integral at most `K (2A² + 64)`, via
  `log u ≤ 4 u^{1/4}` and the integrals of `u^{−2}` and `u^{−3/2}`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

/-! ## The window integral -/

theorem integral_Icc_inv_one_add (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in Icc 0 T, 1 / (1 + t) = Real.log (1 + T) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have h := intervalIntegral.integral_comp_add_right (fun x : ℝ => 1 / x) (a := 0) (b := T) 1
  simp only [zero_add] at h
  rw [show (fun t : ℝ => 1 / (1 + t)) = fun t => 1 / (t + 1) from funext fun t => by ring, h,
    integral_one_div (by rw [Set.uIcc_of_le (by linarith)]; intro h0; simp at h0; linarith)]
  congr 1; ring

theorem integral_Icc_inv_one_add_sub (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in Icc 0 T, 1 / (1 + (T - t)) = Real.log (1 + T) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ => 1 / (1 + u)) (a := 0) (b := T) T
  simp only [sub_self, sub_zero] at h
  rw [h, intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  exact integral_Icc_inv_one_add T hT

theorem integrableOn_windowWeight (T : ℝ) :
    IntegrableOn (fun t : ℝ => 1 / (1 + (T - t)) + 1 / (1 + t)) (Icc 0 T) := by
  refine ContinuousOn.integrableOn_Icc ?_
  apply ContinuousOn.add
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.2]
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.1]

/-- `∫_0^T (1/(1+(T−t)) + 1/(1+t)) dt = 2 log(1+T)`. -/
theorem integral_Icc_windowWeight (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in Icc 0 T, (1 / (1 + (T - t)) + 1 / (1 + t)) = 2 * Real.log (1 + T) := by
  have h1 : IntegrableOn (fun t : ℝ => 1 / (1 + (T - t))) (Icc 0 T) := by
    refine ContinuousOn.integrableOn_Icc ?_
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.2]
  have h2 : IntegrableOn (fun t : ℝ => 1 / (1 + t)) (Icc 0 T) := by
    refine ContinuousOn.integrableOn_Icc ?_
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht; linarith [ht.1]
  rw [integral_add h1 h2, integral_Icc_inv_one_add T hT, integral_Icc_inv_one_add_sub T hT]
  ring

theorem windowWeight_le_two {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    1 / (1 + (T - t)) + 1 / (1 + t) ≤ 2 := by
  have h1 : 1 / (1 + (T - t)) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h2 : 1 / (1 + t) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

theorem montgomeryWindowWeight_nonneg {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    0 ≤ 1 / (1 + (T - t)) + 1 / (1 + t) := by
  have : 0 < 1 + (T - t) := by linarith
  positivity

/-! ## Power integrals on half-lines -/

theorem hasDerivAt_shift_rpow (a p : ℝ) {t : ℝ} (ht : a ≤ t) :
    HasDerivAt (fun s : ℝ => (1 + (s - a)) ^ p) (p * (1 + (t - a)) ^ (p - 1)) t := by
  have h : HasDerivAt (fun s : ℝ => 1 + (s - a)) 1 t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_add 1
  have := h.rpow_const (p := p) (Or.inl (by linarith))
  simpa using this

theorem hasDerivAt_mirror_rpow (a p : ℝ) {t : ℝ} (ht : t ≤ a) :
    HasDerivAt (fun s : ℝ => (1 + (a - s)) ^ p) (-(p * (1 + (a - t)) ^ (p - 1))) t := by
  have h : HasDerivAt (fun s : ℝ => 1 + (a - s)) (-1) t := by
    simpa using ((hasDerivAt_id t).const_sub a).const_add 1
  have := h.rpow_const (p := p) (Or.inl (by linarith))
  convert this using 1; ring

theorem tendsto_shift_rpow_neg (a : ℝ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun s : ℝ => (1 + (s - a)) ^ (-p)) atTop (nhds 0) := by
  have h1 : Tendsto (fun s : ℝ => s + (1 - a)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have h2 := (tendsto_rpow_neg_atTop hp).comp h1
  refine h2.congr fun s => ?_
  simp only [Function.comp]; ring_nf

theorem tendsto_mirror_rpow_neg (a : ℝ) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun s : ℝ => (1 + (a - s)) ^ (-p)) atBot (nhds 0) := by
  have h1 : Tendsto (fun s : ℝ => (1 + a) + (-s)) atBot atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_neg_atBot_atTop
  have h2 := (tendsto_rpow_neg_atTop hp).comp h1
  refine h2.congr fun s => ?_
  simp only [Function.comp]; ring_nf

/-- `∫_a^∞ (1+(t−a))^{−p} dt = 1/(p−1)` for `p > 1`, with integrability. -/
theorem integral_Ioi_shift_rpow (a : ℝ) {p : ℝ} (hp : 1 < p) :
    IntegrableOn (fun t : ℝ => (1 + (t - a)) ^ (-p)) (Ioi a) ∧
      ∫ t in Ioi a, (1 + (t - a)) ^ (-p) = 1 / (p - 1) := by
  set g : ℝ → ℝ := fun s => -(1 / (p - 1)) * (1 + (s - a)) ^ (-(p - 1)) with hg
  have hp0 : p - 1 ≠ 0 := by linarith
  have hderiv : ∀ t ∈ Ioi a, HasDerivAt g ((1 + (t - a)) ^ (-p)) t := by
    intro t ht
    have := (hasDerivAt_shift_rpow a (-(p - 1)) (le_of_lt ht)).const_mul (-(1 / (p - 1)))
    have key : -(1 / (p - 1)) * (-(p - 1) * (1 + (t - a)) ^ (-(p - 1) - 1))
        = (1 + (t - a)) ^ (-p) := by
      rw [show -(p - 1) - 1 = -p by ring]
      field_simp
    rw [hg]
    exact this.congr_deriv key
  have hcont : ContinuousWithinAt g (Ici a) a := by
    have := (hasDerivAt_shift_rpow a (-(p - 1)) (le_refl a)).const_mul (-(1 / (p - 1)))
    exact this.continuousAt.continuousWithinAt
  have hnonneg : ∀ t ∈ Ioi a, 0 ≤ (1 + (t - a)) ^ (-p) := fun t ht =>
    Real.rpow_nonneg (by simp only [mem_Ioi] at ht; linarith) _
  have htend : Tendsto g atTop (nhds 0) := by
    have := (tendsto_shift_rpow_neg a (p := p - 1) (by linarith)).const_mul (-(1 / (p - 1)))
    simpa [hg] using this
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hderiv hnonneg htend, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg htend]
  simp [hg]

/-- `∫_{−∞}^a (1+(a−t))^{−p} dt = 1/(p−1)` for `p > 1`, with integrability. -/
theorem integral_Iic_mirror_rpow (a : ℝ) {p : ℝ} (hp : 1 < p) :
    IntegrableOn (fun t : ℝ => (1 + (a - t)) ^ (-p)) (Iic a) ∧
      ∫ t in Iic a, (1 + (a - t)) ^ (-p) = 1 / (p - 1) := by
  set g : ℝ → ℝ := fun s => (1 / (p - 1)) * (1 + (a - s)) ^ (-(p - 1)) with hg
  have hp0 : p - 1 ≠ 0 := by linarith
  have hderiv : ∀ t ∈ Iio a, HasDerivAt g ((1 + (a - t)) ^ (-p)) t := by
    intro t ht
    have := (hasDerivAt_mirror_rpow a (-(p - 1)) (le_of_lt ht)).const_mul (1 / (p - 1))
    have key : 1 / (p - 1) * -(-(p - 1) * (1 + (a - t)) ^ (-(p - 1) - 1))
        = (1 + (a - t)) ^ (-p) := by
      rw [show -(p - 1) - 1 = -p by ring]
      field_simp
    rw [hg]
    exact this.congr_deriv key
  have hcont : ContinuousWithinAt g (Iic a) a := by
    have := (hasDerivAt_mirror_rpow a (-(p - 1)) (le_refl a)).const_mul (1 / (p - 1))
    exact this.continuousAt.continuousWithinAt
  have htend : Tendsto g atBot (nhds 0) := by
    have := (tendsto_mirror_rpow_neg a (p := p - 1) (by linarith)).const_mul (1 / (p - 1))
    simpa [hg] using this
  have hint : IntegrableOn (fun t : ℝ => (1 + (a - t)) ^ (-p)) (Iic a) := by
    have h := (integral_Ioi_shift_rpow (-a) hp).1.comp_neg
    rw [Set.neg_Ioi, neg_neg] at h
    refine (h.congr_fun (fun t _ => ?_) measurableSet_Iio).congr_set_ae Iio_ae_eq_Iic.symm
    ring_nf
  refine ⟨hint, ?_⟩
  rw [integral_Iic_of_hasDerivAt_of_tendsto hcont hderiv hint htend]
  simp [hg]

/-! ## The logarithmic majorant -/

theorem rpow_neg_two_eq {u : ℝ} (hu : 0 < u) : u ^ (-2 : ℝ) = 1 / u ^ 2 := by
  rw [Real.rpow_neg hu.le, Real.rpow_two, one_div]

theorem rpow_neg_three_halves_eq {u : ℝ} (hu : 0 < u) :
    u ^ (-(3 / 2) : ℝ) = u ^ ((1 / 2 : ℝ)) / u ^ 2 := by
  rw [← Real.rpow_two, ← Real.rpow_sub hu]; norm_num

/-- `((A + log u)/u)² ≤ 2A² u^{−2} + 32 u^{−3/2}` for `u ≥ 1`, `A ≥ 0`. -/
theorem log_ratio_sq_le {A u : ℝ} (hu : 1 ≤ u) :
    ((A + Real.log u) / u) ^ 2 ≤ 2 * A ^ 2 * u ^ (-2 : ℝ) + 32 * u ^ (-(3 / 2) : ℝ) := by
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have hlog : Real.log u ≤ 4 * u ^ ((1 / 4 : ℝ)) := by
    have := Real.log_le_rpow_div hu0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [div_eq_mul_inv, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at this
    linarith
  have hsq : (Real.log u) ^ 2 ≤ 16 * u ^ ((1 / 2 : ℝ)) := by
    have h4 : (u ^ ((1 / 4 : ℝ))) ^ 2 = u ^ ((1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    have hq : 0 ≤ u ^ ((1 / 4 : ℝ)) := Real.rpow_nonneg hu0.le _
    calc (Real.log u) ^ 2 ≤ (4 * u ^ ((1 / 4 : ℝ))) ^ 2 := by gcongr
      _ = 16 * u ^ ((1 / 2 : ℝ)) := by rw [mul_pow, h4]; norm_num
  have hsum : (A + Real.log u) ^ 2 ≤ 2 * A ^ 2 + 32 * u ^ ((1 / 2 : ℝ)) := by
    nlinarith [sq_nonneg (A - Real.log u)]
  rw [div_pow, rpow_neg_two_eq hu0, rpow_neg_three_halves_eq hu0]
  have hu2 : 0 < u ^ 2 := by positivity
  rw [div_le_iff₀ hu2]
  calc (A + Real.log u) ^ 2 ≤ 2 * A ^ 2 + 32 * u ^ ((1 / 2 : ℝ)) := hsum
    _ = (2 * A ^ 2 * (1 / u ^ 2) + 32 * (u ^ ((1 / 2 : ℝ)) / u ^ 2)) * u ^ 2 := by
        field_simp

/-- A non-negative function on `(a, ∞)` bounded by `K ((A + log(1+(t−a)))/(1+(t−a)))²` is
integrable with integral at most `K (2A² + 64)`. -/
theorem integral_Ioi_le_of_log_bound {φ : ℝ → ℝ} {a A K : ℝ} (hK : 0 ≤ K)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Ioi a)))
    (h0 : ∀ t ∈ Ioi a, 0 ≤ φ t)
    (hb : ∀ t ∈ Ioi a, φ t ≤ K * ((A + Real.log (1 + (t - a))) / (1 + (t - a))) ^ 2) :
    IntegrableOn φ (Ioi a) ∧ ∫ t in Ioi a, φ t ≤ K * (2 * A ^ 2 + 64) := by
  obtain ⟨hi2, hv2⟩ := integral_Ioi_shift_rpow a (p := 2) (by norm_num)
  obtain ⟨hi3, hv3⟩ := integral_Ioi_shift_rpow a (p := 3 / 2) (by norm_num)
  set m : ℝ → ℝ := fun t => K * (2 * A ^ 2 * (1 + (t - a)) ^ (-2 : ℝ)
    + 32 * (1 + (t - a)) ^ (-(3 / 2) : ℝ)) with hm
  have hmint : IntegrableOn m (Ioi a) := by
    have h1 : IntegrableOn (fun t : ℝ => 2 * A ^ 2 * (1 + (t - a)) ^ (-2 : ℝ)) (Ioi a) :=
      hi2.const_mul _
    have h2 : IntegrableOn (fun t : ℝ => 32 * (1 + (t - a)) ^ (-(3 / 2) : ℝ)) (Ioi a) :=
      hi3.const_mul _
    have h3 : IntegrableOn (fun t : ℝ => 2 * A ^ 2 * (1 + (t - a)) ^ (-2 : ℝ)
        + 32 * (1 + (t - a)) ^ (-(3 / 2) : ℝ)) (Ioi a) := h1.add h2
    exact h3.const_mul K
  have hle : ∀ t ∈ Ioi a, φ t ≤ m t := by
    intro t ht
    refine (hb t ht).trans ?_
    have hu : 1 ≤ 1 + (t - a) := by simp only [mem_Ioi] at ht; linarith
    have := log_ratio_sq_le (A := A) hu
    simp only [hm]
    exact mul_le_mul_of_nonneg_left this hK
  have hφint : IntegrableOn φ (Ioi a) := by
    refine Integrable.mono' hmint.integrable hφ ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 t ht)]
    exact hle t ht
  refine ⟨hφint, ?_⟩
  calc ∫ t in Ioi a, φ t ≤ ∫ t in Ioi a, m t :=
        setIntegral_mono_on hφint hmint measurableSet_Ioi hle
    _ = K * (2 * A ^ 2 + 64) := by
        simp only [hm]
        rw [integral_const_mul, integral_add (hi2.const_mul _) (hi3.const_mul _),
          integral_const_mul, integral_const_mul, hv2, hv3]
        norm_num

/-- The mirrored statement on `(−∞, a]`. -/
theorem integral_Iic_le_of_log_bound {φ : ℝ → ℝ} {a A K : ℝ} (hK : 0 ≤ K)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Iic a)))
    (h0 : ∀ t ∈ Iic a, 0 ≤ φ t)
    (hb : ∀ t ∈ Iic a, φ t ≤ K * ((A + Real.log (1 + (a - t))) / (1 + (a - t))) ^ 2) :
    IntegrableOn φ (Iic a) ∧ ∫ t in Iic a, φ t ≤ K * (2 * A ^ 2 + 64) := by
  obtain ⟨hi2, hv2⟩ := integral_Iic_mirror_rpow a (p := 2) (by norm_num)
  obtain ⟨hi3, hv3⟩ := integral_Iic_mirror_rpow a (p := 3 / 2) (by norm_num)
  set m : ℝ → ℝ := fun t => K * (2 * A ^ 2 * (1 + (a - t)) ^ (-2 : ℝ)
    + 32 * (1 + (a - t)) ^ (-(3 / 2) : ℝ)) with hm
  have hmint : IntegrableOn m (Iic a) := by
    have h1 : IntegrableOn (fun t : ℝ => 2 * A ^ 2 * (1 + (a - t)) ^ (-2 : ℝ)) (Iic a) :=
      hi2.const_mul _
    have h2 : IntegrableOn (fun t : ℝ => 32 * (1 + (a - t)) ^ (-(3 / 2) : ℝ)) (Iic a) :=
      hi3.const_mul _
    have h3 : IntegrableOn (fun t : ℝ => 2 * A ^ 2 * (1 + (a - t)) ^ (-2 : ℝ)
        + 32 * (1 + (a - t)) ^ (-(3 / 2) : ℝ)) (Iic a) := h1.add h2
    exact h3.const_mul K
  have hle : ∀ t ∈ Iic a, φ t ≤ m t := by
    intro t ht
    refine (hb t ht).trans ?_
    have hu : 1 ≤ 1 + (a - t) := by simp only [mem_Iic] at ht; linarith
    have := log_ratio_sq_le (A := A) hu
    simp only [hm]
    exact mul_le_mul_of_nonneg_left this hK
  have hφint : IntegrableOn φ (Iic a) := by
    refine Integrable.mono' hmint.integrable hφ ?_
    refine ae_restrict_of_forall_mem measurableSet_Iic fun t ht => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 t ht)]
    exact hle t ht
  refine ⟨hφint, ?_⟩
  calc ∫ t in Iic a, φ t ≤ ∫ t in Iic a, m t :=
        setIntegral_mono_on hφint hmint measurableSet_Iic hle
    _ = K * (2 * A ^ 2 + 64) := by
        simp only [hm]
        rw [integral_const_mul, integral_add (hi2.const_mul _) (hi3.const_mul _),
          integral_const_mul, integral_const_mul, hv2, hv3]
        norm_num

end RHTower
