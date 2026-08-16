import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel

/-!
# Euler's integral for a contact of order `m`

The regularized capacity of a source with a ground contact of order `m` is, after the natural
rescaling, the reciprocal of `c s^{2m} + r`.  Its total mass is Euler's integral

`∫_ℝ ds/(c s^{2m} + r) = (π/m) csc(π/2m) · c^{-1/(2m)} r^{1/(2m)-1}`,

obtained from the Mellin kernel of `1/(1+y)` by the substitution `y = (c/r)s^{2m}`.  The kernel
itself is the Beta integral at complementary arguments, which the gamma reflection formula
evaluates as `π/sin(πa)`.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The real Mellin kernel of `1/(1+y)`.** -/
theorem integral_Ioi_rpow_div_one_add {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    (∫ y in Ioi (0 : ℝ), y ^ (a - 1) / (1 + y)) = Real.pi / Real.sin (Real.pi * a) := by
  have hw : (0 : ℝ) < ((a : ℂ)).re := by simpa using ha
  have hc : ((a : ℂ)).re < ((1 : ℂ)).re := by simpa using ha1
  have hcomplex := integral_halfLine_beta hw hc
  have hgamma : Complex.Gamma (a : ℂ) * Complex.Gamma (1 - (a : ℂ)) / Complex.Gamma 1
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (a : ℂ)) := by
    rw [Complex.Gamma_one, div_one]
    exact Complex.Gamma_mul_Gamma_one_sub (a : ℂ)
  rw [hgamma] at hcomplex
  have hintegrand : ∀ y ∈ Ioi (0 : ℝ),
      ((y : ℂ) ^ ((a : ℂ) - 1) * (1 + (y : ℂ)) ^ (-(1 : ℂ)))
        = ((y ^ (a - 1) / (1 + y) : ℝ) : ℂ) := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
    have hpow : ((y ^ (a - 1) : ℝ) : ℂ) = (y : ℂ) ^ ((a - 1 : ℝ) : ℂ) :=
      Complex.ofReal_cpow hy0 (a - 1)
    have hcast : ((a - 1 : ℝ) : ℂ) = (a : ℂ) - 1 := by push_cast; ring
    have hden : (1 + (y : ℂ)) ^ (-(1 : ℂ)) = (((1 + y : ℝ) : ℂ))⁻¹ := by
      rw [Complex.cpow_neg_one]
      push_cast
      ring
    rw [hden, Complex.ofReal_div, hpow, hcast, div_eq_mul_inv]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hintegrand,
    integral_complex_ofReal] at hcomplex
  have hsin : Complex.sin ((Real.pi : ℂ) * (a : ℂ)) = ((Real.sin (Real.pi * a) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sin]
  rw [hsin, ← Complex.ofReal_div] at hcomplex
  exact_mod_cast hcomplex

/-- The half-line integral of the shifted power reciprocal. -/
theorem integral_Ioi_rpow_div_linear {a c r : ℝ} (ha : 0 < a) (ha1 : a < 1) (hc : 0 < c)
    (hr : 0 < r) :
    (∫ y in Ioi (0 : ℝ), y ^ (a - 1) / (c * y + r))
      = c ^ (-a) * r ^ (a - 1) * (Real.pi / Real.sin (Real.pi * a)) := by
  have hb : (0 : ℝ) < r / c := div_pos hr hc
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => y ^ (a - 1) / (c * y + r)) 0 hb
  rw [mul_zero] at hscale
  have hval : ∀ u : ℝ, 0 < u →
      (r / c * u) ^ (a - 1) / (c * (r / c * u) + r)
        = (r / c) ^ (a - 1) * r⁻¹ * (u ^ (a - 1) / (1 + u)) := by
    intro u hu
    have hmul : (r / c * u) ^ (a - 1) = (r / c) ^ (a - 1) * u ^ (a - 1) :=
      Real.mul_rpow (le_of_lt hb) (le_of_lt hu)
    have hden : c * (r / c * u) + r = r * (1 + u) := by
      field_simp
      ring
    rw [hmul, hden]
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun u hu => hval u hu)] at hscale
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_div_one_add ha ha1] at hscale
  have hcinv : (r / c : ℝ)⁻¹ • (∫ y in Ioi (0 : ℝ), y ^ (a - 1) / (c * y + r))
      = (r / c)⁻¹ * ∫ y in Ioi (0 : ℝ), y ^ (a - 1) / (c * y + r) := rfl
  rw [hcinv] at hscale
  have hne : (r / c : ℝ) ≠ 0 := ne_of_gt hb
  have hsolve : (∫ y in Ioi (0 : ℝ), y ^ (a - 1) / (c * y + r))
      = (r / c) * ((r / c) ^ (a - 1) * r⁻¹ * (Real.pi / Real.sin (Real.pi * a))) := by
    field_simp at hscale ⊢
    linarith [hscale]
  rw [hsolve]
  have hsplit : (r / c : ℝ) * (r / c) ^ (a - 1) = (r / c) ^ a := by
    nth_rewrite 1 [← Real.rpow_one (r / c)]
    rw [← Real.rpow_add hb]
    ring_nf
  have hdiv : (r / c : ℝ) ^ a = r ^ a * c ^ (-a) := by
    rw [Real.div_rpow (le_of_lt hr) (le_of_lt hc), Real.rpow_neg (le_of_lt hc)]
    ring
  have hr1 : r ^ a * r⁻¹ = r ^ (a - 1) := by
    rw [Real.rpow_sub hr, Real.rpow_one]
    ring
  calc (r / c : ℝ) * ((r / c) ^ (a - 1) * r⁻¹ * (Real.pi / Real.sin (Real.pi * a)))
      = ((r / c) * (r / c) ^ (a - 1)) * r⁻¹ * (Real.pi / Real.sin (Real.pi * a)) := by ring
    _ = (r ^ a * c ^ (-a)) * r⁻¹ * (Real.pi / Real.sin (Real.pi * a)) := by rw [hsplit, hdiv]
    _ = c ^ (-a) * (r ^ a * r⁻¹) * (Real.pi / Real.sin (Real.pi * a)) := by ring
    _ = c ^ (-a) * r ^ (a - 1) * (Real.pi / Real.sin (Real.pi * a)) := by rw [hr1]

/-- **(HCD.17) half-line form.**  The mass of the rescaled contact profile on the positive axis. -/
theorem integral_Ioi_inv_contact {p c r : ℝ} (hp : 1 < p) (hc : 0 < c) (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), (c * t ^ p + r)⁻¹)
      = p⁻¹ * (c ^ (-p⁻¹) * r ^ (p⁻¹ - 1) * (Real.pi / Real.sin (Real.pi * p⁻¹))) := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have ha : (0 : ℝ) < p⁻¹ := inv_pos.2 hp0
  have ha1 : p⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right
    exact hp
  have hsub := MeasureTheory.integral_comp_rpow_Ioi
    (fun y : ℝ => p⁻¹ * (y ^ (p⁻¹ - 1) / (c * y + r))) hpne
  have hval : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      (|p| * x ^ (p - 1)) • (p⁻¹ * ((x ^ p) ^ (p⁻¹ - 1) / (c * x ^ p + r)))
        = (c * x ^ p + r)⁻¹ := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have habs : |p| = p := abs_of_pos hp0
    have hpow : (x ^ p) ^ (p⁻¹ - 1) = x ^ (1 - p) := by
      rw [← Real.rpow_mul (le_of_lt hx0)]
      congr 1
      field_simp
    rw [habs, hpow, smul_eq_mul]
    have hcomb : x ^ (p - 1) * x ^ (1 - p) = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    calc p * x ^ (p - 1) * (p⁻¹ * (x ^ (1 - p) / (c * x ^ p + r)))
        = (p * p⁻¹) * (x ^ (p - 1) * x ^ (1 - p)) * (c * x ^ p + r)⁻¹ := by
          rw [div_eq_mul_inv]; ring
      _ = (c * x ^ p + r)⁻¹ := by rw [mul_inv_cancel₀ hpne, hcomb]; ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hval] at hsub
  rw [hsub, MeasureTheory.integral_const_mul, integral_Ioi_rpow_div_linear ha ha1 hc hr]

/-! ## Integrability and the two-sided mass -/

theorem measurable_contactDenominator (c r p : ℝ) :
    Measurable fun t : ℝ => (c * |t| ^ p + r)⁻¹ := by
  have habs : Measurable fun t : ℝ => |t| := continuous_abs.measurable
  exact (((habs.pow_const p).const_mul c).add_const r).inv

theorem contactDenominator_pos {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (p t : ℝ) :
    0 < c * |t| ^ p + r := by
  have h : 0 ≤ c * |t| ^ p := mul_nonneg hc.le (Real.rpow_nonneg (abs_nonneg t) p)
  linarith

theorem integrableOn_contactProfile_Ioi {c r p : ℝ} (hp : 1 < p) (hc : 0 < c) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (c * |t| ^ p + r)⁻¹) (Ioi 0) := by
  have hmeasNear : AEStronglyMeasurable (fun t : ℝ => (c * |t| ^ p + r)⁻¹)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_contactDenominator c r p).aestronglyMeasurable
  have hmeasFar : AEStronglyMeasurable (fun t : ℝ => (c * |t| ^ p + r)⁻¹)
      (volume.restrict (Ioi (1 : ℝ))) :=
    (measurable_contactDenominator c r p).aestronglyMeasurable
  have hnear : IntegrableOn (fun t : ℝ => (c * |t| ^ p + r)⁻¹) (Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => r⁻¹) (Ioc (0 : ℝ) 1) volume :=
      integrableOn_const (by simp [Real.volume_Ioc]) (by simp)
    refine Integrable.mono' hconst hmeasNear ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (contactDenominator_pos hc hr p t))]
    refine inv_anti₀ hr ?_
    have h : 0 ≤ c * |t| ^ p := mul_nonneg hc.le (Real.rpow_nonneg (abs_nonneg t) p)
    linarith
  have hfar : IntegrableOn (fun t : ℝ => (c * |t| ^ p + r)⁻¹) (Ioi 1) := by
    have hdom : IntegrableOn (fun t : ℝ => c⁻¹ * t ^ (-p)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul c⁻¹
    refine Integrable.mono' hdom hmeasFar ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht1
    have habs : |t| = t := abs_of_pos ht0
    have hpow : (0 : ℝ) < t ^ p := Real.rpow_pos_of_pos ht0 p
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (contactDenominator_pos hc hr p t)), habs]
    have hstep : c⁻¹ * t ^ (-p) = (c * t ^ p)⁻¹ := by
      rw [mul_inv, Real.rpow_neg ht0.le]
    rw [hstep]
    refine inv_anti₀ (mul_pos hc hpow) ?_
    linarith
  have hunion : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hcomb := hnear.union hfar
  rwa [hunion] at hcomb

theorem integrable_contactProfile {c r p : ℝ} (hp : 1 < p) (hc : 0 < c) (hr : 0 < r) :
    Integrable fun t : ℝ => (c * |t| ^ p + r)⁻¹ := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
  have hiff := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (measurableEmbedding_neg (α := ℝ))
    (f := fun t : ℝ => (c * |t| ^ p + r)⁻¹) (s := Ioi 0)
  have hcomp : IntegrableOn ((fun t : ℝ => (c * |t| ^ p + r)⁻¹) ∘ (fun x : ℝ => -x))
      ((fun x : ℝ => -x) ⁻¹' Ioi 0) := hiff.2 (integrableOn_contactProfile_Ioi hp hc hr)
  rw [hpre] at hcomp
  have hneg : IntegrableOn (fun t : ℝ => (c * |t| ^ p + r)⁻¹) (Iio 0) := by
    refine hcomp.congr_fun (fun t _ => ?_) measurableSet_Iio
    simp only [Function.comp_apply, abs_neg]
  have hzero : IntegrableOn (fun t : ℝ => (c * |t| ^ p + r)⁻¹) {(0 : ℝ)} := by
    simp [IntegrableOn]
  have hall : Iio (0 : ℝ) ∪ ({(0 : ℝ)} ∪ Ioi 0) = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_univ,
      iff_true]
    rcases lt_trichotomy t 0 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hcomb := hneg.union (hzero.union (integrableOn_contactProfile_Ioi hp hc hr))
  rw [hall] at hcomb
  rwa [IntegrableOn, Measure.restrict_univ] at hcomb

theorem integral_even_eq_two_mul {f : ℝ → ℝ} (hf : Integrable f) (he : ∀ x, f (-x) = f x) :
    (∫ x, f x) = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi 0 = Iio 0 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio, neg_pos]
  have hrefl := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_neg (α := ℝ)) f (Ioi 0)
  rw [hpre] at hrefl
  have hle : (∫ x in Iio (0 : ℝ), f x) = ∫ y in Ioi (0 : ℝ), f y := by
    rw [← hrefl]
    exact setIntegral_congr_fun measurableSet_Iio fun x _ => (he x).symm
  have hadd := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hf
  rw [compl_Iic, integral_Iic_eq_integral_Iio, hle] at hadd
  linarith

/-- **(HCD.17) The total mass of the rescaled contact profile.** -/
theorem integral_contactProfile {c r p : ℝ} (hp : 1 < p) (hc : 0 < c) (hr : 0 < r) :
    (∫ t : ℝ, (c * |t| ^ p + r)⁻¹)
      = 2 * p⁻¹ * (c ^ (-p⁻¹) * r ^ (p⁻¹ - 1) * (Real.pi / Real.sin (Real.pi * p⁻¹))) := by
  have heven : ∀ x : ℝ, (c * |(-x)| ^ p + r)⁻¹ = (c * |x| ^ p + r)⁻¹ := by
    intro x
    rw [abs_neg]
  rw [integral_even_eq_two_mul (integrable_contactProfile hp hc hr) heven]
  have hIoi : (∫ t in Ioi (0 : ℝ), (c * |t| ^ p + r)⁻¹)
      = ∫ t in Ioi (0 : ℝ), (c * t ^ p + r)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [abs_of_pos ht]
  rw [hIoi, integral_Ioi_inv_contact hp hc hr]
  ring

/-- **(HCD.7)/(HCD.17) The contact-order constant.**  For a contact of order `m` the rescaled
profile has total mass `K_m c^{-1/(2m)} r^{1/(2m)-1}` with `K_m = (π/m) csc(π/(2m))`. -/
theorem integral_contactProfile_order {m : ℕ} (hm : 1 ≤ m) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    (∫ t : ℝ, (c * t ^ (2 * m) + r)⁻¹)
      = Real.pi / (m : ℝ) / Real.sin (Real.pi / (2 * (m : ℝ)))
        * (c ^ (-(2 * (m : ℝ))⁻¹) * r ^ ((2 * (m : ℝ))⁻¹ - 1)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : (1 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have hpinv : (((2 * m : ℕ) : ℝ))⁻¹ = (2 * (m : ℝ))⁻¹ := by push_cast; ring
  have hpow : ∀ t : ℝ, |t| ^ (((2 * m : ℕ)) : ℝ) = t ^ (2 * m) := by
    intro t
    rw [Real.rpow_natCast]
    exact (Even.pow_abs ⟨m, by ring⟩ t)
  have hmain := integral_contactProfile (c := c) (r := r) (p := ((2 * m : ℕ) : ℝ)) hp hc hr
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => by
    rw [hpow t])] at hmain
  rw [hmain, hpinv]
  have hpi : Real.pi * (2 * (m : ℝ))⁻¹ = Real.pi / (2 * (m : ℝ)) := by
    rw [div_eq_mul_inv]
  rw [hpi]
  have hmne : (m : ℝ) ≠ 0 := by linarith
  field_simp

/-- The contact profile in natural-power form is integrable. -/
theorem integrable_contactProfile_order {m : ℕ} (hm : 1 ≤ m) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    Integrable fun t : ℝ => (c * t ^ (2 * m) + r)⁻¹ := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : (1 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have hpow : ∀ t : ℝ, |t| ^ (((2 * m : ℕ)) : ℝ) = t ^ (2 * m) := by
    intro t
    rw [Real.rpow_natCast]
    exact Even.pow_abs ⟨m, by ring⟩ t
  have hmain := integrable_contactProfile (c := c) (r := r) (p := ((2 * m : ℕ) : ℝ)) hp hc hr
  refine hmain.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [hpow t]

/-- The contact profile is positive. -/
theorem contactProfile_order_pos {m : ℕ} {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (t : ℝ) :
    0 < c * t ^ (2 * m) + r := by
  have hpow : (0 : ℝ) ≤ t ^ (2 * m) := Even.pow_nonneg ⟨m, by ring⟩ t
  nlinarith

end GaloisForLFunctions.HTGeometry

end
