import GaloisForLFunctions.HTGeometry.DirichletWirtinger

/-!
# Stable Wirtinger inequality on an interval

For `f` of class `C¹` on `[a, b]`, `L = b - a` and `ε > 0`:
`∫_a^b |f|² ≤ (1+ε)² (L/π)² ∫_a^b |f'|² + (1 + ε⁻¹)(2 + 2(1+ε)/π²) L (|f(a)|² + |f(b)|²)`.

Subtract the linear interpolant of the endpoint values, apply the sharp Dirichlet inequality to
the difference, and absorb the interpolant with Young's inequality
`(u + v)² ≤ (1+ε)u² + (1+ε⁻¹)v²`. The leading constant `(L/π)²` is sharp as `ε → 0`; this is the
endpoint-stable Poincaré–Wirtinger estimate used for uniqueness sets of Fourier pairs.
-/

open MeasureTheory intervalIntegral Set Complex Real

namespace GaloisForLFunctions.HTGeometry

private lemma add_sq_le_young {ε u v : ℝ} (hε : 0 < ε) :
    (u + v) ^ 2 ≤ (1 + ε) * u ^ 2 + (1 + ε⁻¹) * v ^ 2 := by
  have h : (1 + ε) * u ^ 2 + (1 + ε⁻¹) * v ^ 2 - (u + v) ^ 2 = (ε * u - v) ^ 2 / ε := by
    field_simp; ring
  have : 0 ≤ (ε * u - v) ^ 2 / ε := by positivity
  linarith

private lemma norm_add_sq_le_young {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    ‖z + w‖ ^ 2 ≤ (1 + ε) * ‖z‖ ^ 2 + (1 + ε⁻¹) * ‖w‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le z w) 2).trans (add_sq_le_young hε)

/-- Wirtinger's inequality with endpoint values: sharp leading constant up to `(1+ε)²`, plus an
endpoint term of size `O_ε(L(|f(a)|² + |f(b)|²))`. -/
theorem stable_wirtinger_intervalIntegral {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (hab : a < b)
    {f f' : ℝ → ℂ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf'c : ContinuousOn f' (Icc a b)) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ (1 + ε) ^ 2 * ((b - a) / π) ^ 2 * (∫ x in a..b, ‖f' x‖ ^ 2)
      + (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * (b - a) * (‖f a‖ ^ 2 + ‖f b‖ ^ 2) := by
  set L := b - a with hLdef
  have hL : 0 < L := by rw [hLdef]; linarith
  set m : ℂ := (f b - f a) / (L : ℂ) with hm
  set ℓ : ℝ → ℂ := fun x => f a + ((x - a : ℝ) : ℂ) * m with hℓ
  set h : ℝ → ℂ := fun x => f x - ℓ x with hh
  have hhd : ∀ x ∈ Icc a b, HasDerivAt h (f' x - m) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => ((y - a : ℝ) : ℂ)) 1 x := by
      have := ((hasDerivAt_id x).sub_const a).ofReal_comp
      simpa using this
    have h2 := (h1.mul_const m).const_add (f a)
    have h3 := (hf x hx).sub h2
    convert h3 using 1 <;> first | (ext y; simp [hh, hℓ]) | simp
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hha : h a = 0 := by simp [hh, hℓ]
  have hhb : h b = 0 := by
    simp only [hh, hℓ, hm]
    rw [show ((b - a : ℝ) : ℂ) = (L : ℂ) by simp [hLdef]]
    field_simp; ring
  have hD := dirichlet_wirtinger_intervalIntegral hab hhd (hf'c.sub continuousOn_const) hha hhb
  have hfc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc a b) := fun x hx => (hhd x hx).continuousAt.continuousWithinAt
  set E : ℝ := ‖f a‖ ^ 2 + ‖f b‖ ^ 2 with hE
  have hℓle : ∀ x ∈ Icc a b, ‖ℓ x‖ ^ 2 ≤ 2 * E := by
    intro x hx
    have hθ0 : 0 ≤ (x - a) / L := div_nonneg (by linarith [hx.1]) hL.le
    have hθ1 : (x - a) / L ≤ 1 := by rw [div_le_one hL]; linarith [hx.2]
    have hrepr : ℓ x = ((1 - (x - a) / L : ℝ) : ℂ) * f a + (((x - a) / L : ℝ) : ℂ) * f b := by
      simp only [hℓ, hm]; push_cast; field_simp; ring
    have hn : ‖ℓ x‖ ≤ ‖f a‖ + ‖f b‖ := by
      rw [hrepr]
      calc _ ≤ ‖((1 - (x - a) / L : ℝ) : ℂ) * f a‖ + ‖(((x - a) / L : ℝ) : ℂ) * f b‖ := norm_add_le _ _
        _ = (1 - (x - a) / L) * ‖f a‖ + (x - a) / L * ‖f b‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
        _ ≤ ‖f a‖ + ‖f b‖ := by nlinarith [norm_nonneg (f a), norm_nonneg (f b)]
    nlinarith [norm_nonneg (ℓ x), norm_nonneg (f a), norm_nonneg (f b),
      sq_nonneg (‖f a‖ - ‖f b‖)]
  have hmle : ‖m‖ ^ 2 ≤ 2 * E / L ^ 2 := by
    rw [hm, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, div_pow,
      div_le_div_iff_of_pos_right (by positivity)]
    have := norm_sub_le (f b) (f a)
    nlinarith [norm_nonneg (f a), norm_nonneg (f b), norm_nonneg (f b - f a),
      sq_nonneg (‖f a‖ - ‖f b‖)]
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  -- pointwise bounds integrated
  have B1 : ∫ x in a..b, ‖f x‖ ^ 2 ≤ ∫ x in a..b, ((1 + ε) * ‖h x‖ ^ 2 + (1 + ε⁻¹) * (2 * E)) := by
    apply intervalIntegral.integral_mono_on hab.le
    · exact (hfc.norm.pow 2).intervalIntegrable_of_Icc hab.le
    · exact ((continuousOn_const.mul (hhc.norm.pow 2)).add continuousOn_const).intervalIntegrable_of_Icc
        hab.le
    · intro x hx
      have e : f x = h x + ℓ x := by simp [hh]
      rw [e]
      calc _ ≤ (1 + ε) * ‖h x‖ ^ 2 + (1 + ε⁻¹) * ‖ℓ x‖ ^ 2 := norm_add_sq_le_young hε _ _
        _ ≤ _ := by gcongr; exact hℓle x hx
  have B2 : ∫ x in a..b, ‖f' x - m‖ ^ 2 ≤ ∫ x in a..b, ((1 + ε) * ‖f' x‖ ^ 2 + (1 + ε⁻¹) * ‖m‖ ^ 2) := by
    apply intervalIntegral.integral_mono_on hab.le
    · exact ((hf'c.sub continuousOn_const).norm.pow 2).intervalIntegrable_of_Icc hab.le
    · exact ((continuousOn_const.mul (hf'c.norm.pow 2)).add continuousOn_const).intervalIntegrable_of_Icc
        hab.le
    · intro x _
      have := norm_add_sq_le_young hε (f' x) (-m)
      simpa [sub_eq_add_neg] using this
  have iH : IntervalIntegrable (fun x => ‖h x‖ ^ 2) volume a b :=
    (hhc.norm.pow 2).intervalIntegrable_of_Icc hab.le
  have iF' : IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a b :=
    (hf'c.norm.pow 2).intervalIntegrable_of_Icc hab.le
  rw [intervalIntegral.integral_add (iH.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at B1
  rw [intervalIntegral.integral_add (iF'.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at B2
  simp only [← hLdef] at B1 B2 hD
  have hπ : 0 < π := Real.pi_pos
  have hK : 0 ≤ (L / π) ^ 2 := by positivity
  have hL0 : L ≠ 0 := hL.ne'
  have hπ0 : π ≠ 0 := hπ.ne'
  have hε0 : ε ≠ 0 := hε.ne'
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hεi : 0 ≤ 1 + ε⁻¹ := by positivity
  have hmL : L * ‖m‖ ^ 2 ≤ 2 * E / L := by
    calc L * ‖m‖ ^ 2 ≤ L * (2 * E / L ^ 2) := by gcongr
      _ = 2 * E / L := by field_simp; try ring
  set IF : ℝ := ∫ x in a..b, ‖f' x‖ ^ 2 with hIF
  set IH : ℝ := ∫ x in a..b, ‖h x‖ ^ 2 with hIH
  set IM : ℝ := ∫ x in a..b, ‖f' x - m‖ ^ 2 with hIM
  have step : IH ≤ (L / π) ^ 2 * ((1 + ε) * IF + (1 + ε⁻¹) * (2 * E / L)) := by
    have hC : L * ((1 + ε⁻¹) * ‖m‖ ^ 2) ≤ (1 + ε⁻¹) * (2 * E / L) := by
      calc L * ((1 + ε⁻¹) * ‖m‖ ^ 2) = (1 + ε⁻¹) * (L * ‖m‖ ^ 2) := by ring
        _ ≤ (1 + ε⁻¹) * (2 * E / L) := mul_le_mul_of_nonneg_left hmL hεi
    calc IH ≤ (L / π) ^ 2 * IM := hD
      _ ≤ (L / π) ^ 2 * ((1 + ε) * IF + (1 + ε⁻¹) * (2 * E / L)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        linarith [B2, hC]
  have last : (1 + ε) * ((L / π) ^ 2 * ((1 + ε) * IF + (1 + ε⁻¹) * (2 * E / L)))
      + L * ((1 + ε⁻¹) * (2 * E))
      = (1 + ε) ^ 2 * (L / π) ^ 2 * IF + (1 + ε⁻¹) * (2 + 2 * (1 + ε) / π ^ 2) * L * E := by
    field_simp; ring
  have B1' : ∫ x in a..b, ‖f x‖ ^ 2 ≤ (1 + ε) * IH + L * ((1 + ε⁻¹) * (2 * E)) := by
    linarith [B1]
  calc ∫ x in a..b, ‖f x‖ ^ 2 ≤ (1 + ε) * IH + L * ((1 + ε⁻¹) * (2 * E)) := B1'
    _ ≤ (1 + ε) * ((L / π) ^ 2 * ((1 + ε) * IF + (1 + ε⁻¹) * (2 * E / L)))
        + L * ((1 + ε⁻¹) * (2 * E)) := by
      have := mul_le_mul_of_nonneg_left step hε1
      linarith
    _ = _ := last

end GaloisForLFunctions.HTGeometry
