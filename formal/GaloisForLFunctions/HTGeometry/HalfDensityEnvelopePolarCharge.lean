import GaloisForLFunctions.HTGeometry.HalfLineCoshPrimitive

/-!
# One half-density envelope discharges every integrability hypothesis of the polar estimate

The abstract polar-charge estimate takes ten separate integrability inputs about the source.  A
single pointwise envelope

```text
|R(s)| ≤ K exp (-s/2),      s ≥ 0,
```

together with continuity, supplies all of them: every integrand in the estimate is dominated by a
constant multiple of `exp (-s)` on the half line, the two-dimensional cross integrand by a constant
multiple of `exp (-s)` on the product, and the two autocorrelation integrands by the product
integrability through Fubini.

The estimate then reads with explicit constants:

```text
|PPol(R, a)| ≤ 4 M K + 4 K²,
```

with `M` the bound on the growing primitive.  This is the shape the radial source consumes: the BV
lattice envelope supplies exactly one hypothesis.
-/

noncomputable section

open MeasureTheory Set

namespace HTGeometry

/-- Domination by a multiple of `exp (-s)` on the half line. -/
theorem integrableOn_Ioi_of_exp_bound {f : ℝ → ℝ} {B : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hb : ∀ s : ℝ, 0 < s → |f s| ≤ B * Real.exp (-s)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul B) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
  simpa [Real.norm_eq_abs] using hb s hs

theorem exp_neg_half_mul_self (s : ℝ) :
    Real.exp (-s / 2) * Real.exp (-s / 2) = Real.exp (-s) := by
  rw [← Real.exp_add]
  ring_nf

section Envelope

variable {R : ℝ → ℝ} {K : ℝ}

/-- The envelope bounds the source's square. -/
theorem sq_le_of_envelope (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {s : ℝ} (hs : 0 ≤ s) :
    R s ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * Real.exp (-s) := by
  have h := henv s hs
  have hnn : (0 : ℝ) ≤ |R s| := abs_nonneg _
  have hb : (0 : ℝ) ≤ K * Real.exp (-s / 2) := by positivity
  have hsq : |R s| ^ (2 : ℕ) ≤ (K * Real.exp (-s / 2)) ^ (2 : ℕ) := by nlinarith
  calc R s ^ (2 : ℕ) = |R s| ^ (2 : ℕ) := (sq_abs _).symm
    _ ≤ (K * Real.exp (-s / 2)) ^ (2 : ℕ) := hsq
    _ = K ^ (2 : ℕ) * Real.exp (-s) := by
        have hsq2 : Real.exp (-s / 2) ^ (2 : ℕ) = Real.exp (-s) := by
          rw [sq, exp_neg_half_mul_self]
        rw [mul_pow, hsq2]

theorem integrableOn_sq_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    IntegrableOn (fun s : ℝ => R s ^ (2 : ℕ)) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ (2 : ℕ))
    (hmeas.pow_const 2).aestronglyMeasurable.restrict (fun s hs => ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact sq_le_of_envelope hK henv hs.le

theorem integral_sq_le_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    (∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ)) ≤ K ^ (2 : ℕ) := by
  have hmaj : IntegrableOn (fun s : ℝ => K ^ (2 : ℕ) * Real.exp (-s)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have hle : (∫ s in Ioi (0 : ℝ), R s ^ (2 : ℕ)) ≤ ∫ s in Ioi (0 : ℝ), K ^ (2 : ℕ) * Real.exp (-s) := by
    refine integral_mono_ae (integrableOn_sq_of_envelope hmeas hK henv) hmaj ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    exact sq_le_of_envelope hK henv hs.le
  have hval : (∫ s in Ioi (0 : ℝ), K ^ (2 : ℕ) * Real.exp (-s)) = K ^ (2 : ℕ) := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
    simp
  linarith [hle, hval.le, hval.ge]

theorem integrableOn_expNegHalf_mul_of_envelope (hmeas : Measurable R)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    IntegrableOn (fun s : ℝ => Real.exp (-s / 2) * R s) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K)
    ((((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).measurable).mul
      hmeas).aestronglyMeasurable.restrict) (fun s hs => ?_)
  rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-s / 2) * |R s| ≤ Real.exp (-s / 2) * (K * Real.exp (-s / 2)) :=
        mul_le_mul_of_nonneg_left (henv s hs.le) (Real.exp_pos _).le
    _ = K * Real.exp (-s) := by rw [← mul_assoc, mul_comm (Real.exp (-s / 2)) K, mul_assoc,
        exp_neg_half_mul_self]

theorem integral_abs_expNegHalf_mul_le_of_envelope (hmeas : Measurable R)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) :
    (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|) ≤ K := by
  have hmaj : IntegrableOn (fun s : ℝ => K * Real.exp (-s)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_Ioi 0).const_mul _
  have habs : IntegrableOn (fun s : ℝ => |Real.exp (-s / 2) * R s|) (Ioi (0 : ℝ)) :=
    (integrableOn_expNegHalf_mul_of_envelope hmeas henv).abs
  have hle : (∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s|)
      ≤ ∫ s in Ioi (0 : ℝ), K * Real.exp (-s) := by
    refine integral_mono_ae habs hmaj ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs => ?_)
    show |Real.exp (-s / 2) * R s| ≤ K * Real.exp (-s)
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-s / 2) * |R s| ≤ Real.exp (-s / 2) * (K * Real.exp (-s / 2)) :=
          mul_le_mul_of_nonneg_left (henv s hs.le) (Real.exp_pos _).le
      _ = K * Real.exp (-s) := by rw [← mul_assoc, mul_comm (Real.exp (-s / 2)) K, mul_assoc,
          exp_neg_half_mul_self]
  have hval : (∫ s in Ioi (0 : ℝ), K * Real.exp (-s)) = K := by
    rw [integral_const_mul, integral_exp_neg_Ioi]
    simp
  linarith [hle, hval.le, hval.ge]

theorem shifted_envelope {h : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {s : ℝ} (hs : 0 ≤ s) :
    |R (s + h)| ≤ K * Real.exp (-s / 2) := by
  refine (henv (s + h) (by linarith)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK
  refine Real.exp_le_exp.mpr ?_
  linarith

theorem integrableOn_sq_comp_add_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun s : ℝ => R (s + h) ^ (2 : ℕ)) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ (2 : ℕ))
    (((hmeas.comp (measurable_id.add_const _)).pow_const 2).aestronglyMeasurable.restrict)
    (fun s hs => ?_)
  have hb := shifted_envelope hh hK henv hs.le
  have hnn : (0 : ℝ) ≤ |R (s + h)| := abs_nonneg _
  have hsq2 : Real.exp (-s / 2) ^ (2 : ℕ) = Real.exp (-s) := by rw [sq, exp_neg_half_mul_self]
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  calc |R (s + h)| ^ (2 : ℕ) ≤ (K * Real.exp (-s / 2)) ^ (2 : ℕ) := by nlinarith
    _ = K ^ (2 : ℕ) * Real.exp (-s) := by rw [mul_pow, hsq2]

theorem integrableOn_mul_comp_add_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {h : ℝ} (hh : 0 ≤ h) :
    IntegrableOn (fun s : ℝ => R (s + h) * R s) (Ioi (0 : ℝ)) := by
  refine integrableOn_Ioi_of_exp_bound (B := K ^ (2 : ℕ))
    (((hmeas.comp (measurable_id.add_const _)).mul hmeas).aestronglyMeasurable.restrict)
    (fun s hs => ?_)
  have hb := shifted_envelope hh hK henv hs.le
  have hb0 := henv s hs.le
  have hsq2 : Real.exp (-s / 2) ^ (2 : ℕ) = Real.exp (-s) := by rw [sq, exp_neg_half_mul_self]
  rw [abs_mul]
  calc |R (s + h)| * |R s| ≤ (K * Real.exp (-s / 2)) * (K * Real.exp (-s / 2)) :=
        mul_le_mul hb hb0 (abs_nonneg _) (by positivity)
    _ = K ^ (2 : ℕ) * Real.exp (-s) := by
        rw [show (K * Real.exp (-s / 2)) * (K * Real.exp (-s / 2))
          = K ^ (2 : ℕ) * Real.exp (-s / 2) ^ (2 : ℕ) by ring, hsq2]

theorem intervalIntegrable_expHalf_mul (hcont : Continuous R) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y :=
  ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hcont).intervalIntegrable x y

theorem continuous_halfLineExpPrimitive
    (hlocal : ∀ x y : ℝ,
      IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y) :
    Continuous (halfLineExpPrimitive R) :=
  intervalIntegral.continuous_primitive hlocal 0

/-- **The two-dimensional cross integrand is dominated.**  On the lag rectangle the weight is at
most `exp a`, so the envelope dominates the whole product by `K² exp a · exp (-s)`. -/
theorem integrable_prod_expHalf_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {a eps : ℝ} (_ha : 0 ≤ a)
    (heps : |eps| = 1) :
    Integrable (Function.uncurry (fun h s : ℝ => Real.exp (eps * h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmaj : Integrable (fun p : ℝ × ℝ => (K ^ (2 : ℕ) * Real.exp a) * Real.exp (-p.2))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun _ : ℝ => K ^ (2 : ℕ) * Real.exp a)
        (volume.restrict (Ioc (0 : ℝ) (2 * a))) :=
      integrableOn_const measure_Ioc_lt_top.ne enorm_ne_top
    exact h1.mul_prod (integrableOn_exp_neg_Ioi 0)
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (fun h s : ℝ => Real.exp (eps * h / 2) * R (s + h) * R s))
      ((volume.restrict (Ioc (0 : ℝ) (2 * a))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable fun p : ℝ × ℝ => Real.exp (eps * p.1 / 2) :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_fst).div_const 2)).measurable
    have h2 : Measurable fun p : ℝ × ℝ => R (p.2 + p.1) :=
      hmeas.comp (measurable_snd.add measurable_fst)
    have h3 : Measurable fun p : ℝ × ℝ => R p.2 := hmeas.comp measurable_snd
    exact (h1.mul h2).mul h3
  refine Integrable.mono' hmaj hmeas ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioi)).mpr ?_
  filter_upwards with p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hh0 : (0 : ℝ) ≤ p.1 := le_of_lt hp1.1
  have hs0 : (0 : ℝ) ≤ p.2 := le_of_lt hp2
  have hweight : Real.exp (eps * p.1 / 2) ≤ Real.exp a := by
    refine Real.exp_le_exp.mpr ?_
    calc eps * p.1 / 2 ≤ |eps * p.1 / 2| := le_abs_self _
      _ = p.1 / 2 := by
          rw [abs_div, abs_mul, heps, one_mul, abs_of_nonneg hh0, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ a := by linarith [hp1.2]
  have hb := shifted_envelope hh0 hK henv hs0
  have hb0 := henv p.2 hs0
  have hsq2 : Real.exp (-p.2 / 2) ^ (2 : ℕ) = Real.exp (-p.2) := by rw [sq, exp_neg_half_mul_self]
  show ‖Real.exp (eps * p.1 / 2) * R (p.2 + p.1) * R p.2‖ ≤ K ^ (2 : ℕ) * Real.exp a * Real.exp (-p.2)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (eps * p.1 / 2) * |R (p.2 + p.1)| * |R p.2|
      ≤ Real.exp a * ((K * Real.exp (-p.2 / 2)) * (K * Real.exp (-p.2 / 2))) := by
        refine mul_le_mul (mul_le_mul hweight hb (abs_nonneg _) (Real.exp_pos _).le) hb0
          (abs_nonneg _) (by positivity) |>.trans (le_of_eq ?_)
        ring
    _ = K ^ (2 : ℕ) * Real.exp a * Real.exp (-p.2) := by
        rw [show (K * Real.exp (-p.2 / 2)) * (K * Real.exp (-p.2 / 2))
          = K ^ (2 : ℕ) * Real.exp (-p.2 / 2) ^ (2 : ℕ) by ring, hsq2]
        ring

/-- **Both weighted autocorrelation integrands are integrable on the lag interval.**  Fubini turns
the product integrability into integrability of the inner integral. -/
theorem integrableOn_expWeight_mul_autocorrelation_of_envelope (hmeas : Measurable R) (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {a eps : ℝ} (ha : 0 ≤ a)
    (heps : |eps| = 1) :
    IntegrableOn (fun h : ℝ => Real.exp (eps * h / 2) * halfLineAutocorrelation R h)
      (Ioc 0 (2 * a)) := by
  have hprod := integrable_prod_expHalf_of_envelope hmeas hK henv ha heps
  have hfub := hprod.integral_prod_left
  refine hfub.congr (Filter.Eventually.of_forall fun h => ?_)
  show (∫ s : ℝ, Real.exp (eps * h / 2) * R (s + h) * R s ∂(volume.restrict (Ioi (0 : ℝ))))
      = Real.exp (eps * h / 2) * halfLineAutocorrelation R h
  rw [halfLineAutocorrelation, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  ring

/-- The pairing of the decaying branch with a primitive increment is integrable. -/
theorem integrableOn_expNegHalf_mul_primitive_diff_of_envelope (hmeas : Measurable R)
    (hlocal : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y)
    (hK : 0 ≤ K)
    (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2)) {a M : ℝ} (ha : 0 ≤ a)
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M) :
    IntegrableOn (fun s : ℝ => (Real.exp (-s / 2) * R s)
      * (halfLineExpPrimitive R (s + 2 * a) - halfLineExpPrimitive R s)) (Ioi (0 : ℝ)) := by
  have hM : (0 : ℝ) ≤ M := by
    have h0 := hA 0 le_rfl
    have hz : halfLineExpPrimitive R 0 = 0 := by
      rw [halfLineExpPrimitive, intervalIntegral.integral_same]
    rw [hz] at h0
    simpa using h0
  have hprim := continuous_halfLineExpPrimitive hlocal
  refine integrableOn_Ioi_of_exp_bound (B := 2 * M * K)
    (((((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).measurable).mul hmeas).mul
      (((hprim.comp (continuous_id.add continuous_const)).sub
        hprim).measurable)).aestronglyMeasurable.restrict)
    (fun s hs => ?_)
  have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
  have h1 : |Real.exp (-s / 2) * R s| ≤ K * Real.exp (-s) := by
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-s / 2) * |R s| ≤ Real.exp (-s / 2) * (K * Real.exp (-s / 2)) :=
          mul_le_mul_of_nonneg_left (henv s hs0) (Real.exp_pos _).le
      _ = K * Real.exp (-s) := by
          rw [← mul_assoc, mul_comm (Real.exp (-s / 2)) K, mul_assoc, exp_neg_half_mul_self]
  have h2 : |halfLineExpPrimitive R (s + 2 * a) - halfLineExpPrimitive R s| ≤ 2 * M := by
    refine (abs_sub _ _).trans ?_
    have hb1 := hA (s + 2 * a) (by linarith)
    have hb2 := hA s hs0
    linarith
  rw [abs_mul]
  calc |Real.exp (-s / 2) * R s| * |halfLineExpPrimitive R (s + 2 * a) - halfLineExpPrimitive R s|
      ≤ (K * Real.exp (-s)) * (2 * M) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 2 * M * K * Real.exp (-s) := by ring

/-- **The polar charge under one half-density envelope.**  Continuity and the envelope discharge
every integrability hypothesis of the abstract estimate, and the two remaining integrals are
bounded by `K` and `K²`. -/
theorem abs_polarCharge_le_of_envelope (hmeas : Measurable R)
    (hlocal : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (t / 2) * R t) volume x y)
    {a M K : ℝ} (ha : 0 ≤ a)
    (hK : 0 ≤ K) (henv : ∀ s : ℝ, 0 ≤ s → |R s| ≤ K * Real.exp (-s / 2))
    (hA : ∀ t : ℝ, 0 ≤ t → |halfLineExpPrimitive R t| ≤ M) :
    |polarCharge R a| ≤ 4 * M * K + 4 * K ^ (2 : ℕ) := by
  have hM : (0 : ℝ) ≤ M := by
    have h0 := hA 0 le_rfl
    have hz : halfLineExpPrimitive R 0 = 0 := by
      rw [halfLineExpPrimitive, intervalIntegral.integral_same]
    rw [hz] at h0
    simpa using h0
  have hpos : |(1 : ℝ)| = 1 := abs_one
  have hneg : |(-1 : ℝ)| = 1 := by norm_num
  have hmain := abs_polarCharge_le R ha hA
    (integrableOn_sq_of_envelope hmeas hK henv)
    (fun h hh => integrableOn_sq_comp_add_of_envelope hmeas hK henv hh)
    (fun h hh => integrableOn_mul_comp_add_of_envelope hmeas hK henv hh)
    hlocal
    (by
      have h := integrable_prod_expHalf_of_envelope hmeas hK henv ha hpos
      refine h.congr (Filter.Eventually.of_forall fun p => ?_)
      show Real.exp (1 * p.1 / 2) * R (p.2 + p.1) * R p.2
        = Real.exp (p.1 / 2) * R (p.2 + p.1) * R p.2
      rw [one_mul])
    (integrableOn_expNegHalf_mul_of_envelope hmeas henv)
    (integrableOn_expNegHalf_mul_primitive_diff_of_envelope hmeas hlocal hK henv ha hA)
    (by
      have h := integrableOn_expWeight_mul_autocorrelation_of_envelope hmeas hK henv ha hpos
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      show Real.exp (1 * x / 2) * halfLineAutocorrelation R x
        = Real.exp (x / 2) * halfLineAutocorrelation R x
      rw [one_mul])
    (by
      have h := integrableOn_expWeight_mul_autocorrelation_of_envelope hmeas hK henv ha hneg
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      show Real.exp (-1 * x / 2) * halfLineAutocorrelation R x
        = Real.exp (-x / 2) * halfLineAutocorrelation R x
      rw [show (-1 : ℝ) * x / 2 = -x / 2 by ring])
  have hI1 := integral_abs_expNegHalf_mul_le_of_envelope hmeas henv
  have hI2 := integral_sq_le_of_envelope hmeas hK henv
  have hI1nn : (0 : ℝ) ≤ ∫ s in Ioi (0 : ℝ), |Real.exp (-s / 2) * R s| :=
    integral_nonneg (fun s => abs_nonneg _)
  nlinarith [hmain, hI1, hI2, hM, hK, hI1nn]

end Envelope

end HTGeometry
