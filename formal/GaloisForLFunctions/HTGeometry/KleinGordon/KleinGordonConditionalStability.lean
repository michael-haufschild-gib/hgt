import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonLowPass

/-!
# Conditional stability: reconstruction below a fixed frequency

The inverse problem is ill-posed, and the witness is a perturbation living above frequency `R` whose
field is invisible. Restricting the perturbation to *low* frequencies removes the witness, and this
file shows it removes the ill-posedness with it: on the class of perturbations that only couple
frequencies below `R`, the forward map **is** bounded below, with a constant that is explicit in `R`
and in the length of the observation window.

The argument reads the perturbation off the short-time behaviour of the field. Starting from rest at
a low-frequency datum, the solution leaves it at second order (`‖u(s) − f‖ = O(s²)`), and the Duhamel
source integral is

`∫₀ˣ (sin((x−s)⟨D⟩)/⟨D⟩)(A u(s)) ds = (x²/2)·Af + O(x⁴)`,

the error coming from the two Taylor estimates of the previous file. The left-hand side is bounded by
the observed discrepancy. Choosing the probing time `x` small enough — how small depends only on `R`
and on the size of the perturbations — makes the `O(x⁴)` terms absorbable, and what survives is a
lower bound for `‖A‖` in terms of the discrepancy.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The linear profile integrates to the quadratic one. -/
theorem intervalIntegral_ofReal_sub_smul (x : ℝ) (v : Lp ℂ 2 (volume : Measure E)) :
    (∫ s in (0 : ℝ)..x, ((x - s : ℝ) : ℂ) • v) = ((x ^ 2 / 2 : ℝ) : ℂ) • v := by
  rw [intervalIntegral.integral_smul_const]
  congr 1
  rw [intervalIntegral.integral_ofReal]
  congr 1
  have hIid : IntervalIntegrable (fun s : ℝ => s) volume 0 x :=
    continuous_id.intervalIntegrable 0 x
  rw [intervalIntegral.integral_sub intervalIntegrable_const hIid,
    intervalIntegral.integral_const, integral_id]
  simp only [sub_zero, smul_eq_mul]
  ring

section Departure

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **A solution starting from rest at a low-frequency datum leaves it at second order.** -/
theorem norm_kgFieldMild_sub_data_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (R : ℝ)
    (z : Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    ‖kgFieldMild W (kgLowPassOp R z) 0 s - kgLowPassOp R z‖
      ≤ ((1 + R ^ 2) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ 2 := by
  have hfree : kgFieldFree (kgLowPassOp (E := E) R z) 0 s = kgCosOp s (kgLowPassOp R z) := by
    rw [kgFieldFree, map_zero, add_zero]
  have h1 : ‖kgFieldMild W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s‖
      ≤ b * ((‖kgLowPassOp (E := E) R z‖ + ‖(0 : Lp ℂ 2 (volume : Measure E))‖)
          * Real.exp (b * |s|)) * s ^ 2 :=
    norm_kgFieldMild_sub_free_le_sq hb0 hW _ 0 s
  have hPz : ‖kgLowPassOp (E := E) R z‖ ≤ ‖z‖ := norm_kgLowPassOp_apply_le R z
  have h1' : ‖kgFieldMild W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s‖
      ≤ b * Real.exp (b * |s|) * ‖z‖ * s ^ 2 := by
    refine h1.trans ?_
    have hexp : (0 : ℝ) < Real.exp (b * |s|) := Real.exp_pos _
    have hsq : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    have hstep : (‖kgLowPassOp (E := E) R z‖ + ‖(0 : Lp ℂ 2 (volume : Measure E))‖)
        * Real.exp (b * |s|) ≤ ‖z‖ * Real.exp (b * |s|) := by
      rw [norm_zero, add_zero]
      exact mul_le_mul_of_nonneg_right hPz hexp.le
    nlinarith [mul_le_mul_of_nonneg_left hstep hb0]
  have h2 : ‖kgFieldFree (kgLowPassOp (E := E) R z) 0 s - kgLowPassOp R z‖
      ≤ s ^ 2 * (1 + R ^ 2) / 2 * ‖z‖ := by
    rw [hfree]
    exact norm_kgCosOp_lowPass_sub_le s R z
  have hsplit : kgFieldMild W (kgLowPassOp R z) 0 s - kgLowPassOp R z
      = (kgFieldMild W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s)
        + (kgFieldFree (kgLowPassOp R z) 0 s - kgLowPassOp R z) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hfin : b * Real.exp (b * |s|) * ‖z‖ * s ^ 2 + s ^ 2 * (1 + R ^ 2) / 2 * ‖z‖
      = ((1 + R ^ 2) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ 2 := by ring
  rw [← hfin]
  exact add_le_add h1' h2

end Departure

/-! ## Reading the perturbation off the short-time field -/

section Conditional

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The Duhamel source integral is quadratic in the probing time**, with an `O(x⁴)` error, once the
perturbation and the datum live below a fixed frequency. -/
theorem norm_kgSource_sub_smul_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) {R : ℝ}
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ - W₂) v) = (W₁ - W₂) v)
    (z : Lp ℂ 2 (volume : Measure E)) {x : ℝ} (hx : 0 ≤ x) :
    ‖(∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s)))
        - ((x ^ 2 / 2 : ℝ) : ℂ) • ((W₁ - W₂) (kgLowPassOp R z))‖
      ≤ (‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖)
          + (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp R z)‖ / 6) * x ^ 4 := by
  set A := W₁ - W₂ with hA
  set f := kgLowPassOp (E := E) R z with hf
  set u := kgFieldMild W₁ f 0 with hu
  set K : ℝ := ((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖ with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hAf0 : (0 : ℝ) ≤ ‖A f‖ := norm_nonneg _
  have hcu : Continuous u := continuous_kgFieldMild hb0 hW₁ f 0
  have hA1 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (A (u s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) (A.continuous.comp hcu)
  have hlin : (∫ s in (0 : ℝ)..x, ((x - s : ℝ) : ℂ) • (A f)) = ((x ^ 2 / 2 : ℝ) : ℂ) • (A f) :=
    intervalIntegral_ofReal_sub_smul x (A f)
  have hIlin : IntervalIntegrable (fun s : ℝ => ((x - s : ℝ) : ℂ) • (A f)) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
      continuous_const
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) x,
      ‖kgSinFreqOp (x - s) (A (u s)) - ((x - s : ℝ) : ℂ) • (A f)‖
        ≤ ‖A‖ * K * x ^ 3 + (1 + R ^ 2) * ‖A f‖ / 6 * x ^ 3 := by
    intro s hs
    have hts : |x - s| ≤ x := by
      have hts' := abs_sub_le_abs_of_mem_uIoc_zero hs
      rwa [abs_of_nonneg hx] at hts'
    have habs : |s| ≤ x := by
      have habs' := abs_le_abs_of_mem_uIoc_zero hs
      rwa [abs_of_nonneg hx] at habs'
    have hsplit : kgSinFreqOp (x - s) (A (u s)) - ((x - s : ℝ) : ℂ) • (A f)
        = kgSinFreqOp (x - s) (A (u s) - A f)
          + (kgSinFreqOp (x - s) (A f) - ((x - s : ℝ) : ℂ) • (A f)) := by
      rw [map_sub]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have h1 : ‖kgSinFreqOp (x - s) (A (u s) - A f)‖ ≤ |x - s| * ‖A (u s) - A f‖ :=
        norm_kgSinFreqOp_apply_le_abs (x - s) _
      have h2 : ‖A (u s) - A f‖ ≤ ‖A‖ * ‖u s - f‖ := by
        rw [← map_sub]
        exact A.le_opNorm _
      have h3 : ‖u s - f‖ ≤ ((1 + R ^ 2) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ 2 :=
        norm_kgFieldMild_sub_data_le hb0 hW₁ R z s
      have hexp : Real.exp (b * |s|) ≤ Real.exp (b * x) := by
        refine Real.exp_le_exp.mpr ?_
        exact mul_le_mul_of_nonneg_left habs hb0
      have h4 : ‖u s - f‖ ≤ K * s ^ 2 := by
        refine h3.trans ?_
        rw [hK]
        have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
        have hs2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
        have hbm : b * Real.exp (b * |s|) ≤ b * Real.exp (b * x) :=
          mul_le_mul_of_nonneg_left hexp hb0
        have hco : (1 + R ^ 2) / 2 + b * Real.exp (b * |s|)
            ≤ (1 + R ^ 2) / 2 + b * Real.exp (b * x) := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco hz0) hs2
      have hs2x : s ^ 2 ≤ x ^ 2 := by
        have hpw := pow_le_pow_left₀ (abs_nonneg s) habs 2
        rwa [sq_abs] at hpw
      have h5 : ‖u s - f‖ ≤ K * x ^ 2 := h4.trans (mul_le_mul_of_nonneg_left hs2x hK0)
      calc ‖kgSinFreqOp (x - s) (A (u s) - A f)‖ ≤ |x - s| * ‖A (u s) - A f‖ := h1
        _ ≤ x * (‖A‖ * (K * x ^ 2)) := by
            refine mul_le_mul hts (h2.trans (mul_le_mul_of_nonneg_left h5 (norm_nonneg A)))
              (norm_nonneg _) hx
        _ = ‖A‖ * K * x ^ 3 := by ring
    · have hAfP : A f = kgLowPassOp R (A f) := (hAran f).symm
      have hkey := norm_kgSinFreqOp_lowPass_sub_smul_le (E := E) (x - s) R (A f)
      rw [← hAfP] at hkey
      refine hkey.trans ?_
      have hcube : |x - s| ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hts 3
      have hfac : (0 : ℝ) ≤ (1 + R ^ 2) * ‖A f‖ / 6 := by positivity
      calc |x - s| ^ 3 * (1 + R ^ 2) / 6 * ‖A f‖
          = (1 + R ^ 2) * ‖A f‖ / 6 * |x - s| ^ 3 := by ring
        _ ≤ (1 + R ^ 2) * ‖A f‖ / 6 * x ^ 3 := mul_le_mul_of_nonneg_left hcube hfac
  have hsub : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (A (u s)))
        - ((x ^ 2 / 2 : ℝ) : ℂ) • (A f)
      = ∫ s in (0 : ℝ)..x, (kgSinFreqOp (x - s) (A (u s)) - ((x - s : ℝ) : ℂ) • (A f)) := by
    rw [intervalIntegral.integral_sub (hA1.intervalIntegrable (μ := volume) 0 x) hIlin, hlin]
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  refine hle.trans ?_
  rw [sub_zero, abs_of_nonneg hx]
  have hrw : (‖A‖ * K * x ^ 3 + (1 + R ^ 2) * ‖A f‖ / 6 * x ^ 3) * x
      = (‖A‖ * K + (1 + R ^ 2) * ‖A f‖ / 6) * x ^ 4 := by ring
  rw [hrw]

set_option maxHeartbeats 1000000 in
/-- **Conditional stability.** On the class of perturbations that only couple frequencies below `R`,
the forward map is bounded below: the operator norm of the difference of two potentials is controlled
by the discrepancy of the fields they produce, with a constant explicit in `R`, in the size `b` of
the perturbations, and in the probing time `x`.

The probing time must be short enough for the two Taylor errors to be absorbed, which is exactly the
hypothesis `x²((1+R²)/2 + b e^{bT}) ≤ 1/8`; it can always be met, and how short it has to be depends
only on `R` and `b`. This is the positive counterpart of the ill-posedness theorem: the obstruction
there lives entirely above frequency `R`. -/
theorem norm_sub_le_of_lowPass (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b) {R : ℝ}
    (hAdom : ∀ v : Lp ℂ 2 (volume : Measure E),
      (W₁ - W₂) (kgLowPassOp R v) = (W₁ - W₂) v)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ - W₂) v) = (W₁ - W₂) v)
    {η T x : ℝ} (hη0 : 0 ≤ η) (hx0 : 0 < x) (hxT : x ≤ T)
    (hxK : x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) ≤ 1 / 8)
    (hobs : ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMild W₁ g k t - kgFieldMild W₂ g k t‖ ≤ η * (‖g‖ + ‖k‖)) :
    ‖W₁ - W₂‖ ≤ 8 * (η * (1 + b * T)) / x ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le hx0 hxT
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hxabs : |x| = x := abs_of_nonneg hx0.le
  have hbT : (0 : ℝ) ≤ 1 + b * T := by positivity
  have hAnn : (0 : ℝ) ≤ ‖W₁ - W₂‖ := norm_nonneg _
  have hR2 : (0 : ℝ) < 1 + R ^ 2 := by positivity
  have hK₀0 : (0 : ℝ) < (1 + R ^ 2) / 2 + b * Real.exp (b * T) := by positivity
  have hquad : x ^ 2 * (1 + R ^ 2) ≤ 1 / 4 := by
    have hle : x ^ 2 * ((1 + R ^ 2) / 2) ≤ x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) := by
      have : (0 : ℝ) ≤ b * Real.exp (b * T) := by positivity
      nlinarith
    linarith
  have hkey : ∀ z : Lp ℂ 2 (volume : Measure E),
      ‖(W₁ - W₂) z‖ ≤ (4 * (η * (1 + b * T)) / x ^ 2 + ‖W₁ - W₂‖ / 2) * ‖z‖ := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hPz : ‖kgLowPassOp (E := E) R z‖ ≤ ‖z‖ := norm_kgLowPassOp_apply_le R z
    have hAz : (W₁ - W₂) z = (W₁ - W₂) (kgLowPassOp R z) := (hAdom z).symm
    have hAf0 : (0 : ℝ) ≤ ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ := norm_nonneg _
    have hΔ : ∀ s : ℝ, |s| ≤ T →
        ‖kgFieldMild W₁ (kgLowPassOp R z) 0 s - kgFieldMild W₂ (kgLowPassOp R z) 0 s‖
          ≤ η * ‖z‖ := by
      intro s hs
      refine (hobs (kgLowPassOp R z) 0 s hs).trans ?_
      rw [norm_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hPz hη0
    have hDuh : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          (W₂ (kgFieldMild W₁ (kgLowPassOp R z) 0 s
            - kgFieldMild W₂ (kgLowPassOp R z) 0 s))‖ ≤ b * (η * ‖z‖) * x := by
      have hbd2 : ∀ s ∈ Set.uIoc (0 : ℝ) x, ‖kgSinFreqOp (x - s)
          (W₂ (kgFieldMild W₁ (kgLowPassOp R z) 0 s
            - kgFieldMild W₂ (kgLowPassOp R z) 0 s))‖ ≤ b * (η * ‖z‖) := by
        intro s hs
        have hsT : |s| ≤ T := by
          have hsx := abs_le_abs_of_mem_uIoc_zero hs
          rw [hxabs] at hsx
          linarith
        have h1 := norm_kgSinFreqOp_apply_le (E := E) (x - s)
          (W₂ (kgFieldMild W₁ (kgLowPassOp R z) 0 s - kgFieldMild W₂ (kgLowPassOp R z) 0 s))
        have h2 := W₂.le_of_opNorm_le hW₂
          (kgFieldMild W₁ (kgLowPassOp R z) 0 s - kgFieldMild W₂ (kgLowPassOp R z) 0 s)
        have h3 := hΔ s hsT
        have h4 : b * ‖kgFieldMild W₁ (kgLowPassOp R z) 0 s
            - kgFieldMild W₂ (kgLowPassOp R z) 0 s‖ ≤ b * (η * ‖z‖) :=
          mul_le_mul_of_nonneg_left h3 hb0
        linarith
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd2
      rwa [sub_zero, hxabs] at h
    have hGeq : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s)))
        = (kgFieldMild W₁ (kgLowPassOp R z) 0 x - kgFieldMild W₂ (kgLowPassOp R z) 0 x)
          - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              (W₂ (kgFieldMild W₁ (kgLowPassOp R z) 0 s
                - kgFieldMild W₂ (kgLowPassOp R z) 0 s)) := by
      rw [kgFieldMild_sub_potential hb0 hW₁ hW₂ (kgLowPassOp R z) 0 x]
      abel
    have hGle : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s))‖ ≤ η * ‖z‖ * (1 + b * T) := by
      rw [hGeq]
      refine (norm_sub_le _ _).trans ?_
      have hΔx := hΔ x (by rw [hxabs]; exact hxT)
      have hb1 : b * (η * ‖z‖) * x ≤ b * (η * ‖z‖) * T :=
        mul_le_mul_of_nonneg_left hxT (by positivity)
      nlinarith [hΔx, hDuh]
    have hmain := norm_kgSource_sub_smul_le hb0 hW₁ hAran z hx0.le
    have hsmulnorm : ‖((x ^ 2 / 2 : ℝ) : ℂ) • ((W₁ - W₂) (kgLowPassOp (E := E) R z))‖
        = x ^ 2 / 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 / 2)]
    have hlower : x ^ 2 / 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖
        ≤ η * ‖z‖ * (1 + b * T)
          + (‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖)
            + (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6) * x ^ 4 := by
      have htri : x ^ 2 / 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖
          ≤ ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s))‖
            + ‖(∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
                ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s)))
              - ((x ^ 2 / 2 : ℝ) : ℂ) • ((W₁ - W₂) (kgLowPassOp R z))‖ := by
        rw [← hsmulnorm]
        have hh := norm_sub_le
          (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s)))
          ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              ((W₁ - W₂) (kgFieldMild W₁ (kgLowPassOp R z) 0 s)))
            - ((x ^ 2 / 2 : ℝ) : ℂ) • ((W₁ - W₂) (kgLowPassOp R z)))
        rwa [sub_sub_cancel] at hh
      linarith [htri, hGle, hmain]
    have hexpx : Real.exp (b * x) ≤ Real.exp (b * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxT hb0)
    have hKle : ((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖
        ≤ ((1 + R ^ 2) / 2 + b * Real.exp (b * T)) * ‖z‖ := by
      have : b * Real.exp (b * x) ≤ b * Real.exp (b * T) :=
        mul_le_mul_of_nonneg_left hexpx hb0
      nlinarith
    have hterm1 : ‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ 4
        ≤ x ^ 2 * ‖W₁ - W₂‖ * ‖z‖ / 8 := by
      have h1 : ‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ 4
          ≤ ‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * T)) * ‖z‖) * x ^ 4 := by
        have hx4 : (0 : ℝ) ≤ x ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hKle hAnn]
      have h2 : ‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * T)) * ‖z‖) * x ^ 4
          = (x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T))) * (x ^ 2 * ‖W₁ - W₂‖ * ‖z‖) := by
        ring
      have h3 : (x ^ 2 * ((1 + R ^ 2) / 2 + b * Real.exp (b * T))) * (x ^ 2 * ‖W₁ - W₂‖ * ‖z‖)
          ≤ (1 / 8) * (x ^ 2 * ‖W₁ - W₂‖ * ‖z‖) := by
        refine mul_le_mul_of_nonneg_right hxK ?_
        positivity
      linarith
    have hterm2 : (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ 4
        ≤ x ^ 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 24 := by
      have h2 : (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ 4
          = (x ^ 2 * (1 + R ^ 2)) * (x ^ 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6) := by
        ring
      have h3 : (x ^ 2 * (1 + R ^ 2)) * (x ^ 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6)
          ≤ (1 / 4) * (x ^ 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6) := by
        refine mul_le_mul_of_nonneg_right hquad ?_
        positivity
      linarith
    have hfin : x ^ 2 / 4 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖
        ≤ η * ‖z‖ * (1 + b * T) + x ^ 2 * ‖W₁ - W₂‖ * ‖z‖ / 8 := by
      have hexpand : (‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖)
            + (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6) * x ^ 4
          = ‖W₁ - W₂‖ * (((1 + R ^ 2) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ 4
            + (1 + R ^ 2) * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ 4 := by ring
      rw [hexpand] at hlower
      have hm : (0 : ℝ) ≤ x ^ 2 * ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖ := by positivity
      linarith
    rw [hAz]
    have hdiv : ‖(W₁ - W₂) (kgLowPassOp (E := E) R z)‖
        ≤ 4 * (η * ‖z‖ * (1 + b * T)) / x ^ 2 + ‖W₁ - W₂‖ * ‖z‖ / 2 := by
      rw [div_add' _ _ _ hx2.ne', le_div_iff₀ hx2]
      nlinarith [hfin]
    refine hdiv.trans ?_
    rw [le_iff_eq_or_lt]
    left
    field_simp
  have hop := ContinuousLinearMap.opNorm_le_bound (W₁ - W₂)
    (by positivity : (0:ℝ) ≤ 4 * (η * (1 + b * T)) / x ^ 2 + ‖W₁ - W₂‖ / 2) hkey
  have hop2 : ‖W₁ - W₂‖ / 2 ≤ 4 * (η * (1 + b * T)) / x ^ 2 := by linarith
  have hop3 : ‖W₁ - W₂‖ / 2 * x ^ 2 ≤ 4 * (η * (1 + b * T)) := by
    have hmul := mul_le_mul_of_nonneg_right hop2 hx2.le
    rwa [div_mul_cancel₀ _ hx2.ne'] at hmul
  rw [le_div_iff₀ hx2]
  linarith

end Conditional

end GaloisForLFunctions.HTGeometry
