import GaloisForLFunctions.HTGeometry.KleinGordonBandStability
import GaloisForLFunctions.HTGeometry.KleinGordonTimePotentialStability

/-!
# Reading a moving background off the short-time field

The conditional stability estimate reconstructs a *fixed* perturbation from the field it produces.
A clock, however, reads a background that moves, and the reconstruction can only be local in time:
what the short-time field sees is the perturbation *at the initial instant*, blurred by however much
the perturbation moves during the probing.

That is exactly what comes out. Splitting the source as

`W(s)u(s) − W(0)f = (W(s)−W(0))u(s) + W(0)(u(s)−f)`,

the second term is the autonomous error, of order `x⁴` after integration; the first is new and of
order `L x³`, where `L` is the Lipschitz constant of the perturbation in time. Dividing by the `x²`
that carries the signal leaves

`‖W₁(0) − W₂(0)‖ ≤ 8η(1+bT)/x² + 8Le^{bT}x`,

a reconstruction error with two competing terms: shortening the probe amplifies the observational
noise `η`, lengthening it admits more of the background's own motion. A static background is the case
`L = 0`, where the second term disappears and the autonomous estimate is recovered.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Departure

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **A solution in a moving background, starting from rest at a low-frequency datum, leaves it at
second order.** -/
theorem norm_kgFieldMildT_sub_data_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r y)
    (R : ℝ) (z : Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    ‖kgFieldMildT W (kgLowPassOp R z) 0 s - kgLowPassOp R z‖
      ≤ ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ (2 : ℕ) := by
  have hfree : kgFieldFree (kgLowPassOp (E := E) R z) 0 s = kgCosOp s (kgLowPassOp R z) := by
    rw [kgFieldFree, map_zero, add_zero]
  have h1 : ‖kgFieldMildT W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s‖
      ≤ b * ((‖kgLowPassOp (E := E) R z‖ + ‖(0 : Lp ℂ 2 (volume : Measure E))‖)
          * Real.exp (b * |s|)) * s ^ (2 : ℕ) :=
    norm_kgFieldMildT_sub_free_le_sq hb0 hWb hWs _ 0 s
  have hPz : ‖kgLowPassOp (E := E) R z‖ ≤ ‖z‖ := norm_kgLowPassOp_apply_le R z
  have h1' : ‖kgFieldMildT W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s‖
      ≤ b * Real.exp (b * |s|) * ‖z‖ * s ^ (2 : ℕ) := by
    refine h1.trans ?_
    have hexp : (0 : ℝ) < Real.exp (b * |s|) := Real.exp_pos _
    have hsq : (0 : ℝ) ≤ s ^ (2 : ℕ) := sq_nonneg s
    have hstep : (‖kgLowPassOp (E := E) R z‖ + ‖(0 : Lp ℂ 2 (volume : Measure E))‖)
        * Real.exp (b * |s|) ≤ ‖z‖ * Real.exp (b * |s|) := by
      rw [norm_zero, add_zero]
      exact mul_le_mul_of_nonneg_right hPz hexp.le
    nlinarith [mul_le_mul_of_nonneg_left hstep hb0]
  have h2 : ‖kgFieldFree (kgLowPassOp (E := E) R z) 0 s - kgLowPassOp R z‖
      ≤ s ^ (2 : ℕ) * (1 + R ^ (2 : ℕ)) / 2 * ‖z‖ := by
    rw [hfree]
    exact norm_kgCosOp_lowPass_sub_le s R z
  have hsplit : kgFieldMildT W (kgLowPassOp R z) 0 s - kgLowPassOp R z
      = (kgFieldMildT W (kgLowPassOp R z) 0 s - kgFieldFree (kgLowPassOp R z) 0 s)
        + (kgFieldFree (kgLowPassOp R z) 0 s - kgLowPassOp R z) := by abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hfin : b * Real.exp (b * |s|) * ‖z‖ * s ^ (2 : ℕ) + s ^ (2 : ℕ) * (1 + R ^ (2 : ℕ)) / 2 * ‖z‖
      = ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ (2 : ℕ) := by ring
  rw [← hfin]
  exact add_le_add h1' h2

end Departure

/-! ## The source integral in a moving background -/

section Source

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- The source of the difference of two moving backgrounds is continuous. -/
theorem continuous_kgPotentialDiffSource (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun s : ℝ => (W₁ s - W₂ s) (kgFieldMildT W₁ f h s) := by
  have hcu : Continuous (kgFieldMildT W₁ f h) := continuous_kgFieldMildT hb0 hW₁b hW₁s f h
  have hA : Continuous fun s : ℝ => W₁ s (kgFieldMildT W₁ f h s) :=
    continuous_of_strong_comp hW₁b hW₁s continuous_id hcu
  have hB : Continuous fun s : ℝ => W₂ s (kgFieldMildT W₁ f h s) :=
    continuous_of_strong_comp hW₂b hW₂s continuous_id hcu
  refine (hA.sub hB).congr fun s => ?_
  simp only [Pi.sub_apply, sub_apply]

set_option maxHeartbeats 1000000 in
/-- **The Duhamel source integral is quadratic in the probing time**, up to an error of order `x⁴`
from the motion of the datum and an error of order `Lx³` from the motion of the background. -/
theorem norm_kgSourceT_sub_smul_le (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L) (hLip : ∀ s : ℝ, ‖(W₁ s - W₂ s) - (W₁ 0 - W₂ 0)‖ ≤ L * |s|)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ 0 - W₂ 0) v) = (W₁ 0 - W₂ 0) v)
    (z : Lp ℂ 2 (volume : Measure E)) {x : ℝ} (hx : 0 ≤ x) :
    ‖(∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
        - ((x ^ (2 : ℕ) / 2 : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))‖
      ≤ L * (‖z‖ * Real.exp (b * x)) * x ^ (3 : ℕ)
        + ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ (4 : ℕ)
        + (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ (4 : ℕ) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hAf0 : (0 : ℝ) ≤ ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ := norm_nonneg _
  have hA00 : (0 : ℝ) ≤ ‖W₁ 0 - W₂ 0‖ := norm_nonneg _
  have hPz : ‖kgLowPassOp (E := E) R z‖ ≤ ‖z‖ := norm_kgLowPassOp_apply_le R z
  have hK0 : (0 : ℝ) ≤ ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖ := by positivity
  have hMx : (0 : ℝ) ≤ ‖z‖ * Real.exp (b * x) := by positivity
  have hint : Continuous fun s : ℝ => kgSinFreqOp (x - s)
      ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      (continuous_kgPotentialDiffSource hb0 hW₁b hW₁s hW₂b hW₂s _ 0)
  have hIlin : IntervalIntegrable
      (fun s : ℝ => ((x - s : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))) volume 0 x := by
    refine Continuous.intervalIntegrable ?_ 0 x
    exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul
      continuous_const
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) x,
      ‖kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))
          - ((x - s : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))‖
        ≤ L * (‖z‖ * Real.exp (b * x)) * x ^ (2 : ℕ)
          + ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ (3 : ℕ)
          + (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ (3 : ℕ) := by
    intro s hs
    have hts : |x - s| ≤ x := by
      have h := abs_sub_le_abs_of_mem_uIoc_zero hs
      rwa [abs_of_nonneg hx] at h
    have habs : |s| ≤ x := by
      have h := abs_le_abs_of_mem_uIoc_zero hs
      rwa [abs_of_nonneg hx] at h
    have hsplit : kgSinFreqOp (x - s) ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))
          - ((x - s : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))
        = kgSinFreqOp (x - s)
            (((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))
          + kgSinFreqOp (x - s) ((W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
              - (W₁ 0 - W₂ 0) (kgLowPassOp R z))
          + (kgSinFreqOp (x - s) ((W₁ 0 - W₂ 0) (kgLowPassOp R z))
              - ((x - s : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))) := by
      have hvec : ((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
            + ((W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
              - (W₁ 0 - W₂ 0) (kgLowPassOp R z))
            + (W₁ 0 - W₂ 0) (kgLowPassOp R z)
          = (W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s) := by
        simp only [sub_apply]
        abel
      rw [← hvec, map_add, map_add]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · have h1 := norm_kgSinFreqOp_apply_le_abs (E := E) (x - s)
        (((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))
      have h2 : ‖((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)‖
          ≤ L * |s| * ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s‖ :=
        ((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)).le_of_opNorm_le (hLip s) _
      have h3 : ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s‖
          ≤ (‖kgLowPassOp (E := E) R z‖ + ‖(0 : Lp ℂ 2 (volume : Measure E))‖)
            * Real.exp (b * |s|) := norm_kgFieldMildT_le hb0 hW₁b hW₁s _ 0 s
      have h4 : ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s‖ ≤ ‖z‖ * Real.exp (b * x) := by
        refine h3.trans ?_
        rw [norm_zero, add_zero]
        have hexp : Real.exp (b * |s|) ≤ Real.exp (b * x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
        have hpos : (0 : ℝ) < Real.exp (b * |s|) := Real.exp_pos _
        calc ‖kgLowPassOp (E := E) R z‖ * Real.exp (b * |s|)
            ≤ ‖z‖ * Real.exp (b * |s|) := mul_le_mul_of_nonneg_right hPz hpos.le
          _ ≤ ‖z‖ * Real.exp (b * x) := mul_le_mul_of_nonneg_left hexp hz0
      have h5 : L * |s| ≤ L * x := mul_le_mul_of_nonneg_left habs hL0
      calc ‖kgSinFreqOp (x - s)
              (((W₁ s - W₂ s) - (W₁ 0 - W₂ 0)) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))‖
          ≤ |x - s| * ‖((W₁ s - W₂ s) - (W₁ 0 - W₂ 0))
              (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)‖ := h1
        _ ≤ x * (L * x * (‖z‖ * Real.exp (b * x))) := by
            refine mul_le_mul hts (h2.trans ?_) (norm_nonneg _) hx
            exact mul_le_mul h5 h4 (norm_nonneg _) (by positivity)
        _ = L * (‖z‖ * Real.exp (b * x)) * x ^ (2 : ℕ) := by ring
    · have h1 := norm_kgSinFreqOp_apply_le_abs (E := E) (x - s)
        ((W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
          - (W₁ 0 - W₂ 0) (kgLowPassOp R z))
      have h2 : ‖(W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
            - (W₁ 0 - W₂ 0) (kgLowPassOp R z)‖
          ≤ ‖W₁ 0 - W₂ 0‖ * ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s - kgLowPassOp R z‖ := by
        rw [← map_sub]
        exact (W₁ 0 - W₂ 0).le_opNorm _
      have h3 : ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s - kgLowPassOp R z‖
          ≤ ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * |s|)) * ‖z‖ * s ^ (2 : ℕ) :=
        norm_kgFieldMildT_sub_data_le hb0 hW₁b hW₁s R z s
      have hexp : Real.exp (b * |s|) ≤ Real.exp (b * x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
      have hs2x : s ^ (2 : ℕ) ≤ x ^ (2 : ℕ) := by
        have hpw := pow_le_pow_left₀ (abs_nonneg s) habs 2
        rwa [sq_abs] at hpw
      have h4 : ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s - kgLowPassOp R z‖
          ≤ ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖ * x ^ (2 : ℕ) := by
        refine h3.trans ?_
        have hbm : b * Real.exp (b * |s|) ≤ b * Real.exp (b * x) :=
          mul_le_mul_of_nonneg_left hexp hb0
        have hco : (1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * |s|)
            ≤ (1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x) := by linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_right hco hz0) hs2x (sq_nonneg s) hK0
      calc ‖kgSinFreqOp (x - s) ((W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
              - (W₁ 0 - W₂ 0) (kgLowPassOp R z))‖
          ≤ |x - s| * ‖(W₁ 0 - W₂ 0) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)
              - (W₁ 0 - W₂ 0) (kgLowPassOp R z)‖ := h1
        _ ≤ x * (‖W₁ 0 - W₂ 0‖
              * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖ * x ^ (2 : ℕ))) := by
            refine mul_le_mul hts (h2.trans (mul_le_mul_of_nonneg_left h4 hA00))
              (norm_nonneg _) hx
        _ = ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ (3 : ℕ) := by ring
    · have hAfP : (W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)
          = kgLowPassOp R ((W₁ 0 - W₂ 0) (kgLowPassOp R z)) := (hAran _).symm
      have hkey := norm_kgSinFreqOp_lowPass_sub_smul_le (E := E) (x - s) R
        ((W₁ 0 - W₂ 0) (kgLowPassOp R z))
      rw [← hAfP] at hkey
      refine hkey.trans ?_
      have hcube : |x - s| ^ (3 : ℕ) ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hts 3
      have hfac : (0 : ℝ) ≤ (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 := by
        positivity
      calc |x - s| ^ (3 : ℕ) * (1 + R ^ (2 : ℕ)) / 6
            * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖
          = (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * |x - s| ^ (3 : ℕ) := by
            ring
        _ ≤ (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ (3 : ℕ) :=
            mul_le_mul_of_nonneg_left hcube hfac
  have hsub : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
        - ((x ^ (2 : ℕ) / 2 : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))
      = ∫ s in (0 : ℝ)..x, (kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))
        - ((x - s : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))) := by
    rw [intervalIntegral.integral_sub (hint.intervalIntegrable (μ := volume) 0 x) hIlin,
      intervalIntegral_ofReal_sub_smul x ((W₁ 0 - W₂ 0) (kgLowPassOp R z))]
  rw [hsub]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  refine hle.trans ?_
  rw [sub_zero, abs_of_nonneg hx]
  refine le_of_eq ?_
  ring

/-! ## Conditional stability for a moving background -/

set_option maxHeartbeats 1000000 in
/-- **Conditional stability for a moving background.** The perturbation at the initial instant is
determined by the short-time field, up to the observational noise amplified by the probing time and
the background's own motion during the probe. With `L = 0` this is the autonomous estimate. -/
theorem norm_sub_zero_le_of_lowPassT (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L) (hLip : ∀ s : ℝ, ‖(W₁ s - W₂ s) - (W₁ 0 - W₂ 0)‖ ≤ L * |s|)
    (hAdom : ∀ v : Lp ℂ 2 (volume : Measure E),
      (W₁ 0 - W₂ 0) (kgLowPassOp R v) = (W₁ 0 - W₂ 0) v)
    (hAran : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R ((W₁ 0 - W₂ 0) v) = (W₁ 0 - W₂ 0) v)
    {η T x : ℝ} (hη0 : 0 ≤ η) (hx0 : 0 < x) (hxT : x ≤ T)
    (hxK : x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) ≤ 1 / 8)
    (hobs : ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMildT W₁ g k t - kgFieldMildT W₂ g k t‖ ≤ η * (‖g‖ + ‖k‖)) :
    ‖W₁ 0 - W₂ 0‖ ≤ 8 * (η * (1 + b * T)) / x ^ (2 : ℕ) + 8 * (L * Real.exp (b * T)) * x := by
  have hT0 : 0 < T := lt_of_lt_of_le hx0 hxT
  have hx2 : (0 : ℝ) < x ^ (2 : ℕ) := by positivity
  have hxabs : |x| = x := abs_of_nonneg hx0.le
  have hbT : (0 : ℝ) ≤ 1 + b * T := by positivity
  have hAnn : (0 : ℝ) ≤ ‖W₁ 0 - W₂ 0‖ := norm_nonneg _
  have hR2 : (0 : ℝ) < 1 + R ^ (2 : ℕ) := by positivity
  have hexpx : Real.exp (b * x) ≤ Real.exp (b * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxT hb0)
  have hquad : x ^ (2 : ℕ) * (1 + R ^ (2 : ℕ)) ≤ 1 / 4 := by
    have hle : x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2) ≤ x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) := by
      have hnn : (0 : ℝ) ≤ b * Real.exp (b * T) := by positivity
      nlinarith
    linarith
  have hkey : ∀ z : Lp ℂ 2 (volume : Measure E),
      ‖(W₁ 0 - W₂ 0) z‖
        ≤ (4 * (η * (1 + b * T)) / x ^ (2 : ℕ) + 4 * (L * Real.exp (b * T)) * x
            + ‖W₁ 0 - W₂ 0‖ / 2) * ‖z‖ := by
    intro z
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hPz : ‖kgLowPassOp (E := E) R z‖ ≤ ‖z‖ := norm_kgLowPassOp_apply_le R z
    have hAz : (W₁ 0 - W₂ 0) z = (W₁ 0 - W₂ 0) (kgLowPassOp R z) := (hAdom z).symm
    have hAf0 : (0 : ℝ) ≤ ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ := norm_nonneg _
    have hΔ : ∀ s : ℝ, |s| ≤ T →
        ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s - kgFieldMildT W₂ (kgLowPassOp R z) 0 s‖
          ≤ η * ‖z‖ := by
      intro s hs
      refine (hobs (kgLowPassOp R z) 0 s hs).trans ?_
      rw [norm_zero, add_zero]
      exact mul_le_mul_of_nonneg_left hPz hη0
    have hDuh : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          (W₂ s (kgFieldMildT W₁ (kgLowPassOp R z) 0 s
            - kgFieldMildT W₂ (kgLowPassOp R z) 0 s))‖ ≤ b * (η * ‖z‖) * x := by
      have hbd2 : ∀ s ∈ Set.uIoc (0 : ℝ) x, ‖kgSinFreqOp (x - s)
          (W₂ s (kgFieldMildT W₁ (kgLowPassOp R z) 0 s
            - kgFieldMildT W₂ (kgLowPassOp R z) 0 s))‖ ≤ b * (η * ‖z‖) := by
        intro s hs
        have hsT : |s| ≤ T := by
          have hsx := abs_le_abs_of_mem_uIoc_zero hs
          rw [hxabs] at hsx
          linarith
        have h1 := norm_kgSinFreqOp_apply_le (E := E) (x - s)
          (W₂ s (kgFieldMildT W₁ (kgLowPassOp R z) 0 s
            - kgFieldMildT W₂ (kgLowPassOp R z) 0 s))
        have h2 := (W₂ s).le_of_opNorm_le (hW₂b s)
          (kgFieldMildT W₁ (kgLowPassOp R z) 0 s - kgFieldMildT W₂ (kgLowPassOp R z) 0 s)
        have h3 := hΔ s hsT
        have h4 : b * ‖kgFieldMildT W₁ (kgLowPassOp R z) 0 s
            - kgFieldMildT W₂ (kgLowPassOp R z) 0 s‖ ≤ b * (η * ‖z‖) :=
          mul_le_mul_of_nonneg_left h3 hb0
        linarith
      have h := intervalIntegral.norm_integral_le_of_norm_le_const hbd2
      rwa [sub_zero, hxabs] at h
    have hGeq : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
        = (kgFieldMildT W₁ (kgLowPassOp R z) 0 x - kgFieldMildT W₂ (kgLowPassOp R z) 0 x)
          - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              (W₂ s (kgFieldMildT W₁ (kgLowPassOp R z) 0 s
                - kgFieldMildT W₂ (kgLowPassOp R z) 0 s)) := by
      rw [kgFieldMildT_sub_potential hb0 hW₁b hW₁s hW₂b hW₂s (kgLowPassOp R z) 0 x]
      abel
    have hGle : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))‖
        ≤ η * ‖z‖ * (1 + b * T) := by
      rw [hGeq]
      refine (norm_sub_le _ _).trans ?_
      have hΔx := hΔ x (by rw [hxabs]; exact hxT)
      have hb1 : b * (η * ‖z‖) * x ≤ b * (η * ‖z‖) * T :=
        mul_le_mul_of_nonneg_left hxT (by positivity)
      nlinarith [hΔx, hDuh]
    have hmain := norm_kgSourceT_sub_smul_le hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hAran z hx0.le
    have hsmulnorm : ‖((x ^ (2 : ℕ) / 2 : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z))‖
        = x ^ (2 : ℕ) / 2 * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ (2 : ℕ) / 2)]
    have htri : x ^ (2 : ℕ) / 2 * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖
        ≤ ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s))‖
          + ‖(∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
              ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
            - ((x ^ (2 : ℕ) / 2 : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z))‖ := by
      rw [← hsmulnorm]
      have hh := norm_sub_le
        (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
          ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
        ((∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            ((W₁ s - W₂ s) (kgFieldMildT W₁ (kgLowPassOp R z) 0 s)))
          - ((x ^ (2 : ℕ) / 2 : ℝ) : ℂ) • ((W₁ 0 - W₂ 0) (kgLowPassOp R z)))
      rwa [sub_sub_cancel] at hh
    have hterm0 : L * (‖z‖ * Real.exp (b * x)) * x ^ (3 : ℕ)
        ≤ L * Real.exp (b * T) * x * (x ^ (2 : ℕ) * ‖z‖) := by
      have hstep : ‖z‖ * Real.exp (b * x) ≤ ‖z‖ * Real.exp (b * T) :=
        mul_le_mul_of_nonneg_left hexpx hz0
      have hmul := mul_le_mul_of_nonneg_left hstep hL0
      nlinarith [pow_nonneg hx0.le 3]
    have hterm1 : ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ (4 : ℕ)
        ≤ x ^ (2 : ℕ) * ‖W₁ 0 - W₂ 0‖ * ‖z‖ / 8 := by
      have hKle : ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖
          ≤ ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) * ‖z‖ := by
        have hbm : b * Real.exp (b * x) ≤ b * Real.exp (b * T) :=
          mul_le_mul_of_nonneg_left hexpx hb0
        nlinarith
      have h1 : ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * x)) * ‖z‖) * x ^ (4 : ℕ)
          ≤ ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) * ‖z‖) * x ^ (4 : ℕ) := by
        have hx4 : (0 : ℝ) ≤ x ^ (4 : ℕ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hKle hAnn]
      have h2 : ‖W₁ 0 - W₂ 0‖ * (((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) * ‖z‖) * x ^ (4 : ℕ)
          = (x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)))
            * (x ^ (2 : ℕ) * ‖W₁ 0 - W₂ 0‖ * ‖z‖) := by ring
      have h3 : (x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)))
            * (x ^ (2 : ℕ) * ‖W₁ 0 - W₂ 0‖ * ‖z‖)
          ≤ (1 / 8) * (x ^ (2 : ℕ) * ‖W₁ 0 - W₂ 0‖ * ‖z‖) := by
        refine mul_le_mul_of_nonneg_right hxK ?_
        positivity
      linarith
    have hterm2 : (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ (4 : ℕ)
        ≤ x ^ (2 : ℕ) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 24 := by
      have h2 : (1 + R ^ (2 : ℕ)) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6 * x ^ (4 : ℕ)
          = (x ^ (2 : ℕ) * (1 + R ^ (2 : ℕ)))
            * (x ^ (2 : ℕ) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6) := by ring
      have h3 : (x ^ (2 : ℕ) * (1 + R ^ (2 : ℕ)))
            * (x ^ (2 : ℕ) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6)
          ≤ (1 / 4) * (x ^ (2 : ℕ) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ / 6) := by
        refine mul_le_mul_of_nonneg_right hquad ?_
        positivity
      linarith
    have hfin : x ^ (2 : ℕ) / 4 * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖
        ≤ η * ‖z‖ * (1 + b * T) + L * Real.exp (b * T) * x * (x ^ (2 : ℕ) * ‖z‖)
          + x ^ (2 : ℕ) * ‖W₁ 0 - W₂ 0‖ * ‖z‖ / 8 := by
      have hm : (0 : ℝ) ≤ x ^ (2 : ℕ) * ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖ := by positivity
      linarith [htri, hGle, hmain, hterm0, hterm1, hterm2]
    rw [hAz]
    have hdiv : ‖(W₁ 0 - W₂ 0) (kgLowPassOp (E := E) R z)‖
        ≤ 4 * (η * ‖z‖ * (1 + b * T)) / x ^ (2 : ℕ) + 4 * (L * Real.exp (b * T)) * x * ‖z‖
          + ‖W₁ 0 - W₂ 0‖ * ‖z‖ / 2 := by
      rw [div_add' _ _ _ hx2.ne', div_add' _ _ _ hx2.ne', le_div_iff₀ hx2]
      nlinarith [hfin]
    refine hdiv.trans ?_
    refine le_of_eq ?_
    field_simp
  have hop := ContinuousLinearMap.opNorm_le_bound (W₁ 0 - W₂ 0)
    (by positivity : (0:ℝ) ≤ 4 * (η * (1 + b * T)) / x ^ (2 : ℕ) + 4 * (L * Real.exp (b * T)) * x
      + ‖W₁ 0 - W₂ 0‖ / 2) hkey
  have hop2 : ‖W₁ 0 - W₂ 0‖ * x ^ (2 : ℕ)
      ≤ 4 * (η * (1 + b * T)) + 4 * (L * Real.exp (b * T)) * x * x ^ (2 : ℕ)
        + ‖W₁ 0 - W₂ 0‖ / 2 * x ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right hop hx2.le
    rwa [add_mul, add_mul, div_mul_cancel₀ _ hx2.ne'] at hmul
  rw [div_add' _ _ _ hx2.ne', le_div_iff₀ hx2]
  linarith

end Source

end GaloisForLFunctions.HTGeometry
