import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily

/-!
# Vertical-time hyperbolic dominance of conjugate spectral pairs

Conjugation makes an admissible spectral trace real on the positive real-time axis, but it does not
create decay on vertical complex-time lines.  For `p = M + iK` and `tau = sigma + iu`, the pair

`exp (-tau p) + exp (-tau conj(p))`

has arms of norms `exp (-sigma M + uK)` and `exp (-sigma M - uK)`.  Reverse triangle gives a sharp
lower bound by their difference.  More strongly, after normalization by the growing arm, the norm
of the pair tends to one whenever `K > 0` and `u -> +infinity`.

This is an exact no-go for attempts to beat a vertical-line entropy wall by pairing each point only
with its conjugate.  The result uses only the abstract spectral-family interface.
-/

open Complex Filter

namespace HTGeometry

noncomputable section

namespace AbstractSpectralFamily

variable {ι : Type*} (F : AbstractSpectralFamily ι)

/-- A conjugate spectral pair is exactly a complex cosine times its common real-height damping. -/
theorem term_add_inv_eq_two_exp_mul_cos (τ : ℂ) (i : ι) :
    F.term τ i + F.term τ (F.inv i) =
      2 * Complex.exp (-τ * ((F.pt i).re : ℂ)) *
        Complex.cos (τ * ((F.pt i).im : ℂ)) := by
  have hp : F.pt i = ((F.pt i).re : ℂ) + ((F.pt i).im : ℂ) * I := by
    exact (Complex.re_add_im (F.pt i)).symm
  have hc : (starRingEnd ℂ) (F.pt i) =
      ((F.pt i).re : ℂ) - ((F.pt i).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [term, term, F.conj_stable i]
  rw [show -τ * F.pt i =
      -τ * ((F.pt i).re : ℂ) + -(τ * ((F.pt i).im : ℂ)) * I by
        calc
          -τ * F.pt i = -τ * (((F.pt i).re : ℂ) + ((F.pt i).im : ℂ) * I) := by
            congr 1
          _ = _ := by ring]
  rw [show -τ * (starRingEnd ℂ) (F.pt i) =
      -τ * ((F.pt i).re : ℂ) + (τ * ((F.pt i).im : ℂ)) * I by
        calc
          -τ * (starRingEnd ℂ) (F.pt i) =
              -τ * (((F.pt i).re : ℂ) - ((F.pt i).im : ℂ) * I) := by
                congr 1
          _ = _ := by ring]
  rw [Complex.exp_add, Complex.exp_add, ← mul_add]
  rw [show Complex.exp (-(τ * ((F.pt i).im : ℂ)) * I) +
      Complex.exp ((τ * ((F.pt i).im : ℂ)) * I) =
      2 * Complex.cos (τ * ((F.pt i).im : ℂ)) by
        rw [Complex.two_cos]
        ring]
  ring

/-- Exact norm of one spectral arm on a vertical complex-time line. -/
theorem norm_term_vertical (σ u : ℝ) (i : ι) :
    ‖F.term ((σ : ℂ) + (u : ℂ) * I) i‖ =
      Real.exp (-σ * (F.pt i).re + u * (F.pt i).im) := by
  rw [F.norm_term]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Exact norm of the conjugate arm on a vertical complex-time line. -/
theorem norm_term_vertical_inv (σ u : ℝ) (i : ι) :
    ‖F.term ((σ : ℂ) + (u : ℂ) * I) (F.inv i)‖ =
      Real.exp (-σ * (F.pt i).re - u * (F.pt i).im) := by
  rw [F.norm_term, F.conj_stable]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Reverse triangle exposes the hyperbolic, rather than cancelling, size of a conjugate pair. -/
theorem exp_mul_abs_exp_sub_exp_le_norm_term_add_inv (σ u : ℝ) (i : ι) :
    Real.exp (-σ * (F.pt i).re) *
        |Real.exp (u * (F.pt i).im) - Real.exp (-(u * (F.pt i).im))| ≤
      ‖F.term ((σ : ℂ) + (u : ℂ) * I) i +
        F.term ((σ : ℂ) + (u : ℂ) * I) (F.inv i)‖ := by
  let τ : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hrev :
      |‖F.term τ i‖ - ‖F.term τ (F.inv i)‖| ≤
        ‖F.term τ i + F.term τ (F.inv i)‖ := by
    simpa only [norm_neg, sub_neg_eq_add] using
      (abs_norm_sub_norm_le (F.term τ i) (-F.term τ (F.inv i)))
  rw [F.norm_term_vertical, F.norm_term_vertical_inv] at hrev
  rw [show Real.exp (-σ * (F.pt i).re + u * (F.pt i).im) =
      Real.exp (-σ * (F.pt i).re) * Real.exp (u * (F.pt i).im) by
        rw [← Real.exp_add]] at hrev
  rw [show Real.exp (-σ * (F.pt i).re - u * (F.pt i).im) =
      Real.exp (-σ * (F.pt i).re) * Real.exp (-(u * (F.pt i).im)) by
        rw [← Real.exp_add]
        congr 1] at hrev
  have heq :
      Real.exp (-σ * (F.pt i).re) *
          |Real.exp (u * (F.pt i).im) - Real.exp (-(u * (F.pt i).im))| =
        |Real.exp (-σ * (F.pt i).re) * Real.exp (u * (F.pt i).im) -
          Real.exp (-σ * (F.pt i).re) * Real.exp (-(u * (F.pt i).im))| := by
    rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [heq]
  exact hrev

/-- If the first arm is dominant, the pair retains it up to the explicit relative error
`exp (-2uK)`. -/
theorem dominant_arm_mul_one_sub_exp_le_norm_term_add_inv (σ u : ℝ) (i : ι)
    (hu : 0 ≤ u * (F.pt i).im) :
    Real.exp (-σ * (F.pt i).re + u * (F.pt i).im) *
        (1 - Real.exp (-2 * (u * (F.pt i).im))) ≤
      ‖F.term ((σ : ℂ) + (u : ℂ) * I) i +
        F.term ((σ : ℂ) + (u : ℂ) * I) (F.inv i)‖ := by
  have h := F.exp_mul_abs_exp_sub_exp_le_norm_term_add_inv σ u i
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))] at h
  calc
    Real.exp (-σ * (F.pt i).re + u * (F.pt i).im) *
        (1 - Real.exp (-2 * (u * (F.pt i).im))) =
      Real.exp (-σ * (F.pt i).re) *
        (Real.exp (u * (F.pt i).im) - Real.exp (-(u * (F.pt i).im))) := by
          rw [mul_sub, mul_one, mul_sub]
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    _ ≤ _ := h

/-- At every vertical time, normalized pair norm differs from the selected arm by at most the
opposite-to-selected arm ratio. -/
theorem abs_norm_term_add_inv_div_dominant_sub_one_le (σ u : ℝ) (i : ι) :
    |‖F.term ((σ : ℂ) + (u : ℂ) * I) i +
          F.term ((σ : ℂ) + (u : ℂ) * I) (F.inv i)‖ /
        Real.exp (-σ * (F.pt i).re + u * (F.pt i).im) - 1| ≤
      Real.exp (-2 * (u * (F.pt i).im)) := by
  let τ : ℂ := (σ : ℂ) + (u : ℂ) * I
  let d : ℝ := Real.exp (-σ * (F.pt i).re + u * (F.pt i).im)
  have hd : 0 < d := Real.exp_pos _
  have hraw :
      |‖F.term τ i + F.term τ (F.inv i)‖ - ‖F.term τ i‖| ≤
        ‖F.term τ (F.inv i)‖ := by
    have h := abs_norm_sub_norm_le
      (F.term τ i + F.term τ (F.inv i)) (F.term τ i)
    simpa only [add_sub_cancel_left] using h
  rw [F.norm_term_vertical, F.norm_term_vertical_inv] at hraw
  change |‖F.term τ i + F.term τ (F.inv i)‖ / d - 1| ≤ _
  have heq :
      |‖F.term τ i + F.term τ (F.inv i)‖ / d - 1| =
        |‖F.term τ i + F.term τ (F.inv i)‖ - d| / d := by
    rw [show ‖F.term τ i + F.term τ (F.inv i)‖ / d - 1 =
        (‖F.term τ i + F.term τ (F.inv i)‖ - d) / d by field_simp]
    rw [abs_div, abs_of_pos hd]
  rw [heq]
  calc
    |‖F.term τ i + F.term τ (F.inv i)‖ - d| / d ≤
        Real.exp (-σ * (F.pt i).re - u * (F.pt i).im) / d := by
          exact div_le_div_of_nonneg_right hraw hd.le
    _ = Real.exp (-2 * (u * (F.pt i).im)) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- **Conjugate-pair vertical no-go.**  For a point in the upper spectral half-plane, the norm of
its conjugate pair, divided by the growing arm, tends to one.  Involution-local pairing therefore
preserves the arm's exponential type exactly. -/
theorem tendsto_norm_term_add_inv_div_dominant_atTop_one
    (σ : ℝ) (i : ι) (hi : 0 < (F.pt i).im) :
    Tendsto
      (fun u : ℝ =>
        ‖F.term ((σ : ℂ) + (u : ℂ) * I) i +
            F.term ((σ : ℂ) + (u : ℂ) * I) (F.inv i)‖ /
          Real.exp (-σ * (F.pt i).re + u * (F.pt i).im))
      atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun u => abs_nonneg _)
      (Eventually.of_forall fun u =>
        F.abs_norm_term_add_inv_div_dominant_sub_one_le σ u i)
  apply Real.tendsto_exp_atBot.comp
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (tendsto_id.const_mul_atTop_of_neg
      (by linarith : -2 * (F.pt i).im < 0))

end AbstractSpectralFamily

end

end HTGeometry
