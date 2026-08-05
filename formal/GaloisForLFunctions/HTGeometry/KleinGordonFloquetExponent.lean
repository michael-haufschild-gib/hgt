import GaloisForLFunctions.HTGeometry.KleinGordonNoFreeDrift

/-!
# The Floquet exponent is bounded by the strength of the background

The annulus of statement 392 is a multiplicative statement; taking logarithms turns it into the
statement a physicist reads. A multiplier `k` describes a mode multiplied by `k` each period, so its
**Floquet exponent** is `log|k| / T`, the growth rate per unit time. The annulus says

`|log|k|| ≤ b·|T|`,

so the exponent obeys `|log|k| / T| ≤ b`: **a mode cannot grow or decay faster than the strength of
the background it moves in**, whatever the period. That is the energy estimate `‖v(t)‖ ≤ ‖v(0)‖e^{b|t|}`
of statement 186 in spectral form, and it is sharp — the free field has `b = 0` and exponent zero
(statement 347).
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Exponent

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The logarithm of a Floquet multiplier is bounded by `b·|T|`.** -/
theorem abs_log_norm_le_of_mem_spectrum_kgMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    |Real.log ‖k‖| ≤ b * |T| := by
  obtain ⟨hlow, hhigh⟩ := mem_annulus_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk
  have hpos : 0 < ‖k‖ := lt_of_lt_of_le (Real.exp_pos _) hlow
  have hup : Real.log ‖k‖ ≤ b * |T| := by
    have h := Real.log_le_log hpos hhigh
    rwa [Real.log_exp] at h
  have hdown : -(b * |T|) ≤ Real.log ‖k‖ := by
    have h := Real.log_le_log (Real.exp_pos (-(b * |T|))) hlow
    rwa [Real.log_exp] at h
  exact abs_le.mpr ⟨hdown, hup⟩

/-- **The Floquet exponent is bounded by the strength of the background.** A mode grows or decays no
faster than `e^{b|t|}`, whatever the period. -/
theorem abs_floquetExponent_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : T ≠ 0) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    |Real.log ‖k‖ / T| ≤ b := by
  have habs := abs_log_norm_le_of_mem_spectrum_kgMonodromy hb0 hWb hWs hper hk
  have hTpos : 0 < |T| := abs_pos.mpr hT
  rw [abs_div]
  rw [div_le_iff₀ hTpos]
  exact habs

end Exponent

end GaloisForLFunctions.HTGeometry
