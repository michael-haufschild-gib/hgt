import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Integrating against a majorant with one exceptional unit window

A nonnegative integrand that is dominated by a majorant everywhere except on a window of length two,
where it is merely bounded, integrates to at most the integral of the majorant plus twice that bound:

```text
∫_{-T}^{T} Φ ≤ ∫_{-T}^{T} Φ₁ + 2K,
```

whenever `Φ ≤ Φ₁` off `[c−1, c+1]` and `Φ ≤ K` on it.  The window contributes only its own length times
the local bound, so an exceptional cell whose local bound is small — for instance because a decaying
kernel is evaluated far from the origin — costs exactly that much and no more.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Membership in the unit window around `c`. -/
theorem mem_unit_window_iff {c t : ℝ} : t ∈ Set.Icc (c - 1) (c + 1) ↔ |t - c| ≤ 1 := by
  rw [Set.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem one_le_abs_sub_of_not_mem_window {c t : ℝ} (h : t ∉ Set.Icc (c - 1) (c + 1)) :
    1 ≤ |t - c| := by
  by_contra hcon
  exact h (mem_unit_window_iff.2 (le_of_lt (not_le.1 hcon)))

/-- **A majorant with one exceptional unit window.**  Outside `[c−1, c+1]` the integrand is dominated
by `Φ₁`; inside it is bounded by `K`.  The window has length two, so it costs `2K`. -/
theorem intervalIntegral_le_of_punctured_majorant {Φ Φ₁ : ℝ → ℝ} {T c K : ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ₁) (hT : 0 ≤ T)
    (hΦ10 : ∀ t, 0 ≤ Φ₁ t) (hK : 0 ≤ K)
    (hout : ∀ t, |t| ≤ T → 1 ≤ |t - c| → Φ t ≤ Φ₁ t)
    (hin : ∀ t, |t| ≤ T → |t - c| ≤ 1 → Φ t ≤ K) :
    (∫ t in (-T)..T, Φ t) ≤ (∫ t in (-T)..T, Φ₁ t) + 2 * K := by
  have hle : -T ≤ T := by linarith
  have hconv : ∀ f : ℝ → ℝ, (∫ t in (-T)..T, f t) = ∫ t in Set.Icc (-T) T, f t := by
    intro f
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hconv Φ, hconv Φ₁]
  have hWtop : (volume (Set.Icc (c - 1) (c + 1))) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hΦint : IntegrableOn Φ (Set.Icc (-T) T) := hΦc.integrableOn_Icc
  have hΦ1int : IntegrableOn Φ₁ (Set.Icc (-T) T) := hΦ1c.integrableOn_Icc
  have hsplit := MeasureTheory.integral_inter_add_sdiff (μ := volume) (f := Φ)
    (s := Set.Icc (-T) T) (t := Set.Icc (c - 1) (c + 1)) measurableSet_Icc hΦint
  have hintop : (volume (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1))) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono Set.inter_subset_right)
  -- the exceptional window
  have hinner : (∫ t in (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1)), Φ t) ≤ 2 * K := by
    have hb : ∀ t ∈ Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1), Φ t ≤ K := fun t ht =>
      hin t (abs_le.2 ⟨ht.1.1, ht.1.2⟩) (mem_unit_window_iff.1 ht.2)
    have hconstint : IntegrableOn (fun _ : ℝ => K)
        (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1)) :=
      integrableOn_const hintop (by simp)
    have hmono := MeasureTheory.setIntegral_mono_on (hΦint.mono_set Set.inter_subset_left)
      hconstint (measurableSet_Icc.inter measurableSet_Icc) hb
    rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
    have hmeas : (volume : Measure ℝ).real (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1)) ≤ 2 := by
      have h1 := measureReal_mono (μ := (volume : Measure ℝ))
        (Set.inter_subset_right (s := Set.Icc (-T) T) (t := Set.Icc (c - 1) (c + 1))) hWtop
      have h2 : (volume : Measure ℝ).real (Set.Icc (c - 1) (c + 1)) = 2 := by
        rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
        ring
      linarith [h1, h2.le, h2.ge]
    calc (∫ t in (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1)), Φ t)
        ≤ (volume : Measure ℝ).real (Set.Icc (-T) T ∩ Set.Icc (c - 1) (c + 1)) * K := hmono
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right hmeas hK
  -- the ordinary part
  have houter : (∫ t in (Set.Icc (-T) T \ Set.Icc (c - 1) (c + 1)), Φ t)
      ≤ ∫ t in Set.Icc (-T) T, Φ₁ t := by
    have hb : ∀ t ∈ Set.Icc (-T) T \ Set.Icc (c - 1) (c + 1), Φ t ≤ Φ₁ t := fun t ht =>
      hout t (abs_le.2 ⟨ht.1.1, ht.1.2⟩) (one_le_abs_sub_of_not_mem_window ht.2)
    have hmono := MeasureTheory.setIntegral_mono_on
      (hΦint.mono_set Set.sdiff_subset) (hΦ1int.mono_set Set.sdiff_subset)
      (measurableSet_Icc.diff measurableSet_Icc) hb
    refine le_trans hmono ?_
    refine MeasureTheory.setIntegral_mono_set hΦ1int ?_ ?_
    · exact Filter.Eventually.of_forall fun t => hΦ10 t
    · exact Filter.Eventually.of_forall fun t ht => ht.1
  linarith [hsplit, hinner, houter]

end

end GaloisForLFunctions.HTGeometry
