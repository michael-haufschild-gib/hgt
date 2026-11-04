import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture

/-!
# Windows blind to a lattice

Kernel design (question Q5) asks for windows that exclude tilted points against real
configurations, not just against single points. For the real lattice `hℤ` the answer is explicit.

* **Shifts multiply the transform** (`paperFT_shift`). `(f(· + c))^(w) = e^{−iwc} f̂(w)`.
* **The lattice window** (`exists_window_blind_to_lattice`). For every aperture `r > π/h` and every
  point `z ∉ hℤ` there is a window of aperture `r` whose transform vanishes on all of `hℤ` and not
  at `z`: `f(u) = b(u + π/h) − b(u − π/h)` has transform `−2i sin(πw/h) b̂(w)`.

So against the full real lattice of spacing `h`, every tilted point is seen by a single window as
soon as the aperture exceeds `π/h`, the same threshold at which tilted columns of spacing `h` stop
hiding (`offLineLattice_mimic_iff` with `L = 2π/h`). The camera's separating power against a lattice
and the lattice's mimicry threshold coincide.
-/

open MeasureTheory Complex Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-- **Shifts multiply the transform.** -/
theorem paperFT_shift (f : ℝ → ℂ) (c : ℝ) (w : ℂ) :
    paperFT (fun u => f (u + c)) w = cexp (-(I * w * c)) * paperFT f w := by
  rw [paperFT_def, paperFT_def, ← integral_const_mul]
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => cexp (-(I * w * c)) * (f u * cexp (I * w * u))) c
  rw [← h]
  congr 1 with u
  rw [show cexp (I * w * ((u + c : ℝ) : ℂ)) = cexp (I * w * u) * cexp (I * w * c) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]
  rw [show cexp (-(I * w * c)) * (f (u + c) * (cexp (I * w * u) * cexp (I * w * c))) =
    f (u + c) * cexp (I * w * u) * (cexp (-(I * w * c)) * cexp (I * w * c)) by ring,
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **A window blind to the lattice `hℤ` that sees a given point off it.** -/
theorem exists_window_blind_to_lattice {h r : ℝ} (hh : 0 < h) (hr : π / h < r) {z : ℂ}
    (hz : ∀ k : ℤ, z ≠ k * h) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ k : ℤ, paperFT f ((k : ℂ) * h) = 0) ∧
      paperFT f z ≠ 0 := by
  set c := π / h with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨b, hb, hb1⟩ := exists_window_paperFT_eq_one (by linarith : 0 < r - c) z
  have hbc := hb.hasCompactSupport
  let f : ℝ → ℂ := fun u => b (u + c) - b (u - c)
  have hft : ∀ w : ℂ, paperFT f w = -(2 * I) * Complex.sin (w * c) * paperFT b w := by
    intro w
    have h1 := paperFT_shift b c w
    have h2 := paperFT_shift b (-c) w
    simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at h2
    have hsplit : paperFT f w = paperFT (fun u => b (u + c)) w - paperFT (fun u => b (u - c)) w := by
      have i1 : Integrable fun u : ℝ => b (u + c) * cexp (I * w * u) :=
        ((hb.1.continuous.comp (continuous_id.add continuous_const)).mul
          (by fun_prop)).integrable_of_hasCompactSupport
          ((hbc.comp_homeomorph (Homeomorph.addRight c)).mul_right)
      have i2 : Integrable fun u : ℝ => b (u - c) * cexp (I * w * u) :=
        ((hb.1.continuous.comp (continuous_id.sub continuous_const)).mul
          (by fun_prop)).integrable_of_hasCompactSupport
          ((hbc.comp_homeomorph (Homeomorph.subRight c)).mul_right)
      rw [paperFT_def, paperFT_def, paperFT_def, ← integral_sub i1 i2]
      congr 1 with u; simp only [f]; ring
    rw [hsplit, h1, h2, Complex.sin,
      show -(I * w * (c : ℂ)) = -(w * c) * I by ring,
      show -(I * w * -(c : ℂ)) = (w * c) * I by ring]
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (cexp (-(w * c) * I) - cexp ((w * c) * I)) * paperFT b w * hI
  have hsupp : ∀ u, f u ≠ 0 → u ∈ Icc (-r) r := by
    intro u hu
    have hbs := hb.2
    by_cases h1 : b (u + c) = 0
    · have h2 : b (u - c) ≠ 0 := fun h2 => hu (by simp [f, h1, h2])
      obtain ⟨l, u'⟩ := hbs (subset_tsupport _ h2)
      exact ⟨by linarith, by linarith⟩
    · obtain ⟨l, u'⟩ := hbs (subset_tsupport _ h1)
      exact ⟨by linarith, by linarith⟩
  refine ⟨f, ⟨?_, closure_minimal (fun u hu => hsupp u hu) isClosed_Icc⟩, fun k => ?_, ?_⟩
  · exact (hb.1.comp (contDiff_id.add contDiff_const)).sub (hb.1.comp (contDiff_id.sub contDiff_const))
  · have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
    rw [hft, show (k : ℂ) * h * c = (k : ℂ) * π by rw [hc]; push_cast; field_simp,
      Complex.sin_int_mul_pi, mul_zero, zero_mul]
  · rw [hft, hb1, mul_one]
    refine mul_ne_zero (by simp [Complex.I_ne_zero]) fun h0 => ?_
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
    apply hz k
    have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [hc] at hk
    push_cast at hk
    field_simp at hk
    linear_combination hk

end GaloisForLFunctions.ZeroConfigurationGeometry
