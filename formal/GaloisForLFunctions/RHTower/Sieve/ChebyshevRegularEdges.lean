import GaloisForLFunctions.RHTower.Sieve.ChebyshevHorizontalDslope

/-!
# The edges of the regular part

The regular part `zetaLogDerivReg = -G'/G` is bounded on a zero-free region, and the cutoff's
transform decays like `C/T²` at height `T`.  So the horizontal edges of `zetaLogDerivReg · W` are at
most `(d-c)·R·C/T²`, and the left vertical edge is `M` times the vertical mass of the transform.

Both bounds take the size of the regular part as a hypothesis: that is the only genuinely
zeta-analytic input, supplied by the zero-free region.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **A horizontal edge of the regular part.** -/
theorem norm_integral_horizontal_reg_le {N H C R : ℝ} {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hT : T ≠ 0) (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ Set.uIoc c d, ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ R)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ (d - c) * (R * (C / |T| ^ (1 + 1))) := by
  have hTpos : (0 : ℝ) < |T| := abs_pos.2 hT
  have hpt : ∀ x ∈ Set.uIoc c d,
      ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
      ≤ R * (C / |T| ^ (1 + 1)) := by
    intro x hx
    have hxmem := hx
    rw [Set.uIoc_of_le hcd] at hxmem
    have hre : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I).im = T := by simp
    have hW : ‖mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ C / |T| ^ (1 + 1) := by
      have h := hbd ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        (by rw [hre]; exact lt_of_lt_of_le hc hxmem.1.le) (by rw [hre]; exact hxmem.2)
      rw [him] at h
      rw [le_div_iff₀ (by positivity)]
      linarith [h]
    rw [norm_mul]
    exact mul_le_mul (hR x hx) hW (norm_nonneg _) hR0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at h
  linarith [h]

/-- The regular part is continuous along a zero-free line off the abscissa `1`. -/
theorem continuousOn_zetaLogDerivReg_line {c T : ℝ} (hc : c ≠ 1)
    (hzf : ∀ y ∈ Set.uIcc (-T) T, riemannZeta ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 0) :
    ContinuousOn (fun y : ℝ => zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-T) T) := by
  intro y hy
  have hne : ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 1 :=
    fun h => sub_one_ne_zero_line_of_ne (y := y) hc (by rw [h]; ring)
  have hin : Continuous fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I) := by fun_prop
  exact (ContinuousAt.comp (g := zetaLogDerivReg)
    (f := fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I))
    ((differentiableAt_zetaLogDerivReg
      ((zetaResidueUnit_ne_zero_iff hne).2 (hzf y hy))).continuousAt)
    hin.continuousAt).continuousWithinAt

/-- **The left vertical edge of the regular part.** -/
theorem norm_integral_left_vertical_reg_le {N H c T C M : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc0 : 0 < c) (hc : c ≠ 1) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hzf : ∀ y ∈ Set.uIcc (-T) T, riemannZeta ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
    (hreg : ∀ y ∈ Set.Icc (-T) T, ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ M * (2 * ((N + H) ^ c / c) + 2 * C) :=
  norm_integral_vertical_edge_le hN hH hc0 hT hM hbd
    (continuousOn_zetaLogDerivReg_line hc hzf) hreg

end RHTower.Sieve
