import GaloisForLFunctions.RHTower.Sieve.ChebyshevPerronIdentity

/-!
# Splitting the truncated Chebyshev integral

The three-piece decomposition of the integrand cannot be integrated term by term over the **whole**
line: the pole term `W(1)·(s-1)⁻¹` decays like `1/|y|` there and is not integrable, even though the
full integrand is.  The splitting is therefore applied only after truncation, where every piece is
continuous on a compact interval and integrability is automatic.

This is why the contour argument truncates first and splits second, and not the other way round.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- On a line right of the pole, the divided difference is an explicit quotient. -/
theorem dslope_mellin_line {N H : ℝ} {d y : ℝ} (hd : 1 < d) :
    dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I)
      = (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
          - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1)
        / (((d : ℂ) + (y : ℝ) * Complex.I) - 1) := by
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hne : ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [dslope_of_ne _ hne, slope_def_field]

/-- The line stays away from the pole. -/
theorem sub_one_ne_zero_line {d y : ℝ} (hd : 1 < d) :
    ((d : ℂ) + (y : ℝ) * Complex.I) - 1 ≠ 0 := by
  have hre : (((d : ℂ) + (y : ℝ) * Complex.I) - 1).re = d - 1 := by simp
  intro h
  rw [h] at hre
  simp at hre
  linarith

/-- **The truncated Chebyshev integral splits into three.** -/
theorem integral_truncated_chebyshev_split {N H : ℝ} (hH : 0 < H) {d T : ℝ} (hd : 1 < d) :
    (∫ y : ℝ in (-T)..T, (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
          ((d : ℂ) + (y : ℝ) * Complex.I)
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
        + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)))
      = (∫ y : ℝ in (-T)..T, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
        + (∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hd0
  have hlin : Continuous fun y : ℝ => ((d : ℂ) + (y : ℝ) * Complex.I) - 1 := by fun_prop
  have hinv : Continuous fun y : ℝ => (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ :=
    hlin.inv₀ fun y => sub_one_ne_zero_line hd
  have h1 : Continuous fun y : ℝ =>
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I) := by
    have : (fun y : ℝ => dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I))
        = fun y : ℝ => (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)
            - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1)
          * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ := by
      funext y
      rw [dslope_mellin_line hd, div_eq_mul_inv]
    rw [this]
    exact (hWcont.sub continuous_const).mul hinv
  have h2 : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
        * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ := continuous_const.mul hinv
  have h3 : Continuous fun y : ℝ =>
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) := by
    have hreg : Continuous fun y : ℝ => zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I) := by
      refine continuous_iff_continuousAt.2 fun y => ?_
      have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
      have hne : ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
        intro h
        rw [h] at hre
        simp at hre
        linarith
      have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
      have hin : Continuous fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I) := by fun_prop
      exact ContinuousAt.comp (g := zetaLogDerivReg)
        (f := fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I))
        ((differentiableAt_zetaLogDerivReg
          ((zetaResidueUnit_ne_zero_iff hne).2 hz)).continuousAt) hin.continuousAt
    exact hreg.mul hWcont
  have hA := intervalIntegral.integral_add (a := -T) (b := T) (μ := volume)
    (f := fun y : ℝ => dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
      ((d : ℂ) + (y : ℝ) * Complex.I))
    (g := fun y : ℝ => mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
      * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
    (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)
  have hB := intervalIntegral.integral_add (a := -T) (b := T) (μ := volume)
    (f := fun y : ℝ => dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I)
      + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
        * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
    (g := fun y : ℝ => zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((d : ℂ) + (y : ℝ) * Complex.I))
    ((h1.add h2).intervalIntegrable _ _) (h3.intervalIntegrable _ _)
  rw [hB, hA]

end RHTower.Sieve
