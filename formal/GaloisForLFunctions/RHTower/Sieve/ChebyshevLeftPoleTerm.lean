import GaloisForLFunctions.RHTower.Sieve.ChebyshevShiftedError

/-!
# The pole term on the left edge

The divided difference is holomorphic, so it shifts with no residue — but it is *not* small on the
left edge, because it still contains the pole term:

    dslope W 1 (s) = W(s)/(s-1) - W(1)/(s-1),

and on `Re s = c < 1` the second summand integrates to `-W(1)·2·arctan(T/(c-1))`, which tends to
`+π·W(1)`.  That is the other half of the residue: the right line supplies `π·W(1)` and the left line
the remaining `π·W(1)`, together the `2π·W(1)` demanded by the residue theorem.

Extracting it is what makes the left edge genuinely small: what is left there is
`∫ W(c+iy)/(c-1+iy) dy`, controlled by the decay of `W` alone.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The line `Re s = a` avoids the pole as soon as `a ≠ 1`. -/
theorem sub_one_ne_zero_line_of_ne {a y : ℝ} (ha : a ≠ 1) :
    ((a : ℂ) + (y : ℝ) * Complex.I) - 1 ≠ 0 := by
  have hre : (((a : ℂ) + (y : ℝ) * Complex.I) - 1).re = a - 1 := by simp
  intro h
  rw [h] at hre
  simp at hre
  exact ha (by linarith)

/-- **The pole term on any line off the abscissa `1`.** -/
theorem integral_pole_term_line_of_ne {N H : ℝ} {a T : ℝ} (ha : a ≠ 1) :
    (∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
        * (((a : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      = mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
          * ((2 * Real.arctan (T / (a - 1)) : ℝ) : ℂ) := by
  have ha0 : (a - 1 : ℝ) ≠ 0 := fun h => ha (by linarith)
  have hrw : ∀ y : ℝ, ((a : ℂ) + (y : ℝ) * Complex.I) - 1
      = ((a - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
    intro y; push_cast; ring
  have heq : (∫ y : ℝ in (-T)..T, (((a : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T, (((a - 1 : ℝ) : ℂ) + (y : ℝ) * Complex.I)⁻¹ :=
    intervalIntegral.integral_congr (fun y _ => by rw [hrw y])
  rw [intervalIntegral.integral_const_mul, heq, integral_vertical_pole ha0]

/-- **The left-edge divided difference, with its pole term extracted.** -/
theorem integral_dslope_mellin_left_eq {N H : ℝ} (hH : 0 < H) {c T : ℝ} (hc0 : 0 < c)
    (hc : c ≠ 1) :
    (∫ y : ℝ in (-T)..T, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)
            * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * ((2 * Real.arctan (T / (c - 1)) : ℝ) : ℂ) := by
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hc0
  have hlin : Continuous fun y : ℝ => ((c : ℂ) + (y : ℝ) * Complex.I) - 1 := by fun_prop
  have hinv : Continuous fun y : ℝ => (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ :=
    hlin.inv₀ fun y => sub_one_ne_zero_line_of_ne hc
  have hf : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
        * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ := hWcont.mul hinv
  have hg : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
        * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ := continuous_const.mul hinv
  have hpt : ∀ y : ℝ, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
      ((c : ℂ) + (y : ℝ) * Complex.I)
      = mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I)
          * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
          * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ := by
    intro y
    have hne : ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 1 :=
      fun h => sub_one_ne_zero_line_of_ne (y := y) hc (by rw [h]; ring)
    have hsplit := mellin_div_sub_one_split (N := N) (H := H) hne
    rw [show mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)
        * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
        = (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I) by ring, hsplit]
    ring
  have hcongr : (∫ y : ℝ in (-T)..T,
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((c : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ in (-T)..T,
        (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
            * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
          - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹) :=
    intervalIntegral.integral_congr (fun y _ => hpt y)
  rw [hcongr, intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), integral_pole_term_line_of_ne hc]

end RHTower.Sieve
