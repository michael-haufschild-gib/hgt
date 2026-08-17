import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistShiftedBound
import GaloisForLFunctions.RHTower.Sieve.VerticalMassSharp

/-!
# The left edge of the twisted contour

The divided difference at the twist pole is holomorphic, so it shifts to the left edge with no
residue — but, exactly as in the untwisted case, it is not *small* there, because it still carries
the pole term:

    dslope W (1-iτ) s  =  W(s)/(s+iτ-1) - W(1-iτ)/(s+iτ-1),

and on `Re s = c < 1` the second summand integrates to `-W(1-iτ)·twistMainFactor c T τ`, whose real
part tends to `+π·W(1-iτ)`.  Together with the `π·W(1-iτ)` supplied by the right line this is the
`2π·W(1-iτ)` demanded by the residue theorem.

After the extraction what is left on the left edge is `∫ W(c+iy)/(c-1+i(y+τ)) dy`, and the pole
factor there is bounded by `(1-c)⁻¹` *uniformly in the twist*: the twist moves the pole vertically
only, so its horizontal distance to the edge is the untwisted one.  That uniformity is the whole
reason the twisted contour costs nothing extra on the left.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- A vertical line off the abscissa `1` never meets the twist pole, whatever the twist: the twist
moves the pole vertically, and the two real parts already differ. -/
theorem line_ne_twistPole_of_ne {c y τ : ℝ} (hc : c ≠ 1) :
    ((c : ℂ) + (y : ℝ) * Complex.I) ≠ twistPole τ := by
  intro h
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
  rw [h, twistPole_re] at hre
  exact hc hre.symm

/-- The shifted linear factor is nonzero on every line off the abscissa `1`. -/
theorem sub_twistPole_ne_zero_line_of_ne {c y τ : ℝ} (hc : c ≠ 1) :
    (c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 ≠ 0 := by
  rw [← sub_twistPole]
  exact sub_ne_zero.2 (line_ne_twistPole_of_ne hc)

/-- **The twisted pole term on any line off the abscissa `1`.**  The closed form of the truncated
pole integral does not care which side of the abscissa the line lies on; only `c ≠ 1` is used. -/
theorem integral_twist_pole_term_line_of_ne {N H : ℝ} {c T τ : ℝ} (hc : c ≠ 1) :
    (∫ y : ℝ in (-T)..T,
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
          * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
      = mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
          * twistMainFactor c T τ := by
  have hα : (c - 1 : ℝ) ≠ 0 := fun h => hc (by linarith)
  have hrw : ∀ y : ℝ, (c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1
      = (((c - 1 : ℝ)) : ℂ) + ((y + τ : ℝ)) * Complex.I := by
    intro y
    push_cast
    ring
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_congr
      (g := fun y : ℝ => ((((c - 1 : ℝ)) : ℂ) + ((y + τ : ℝ)) * Complex.I)⁻¹)
      (fun y _ => by rw [hrw y]),
    integral_vertical_pole_shift hα, twistMainFactor]

/-- **The left-edge divided difference, with its twisted pole term extracted.** -/
theorem integral_dslope_mellin_twist_left_eq {N H : ℝ} (hH : 0 < H) {c T τ : ℝ} (hc0 : 0 < c)
    (hc : c ≠ 1) :
    (∫ y : ℝ in (-T)..T,
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ y : ℝ in (-T)..T,
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
              * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * twistMainFactor c T τ := by
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hc0
  have hlin : Continuous fun y : ℝ =>
      (c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 := by fun_prop
  have hinv : Continuous fun y : ℝ =>
      ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ :=
    hlin.inv₀ fun y => sub_twistPole_ne_zero_line_of_ne hc
  have hf : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
        * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ := hWcont.mul hinv
  have hg : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
        * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ := continuous_const.mul hinv
  have hpt : ∀ y : ℝ,
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((c : ℂ) + (y : ℝ) * Complex.I)
        = mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
            * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ := by
    intro y
    rw [dslope_of_ne _ (line_ne_twistPole_of_ne (τ := τ) hc), slope_def_field, sub_twistPole,
      div_eq_mul_inv, sub_mul]
  rw [intervalIntegral.integral_congr (fun y _ => hpt y),
    intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    integral_twist_pole_term_line_of_ne hc]

/-- The twisted pole factor is bounded on a line left of the abscissa `1`, uniformly in the twist:
the twist is purely imaginary and the real part alone already gives the distance. -/
theorem norm_inv_sub_twistPole_line_le {c y τ : ℝ} (hc : c < 1) :
    ‖((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹‖ ≤ (1 - c)⁻¹ := by
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1).re = c - 1 := by simp
  have hge : (1 - c : ℝ)
      ≤ ‖(c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)
    rw [hre, abs_of_nonpos (by linarith)] at h
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hge

/-- **The pole-free left edge of the twisted contour.**  Once the pole term is extracted the edge is
controlled by the vertical mass of the cutoff's transform alone, with the twist entering only
through the constant `(1-c)⁻¹` — which is twist-independent. -/
theorem norm_integral_left_vertical_twist_pole_free_le {N H c T C τ : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc0 : 0 < c) (hc : c < 1) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ y : ℝ in (-T)..T,
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
          * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹‖
      ≤ (1 - c)⁻¹ * (2 * ((N + H) ^ c / c) + 2 * C) := by
  have hcongr : (∫ y : ℝ in (-T)..T,
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
          * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
      = ∫ y : ℝ in (-T)..T,
          (fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹) ((c : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I) :=
    intervalIntegral.integral_congr (fun y _ => by dsimp only; ring)
  rw [hcongr]
  refine norm_integral_vertical_edge_le hN hH hc0 hT (inv_nonneg.2 (by linarith)) hbd
    (F := fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹) ?_ ?_
  · have hlin : Continuous fun y : ℝ =>
        (c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 := by fun_prop
    exact (hlin.inv₀ fun y => sub_twistPole_ne_zero_line_of_ne hc.ne).continuousOn
  · exact fun y _ => norm_inv_sub_twistPole_line_le hc

end RHTower.Sieve
