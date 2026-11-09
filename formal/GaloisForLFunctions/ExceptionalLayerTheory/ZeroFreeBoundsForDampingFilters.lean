import GaloisForLFunctions.ExceptionalLayerTheory.EulerBoundsForDampingFilters
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodArbitraryConstant
import GaloisForLFunctions.RHTower.MoebiusAbelSmoothedSaving
import GaloisForLFunctions.RHTower.KuznetsovWhittakerStripBounds
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Zero-free-region bounds for the filtered prime current

A local shift of the Mellin contour uses only zeta heights comparable to the
observation height. The filter retains its spacing gain along every edge.
-/

open Complex Filter Set Topology MeasureTheory RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Polynomial weights preserve an exponential Gaussian Mellin envelope,
uniformly on every closed strip of positive real parts. -/
theorem exists_weighted_gaussianMBKernel_strip_envelope {l u : ℝ}
    (hl : 0 < l) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y x v : ℝ, 0 < y → l ≤ x → x ≤ u →
      ‖gaussianMBKernel y ((x : ℂ) + v * I)‖ * (1 + |v|) ^ n ≤
        C * y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by
  obtain ⟨A, M, hA, hb⟩ :=
    GaloisForLFunctions.RHTower.DeckPointPair.exists_bound_norm_Gamma_strip_all
      (a := l / 2) (b := u / 2) (by positivity)
  let δ : ℝ := Real.pi / 4 - 1 / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [Real.pi_gt_three]
  let D : ℝ := Real.exp δ * ((M + n).factorial : ℝ) / δ ^ (M + n)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨A / 2 * D + 1, by positivity, ?_⟩
  intro y x v hy hx1 hx2
  have hg := hb (x / 2) (v / 2) (by linarith only [hx1]) (by linarith only [hx2])
  have hv : |v / 2| ≤ |v| := by rw [abs_div, abs_two]; linarith only [abs_nonneg v]
  have hg' : ‖Complex.Gamma (((x / 2 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I)‖ ≤
      A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|)) := by
    have he : -(Real.pi * |v / 2| / 2) = -(Real.pi / 4 * |v|) := by
      rw [abs_div, abs_two]
      ring
    rw [he] at hg
    exact hg.trans (by gcongr)
  have hp : (1 + |v|) ^ (M + n) * Real.exp (-(δ * |v|)) ≤ D := by
    have hh := HTGeometry.pow_mul_exp_neg_le hδ (M + n)
      (by positivity : 0 ≤ 1 + |v|)
    calc
      _ = Real.exp δ * ((1 + |v|) ^ (M + n) * Real.exp (-(δ * (1 + |v|)))) := by
        rw [mul_left_comm, ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp δ * (((M + n).factorial : ℝ) / δ ^ (M + n)) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ = D := by dsimp only [D]; ring
  have he : Real.exp (-(Real.pi / 4 * |v|)) =
      Real.exp (-(δ * |v|)) * Real.exp (-(|v| / 2)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [δ]
    ring
  rw [norm_gaussianMBKernel_line hy]
  calc
    _ ≤ 1 / 2 * (A * (1 + |v|) ^ M * Real.exp (-(Real.pi / 4 * |v|))) *
        y ^ (-(x / 2)) * (1 + |v|) ^ n := by gcongr
    _ = (A / 2 * ((1 + |v|) ^ (M + n) * Real.exp (-(δ * |v|)))) *
        y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by rw [he, pow_add]; ring
    _ ≤ (A / 2 * D) * y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by gcongr
    _ ≤ _ := by gcongr; linarith

/-- The whole divisor filter and Gamma kernel have a common strip envelope.
The spacing loss is exactly the number of filter factors. -/
theorem exists_divisorFilter_kernel_strip_envelope (F : Finset XiZeroCopy)
    (ρ : ℂ) (σ β l u : ℝ) (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ y h t x v : ℝ,
      0 < y → 0 ≤ h → h ≤ 1 → l ≤ x → x ≤ u →
      ‖(divisorDampingFilter F ρ β h).eval
          (Complex.exp ((h : ℂ) *
            ((((σ : ℂ) + t * I) + ((x : ℂ) + v * I)) - β))) *
        gaussianMBKernel y ((x : ℂ) + v * I)‖ ≤
      C * h ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
        (1 + |t|) ^ (1 + (F.filter (fun q => xiZero q ≠ ρ)).card) *
          y ^ (-(x / 2)) * Real.exp (-(|v| / 2)) := by
  classical
  let d := 1 + (F.filter (fun q => xiZero q ≠ ρ)).card
  obtain ⟨B, hB, hb⟩ := exists_divisorDampingFilter_strip_bound F ρ β (|σ| + |u|)
  obtain ⟨A, hA, hgauss⟩ := exists_weighted_gaussianMBKernel_strip_envelope (u := u) hl d
  refine ⟨B ^ d * A, by positivity, ?_⟩
  intro y h t x v hy hh hh1 hx1 hx2
  have hx0 : 0 ≤ x := hl.le.trans hx1
  have hreal : |σ + x| ≤ |σ| + |u| := by
    calc
      _ ≤ |σ| + |x| := abs_add_le _ _
      _ = |σ| + x := by rw [abs_of_nonneg hx0]
      _ ≤ |σ| + |u| := add_le_add_left (hx2.trans (le_abs_self u)) _
  have hp := hb (σ + x) h t v hreal hh hh1
  have hline : ((σ : ℂ) + t * I) + ((x : ℂ) + v * I) =
      ((σ + x : ℝ) : ℂ) + (t + v) * I := by push_cast; ring
  rw [norm_mul, hline]
  calc
    _ ≤ (h * B * (1 + |t|) * (1 + |v|)) ^ d *
        ‖gaussianMBKernel y ((x : ℂ) + v * I)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = B ^ d * h ^ d * (1 + |t|) ^ d *
        (‖gaussianMBKernel y ((x : ℂ) + v * I)‖ * (1 + |v|) ^ d) := by
      simp only [mul_pow]
      ring
    _ ≤ B ^ d * h ^ d * (1 + |t|) ^ d *
        (A * y ^ (-(x / 2)) * Real.exp (-(|v| / 2))) := by
      gcongr
      exact hgauss y x v hy hx1 hx2
    _ = _ := by ring

end GaloisForLFunctions.ExceptionalLayerTheory
