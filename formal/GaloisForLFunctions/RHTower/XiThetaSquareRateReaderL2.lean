import GaloisForLFunctions.RHTower.XiThetaSquareRateReaderNorm
import GaloisForLFunctions.HTGeometry.HalfLineExponentialResidualLimit

/-!
# The source-side `L²` reader of the theta square rates

The canonical biorthogonal reader of the half-line exponential system of the physical heat rates
`λ_k = π (k+1)²` has the exact norm predicted by the theta square-rate card,

`‖r_n‖ = √(2/π) · sinh (π (n+1))`,

and its Laplace pairings with the heat exponentials are the Kronecker delta.  The coefficient
functional of the card is the reader pairing rescaled by `exp (λ_n)`.
-/

open Filter Topology MeasureTheory
open scoped InnerProductSpace
open InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem sinh_heatRate_pos (n : ℕ) : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
  have hx : (0 : ℝ) < Real.pi * ((n : ℝ) + 1) := by positivity
  have h0 : Real.sinh 0 < Real.sinh (Real.pi * ((n : ℝ) + 1)) := Real.sinh_lt_sinh.mpr hx
  rwa [Real.sinh_zero] at h0

/-- **The exact co-distance of the theta square-rate system.** -/
theorem norm_expResidual_heatRate (n : ℕ) :
    ‖expResidual heatRateSeq heatRateSeq_pos n‖ =
      Real.sqrt (Real.pi / 2) / Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
  have hsinhpos := sinh_heatRate_pos n
  have hnorm := tendsto_normSq_gramSchmidt_heatRate n
  have hsqrt : Tendsto
      (fun N : ℕ => ‖gramSchmidt ℂ
        (expSystem (fun k => heatRateSeq (coIdx n N k)) (fun _ => heatRateSeq_pos _)) N‖)
      atTop (nhds (Real.sqrt (Real.pi / (2 * Real.sinh (Real.pi * ((n : ℝ) + 1)) ^ 2)))) := by
    have hcomp := (Real.continuous_sqrt.tendsto _).comp hnorm
    rw [Function.comp_def] at hcomp
    refine hcomp.congr (fun N => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  have hres := norm_expResidual_eq_of_tendsto heatRateSeq_pos hsqrt
  rw [hres]
  have hsplit : Real.pi / (2 * Real.sinh (Real.pi * ((n : ℝ) + 1)) ^ 2) =
      (Real.pi / 2) / (Real.sinh (Real.pi * ((n : ℝ) + 1))) ^ 2 := by
    field_simp
  rw [hsplit, Real.sqrt_div (by positivity), Real.sqrt_sq (le_of_lt hsinhpos)]

theorem expResidual_heatRate_ne_zero (n : ℕ) :
    expResidual heatRateSeq heatRateSeq_pos n ≠ 0 := by
  intro h
  have hval := norm_expResidual_heatRate n
  rw [h, norm_zero] at hval
  have hpos : 0 < Real.sqrt (Real.pi / 2) / Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
    have := sinh_heatRate_pos n
    have hs : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [← hval] at hpos
  exact lt_irrefl 0 hpos

/-- The canonical source-side reader of the `n`-th theta square rate. -/
def thetaSquareRateReader (n : ℕ) : Lp ℂ 2 halfLineLaplaceMeasure :=
  expReader heatRateSeq heatRateSeq_pos n

/-- **Equation `(4)`.**  The reader pairs with the heat exponentials as a Kronecker delta. -/
theorem inner_expSystem_thetaSquareRateReader (n m : ℕ) :
    inner ℂ (expSystem heatRateSeq heatRateSeq_pos m) (thetaSquareRateReader n) =
      if m = n then 1 else 0 :=
  inner_expSystem_expReader heatRateSeq_pos (expResidual_heatRate_ne_zero n) m

/-- **Equation `(3)`.**  The exact reader norm. -/
theorem norm_thetaSquareRateReader (n : ℕ) :
    ‖thetaSquareRateReader n‖ =
      Real.sqrt (2 / Real.pi) * Real.sinh (Real.pi * ((n : ℝ) + 1)) := by
  have hsinhpos := sinh_heatRate_pos n
  have hs : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr (by positivity)
  rw [thetaSquareRateReader,
    norm_expReader heatRateSeq_pos (expResidual_heatRate_ne_zero n),
    norm_expResidual_heatRate]
  have hinv : (Real.sqrt (Real.pi / 2))⁻¹ = Real.sqrt (2 / Real.pi) := by
    rw [← Real.sqrt_inv]
    congr 1
    rw [inv_div]
  rw [inv_div, div_eq_mul_inv, hinv, mul_comm]

/-- **Equation `(2)`, canonicity.**  The reader is the unique biorthogonal element of the closed
span of the heat exponential system. -/
theorem thetaSquareRateReader_unique {n : ℕ} {r : Lp ℂ 2 halfLineLaplaceMeasure}
    (hr : r ∈ expFullSpan heatRateSeq heatRateSeq_pos)
    (h : ∀ m, inner ℂ (expSystem heatRateSeq heatRateSeq_pos m) r =
      if m = n then 1 else 0) :
    r = thetaSquareRateReader n := by
  refine eq_of_inner_expSystem_eq heatRateSeq_pos hr
    (expReader_mem_expFullSpan heatRateSeq_pos n) (fun m => ?_)
  rw [h m, thetaSquareRateReader] at *
  exact (inner_expSystem_expReader heatRateSeq_pos (expResidual_heatRate_ne_zero n) m).symm

/-- **Equation `(5)`.**  The fixed-index coefficient functional of the card. -/
def thetaSquareRateCoefficient (n : ℕ) (f : Lp ℂ 2 halfLineLaplaceMeasure) : ℂ :=
  Complex.exp ((heatRateSeq n : ℂ)) * inner ℂ (thetaSquareRateReader n) f

end

end RHTower
