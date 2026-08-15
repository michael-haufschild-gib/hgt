import GaloisForLFunctions.RHTower.GaussCubicOuterDefect
import GaloisForLFunctions.RHTower.GaussConvolutionCoefficient

/-!
# Harmonic convolution kernel of the squared prime scale

The cubic outer defect contains multiplication by `B²`.  Treating it as one piecewise-exponential
multiplier avoids an artificial extra convolution variable and gives the sharp harmonic kernel
`2p²/(1+|j|)`.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions

noncomputable section

/-- Squared prime-scale symbol on the circle. -/
def gaussPrimeScaleSqCircle (p : ℝ) (z : AddCircle (1 : ℝ)) : ℂ :=
  gaussPrimeScaleCircle p z * gaussPrimeScaleCircle p z

theorem measurable_gaussPrimeScaleSqCircle (p : ℝ) :
    Measurable (gaussPrimeScaleSqCircle p) :=
  (measurable_gaussPrimeScaleCircle p).mul (measurable_gaussPrimeScaleCircle p)

theorem gaussPrimeScaleSqCircle_real (p : ℝ) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (gaussPrimeScaleSqCircle p z) = gaussPrimeScaleSqCircle p z := by
  simp only [gaussPrimeScaleSqCircle, map_mul, gaussPrimeScaleCircle_real]

theorem norm_gaussPrimeScaleSqCircle_le {p : ℝ} (hp : 1 < p)
    (z : AddCircle (1 : ℝ)) :
    ‖gaussPrimeScaleSqCircle p z‖ ≤ p := by
  rw [gaussPrimeScaleSqCircle, norm_mul]
  have hB := norm_gaussPrimeScaleCircle_le hp z
  have hsqrt : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  nlinarith [norm_nonneg (gaussPrimeScaleCircle p z), Real.sqrt_nonneg p]

/-- `B²` bundled as one multiplier. -/
def gaussPrimeScaleSqBlock {p : ℝ} (hp : 1 < p) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  MeasureTheory.lpBoundedMulCLM (measurable_gaussPrimeScaleSqCircle p)
    (by linarith : 0 ≤ p) (norm_gaussPrimeScaleSqCircle_le hp)

theorem gaussPrimeScaleSqBlock_apply {p : ℝ} (hp : 1 < p)
    (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussPrimeScaleSqBlock hp u = gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp u) := by
  refine Lp.ext ?_
  refine (MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ u).trans ?_
  refine Filter.EventuallyEq.trans ?_ (gaussPrimeScaleBlock_coeFn hp (gaussPrimeScaleBlock hp u)).symm
  filter_upwards [gaussPrimeScaleBlock_coeFn hp u] with z hz
  rw [hz, gaussPrimeScaleSqCircle]
  ring

/-- The squared scale is a single exponential piece of exponent `-log p`. -/
theorem isExpPiecewise_gaussPrimeScaleSqCircle {p : ℝ} (hp : 1 < p) :
    IsExpPiecewise (-Real.log p) 1 (fun i => if i = 0 then 0 else 1)
      (fun _ => ((p : ℝ) : ℂ)) (gaussPrimeScaleSqCircle p) where
  base := by norm_num
  top := by norm_num
  mono := by intro i hi; interval_cases i; norm_num
  nonneg := by intro i hi; interval_cases i; norm_num
  le_one := by intro i hi; interval_cases i; norm_num
  eq := by
    intro i hi x hx
    interval_cases i
    norm_num at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hval : gaussPrimeScaleCircle p ((x : ℝ) : AddCircle (1 : ℝ)) =
        (gaussPrimeScale p x : ℂ) := gaussPrimeScaleCircle_coe ⟨hx0, hx1.le⟩
    rw [gaussPrimeScaleSqCircle, hval, gaussPrimeScale_eq_expPiece (by linarith : 0 < p)]
    have hs : ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) = (p : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (by linarith)
    calc
      ((Real.sqrt p : ℂ) * Complex.exp ((-(Real.log p / 2) : ℝ) * (x : ℂ))) *
          ((Real.sqrt p : ℂ) * Complex.exp ((-(Real.log p / 2) : ℝ) * (x : ℂ))) =
        ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) *
          (Complex.exp ((-(Real.log p / 2) : ℝ) * (x : ℂ)) *
            Complex.exp ((-(Real.log p / 2) : ℝ) * (x : ℂ))) := by ring
      _ = (p : ℂ) * Complex.exp
          (((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ) +
            (((-(Real.log p / 2) : ℝ) : ℂ) * (x : ℂ))) := by
        rw [hs, Complex.exp_add]
      _ = (p : ℂ) * Complex.exp (((-Real.log p : ℝ) : ℂ) * (x : ℂ)) := by
        congr 2
        push_cast
        ring

/-- Harmonic kernel bound for `B²`. -/
theorem norm_fourierCoeff_gaussPrimeScaleSqCircle_le {p : ℝ} (hp : 1 < p) (x : ℤ) :
    ‖fourierCoeff (gaussPrimeScaleSqCircle p) x‖ ≤
      2 * p ^ 2 / (1 + (x.natAbs : ℝ)) := by
  have hM : ∀ i : ℕ, ‖((p : ℝ) : ℂ)‖ ≤ p := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hbound := norm_fourierCoeff_of_isExpPiecewise
    (isExpPiecewise_gaussPrimeScaleSqCircle hp) (by positivity) hM x
  refine hbound.trans (le_of_eq ?_)
  have habs : |-Real.log p| = Real.log p := by rw [abs_neg, abs_of_pos (Real.log_pos hp)]
  rw [habs, Real.exp_log (by linarith : 0 < p)]
  push_cast
  ring

/-- Coefficient convolution bound for multiplication by `B²`. -/
theorem norm_fourierCoeff_gaussPrimeScaleSqBlock_le {p : ℝ} (hp : 1 < p)
    (w : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) (j : ℤ) :
    ‖fourierCoeff ((gaussPrimeScaleSqBlock hp w : AddCircle (1 : ℝ) → ℂ)) j‖ ≤
      ∑' l : ℤ, 2 * p ^ 2 / (1 + ((l - j).natAbs : ℝ)) *
        ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖ := by
  have hsum := hasSum_fourierCoeff_lpBoundedMulCLM
    (measurable_gaussPrimeScaleSqCircle p) (by linarith : 0 ≤ p)
    (norm_gaussPrimeScaleSqCircle_le hp) (gaussPrimeScaleSqCircle_real p) w j
  have hmaj : Summable (fun l : ℤ =>
      ‖starRingEnd ℂ (fourierCoeff (gaussPrimeScaleSqCircle p) (l - j)) *
        fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) := by
    have hbase := summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => ‖fourierCoeff (gaussPrimeScaleSqCircle p) x‖) (A := 2 * p ^ 2)
      (fun x => norm_nonneg _) (fun x => norm_fourierCoeff_gaussPrimeScaleSqCircle_le hp x) w j
    refine hbase.congr fun l => ?_
    rw [norm_mul, RCLike.norm_conj]
  have heq : fourierCoeff ((gaussPrimeScaleSqBlock hp w : AddCircle (1 : ℝ) → ℂ)) j =
      ∑' l : ℤ, starRingEnd ℂ (fourierCoeff (gaussPrimeScaleSqCircle p) (l - j)) *
        fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l := hsum.tsum_eq.symm
  rw [heq]
  refine (norm_tsum_le_tsum_norm hmaj).trans ?_
  have hterm : Summable (fun l : ℤ => 2 * p ^ 2 / (1 + ((l - j).natAbs : ℝ)) *
      ‖fourierCoeff ((w : AddCircle (1 : ℝ) → ℂ)) l‖) :=
    summable_harmonicKernel_mul_fourierCoeff
      (κ := fun x => 2 * p ^ 2 / (1 + (x.natAbs : ℝ))) (A := 2 * p ^ 2)
      (fun x => by positivity) (fun x => le_rfl) w j
  refine hmaj.tsum_le_tsum (fun l => ?_) hterm
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right
    (norm_fourierCoeff_gaussPrimeScaleSqCircle_le hp (l - j)) (norm_nonneg _)

end

end RHTower
