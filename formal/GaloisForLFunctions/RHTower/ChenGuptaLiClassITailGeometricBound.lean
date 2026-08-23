import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailPrefixes
import GaloisForLFunctions.RHTower.MobiusExponentialGibbsBoundary

/-!
# Chen--Gupta--Li smoothed detector: explicit finite-tail control

The shifted detector coefficients have a universal norm bound.  Exponential smoothing therefore
turns the difference between the infinite Class-I profile and its first `K` terms into an exact
geometric remainder, uniformly in mollifier length, conductor, character, and detector shift.

At the source scale `x = 1 / (Y + 1)` and the paper's cutoff
`K = ceil ((Y + 1) log^2 (Y + 1))`, the remainder is at most
`2 C (Y + 1) exp (-log^2 (Y + 1))`, hence tends to zero.  This supplies the quantitative
coefficient-tail truncation used before the Class-I/Class-II split in CGL Section 12.1.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem exists_cglShiftedDetectorTail_geometric_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
      (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (K : ℕ),
      ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1 -
          cglShiftedDetectorTailPartialProfile X q χ s x K‖ ≤
        C * Real.exp (-((K : ℝ) * x.1)) / (1 - Real.exp (-x.1)) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_cglShiftedDetectorTailCoefficient_uniformBound
  refine ⟨C, hC, ?_⟩
  intro X q χ s x K
  let f : ℕ → ℂ := fun n => cglShiftedDetectorTailCoefficient X q χ s n *
    Complex.exp (-((n : ℝ) * x.1 : ℝ))
  have hsum : Summable f := summable_cglShiftedDetectorTailCoefficient_laplace X q χ s x
  have hshift : Summable (fun n : ℕ => f (n + K)) :=
    hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have htailEq :
      coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s) x.1 -
          cglShiftedDetectorTailPartialProfile X q χ s x K =
        ∑' n : ℕ, f (n + K) := by
    have hsplit := hsum.sum_add_tsum_nat_add K
    unfold coeffLaplaceProfile cglShiftedDetectorTailPartialProfile
    change (∑' n : ℕ, f n) - ∑ n ∈ Finset.range K, f n = ∑' n : ℕ, f (n + K)
    rw [← hsplit]
    abel
  have hterm : ∀ n : ℕ, ‖f (n + K)‖ ≤
      C * Real.exp (-(((n + K : ℕ) : ℝ) * x.1)) := by
    intro n
    dsimp [f]
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_right (hcoeff X q χ s (n + K)) (Real.exp_pos _).le
  have hmajor : Summable (fun n : ℕ =>
      C * Real.exp (-(((n + K : ℕ) : ℝ) * x.1))) :=
    (summable_exp_neg_nat_mul x.2).comp_injective (fun _ _ h => Nat.add_right_cancel h) |>.mul_left C
  rw [htailEq]
  calc
    ‖∑' n : ℕ, f (n + K)‖ ≤ ∑' n : ℕ, ‖f (n + K)‖ :=
      norm_tsum_le_tsum_norm hshift.norm
    _ ≤ ∑' n : ℕ, C * Real.exp (-(((n + K : ℕ) : ℝ) * x.1)) :=
      hshift.norm.tsum_le_tsum hterm hmajor
    _ = C * (∑' n : ℕ, Real.exp (-(((n + K : ℕ) : ℝ) * x.1))) := by
      rw [tsum_mul_left]
    _ = C * Real.exp (-((K : ℝ) * x.1)) / (1 - Real.exp (-x.1)) := by
      rw [tsum_exp_neg_nat_add x.1 K x.2]
      ring

/-- CGL's source-scale smoothing parameter `x = 1 / (Y + 1)`. -/
def cglClassITailSmoothingScale (Y : ℕ) : CGLPositiveSmoothingScale :=
  ⟨1 / (((Y + 1 : ℕ) : ℝ)), by positivity⟩

/-- CGL's coefficient cutoff `ceil ((Y + 1) log^2 (Y + 1))`. -/
noncomputable def cglClassITailTruncationCutoff (Y : ℕ) : ℕ :=
  Nat.ceil ((((Y + 1 : ℕ) : ℝ)) * Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2)

theorem tendsto_cglClassITail_logSquareMajorant_zero (C : ℝ) :
    Tendsto (fun Y : ℕ =>
      2 * C * (((Y + 1 : ℕ) : ℝ)) *
        Real.exp (-(Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2)))
      atTop (𝓝 0) := by
  have hy : Tendsto (fun Y : ℕ => (((Y + 1 : ℕ) : ℝ))) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun Y : ℕ => Real.log (((Y + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hy
  have hlogSub : Tendsto
      (fun Y : ℕ => Real.log (((Y + 1 : ℕ) : ℝ)) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      hlog.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)) (f := atTop))
  have hgain : Tendsto (fun Y : ℕ =>
      Real.log (((Y + 1 : ℕ) : ℝ)) *
        (Real.log (((Y + 1 : ℕ) : ℝ)) - 1)) atTop atTop :=
    hlog.atTop_mul_atTop₀ hlogSub
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have hscaled := hexp.const_mul (2 * C)
  have hscaled0 : Tendsto (fun Y : ℕ =>
      2 * C * Real.exp (-(Real.log (((Y + 1 : ℕ) : ℝ)) *
        (Real.log (((Y + 1 : ℕ) : ℝ)) - 1)))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaled0.congr'
  exact Filter.Eventually.of_forall (fun Y => by
    have hypos : 0 < (((Y + 1 : ℕ) : ℝ)) := by positivity
    symm
    calc
      2 * C * (((Y + 1 : ℕ) : ℝ)) *
            Real.exp (-(Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2)) =
          2 * C * (Real.exp (Real.log (((Y + 1 : ℕ) : ℝ))) *
            Real.exp (-(Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2))) := by
        rw [Real.exp_log hypos]
        ring
      _ = 2 * C * Real.exp
          (Real.log (((Y + 1 : ℕ) : ℝ)) -
            Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2) := by
        rw [← Real.exp_add]
        congr 2
      _ = 2 * C * Real.exp
          (-(Real.log (((Y + 1 : ℕ) : ℝ)) *
            (Real.log (((Y + 1 : ℕ) : ℝ)) - 1))) := by
        congr 2
        ring)

theorem exists_cglShiftedDetectorTail_source_truncation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
      (s : CGLRightHalfPlanePoint) (Y : ℕ),
      ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s)
            (cglClassITailSmoothingScale Y).1 -
          cglShiftedDetectorTailPartialProfile X q χ s
            (cglClassITailSmoothingScale Y) (cglClassITailTruncationCutoff Y)‖ ≤
        2 * C * (((Y + 1 : ℕ) : ℝ)) *
          Real.exp (-(Real.log (((Y + 1 : ℕ) : ℝ)) ^ 2)) := by
  obtain ⟨C, hC, htail⟩ := exists_cglShiftedDetectorTail_geometric_bound
  refine ⟨C, hC, ?_⟩
  intro X q χ s Y
  let y : ℝ := (((Y + 1 : ℕ) : ℝ))
  have hy : 0 < y := by dsimp [y]; positivity
  have hx : (cglClassITailSmoothingScale Y).1 = 1 / y := by rfl
  have hxOne : (1 / y : ℝ) ≤ 1 := by
    rw [div_le_one hy]
    dsimp [y]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : Y + 1 ≠ 0)
  have hden : (1 / y) / 2 ≤ 1 - Real.exp (-(1 / y)) :=
    half_mul_le_one_sub_exp_neg (by positivity) hxOne
  have hdenPos : 0 < 1 - Real.exp (-(1 / y)) :=
    lt_of_lt_of_le (by positivity) hden
  have hceil : y * Real.log y ^ 2 ≤ (cglClassITailTruncationCutoff Y : ℝ) := by
    exact Nat.le_ceil _
  have hscale : Real.log y ^ 2 ≤ (cglClassITailTruncationCutoff Y : ℝ) * (1 / y) := by
    calc
      Real.log y ^ 2 = (y * Real.log y ^ 2) * (1 / y) := by field_simp
      _ ≤ (cglClassITailTruncationCutoff Y : ℝ) * (1 / y) :=
        mul_le_mul_of_nonneg_right hceil (by positivity)
  have hnum : Real.exp (-((cglClassITailTruncationCutoff Y : ℝ) * (1 / y))) ≤
      Real.exp (-(Real.log y ^ 2)) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hscale)
  have hbase := htail X q χ s (cglClassITailSmoothingScale Y)
    (cglClassITailTruncationCutoff Y)
  rw [hx] at hbase
  refine hbase.trans ?_
  rw [div_le_iff₀ hdenPos]
  calc
    C * Real.exp (-((cglClassITailTruncationCutoff Y : ℝ) * (1 / y))) ≤
        C * Real.exp (-(Real.log y ^ 2)) :=
      mul_le_mul_of_nonneg_left hnum hC.le
    _ = (2 * C * y * Real.exp (-(Real.log y ^ 2))) * ((1 / y) / 2) := by
      field_simp
    _ ≤ (2 * C * y * Real.exp (-(Real.log y ^ 2))) *
        (1 - Real.exp (-(1 / y))) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

theorem cglShiftedDetectorTail_source_truncation_tendsto_zero :
    ∀ (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
      (s : CGLRightHalfPlanePoint),
      Tendsto (fun Y : ℕ =>
        ‖coeffLaplaceProfile (cglShiftedDetectorTailCoefficient X q χ s)
              (cglClassITailSmoothingScale Y).1 -
            cglShiftedDetectorTailPartialProfile X q χ s
              (cglClassITailSmoothingScale Y) (cglClassITailTruncationCutoff Y)‖)
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_cglShiftedDetectorTail_source_truncation_bound
  intro X q χ s
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun Y => hbound X q χ s Y))
    (tendsto_cglClassITail_logSquareMajorant_zero C)

end RHTower
