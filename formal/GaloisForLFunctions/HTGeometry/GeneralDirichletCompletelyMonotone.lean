import GaloisForLFunctions.HTGeometry.GeneralDirichletLandau
import GaloisForLFunctions.HTGeometry.CompletelyMonotoneTower
import GaloisForLFunctions.HTGeometry.AtomicHausdorffSource

/-!
# Completely monotone extension forces convergence everywhere

A general Dirichlet series with nonnegative coefficients and distinct nonnegative frequencies
converges on a half line.  If its germ there extends to a finite completely monotone function on
the whole positive axis, the series already converges at every positive shape.

The mechanism is Hausdorff rather than Bernstein.  Sampling the completely monotone extension on
the arithmetic progression `θ₀ + n` produces a completely monotone sequence, hence a finite source
on `[0,1]`.  Far out on the progression the sample is the power sum of the atomic family with
nodes `exp (-λⱼ)` and weights `aⱼ exp (-θ₀ λⱼ)`, so a power tilt of the source is that atomic
measure; reading its atoms recovers the weights, and finiteness of the source bounds their sum.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- **Landau for completely monotone extensions.**  A nonnegative general Dirichlet series whose
safe germ extends to a finite completely monotone function on `(0,∞)` converges at every positive
shape. -/
theorem summable_gdTwistTerm_of_completelyMonotoneTower [Countable ι] {a lam : ι → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j) (hinj : Function.Injective lam)
    {σ₁ : ℝ} (hsum : ∀ θ : ℝ, σ₁ < θ → Summable (gdTwistTerm a lam θ 0))
    {F : ℕ → ℝ → ℝ} (hF : CompletelyMonotoneTower F)
    (hagree : ∀ θ : ℝ, σ₁ < θ → F 0 θ = gdRealSeries a lam θ)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    Summable (gdTwistTerm a lam θ₀ 0) := by
  classical
  obtain ⟨x, hxval⟩ : ∃ x : ι → HausdorffSourceSpace, ∀ j, (x j : ℝ) = Real.exp (-lam j) :=
    ⟨fun j => ⟨Real.exp (-lam j), Set.mem_Icc.mpr
        ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith [hlam j])⟩⟩, fun _ => rfl⟩
  have hx0 : ∀ j, 0 < (x j : ℝ) := fun j => by rw [hxval]; exact Real.exp_pos _
  have hxinj : Function.Injective x := by
    intro i j hij
    have h := congrArg (fun y : HausdorffSourceSpace => (y : ℝ)) hij
    rw [hxval, hxval] at h
    have := Real.exp_eq_exp.mp h
    exact hinj (by linarith)
  set B : ι → ℝ := fun j => a j * Real.exp (-(θ₀ * lam j)) with hB_def
  have hBnn : ∀ j, 0 ≤ B j := fun j => mul_nonneg (ha j) (Real.exp_pos _).le
  have hpow : ∀ (j : ι) (n : ℕ), B j * (x j : ℝ) ^ n = gdTwistTerm a lam (θ₀ + n) 0 j := by
    intro j n
    rw [hB_def, hxval, gdTwistTerm, pow_zero, mul_one, ← Real.exp_nat_mul]
    show a j * Real.exp (-(θ₀ * lam j)) * Real.exp ((n : ℝ) * -lam j) =
      a j * Real.exp (-((θ₀ + (n : ℝ)) * lam j))
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hcm : HausdorffCompletelyMonotone (fun n : ℕ => F 0 (θ₀ + n * 1)) :=
    fun m k => fwdDiff_one_sample_alternating hF hθ₀ one_pos m k
  obtain ⟨μ, hμfin, hμmom⟩ := exists_hausdorffSource_of_completelyMonotone hcm
  haveI := hμfin
  obtain ⟨N, hN⟩ := exists_nat_gt σ₁
  have hNlt : ∀ m : ℕ, σ₁ < θ₀ + ((N + m : ℕ) : ℝ) := by
    intro m
    have hle : (N : ℝ) ≤ ((N + m : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N m
    linarith
  have hsumN : Summable (fun j => B j * (x j : ℝ) ^ N) := by
    refine (hsum (θ₀ + (N : ℝ)) (by linarith)).congr (fun j => ?_)
    exact (hpow j N).symm
  have hmom : ∀ m : ℕ, hausdorffMoment μ (N + m) = ∑' j, B j * (x j : ℝ) ^ (N + m) := by
    intro m
    have hval : hausdorffMoment μ (N + m) = F 0 (θ₀ + ((N + m : ℕ) : ℝ)) := by
      rw [hμmom]; norm_num
    rw [hval, hagree _ (hNlt m), gdRealSeries]
    exact tsum_congr (fun j => (hpow j (N + m)).symm)
  have hBsum : Summable B :=
    summable_of_hausdorffMoment_eq_atomic hBnn hx0 hxinj hsumN hmom
  refine hBsum.congr (fun j => ?_)
  rw [hB_def, gdTwistTerm, pow_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
