import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeRowsReadPoleProfiles
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsEulersConstant
import GaloisForLFunctions.HTGeometry.HarmonicQuotientSquareError

/-!
# From a completed prime-row correction to a quasimode

The Mertens remainder, logarithmic floor error, and uniformly vanishing row
correction give a vanishing complementary-quotient majorant. Harmonic averaging
then controls the squared residual of the literal finite prime matrix.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticEffectivityTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- The residual of the finite prime matrix on a profile in the pole gauge. -/
def poleProfileResidual (g : ℕ → ℝ) (κ : ℝ) (N n : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 N, weilPrimeKernel n j * (g j * poleVector j)) -
    (Real.log N - (γ + κ)) * (g n * poleVector n)

/-- A bounded profile with a uniformly vanishing completed row correction has
negligible squared prime-matrix residual at logarithmic scale. -/
theorem tendsto_poleProfileResidual_sq_of_correction
    (g : ℕ → ℝ) (κ B : ℝ) (hg : ∀ n, |g n| ≤ B)
    (T : ℕ → ℝ) (hT : Tendsto T atTop (𝓝 0))
    (hcor : ∀ y n, 0 < n → |poleProfileCorrection g y n + κ * g n| ≤ T y) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, poleProfileResidual g κ N n ^ 2) / Real.log N)
      atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun y => mertensSum y - Real.log y + γ
  let F : ℕ → ℝ := fun y => B * (|e y| + 1 / (y : ℝ)) + T y
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, neg_add_cancel] using tendsto_mertensSum_sub_log.add_const γ
  have hF : Tendsto F atTop (𝓝 0) := by
    have hi := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    simpa only [F, abs_zero, zero_add, mul_zero] using
      ((he.abs.add hi).const_mul B).add hT
  apply HTGeometry.tendsto_harmonicQuotient_square_error hF (poleProfileResidual g κ)
  intro N n hn
  have hn0 : 0 < n := (mem_Icc.mp hn).1
  have hnN : n ≤ N := (mem_Icc.mp hn).2
  let r : ℝ := Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
  have hr : 0 ≤ r ∧ r ≤ 1 / ((N / n : ℕ) : ℝ) := roundoff_le hn0 hnN
  have hid : poleProfileResidual g κ N n =
      ((e (N / n) - r) * g n + (poleProfileCorrection g (N / n) n + κ * g n)) *
        poleVector n := by
    rw [poleProfileResidual, sum_weilPrimeKernel_poleProfile_eq_correction g hn0 hnN]
    dsimp only [e, r]
    ring
  have her : |e (N / n) - r| ≤ |e (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
    calc
      |e (N / n) - r| ≤ |e (N / n)| + |r| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg hr.1]; exact add_le_add le_rfl hr.2
  have hbracket :
      |(e (N / n) - r) * g n + (poleProfileCorrection g (N / n) n + κ * g n)| ≤
        F (N / n) := by
    calc
      _ ≤ |(e (N / n) - r) * g n| +
          |poleProfileCorrection g (N / n) n + κ * g n| := abs_add_le _ _
      _ ≤ (|e (N / n)| + 1 / ((N / n : ℕ) : ℝ)) * B + T (N / n) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul her (hg n) (abs_nonneg _) ((abs_nonneg _).trans her))
          (hcor (N / n) n hn0)
      _ = _ := by dsimp only [F]; ring
  rw [hid, abs_mul, abs_of_nonneg (show 0 ≤ poleVector n by unfold poleVector; positivity)]
  calc
    _ ≤ F (N / n) * poleVector n :=
      mul_le_mul_of_nonneg_right hbracket (by unfold poleVector; positivity)
    _ = _ := by unfold poleVector; ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
