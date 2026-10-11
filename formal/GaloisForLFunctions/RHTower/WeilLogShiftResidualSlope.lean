import GaloisForLFunctions.RHTower.WeilLogShiftEdgeLogCorrection
import Mathlib.Analysis.Calculus.MeanValue

/-! Exact logarithmic curvature makes the raw index/correction residual contractive. -/

noncomputable section
namespace RHTower

def finiteWeilEdgeResidualProfile (k : ℕ) (x : ℝ) : ℝ :=
  ((k + 2 : ℕ) : ℝ) * (1 - ((k + 2 : ℕ) : ℝ) *
    (Real.log (((k + 2 : ℕ) : ℝ) + x + 1) - Real.log (((k + 2 : ℕ) : ℝ) + x))) - x

theorem finiteWeilEdgeResidualProfile_at_index (r k : ℕ) (i : Fin (r + 1)) :
    finiteWeilEdgeResidualProfile k (i : ℕ) =
      ((r + 1 : ℕ) : ℝ) * finiteWeilCanonicalEdgeLogCorrection r k i - (i : ℕ) := by
  have hn : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hn' : (r : ℝ) + 1 ≠ 0 := by positivity
  simp only [finiteWeilEdgeResidualProfile, finiteWeilCanonicalEdgeLogCorrection,
    finiteWeilClusterLogNodes_apply, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one]
  field_simp [hn, hn']
  ring_nf

theorem finiteWeilEdgeResidualProfile_hasDerivAt (k : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (finiteWeilEdgeResidualProfile k)
      ((((k + 2 : ℕ) : ℝ) ^ 2 /
        ((((k + 2 : ℕ) : ℝ) + x) * (((k + 2 : ℕ) : ℝ) + x + 1))) - 1) x := by
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have h₀ : 0 < A + x := by linarith
  have h₁ : 0 < A + x + 1 := by linarith
  have hlin := (hasDerivAt_const x A).add (hasDerivAt_id x)
  have hlo := hlin.log h₀.ne'
  have hhi := (hlin.add_const 1).log h₁.ne'
  have h := (((hasDerivAt_const x (1 : ℝ)).sub
    ((hhi.sub hlo).const_mul A)).const_mul A).sub (hasDerivAt_id x)
  simp only [zero_add] at h
  change HasDerivAt (finiteWeilEdgeResidualProfile k)
    (A * (0 - A * (1 / (A + x + 1) - 1 / (A + x))) - 1) x at h
  have heq : A * (0 - A * (1 / (A + x + 1) - 1 / (A + x))) - 1 =
      A ^ 2 / ((A + x) * (A + x + 1)) - 1 := by
    field_simp [h₀.ne', h₁.ne']
    ring
  rw [heq] at h
  exact h

theorem finiteWeilEdgeResidualProfile_deriv_bound (r k : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) r) :
    |deriv (finiteWeilEdgeResidualProfile k) x| ≤
      2 * ((r + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) := by
  rw [(finiteWeilEdgeResidualProfile_hasDerivAt k x hx.1).deriv]
  let A : ℝ := ((k + 2 : ℕ) : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have h₀ : 0 < A + x := by linarith [hx.1]
  have h₁ : 0 < A + x + 1 := by linarith [hx.1]
  have hr : A ^ 2 / ((A + x) * (A + x + 1)) ≤ 1 := by
    apply (div_le_one (mul_pos h₀ h₁)).mpr
    nlinarith only [sq_nonneg x, mul_nonneg hA.le hx.1, hA.le, hx.1]
  have ha : A / (A + x) ≤ 1 := (div_le_one h₀).mpr (by linarith [hx.1])
  have hleft : x / (A + x) ≤ x / A :=
    div_le_div_of_nonneg_left hx.1 hA (by linarith [hx.1])
  have hright : (x + 1) / (A + x + 1) ≤ (x + 1) / A :=
    div_le_div_of_nonneg_left (by linarith [hx.1]) hA (by linarith [hx.1])
  change |A ^ 2 / ((A + x) * (A + x + 1)) - 1| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr hr)]
  calc
    _ = x / (A + x) + (A / (A + x)) * ((x + 1) / (A + x + 1)) := by
      field_simp [h₀.ne', h₁.ne']
      ring
    _ ≤ x / A + (x + 1) / A := add_le_add hleft
      ((mul_le_of_le_one_left (div_nonneg (by linarith [hx.1]) h₁.le) ha).trans hright)
    _ = (2 * x + 1) / A := by ring
    _ ≤ 2 * ((r + 1 : ℕ) : ℝ) / A := by
      apply div_le_div_of_nonneg_right _ hA.le
      push_cast
      linarith [hx.2]

theorem finiteWeilEdgeResidualProfile_lipschitz (r k : ℕ) (x y : Set.Icc (0 : ℝ) r) :
    |finiteWeilEdgeResidualProfile k x - finiteWeilEdgeResidualProfile k y| ≤
      (2 * ((r + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ)) * |(x : ℝ) - y| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (finiteWeilEdgeResidualProfile_hasDerivAt k z hz.1).differentiableAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using
      finiteWeilEdgeResidualProfile_deriv_bound r k z hz)
    (convex_Icc (0 : ℝ) (r : ℝ)) y.property x.property

end RHTower
