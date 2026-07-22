import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-!
# Sharp minimax law for exponentially tilted geometric brackets

An interior point of a logarithmic bracket sees two endpoint tent heights.  If the source
amplitude carries an exponential tilt `beta`, the normalized endpoint profiles are
`exp (-beta * d) * (1 - d / L)` and `exp (beta * (L - d)) * (d / L)`.

The profiles have a unique crossing.  Their minimum is globally bounded by its value at that
crossing, and the bound is attained there.  This gives the exact universal contraction factor
for every positive bracket width and every nonnegative tilt.
-/

/-- Relative location at which the two tilted endpoint profiles balance. -/
def tiltedTentBalance (beta L : ℝ) : ℝ :=
  1 / (1 + Real.exp (beta * L))

/-- Sharp simultaneous contraction factor for a bracket of logarithmic width `L`. -/
def tiltedTentSharpContraction (beta L : ℝ) : ℝ :=
  Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
    (1 - tiltedTentBalance beta L)

/-- Normalized sample at the lower endpoint of the bracket. -/
def tiltedTentLowerProfile (beta L d : ℝ) : ℝ :=
  Real.exp (-(beta * d)) * (1 - d / L)

/-- Normalized sample at the upper endpoint of the bracket. -/
def tiltedTentUpperProfile (beta L d : ℝ) : ℝ :=
  Real.exp (beta * (L - d)) * (d / L)

lemma tiltedTentBalance_mem_Ioo
    (beta L : ℝ) :
    tiltedTentBalance beta L ∈ Set.Ioo (0 : ℝ) 1 := by
  have hdenom : 1 < 1 + Real.exp (beta * L) := by
    linarith [Real.exp_pos (beta * L)]
  rw [tiltedTentBalance, Set.mem_Ioo]
  constructor
  · positivity
  · rw [div_lt_one (by linarith : 0 < 1 + Real.exp (beta * L))]
    exact hdenom

lemma tiltedTent_balance_identity
    {beta L : ℝ} :
    tiltedTentBalance beta L * Real.exp (beta * L) =
      1 - tiltedTentBalance beta L := by
  have hne : 1 + Real.exp (beta * L) ≠ 0 := by positivity
  rw [tiltedTentBalance]
  field_simp
  ring

lemma tiltedTent_balance_point_mem_Icc
    {beta L : ℝ} (hL : 0 < L) :
    tiltedTentBalance beta L * L ∈ Set.Icc (0 : ℝ) L := by
  have hbal := tiltedTentBalance_mem_Ioo beta L
  constructor
  · exact mul_nonneg hbal.1.le hL.le
  · nlinarith [mul_le_mul_of_nonneg_right hbal.2.le hL.le]

lemma tiltedTentLowerProfile_at_balance
    {beta L : ℝ} (hL : 0 < L) :
    tiltedTentLowerProfile beta L (tiltedTentBalance beta L * L) =
      tiltedTentSharpContraction beta L := by
  have hLne : L ≠ 0 := hL.ne'
  rw [tiltedTentLowerProfile, tiltedTentSharpContraction]
  have hdiv : tiltedTentBalance beta L * L / L = tiltedTentBalance beta L := by
    field_simp
  rw [hdiv]

lemma tiltedTentUpperProfile_at_balance
    {beta L : ℝ} (hL : 0 < L) :
    tiltedTentUpperProfile beta L (tiltedTentBalance beta L * L) =
      tiltedTentSharpContraction beta L := by
  have hLne : L ≠ 0 := hL.ne'
  have hdiv : tiltedTentBalance beta L * L / L = tiltedTentBalance beta L := by
    field_simp
  rw [tiltedTentUpperProfile, tiltedTentSharpContraction, hdiv]
  have hexp :
      Real.exp (beta * (L - tiltedTentBalance beta L * L)) =
        Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
          Real.exp (beta * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  calc
    (Real.exp (-(beta * (tiltedTentBalance beta L * L))) * Real.exp (beta * L)) *
        tiltedTentBalance beta L =
      Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
        (tiltedTentBalance beta L * Real.exp (beta * L)) := by ring
    _ = Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
        (1 - tiltedTentBalance beta L) := by rw [tiltedTent_balance_identity]

lemma hasDerivAt_tiltedTentUpperProfile
    {beta L : ℝ} (d : ℝ) :
    HasDerivAt (tiltedTentUpperProfile beta L)
      (Real.exp (beta * (L - d)) / L * (1 - beta * d)) d := by
  change HasDerivAt
    (fun x : ℝ => Real.exp (beta * (L - x)) * (x / L)) _ d
  convert (((((hasDerivAt_const d L).sub (hasDerivAt_id d)).const_mul beta).exp).mul
    ((hasDerivAt_id d).div_const L)) using 1
  · simp only [Pi.sub_apply, id_eq]
    ring

lemma beta_mul_tiltedTent_balance_point_lt_one
    (beta L : ℝ) :
    beta * (tiltedTentBalance beta L * L) < 1 := by
  have hdenom : 0 < 1 + Real.exp (beta * L) := by positivity
  have hqLt : beta * L < 1 + Real.exp (beta * L) := by
    linarith [Real.add_one_le_exp (beta * L)]
  have heq : beta * (tiltedTentBalance beta L * L) =
      (beta * L) / (1 + Real.exp (beta * L)) := by
    rw [tiltedTentBalance]
    field_simp
  rw [heq, div_lt_one hdenom]
  exact hqLt

lemma tiltedTentUpperProfile_monotoneOn_to_balance
    {beta L : ℝ} (hL : 0 < L) (hbeta : 0 ≤ beta) :
    MonotoneOn (tiltedTentUpperProfile beta L)
      (Set.Icc 0 (tiltedTentBalance beta L * L)) := by
  apply monotoneOn_of_deriv_nonneg
    (convex_Icc 0 (tiltedTentBalance beta L * L))
  · intro d _
    exact (hasDerivAt_tiltedTentUpperProfile d).continuousAt.continuousWithinAt
  · intro d _
    exact (hasDerivAt_tiltedTentUpperProfile d).differentiableAt.differentiableWithinAt
  · intro d hd
    rw [interior_Icc] at hd
    rw [(hasDerivAt_tiltedTentUpperProfile d).deriv]
    have hbetaD : beta * d < 1 := by
      calc
        beta * d ≤ beta * (tiltedTentBalance beta L * L) :=
          mul_le_mul_of_nonneg_left hd.2.le hbeta
        _ < 1 := beta_mul_tiltedTent_balance_point_lt_one beta L
    have : 0 < 1 - beta * d := by linarith
    positivity

/-- Exact geometric-bracket minimax law. For every point inside the bracket, one endpoint
profile contracts by at least the sharp factor. -/
theorem tiltedTent_geometricBracket_minimax
    {beta L d : ℝ} (hL : 0 < L) (hbeta : 0 ≤ beta)
    (hd : d ∈ Set.Icc (0 : ℝ) L) :
    min (tiltedTentLowerProfile beta L d) (tiltedTentUpperProfile beta L d) ≤
      tiltedTentSharpContraction beta L := by
  have hbal := tiltedTentBalance_mem_Ioo beta L
  have hdstar := tiltedTent_balance_point_mem_Icc (beta := beta) hL
  by_cases hright : d ≤ tiltedTentBalance beta L * L
  · calc
      min (tiltedTentLowerProfile beta L d) (tiltedTentUpperProfile beta L d) ≤
          tiltedTentUpperProfile beta L d := min_le_right _ _
      _ ≤ tiltedTentUpperProfile beta L (tiltedTentBalance beta L * L) :=
        tiltedTentUpperProfile_monotoneOn_to_balance hL hbeta
          ⟨hd.1, hright⟩ ⟨hdstar.1, le_rfl⟩ hright
      _ = tiltedTentSharpContraction beta L :=
        tiltedTentUpperProfile_at_balance hL
  · have hstarLe : tiltedTentBalance beta L * L ≤ d := le_of_not_ge hright
    have hexpLe : Real.exp (-(beta * d)) ≤
        Real.exp (-(beta * (tiltedTentBalance beta L * L))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hstarLe hbeta
      linarith
    have hheightNonneg : 0 ≤ 1 - d / L := by
      rw [sub_nonneg, div_le_one hL]
      exact hd.2
    have hheightLe : 1 - d / L ≤ 1 - tiltedTentBalance beta L := by
      have : tiltedTentBalance beta L ≤ d / L := by
        rw [le_div_iff₀ hL]
        exact hstarLe
      linarith
    have hexpNonneg :
        0 ≤ Real.exp (-(beta * (tiltedTentBalance beta L * L))) :=
      (Real.exp_pos _).le
    calc
      min (tiltedTentLowerProfile beta L d) (tiltedTentUpperProfile beta L d) ≤
          tiltedTentLowerProfile beta L d := min_le_left _ _
      _ = Real.exp (-(beta * d)) * (1 - d / L) := rfl
      _ ≤ Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
          (1 - tiltedTentBalance beta L) :=
        mul_le_mul hexpLe hheightLe hheightNonneg hexpNonneg
      _ = tiltedTentSharpContraction beta L := rfl

/-- The minimax factor is attained at the balance point, hence cannot be improved. -/
theorem tiltedTent_geometricBracket_minimax_sharp
    {beta L : ℝ} (hL : 0 < L) :
    min
        (tiltedTentLowerProfile beta L (tiltedTentBalance beta L * L))
        (tiltedTentUpperProfile beta L (tiltedTentBalance beta L * L)) =
      tiltedTentSharpContraction beta L := by
  rw [tiltedTentLowerProfile_at_balance hL, tiltedTentUpperProfile_at_balance hL,
    min_self]

/-- The two endpoint profiles cross at exactly one point. -/
theorem tiltedTent_profiles_eq_iff
    {beta L d : ℝ} (hL : 0 < L) :
    tiltedTentLowerProfile beta L d = tiltedTentUpperProfile beta L d ↔
      d = tiltedTentBalance beta L * L := by
  have hLne : L ≠ 0 := hL.ne'
  constructor
  · intro hprofiles
    have hexp : Real.exp (beta * (L - d)) =
        Real.exp (-(beta * d)) * Real.exp (beta * L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [tiltedTentLowerProfile, tiltedTentUpperProfile, hexp, mul_assoc] at hprofiles
    have hcancel : 1 - d / L = Real.exp (beta * L) * (d / L) :=
      mul_left_cancel₀ (ne_of_gt (Real.exp_pos (-(beta * d)))) hprofiles
    rw [tiltedTentBalance]
    field_simp [hLne] at hcancel ⊢
    nlinarith
  · rintro rfl
    exact (tiltedTentLowerProfile_at_balance hL).trans
      (tiltedTentUpperProfile_at_balance hL).symm

/-- Sharp contraction is strictly between zero and one for every nonnegative tilt. -/
theorem tiltedTentSharpContraction_mem_Ioo
    {beta L : ℝ} (hL : 0 < L) (hbeta : 0 ≤ beta) :
    tiltedTentSharpContraction beta L ∈ Set.Ioo (0 : ℝ) 1 := by
  have hbal := tiltedTentBalance_mem_Ioo beta L
  have hfactorPos : 0 < 1 - tiltedTentBalance beta L := sub_pos.mpr hbal.2
  have hfactorLt : 1 - tiltedTentBalance beta L < 1 := sub_lt_self 1 hbal.1
  have hexpPos : 0 < Real.exp (-(beta * (tiltedTentBalance beta L * L))) :=
    Real.exp_pos _
  have hpointNonneg : 0 ≤ tiltedTentBalance beta L * L :=
    (tiltedTent_balance_point_mem_Icc (beta := beta) hL).1
  have hargNonpos : -(beta * (tiltedTentBalance beta L * L)) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg hbeta hpointNonneg)
  have hexpLe : Real.exp (-(beta * (tiltedTentBalance beta L * L))) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hargNonpos
  rw [tiltedTentSharpContraction, Set.mem_Ioo]
  constructor
  · positivity
  · calc
      Real.exp (-(beta * (tiltedTentBalance beta L * L))) *
          (1 - tiltedTentBalance beta L) ≤
        1 * (1 - tiltedTentBalance beta L) :=
          mul_le_mul_of_nonneg_right hexpLe hfactorPos.le
      _ < 1 := by simpa using hfactorLt

end GaloisForLFunctions.HTGeometry
