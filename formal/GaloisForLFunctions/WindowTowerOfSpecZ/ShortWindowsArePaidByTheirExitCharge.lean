import GaloisForLFunctions.WindowTowerOfSpecZ.TheEndProfileOfAWindow
import GaloisForLFunctions.RHTower.WeilLevyBoundaryEscapeCollarPotential
import GaloisForLFunctions.RHTower.WeilLevyOsculatingPotentialFloor

/-!
# Short windows are paid by their exit charge

The end-profile bound turns positivity into a pointwise inequality for the window potential
`V_A = Ω_Γ + Ω(−u) + Ω(A + u) − k_A(u)`. On a prime-free window `k_A = 0`, and by midpoint convexity of
`Ω` the exit potential is smallest at the centre: `Ω(−u) + Ω(A + u) ≥ 2Ω(A/2)`. Hence:

* **Prime-free pointwise payment** (`weilQuad_nonneg_of_primeFree_centre`): if `A < log 2` and
  `Ω_Γ + 2Ω(A/2) ≥ 2 sinh(A/2) − A`, Weil's form is nonnegative on window tests of length `A`.
* **Windows of length `≤ 1/12` are positive by their exit charge**
  (`weilQuad_nonneg_of_le_one_twelfth`): `Ω(1/24) ≥ 68/25` (`archLevyAntideriv_one_div_24_ge`, from the
  closed form `½ log((1+t)/(1−t)) + arctan t`, `t = e^{−1/48}`), `Ω_Γ > −5.373` and
  `2 sinh(A/2) − A ≤ A²/2`. The archimedean exit charge alone — a count of the jumps that leave the
  window — pays the Gamma constant and the pole plane; no estimate of Weil's form enters. The count
  threshold of LST (`1/32`) is improved to `1/12`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open RHTower.WeilLevyPoleGauss

variable {A : ℝ} {H : ℝ → ℝ}

/-! ### Elementary constants -/

/-- `22/5 ≤ log 95`, from `e < 2.7182818286` and `e^{2/5} ≤ 5/3`. -/
theorem log_ninetyfive_ge : (22 / 5 : ℝ) ≤ Real.log 95 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : Real.exp (2 / 5) ≤ 5 / 3 := by
    have h := Real.add_one_le_exp (-(2 / 5))
    have hpos := Real.exp_pos (2 / 5)
    have hprod : Real.exp (2 / 5) * Real.exp (-(2 / 5)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith
  have h4 : Real.exp 4 ≤ 2.7182818286 ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 4
  calc Real.exp (22 / 5) = Real.exp 4 * Real.exp (2 / 5) := by
        rw [← Real.exp_add]; norm_num
    _ ≤ 2.7182818286 ^ 4 * (5 / 3) :=
        mul_le_mul h4 h2 (Real.exp_pos _).le (by positivity)
    _ ≤ 95 := by norm_num

/-- `Ω(1/24) ≥ 68/25`: the exit tail of the Gamma factor at distance `1/24`. -/
theorem archLevyAntideriv_one_div_24_ge : (68 / 25 : ℝ) ≤ archLevyAntideriv (1 / 24) := by
  rw [archLevyAntideriv_eq_log_div (by norm_num)]
  set t := Real.exp (-(1 / 24) / 2) with htdef
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have ht47 : 47 / 48 ≤ t := by
    have := Real.add_one_le_exp (-(1 / 24) / 2)
    rw [htdef]; linarith
  have h95 : (95 : ℝ) ≤ (1 + t) / (1 - t) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hlog : (22 / 5 : ℝ) ≤ Real.log ((1 + t) / (1 - t)) :=
    log_ninetyfive_ge.trans (Real.log_le_log (by norm_num) h95)
  -- `arctan t ≥ arctan(1/√3) = π/6`
  have hs3 : (Real.sqrt 3)⁻¹ ≤ t := by
    have hsq : (48 / 47 : ℝ) ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    calc (Real.sqrt 3)⁻¹ ≤ (48 / 47 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hsq
      _ = 47 / 48 := by norm_num
      _ ≤ t := ht47
  have harc : Real.pi / 6 ≤ Real.arctan t := by
    rw [← Real.arctan_inv_sqrt_three]; exact Real.arctan_strictMono.monotone hs3
  have hpi := Real.pi_gt_d2
  linarith

/-- `2 sinh(A/2) − A ≤ A²/2` for `0 ≤ A ≤ 2`. -/
theorem two_sinh_half_sub_le {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 2) :
    2 * Real.sinh (A / 2) - A ≤ A ^ 2 / 2 := by
  have hx : |A / 2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hx' : |-(A / 2)| ≤ 1 := by rw [abs_neg]; exact hx
  have h1 := Real.abs_exp_sub_one_sub_id_le hx
  have h2 := Real.abs_exp_sub_one_sub_id_le hx'
  rw [abs_le] at h1 h2
  rw [Real.sinh_eq]
  nlinarith [h1.2, h2.1]

/-! ### Prime-free windows -/

theorem windowLevel_eq_one_of_lt {A : ℝ} (hA0 : 0 ≤ A) (hA : A < Real.log 2) :
    windowLevel A = 1 := by
  rw [windowLevel, Nat.floor_eq_iff (Real.exp_pos A).le]
  refine ⟨by simpa using Real.one_le_exp hA0, ?_⟩
  have := Real.exp_lt_exp.mpr hA
  rw [Real.exp_log (by norm_num)] at this
  norm_num
  exact this

theorem canonicalDensity_eq_zero_of_lt {A : ℝ} (hA0 : 0 ≤ A) (hA : A < Real.log 2) (u : ℝ) :
    canonicalDensity A u = 0 := by
  rw [canonicalDensity, windowLevel_eq_one_of_lt hA0 hA]
  rfl

/-- On the open window the exit potential is at least its value at the centre, `2Ω(A/2)`. -/
theorem two_mul_archLevyAntideriv_half_le_exitPotential {u : ℝ} (hu : u ∈ Ioo (-A) 0) :
    2 * archLevyAntideriv (A / 2) ≤ exitPotential A u := by
  rw [exitPotential, indicator_of_mem hu]
  have h := RHTower.WeilLevyBoundaryEscape.two_mul_archLevyAntideriv_midpoint_le_add
    (a := -u) (b := A + u) (by linarith [hu.2]) (by linarith [hu.1])
  rwa [show (-u + (A + u)) / 2 = A / 2 by ring] at h

/-- **Prime-free pointwise payment**: on a prime-free window, `Ω_Γ + 2Ω(A/2) ≥ 2 sinh(A/2) − A`
forces Weil's form to be nonnegative. -/
theorem weilQuad_nonneg_of_primeFree_centre (hH : IsWindowTest A H) (hA0 : 0 ≤ A)
    (hA : A < Real.log 2)
    (hc : 2 * Real.sinh (A / 2) - A ≤ EF.gammaBracket 0 + 2 * archLevyAntideriv (A / 2)) :
    0 ≤ weilQuad H := by
  refine weilQuad_nonneg_of_potential hH hA0 fun u hu => ?_
  rw [windowPotential, canonicalDensity_eq_zero_of_lt hA0 hA]
  have := two_mul_archLevyAntideriv_half_le_exitPotential hu
  linarith

/-- **Windows of length at most `1/12` are positive by their exit charge.** -/
theorem weilQuad_nonneg_of_le_one_twelfth (hH : IsWindowTest A H) (hA0 : 0 < A)
    (hA : A ≤ 1 / 12) : 0 ≤ weilQuad H := by
  have hlog2 : A < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  refine weilQuad_nonneg_of_primeFree_centre hH hA0.le hlog2 ?_
  have hΩ : archLevyAntideriv (1 / 24) ≤ archLevyAntideriv (A / 2) :=
    antitoneOn_archLevyAntideriv (show A / 2 ∈ Ioi 0 from by simp; linarith)
      (show (1 / 24 : ℝ) ∈ Ioi 0 from by norm_num) (by linarith)
  have h24 := archLevyAntideriv_one_div_24_ge
  have hΓ := RHTower.WeilLevyOsculatingFloor.neg_gammaBracket_zero_lt_5373_over_1000
  have hp := two_sinh_half_sub_le hA0.le (by linarith)
  have hA2 : A ^ 2 ≤ 1 / 144 := by nlinarith
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
