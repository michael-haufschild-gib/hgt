import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Backlund's disc count for the real trace of `ζ`

The real trace `σ ↦ Re ζ(σ + iT)` extends to the analytic function

`F_T(z) = (ζ(z + iT) + ζ(z − iT))/2`,

which is real on the real axis by the Schwarz reflection `ζ(s̄) = conj ζ(s)`.  At the centre
`z = 2` it is bounded below by `2 − π²/6 > 0`, because the Dirichlet series gives
`‖ζ(2 + iT) − 1‖ ≤ π²/6 − 1`.  On the sphere of radius `7/4` the crude polynomial bound applies,
since every point there has abscissa at least `1/4` and ordinate at least `T − 7/4`.

Jensen's inequality then bounds the number of zeros of `F_T` in the disc of radius `3/2` — hence the
number of sign changes of `Re ζ(σ + iT)` across `σ ∈ [1/2, 2]` — by `O(log T)`.
-/

open Complex Metric Set MeromorphicOn

noncomputable section

namespace RHTower

/-- The analytic extension of the real trace of `ζ` at height `T`. -/
def zetaRealTrace (T : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + (T : ℂ) * I) + riemannZeta (z - (T : ℂ) * I)) / 2

theorem zetaRealTrace_ofReal (T σ : ℝ) :
    zetaRealTrace T (σ : ℂ) = ((riemannZeta ((σ : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  have hconj : ((σ : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [zetaRealTrace, hconj, riemannZeta_conj]
  rw [Complex.add_conj]
  push_cast
  ring

/-! ## The lower bound at the centre -/

theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : s.re = 2) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  classical
  have h1 : (1 : ℝ) < s.re := by rw [hs]; norm_num
  have hz := zeta_eq_tsum_one_div_nat_cpow h1
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := summable_one_div_nat_cpow.mpr h1
  have hnorm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hs0 : s ≠ 0 := by
        intro hh
        rw [hh] at hs
        simp at hs
      simp [Complex.zero_cpow hs0]
    · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
      rw [norm_div, norm_one, norm_natCast_cpow_of_pos h s, hs]
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hone : (1 : ℂ) / ((1 : ℕ) : ℂ) ^ s = 1 := by
    rw [Nat.cast_one, Complex.one_cpow]
    norm_num
  have hsplit : riemannZeta s - 1
      = ∑' n : ℕ, (if n = 1 then 0 else (1 : ℂ) / (n : ℂ) ^ s) := by
    rw [hz, hsum.tsum_eq_add_tsum_ite 1, hone]
    ring
  have hbaselsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := HasSum.summable _root_.hasSum_zeta_two
  have hbnd : ‖∑' n : ℕ, (if n = 1 then 0 else (1 : ℂ) / (n : ℂ) ^ s)‖
      ≤ ∑' n : ℕ, (if n = 1 then 0 else 1 / (n : ℝ) ^ 2) := by
    refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
    · refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbaselsum
      by_cases h : n = 1
      · simp [h]
      · rw [if_neg h, hnorm n]
    · refine tsum_congr fun n => ?_
      by_cases h : n = 1
      · simp [h]
      · rw [if_neg h, if_neg h, hnorm n]
  have hbasel : ∑' n : ℕ, (if n = 1 then 0 else 1 / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 - 1 := by
    have h := hbaselsum.tsum_eq_add_tsum_ite 1
    rw [HasSum.tsum_eq _root_.hasSum_zeta_two] at h
    have hone' : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [hone'] at h
    linarith
  rw [hsplit]
  exact le_trans hbnd (le_of_eq hbasel)

theorem two_sub_pi_sq_div_six_le_re (T : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re := by
  have hre : ((2 : ℂ) + (T : ℂ) * I).re = 2 := by simp
  have h := norm_riemannZeta_sub_one_le hre
  have hle : |(riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re - 1| ≤ Real.pi ^ 2 / 6 - 1 := by
    refine le_trans ?_ h
    have hval : ((riemannZeta ((2 : ℂ) + (T : ℂ) * I)) - 1).re
        = (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re - 1 := by simp
    rw [← hval]
    exact Complex.abs_re_le_norm _
  rw [abs_le] at hle
  linarith [hle.1]

theorem pi_sq_div_six_lt_two : Real.pi ^ 2 / 6 < 2 := by
  nlinarith [Real.pi_lt_d2, Real.pi_gt_three]

theorem re_riemannZeta_two_add_pos (T : ℝ) :
    0 < (riemannZeta ((2 : ℂ) + (T : ℂ) * I)).re :=
  lt_of_lt_of_le (by linarith [pi_sq_div_six_lt_two]) (two_sub_pi_sq_div_six_le_re T)

theorem zetaRealTrace_two_ne_zero (T : ℝ) : zetaRealTrace T 2 ≠ 0 := by
  have hval : zetaRealTrace T ((2 : ℝ) : ℂ)
      = ((riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)).re : ℂ) := zetaRealTrace_ofReal T 2
  have hcast : (((2 : ℝ) : ℂ)) = (2 : ℂ) := by norm_num
  rw [hcast] at hval
  rw [hval]
  have := re_riemannZeta_two_add_pos T
  simpa using this.ne'

/-! ## Analyticity -/

theorem analyticOnNhd_riemannZeta_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_ne

theorem analyticAt_zetaRealTrace {T : ℝ} (hT : 2 < T) {z : ℂ} (hz : |z.im| ≤ 7 / 4) :
    AnalyticAt ℂ (zetaRealTrace T) z := by
  have hshift : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + (ε : ℂ) * (T : ℂ) * I)) z := by
    intro ε hε
    have hne : (z + (ε : ℂ) * (T : ℂ) * I) ≠ 1 := by
      intro h
      have him : (z + (ε : ℂ) * (T : ℂ) * I).im = 0 := by rw [h]; simp
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
      rcases hε with h1 | h1 <;> subst h1 <;> simp at him <;> [skip; skip] <;>
        · rcases abs_le.mp hz with ⟨hz1, hz2⟩
          linarith
    have hinner : AnalyticAt ℂ (fun w : ℂ => w + (ε : ℂ) * (T : ℂ) * I) z :=
      analyticAt_id.add analyticAt_const
    have hcomp : AnalyticAt ℂ (riemannZeta ∘ fun w : ℂ => w + (ε : ℂ) * (T : ℂ) * I) z :=
      AnalyticAt.comp (analyticOnNhd_riemannZeta_ne_one _ hne) hinner
    simpa [Function.comp_def] using hcomp
  have h1 := hshift 1 (Or.inl rfl)
  have h2 := hshift (-1) (Or.inr rfl)
  have heq : (fun w : ℂ => (riemannZeta (w + (1 : ℝ) * (T : ℂ) * I)
      + riemannZeta (w + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)) / 2) = zetaRealTrace T := by
    funext w
    rw [zetaRealTrace]
    push_cast
    ring_nf
  rw [← heq]
  exact ((h1.add h2).div analyticAt_const two_ne_zero)

theorem analyticOnNhd_zetaRealTrace {T : ℝ} (hT : 2 < T) :
    AnalyticOnNhd ℂ (zetaRealTrace T) (closedBall (2 : ℂ) |(7 / 4 : ℝ)|) := by
  intro z hz
  refine analyticAt_zetaRealTrace hT ?_
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0:ℝ) < 7/4)] at hz
  have := Complex.abs_im_le_norm (z - 2)
  have him : (z - 2).im = z.im := by simp
  rw [him] at this
  linarith

/-! ## The Jensen count -/

/-- **Backlund's disc count.**  The number of zeros of the real trace of `ζ` in the disc of radius
`3/2` about `2` is `O(log T)`. -/
theorem zetaRealTrace_divisor_le {T : ℝ} (hT : 4 ≤ T) :
    ((∑ᶠ u, MeromorphicOn.divisor (zetaRealTrace T) (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) u : ℤ) : ℝ)
      ≤ Real.log ((2 + 8 * (T + 7 / 4)) / ‖zetaRealTrace T 2‖)
          / Real.log ((7 / 4) / (3 / 2)) := by
  have hT2 : (2 : ℝ) < T := by linarith
  refine (analyticOnNhd_zetaRealTrace hT2).sum_divisor_le
    (r := 3 / 2) (R := 7 / 4) (M := 2 + 8 * (T + 7 / 4))
    (by norm_num) (by norm_num) (by linarith) (zetaRealTrace_two_ne_zero T) ?_
  intro z hz
  rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0:ℝ) < 7/4)] at hz
  have hre : (1 : ℝ) / 4 ≤ z.re := by
    have h := Complex.abs_re_le_norm (z - 2)
    have hrz : (z - 2).re = z.re - 2 := by simp
    rw [hrz, hz] at h
    rcases abs_le.mp h with ⟨h1, -⟩
    linarith
  have him : |z.im| ≤ 7 / 4 := by
    have h := Complex.abs_im_le_norm (z - 2)
    have hiz : (z - 2).im = z.im := by simp
    rw [hiz, hz] at h
    exact h
  have hbound : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
      ‖riemannZeta (z + (ε : ℂ) * (T : ℂ) * I)‖ ≤ 2 + 8 * (T + 7 / 4) := by
    intro ε hε
    have hre' : (1 : ℝ) / 4 ≤ (z + (ε : ℂ) * (T : ℂ) * I).re := by
      rcases hε with h1 | h1 <;> subst h1 <;> simpa using hre
    have him' : |(z + (ε : ℂ) * (T : ℂ) * I).im| ≤ T + 7 / 4 := by
      rcases hε with h1 | h1 <;> subst h1 <;>
        · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          rcases abs_le.mp him with ⟨hz1, hz2⟩
          rw [abs_le]
          constructor <;> [skip; skip] <;> · linarith
    have hge : (2 : ℝ) ≤ |(z + (ε : ℂ) * (T : ℂ) * I).im| := by
      rcases hε with h1 | h1 <;> subst h1 <;>
        · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im]
          rcases abs_le.mp him with ⟨hz1, hz2⟩
          rw [le_abs]
          first
            | (left; linarith)
            | (right; linarith)
    refine le_trans (norm_riemannZeta_le_quarter hre' hge) ?_
    linarith [him']
  have hz1 := hbound 1 (Or.inl rfl)
  have hz2 := hbound (-1) (Or.inr rfl)
  have hval : zetaRealTrace T z
      = (riemannZeta (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
        + riemannZeta (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)) / 2 := by
    rw [zetaRealTrace]
    push_cast
    ring_nf
  rw [hval, norm_div]
  have hsum : ‖riemannZeta (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
      + riemannZeta (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)‖ ≤ 2 * (2 + 8 * (T + 7 / 4)) := by
    refine le_trans (norm_add_le _ _) ?_
    linarith
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  linarith [hsum]

theorem norm_zetaRealTrace_two_ge (T : ℝ) :
    2 - Real.pi ^ 2 / 6 ≤ ‖zetaRealTrace T 2‖ := by
  have hval : zetaRealTrace T ((2 : ℝ) : ℂ)
      = ((riemannZeta (((2 : ℝ) : ℂ) + (T : ℂ) * I)).re : ℂ) := zetaRealTrace_ofReal T 2
  have hcast : (((2 : ℝ) : ℂ)) = (2 : ℂ) := by norm_num
  rw [hcast] at hval
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (two_sub_pi_sq_div_six_le_re T) (le_abs_self _)

/-- **`S(T) = O(log T)` input.**  The real trace of `ζ` has at most `O(log T)` zeros in the disc of
radius `3/2` about `2`, hence at most that many sign changes across the critical strip at height
`T`. -/
theorem exists_zetaRealTrace_count_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 4 ≤ T →
      ((∑ᶠ u, MeromorphicOn.divisor (zetaRealTrace T) (closedBall (2 : ℂ) |(3 / 2 : ℝ)|) u : ℤ)
          : ℝ) ≤ c * Real.log T := by
  have hβ : (0 : ℝ) < 2 - Real.pi ^ 2 / 6 := by linarith [pi_sq_div_six_lt_two]
  set β : ℝ := 2 - Real.pi ^ 2 / 6 with hβdef
  set B : ℝ := Real.log β with hBdef
  have hlog76 : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  set u : ℝ := (-B) / Real.log 4 + |B| / Real.log 4 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    rcases le_or_gt B 0 with h | h
    · have h1 : (0 : ℝ) ≤ (-B) / Real.log 4 := div_nonneg (by linarith) hlog4.le
      have h2 : (0 : ℝ) ≤ |B| / Real.log 4 := div_nonneg (abs_nonneg _) hlog4.le
      linarith
    · have habs : |B| = B := abs_of_pos h
      rw [habs]
      have : (-B) / Real.log 4 + B / Real.log 4 = 0 := by ring
      linarith [this]
  refine ⟨(3 + u) / Real.log (7 / 6), div_pos (by linarith) hlog76, ?_⟩
  intro T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlogT0 : (0 : ℝ) < Real.log T := lt_of_lt_of_le hlog4 hlogT
  have hnorm : β ≤ ‖zetaRealTrace T 2‖ := norm_zetaRealTrace_two_ge T
  have hnorm0 : (0 : ℝ) < ‖zetaRealTrace T 2‖ := lt_of_lt_of_le hβ hnorm
  have hM : (0 : ℝ) < 2 + 8 * (T + 7 / 4) := by linarith
  have hquot : Real.log ((2 + 8 * (T + 7 / 4)) / ‖zetaRealTrace T 2‖)
      ≤ 3 * Real.log T - B := by
    rw [Real.log_div hM.ne' hnorm0.ne']
    have h1 : Real.log (2 + 8 * (T + 7 / 4)) ≤ 3 * Real.log T := by
      have hle : (2 : ℝ) + 8 * (T + 7 / 4) ≤ 12 * T := by linarith
      have h2 : Real.log (2 + 8 * (T + 7 / 4)) ≤ Real.log (12 * T) := Real.log_le_log hM hle
      have h3 : Real.log (12 * T) = Real.log 12 + Real.log T :=
        Real.log_mul (by norm_num) hT0.ne'
      have h4 : Real.log 12 ≤ 2 * Real.log T := by
        have h5 : Real.log 12 ≤ Real.log (T ^ 2) := by
          refine Real.log_le_log (by norm_num) ?_
          nlinarith
        rwa [Real.log_pow] at h5
      linarith
    have h6 : B ≤ Real.log ‖zetaRealTrace T 2‖ := Real.log_le_log hβ hnorm
    linarith
  have hBbound : -B ≤ u * Real.log T := by
    rcases le_or_gt B 0 with h | h
    · have habs : |B| = -B := abs_of_nonpos h
      have hval : u = 2 * ((-B) / Real.log 4) := by rw [hu, habs]; ring
      have hstep : (-B) / Real.log 4 * Real.log 4 ≤ (-B) / Real.log 4 * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT (div_nonneg (by linarith) hlog4.le)
      rw [div_mul_cancel₀ _ hlog4.ne'] at hstep
      have hnn : (0 : ℝ) ≤ (-B) / Real.log 4 * Real.log T := by
        exact mul_nonneg (div_nonneg (by linarith) hlog4.le) hlogT0.le
      rw [hval]
      linarith
    · have habs : |B| = B := abs_of_pos h
      have hval : u = 0 := by rw [hu, habs]; ring
      rw [hval, zero_mul]
      linarith
  refine le_trans (zetaRealTrace_divisor_le hT) ?_
  have hratio : (7 : ℝ) / 4 / (3 / 2) = 7 / 6 := by norm_num
  rw [hratio, div_le_iff₀ hlog76]
  have hsimp : (3 + u) / Real.log (7 / 6) * Real.log T * Real.log (7 / 6)
      = (3 + u) * Real.log T := by
    field_simp
  rw [hsimp]
  nlinarith [hquot, hBbound]

end RHTower
