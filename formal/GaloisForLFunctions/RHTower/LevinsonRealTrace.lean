import GaloisForLFunctions.RHTower.LevinsonStripBound
import GaloisForLFunctions.RHTower.LevinsonRightEdge
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound

/-!
# Backlund's disc count for the real trace of the detector

The real trace `σ ↦ Re G(σ + iT)` of the detector `G = ζ + λζ'` (real `λ`) extends to the analytic
function `(G(z+iT) + G(z-iT))/2`, by the Schwarz symmetry `G(s̄) = conj G(s)`.  At the centre
`z = 4` it is at least `7/16`, and on the sphere of radius `4` it obeys the crude polynomial bound.
Jensen's inequality therefore bounds the number of its zeros in the disc of radius `7/2` — hence the
number of sign changes of `Re G(σ+iT)` across `σ ∈ [1/2, 4]` — by `O(log T)`.
-/

open Complex Metric Set MeromorphicOn
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The analytic extension of the real trace of the detector at height `T`. -/
def levinsonGTrace (lam : ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  (levinsonG (lam : ℂ) (z + (T : ℂ) * I) + levinsonG (lam : ℂ) (z - (T : ℂ) * I)) / 2

theorem levinsonGTrace_ofReal (lam T σ : ℝ) :
    levinsonGTrace lam T (σ : ℂ)
      = ((levinsonG (lam : ℂ) ((σ : ℂ) + (T : ℂ) * I)).re : ℂ) := by
  have hconj : ((σ : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((σ : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [levinsonGTrace, hconj, levinsonG_conj, Complex.add_conj]
  push_cast
  ring

/-! ## Analyticity -/

/-- The open horizontal strip on which the trace at height `T ≥ 6` is analytic. -/
def traceStrip : Set ℂ := {z : ℂ | |z.im| < 5}

theorem isOpen_traceStrip : IsOpen traceStrip := by
  have : Continuous fun z : ℂ => |z.im| := Complex.continuous_im.abs
  exact isOpen_lt this continuous_const

theorem convex_traceStrip : Convex ℝ traceStrip := by
  have h : traceStrip = {c : ℂ | -5 < c.im} ∩ {c : ℂ | c.im < 5} := by
    ext z
    simp only [traceStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
  rw [h]
  exact (convex_halfSpace_im_gt (-5)).inter (convex_halfSpace_im_lt 5)

theorem analyticOnNhd_levinsonGTrace_strip {lam T : ℝ} (hT : 6 ≤ T) :
    AnalyticOnNhd ℂ (levinsonGTrace lam T) traceStrip := by
  set U : Set ℂ := traceStrip with hU
  have hUopen : IsOpen U := isOpen_traceStrip
  have hne : ∀ z ∈ U, ∀ ε : ℝ, ε = 1 ∨ ε = -1 → z + (ε : ℂ) * (T : ℂ) * I ≠ 1 := by
    intro z hz ε hε heq
    have hzim : |z.im| < 5 := hz
    have him := congrArg Complex.im heq
    rw [Complex.one_im] at him
    rcases hε with h | h <;> subst h <;>
      · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
        rw [abs_lt] at hzim
        linarith [hzim.1, hzim.2]
  have hdiff : DifferentiableOn ℂ (levinsonGTrace lam T) U := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ => levinsonG (lam : ℂ) (w + (T : ℂ) * I)) z := by
      have hne1 : z + (T : ℂ) * I ≠ 1 := by
        have := hne z hz 1 (Or.inl rfl)
        simpa using this
      exact (analyticAt_levinsonG (lam : ℂ) hne1).differentiableAt.comp z
        (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => levinsonG (lam : ℂ) (w - (T : ℂ) * I)) z := by
      have hne2 : z - (T : ℂ) * I ≠ 1 := by
        have := hne z hz (-1) (Or.inr rfl)
        simpa [sub_eq_add_neg] using this
      exact (analyticAt_levinsonG (lam : ℂ) hne2).differentiableAt.comp z
        (differentiableAt_id.sub_const _)
    exact ((h1.add h2).div_const 2).differentiableWithinAt
  exact hdiff.analyticOnNhd hUopen

theorem closedBall_four_subset_traceStrip {r : ℝ} (hr : |r| ≤ 4) :
    closedBall (4 : ℂ) |r| ⊆ traceStrip := by
  intro z hz
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h := Complex.abs_im_le_norm (z - 4)
  have hiz : (z - 4).im = z.im := by simp
  rw [hiz] at h
  have : |z.im| ≤ 4 := le_trans (le_trans h hz) hr
  exact lt_of_le_of_lt this (by norm_num)

theorem analyticOnNhd_levinsonGTrace {lam T : ℝ} (hT : 6 ≤ T) :
    AnalyticOnNhd ℂ (levinsonGTrace lam T) (closedBall (4 : ℂ) |(4 : ℝ)|) :=
  (analyticOnNhd_levinsonGTrace_strip hT).mono
    (closedBall_four_subset_traceStrip (by norm_num))

/-! ## The lower bound at the centre -/

theorem re_levinsonG_ge_of_four_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ} (hs : 4 ≤ s.re) :
    7 / 16 ≤ (levinsonG lam s).re := by
  have h := norm_levinsonG_sub_one_le_of_four_le hlam hs
  have hre : |(levinsonG lam s - 1).re| ≤ 9 / 16 := le_trans (Complex.abs_re_le_norm _) h
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre
  linarith [hre.1]

theorem norm_levinsonGTrace_center_ge {lam T : ℝ} (hlam : |lam| ≤ 1) :
    7 / 16 ≤ ‖levinsonGTrace lam T 4‖ := by
  have hlamC : ‖(lam : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hcast : ((4 : ℝ) : ℂ) = (4 : ℂ) := by norm_num
  have hval := levinsonGTrace_ofReal lam T 4
  rw [hcast] at hval
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  have hre : (4 : ℝ) ≤ ((4 : ℂ) + (T : ℂ) * I).re := by simp
  exact le_trans (re_levinsonG_ge_of_four_le hlamC hre) (le_abs_self _)

/-! ## The disc count -/

/-- **Backlund's disc count for the detector.**  The real trace has `O(log T)` zeros in the disc of
radius `7/2` about `4`. -/
theorem exists_levinsonGTrace_count_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, |lam| ≤ 1 → ∀ T : ℝ, 6 ≤ T →
      ((∑ᶠ u, MeromorphicOn.divisor (levinsonGTrace lam T)
          (closedBall (4 : ℂ) |(7 / 2 : ℝ)|) u : ℤ) : ℝ) ≤ c * Real.log T := by
  obtain ⟨C, N, hC1, hC⟩ := exists_bound_norm_levinsonG_strip 8
  have hC0 : (0 : ℝ) < C := by linarith
  have hlog87 : (0 : ℝ) < Real.log ((4 : ℝ) / (7 / 2)) := by
    refine Real.log_pos ?_
    norm_num
  set A : ℝ := |Real.log (C * 16 / 7)| + (N : ℝ) * Real.log 8 + (N : ℝ) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]; positivity
  refine ⟨(A + 1) / Real.log ((4 : ℝ) / (7 / 2)), by positivity, ?_⟩
  intro lam hlam T hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogT : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlamC : ‖(lam : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  set M : ℝ := C * (4 * T) ^ N with hM
  have hMbase : (1 : ℝ) ≤ 4 * T := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have : (1 : ℝ) ≤ (4 * T) ^ N := one_le_pow₀ hMbase
    nlinarith
  have hsphere : ∀ z ∈ sphere (4 : ℂ) |(4 : ℝ)|, ‖levinsonGTrace lam T z‖ ≤ M := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hz
    have hre : |z.re| ≤ 8 := by
      have h := Complex.abs_re_le_norm (z - 4)
      have hrz : (z - 4).re = z.re - 4 := by simp
      rw [hrz, hz] at h
      rw [abs_le] at h ⊢
      constructor <;> linarith [h.1, h.2]
    have him : |z.im| ≤ 4 := by
      have h := Complex.abs_im_le_norm (z - 4)
      have hiz : (z - 4).im = z.im := by simp
      rw [hiz, hz] at h
      exact h
    have hbound : ∀ ε : ℝ, ε = 1 ∨ ε = -1 →
        ‖levinsonG (lam : ℂ) (z + (ε : ℂ) * (T : ℂ) * I)‖ ≤ M := by
      intro ε hε
      have hre' : |(z + (ε : ℂ) * (T : ℂ) * I).re| ≤ 8 := by
        rcases hε with h1 | h1 <;> subst h1 <;> simpa using hre
      have himval : ∀ w : ℂ, w = z + ((1 : ℝ) : ℂ) * (T : ℂ) * I ∨
          w = z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I → 2 ≤ |w.im| ∧ |w.im| ≤ T + 4 := by
        intro w hw
        rcases abs_le.mp him with ⟨hz1, hz2⟩
        rcases hw with h1 | h1 <;> subst h1 <;>
          · simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.I_re, Complex.I_im]
            constructor
            · rw [le_abs]
              first
                | (left; linarith)
                | (right; linarith)
            · rw [abs_le]
              constructor <;> linarith
      have hpair := himval (z + (ε : ℂ) * (T : ℂ) * I) (by
        rcases hε with h1 | h1 <;> subst h1
        · left; norm_num
        · right; norm_num)
      have hg := hC (lam : ℂ) hlamC _ hre' hpair.1
      refine le_trans hg ?_
      rw [hM]
      have hmono : (2 * |(z + (ε : ℂ) * (T : ℂ) * I).im|) ^ N ≤ (4 * T) ^ N := by
        refine pow_le_pow_left₀ (by positivity) ?_ N
        have := hpair.2
        linarith
      exact mul_le_mul_of_nonneg_left hmono hC0.le
    have h1 := hbound 1 (Or.inl rfl)
    have h2 := hbound (-1) (Or.inr rfl)
    have hval : levinsonGTrace lam T z
        = (levinsonG (lam : ℂ) (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
          + levinsonG (lam : ℂ) (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)) / 2 := by
      rw [levinsonGTrace]
      push_cast
      ring_nf
    rw [hval, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hsum : ‖levinsonG (lam : ℂ) (z + ((1 : ℝ) : ℂ) * (T : ℂ) * I)
        + levinsonG (lam : ℂ) (z + ((-1 : ℝ) : ℂ) * (T : ℂ) * I)‖ ≤ 2 * M := by
      refine le_trans (norm_add_le _ _) ?_
      linarith
    linarith [hsum]
  have hjensen := sum_divisor_le_of_bounds (c := (4 : ℂ)) (r := (7 / 2 : ℝ)) (R := (4 : ℝ))
    (M := M) (m := (7 / 16 : ℝ)) (f := levinsonGTrace lam T)
    (by norm_num) (by norm_num) hM1 (by norm_num)
    (analyticOnNhd_levinsonGTrace hT) (norm_levinsonGTrace_center_ge hlam) hsphere
  refine le_trans hjensen ?_
  have hnum : Real.log (M / (7 / 16 : ℝ)) ≤ A * Real.log T := by
    have hMpos : (0 : ℝ) < M := by linarith
    have hsplit : Real.log (M / (7 / 16 : ℝ)) = Real.log (C * 16 / 7) + (N : ℝ) * Real.log (4 * T) := by
      rw [hM]
      rw [show C * (4 * T) ^ N / (7 / 16 : ℝ) = (C * 16 / 7) * (4 * T) ^ N by ring]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    rw [hsplit]
    have hlog4T : Real.log (4 * T) ≤ Real.log 8 + Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity)]
      have : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
      linarith
    have hfirst : Real.log (C * 16 / 7) ≤ |Real.log (C * 16 / 7)| := le_abs_self _
    have hlog8 : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h1 : |Real.log (C * 16 / 7)| * 1 ≤ |Real.log (C * 16 / 7)| * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
    have h2 : ((N : ℝ) * Real.log 8) * 1 ≤ ((N : ℝ) * Real.log 8) * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT (by positivity)
    have h3 : (N : ℝ) * Real.log (4 * T) ≤ (N : ℝ) * (Real.log 8 + Real.log T) :=
      mul_le_mul_of_nonneg_left hlog4T hN
    rw [hA]
    nlinarith [h1, h2, h3, hfirst, hlogT, hN, hlog8]
  have hstep : Real.log (M / (7 / 16 : ℝ)) ≤ (A + 1) * Real.log T := by
    nlinarith [hnum, hlogT]
  have hdiv : Real.log (M / (7 / 16 : ℝ)) / Real.log ((4 : ℝ) / (7 / 2))
      ≤ ((A + 1) * Real.log T) / Real.log ((4 : ℝ) / (7 / 2)) := by
    gcongr
  calc Real.log (M / (7 / 16 : ℝ)) / Real.log ((4 : ℝ) / (7 / 2))
      ≤ ((A + 1) * Real.log T) / Real.log ((4 : ℝ) / (7 / 2)) := hdiv
    _ = ((A + 1) / Real.log ((4 : ℝ) / (7 / 2))) * Real.log T := by ring

end RHTower

end
