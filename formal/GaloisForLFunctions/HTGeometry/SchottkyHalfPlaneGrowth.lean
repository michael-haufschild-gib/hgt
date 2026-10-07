import GaloisForLFunctions.HTGeometry.SchottkyDiskGrowth
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# Two omitted values force exponential growth on a half-plane's central ray

The disk's reciprocal-boundary-distance Schottky estimate becomes linear in
the real coordinate under the Cayley map.
-/

open Complex Metric Set
open Bottcher

namespace GaloisForLFunctions.HTGeometry

/-- A holomorphic half-plane map omitting zero and one grows at most exponentially on its ray. -/
theorem exists_exp_ray_bound_of_omitting_halfPlane (R : ℝ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | R < z.re})
    (homit : ∀ z : ℂ, R < z.re → f z ≠ 0 ∧ f z ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖f ((R + t : ℝ) : ℂ)‖ ≤ Real.exp (C * t) := by
  let φ : ℂ → ℂ := fun z => (R : ℂ) + (1 + z) / (1 - z)
  have hne : ∀ z ∈ ball (0 : ℂ) 1, (1 : ℂ) - z ≠ 0 := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    exact sub_ne_zero.mpr (by intro he; simp [← he] at hn)
  have hφ : ∀ z ∈ ball (0 : ℂ) 1, R < (φ z).re := by
    intro z hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have hy := cayleyInv_im_pos_of_norm_lt_one hn
    have he : (φ z).re = R + (cayleyInv z).im := by
      simp [φ, cayleyInv, Complex.mul_im]
    rw [he]
    linarith
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := by
    intro z hz
    dsimp [φ]
    have hnum : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun z : ℂ => 1 - z) z := by fun_prop
    exact ((hnum.div hden (hne z hz)).const_add (R : ℂ)).differentiableWithinAt
  have hfd : DifferentiableOn ℂ (f ∘ φ) (ball 0 1) := hf.comp hφd hφ
  obtain ⟨C, hC, hbound⟩ := exists_exp_bound_of_omitting_disk hfd
    (fun z hz => homit (φ z) (hφ z hz))
  refine ⟨C + 20001, by linarith, fun t ht => ?_⟩
  let r : ℝ := (t - 1) / (t + 1)
  have htpos : 0 < t + 1 := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) htpos.le
  have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one htpos]; linarith
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hstep : 1 + r = t * (1 - r) := by dsimp [r]; field_simp; ring
  have hdenr : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr hr1))
  have hquot : (1 + (r : ℂ)) / (1 - (r : ℂ)) = (t : ℂ) := by
    apply (div_eq_iff hdenr).mpr
    exact_mod_cast hstep
  have hchart : φ (r : ℂ) = ((R + t : ℝ) : ℂ) := by
    simp only [φ, hquot, Complex.ofReal_add]
  have hb := hbound (r : ℂ) (by simpa only [hrnorm] using hr1)
  simp only [Function.comp_apply, hchart, hrnorm] at hb
  have harg : C / (1 - r) ≤ C * t := by
    rw [div_le_iff₀ (sub_pos.mpr hr1)]
    calc
      C ≤ C * (1 + r) := by nlinarith [mul_nonneg hC.le hr0]
      _ = C * t * (1 - r) := by rw [hstep]; ring
  have hconst : (20001 : ℝ) ≤ Real.exp 20001 := by
    linarith [Real.add_one_le_exp (20001 : ℝ)]
  calc
    ‖f ((R + t : ℝ) : ℂ)‖ ≤ 20001 * Real.exp (C / (1 - r)) := hb
    _ ≤ 20001 * Real.exp (C * t) := by gcongr
    _ ≤ Real.exp 20001 * Real.exp (C * t) :=
      mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le
    _ = Real.exp (20001 + C * t) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C + 20001) * t) := by apply Real.exp_le_exp.mpr; nlinarith

/-- The same ray bound for any two distinct omitted finite values. -/
theorem exists_exp_ray_bound_of_omitting_two_halfPlane (R : ℝ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | R < z.re}) {a b : ℂ} (hab : a ≠ b)
    (homit : ∀ z : ℂ, R < z.re → f z ≠ a ∧ f z ≠ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ‖f ((R + t : ℝ) : ℂ)‖ ≤ Real.exp (C * t) := by
  let g : ℂ → ℂ := fun z => (f z - a) / (b - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hgd : DifferentiableOn ℂ g {z : ℂ | R < z.re} := (hf.sub_const a).div_const (b - a)
  have hgo : ∀ z : ℂ, R < z.re → g z ≠ 0 ∧ g z ≠ 1 := by
    intro z hz
    obtain ⟨ha, hb⟩ := homit z hz
    refine ⟨div_ne_zero (sub_ne_zero.mpr ha) hba, ?_⟩
    intro he
    have he' : f z - a = b - a := (div_eq_one_iff_eq hba).mp he
    exact hb (by linear_combination he')
  obtain ⟨C, hC, hbound⟩ := exists_exp_ray_bound_of_omitting_halfPlane R hgd hgo
  let M : ℝ := ‖b - a‖ + ‖a‖
  have hM : 0 < M := add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hba) (norm_nonneg a)
  refine ⟨C + M, add_pos hC hM, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hE : 1 ≤ Real.exp (C * t) := Real.one_le_exp (mul_nonneg hC.le ht0)
  have heq : (b - a) * g ((R + t : ℝ) : ℂ) + a = f ((R + t : ℝ) : ℂ) := by
    dsimp [g]
    field_simp
    ring
  have hn : ‖f ((R + t : ℝ) : ℂ)‖ ≤ M * Real.exp (C * t) := by
    rw [← heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hb := mul_le_mul_of_nonneg_left (hbound t ht) (norm_nonneg (b - a))
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hE (norm_nonneg a)]
  have hMe : M ≤ Real.exp (M * t) := by
    have hm : M ≤ M * t := by nlinarith
    linarith [Real.add_one_le_exp (M * t)]
  calc
    ‖f ((R + t : ℝ) : ℂ)‖ ≤ M * Real.exp (C * t) := hn
    _ ≤ Real.exp (M * t) * Real.exp (C * t) :=
      mul_le_mul_of_nonneg_right hMe (Real.exp_pos _).le
    _ = Real.exp ((C + M) * t) := by rw [← Real.exp_add]; congr 1; ring

/-- A fixed polynomial preserves an exponential bound along the shifted real ray. -/
theorem exists_exp_ray_bound_polynomial (R : ℝ) (p : Polynomial ℂ) {f : ℂ → ℂ}
    (hbound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖f ((R + t : ℝ) : ℂ)‖ ≤ Real.exp (C * t)) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 1 ≤ t →
      ‖p.eval (f ((R + t : ℝ) : ℂ))‖ ≤ Real.exp (D * t) := by
  obtain ⟨C, hC, hf⟩ := hbound
  obtain ⟨M, d, hM, hp⟩ := exists_polynomial_norm_bound p
  refine ⟨M + d * (C + 1) + 1, by positivity, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hE : 1 ≤ Real.exp (C * t) := Real.one_le_exp (by positivity)
  have he2 : 2 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hf1 : 1 + ‖f ((R + t : ℝ) : ℂ)‖ ≤ Real.exp ((C + 1) * t) := by
    calc
      _ ≤ 2 * Real.exp (C * t) := by linarith [hf t ht]
      _ ≤ Real.exp t * Real.exp (C * t) :=
        mul_le_mul_of_nonneg_right he2 (Real.exp_pos _).le
      _ = Real.exp ((C + 1) * t) := by rw [← Real.exp_add]; congr 1; ring
  have hMe : M ≤ Real.exp (M * t) := by
    have hm : M ≤ M * t := by nlinarith
    linarith [Real.add_one_le_exp (M * t)]
  calc
    ‖p.eval (f ((R + t : ℝ) : ℂ))‖ ≤ M * (1 + ‖f ((R + t : ℝ) : ℂ)‖) ^ d := hp _
    _ ≤ M * (Real.exp ((C + 1) * t)) ^ d := by gcongr
    _ ≤ Real.exp (M * t) * (Real.exp ((C + 1) * t)) ^ d := by gcongr
    _ = Real.exp ((M + d * (C + 1)) * t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((M + d * (C + 1) + 1) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end GaloisForLFunctions.HTGeometry
