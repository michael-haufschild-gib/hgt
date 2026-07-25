import GaloisForLFunctions.RHTower.XiPoissonCutTrace

/-!
# Half-plane decay for a cut divisor

The Phragmén--Lindelöf argument of the full divisor, run above a height cut.  The twist is by the
cut's own least height, and the imaginary-ray bound holds for the same reason as before: every height
in the cut is at least the cut's least height.
-/

open Complex Filter Asymptotics
open scoped BigOperators

namespace RHTower

noncomputable section

open scoped Classical in
/-- The least height of a cut divisor (junk value `0` when the cut is empty). -/
def xiPoissonCutHeight (g : ℝ) : ℝ :=
  if h : (xiPoissonCut g).Nonempty then
    (xiPoissonPoint (Classical.choose (exists_min_xiPoissonPoint_re_of_nonempty h))).re
  else 0

theorem xiPoissonCutHeight_le {g : ℝ} {q : XiZeroCopy} (hq : q ∈ xiPoissonCut g) :
    xiPoissonCutHeight g ≤ (xiPoissonPoint q).re := by
  classical
  rw [xiPoissonCutHeight, dif_pos ⟨q, hq⟩]
  exact (Classical.choose_spec (exists_min_xiPoissonPoint_re_of_nonempty ⟨q, hq⟩)).2 q hq

theorem xiPoissonCutHeight_nonneg (g : ℝ) : 0 ≤ xiPoissonCutHeight g := by
  classical
  rw [xiPoissonCutHeight]
  split_ifs with h
  · exact xiPoissonPoint_re_nonneg _
  · exact le_refl 0

/-- The cut analogue of the imaginary-ray bound. -/
theorem exp_cutHeight_mul_xiPoissonCutTraceReal_le {g σ : ℝ} (hσ : 0 < σ) {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (xiPoissonCutHeight g * v) * xiPoissonCutTraceReal g (σ + v) ≤
      xiPoissonCutTraceReal g σ := by
  have hterm : ∀ q : xiPoissonCut g,
      Real.exp (xiPoissonCutHeight g * v) * xiPoissonWeight (σ + v) (q : XiZeroCopy) ≤
        xiPoissonWeight σ (q : XiZeroCopy) := by
    intro q
    have hR : xiPoissonCutHeight g ≤ (xiPoissonPoint (q : XiZeroCopy)).re :=
      xiPoissonCutHeight_le q.2
    rw [xiPoissonWeight, xiPoissonWeight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hR, hv]
  calc Real.exp (xiPoissonCutHeight g * v) * xiPoissonCutTraceReal g (σ + v)
      = ∑' q : xiPoissonCut g,
          Real.exp (xiPoissonCutHeight g * v) * xiPoissonWeight (σ + v) (q : XiZeroCopy) := by
        rw [xiPoissonCutTraceReal, tsum_mul_left]
    _ ≤ ∑' q : xiPoissonCut g, xiPoissonWeight σ (q : XiZeroCopy) :=
        Summable.tsum_le_tsum hterm
          ((summable_xiPoissonCutWeight (by linarith) g).mul_left _)
          (summable_xiPoissonCutWeight hσ g)
    _ = xiPoissonCutTraceReal g σ := rfl

/-- The cut-height twist of the cut trace. -/
def xiPoissonCutTwist (g σ : ℝ) (y : ℂ) : ℂ :=
  xiPoissonCutTraceC g ((σ : ℂ) + y * I) *
    Complex.exp (I * (xiPoissonCutHeight g : ℂ) * y)

theorem norm_exp_cutTwist (g : ℝ) (y : ℂ) :
    ‖Complex.exp (I * (xiPoissonCutHeight g : ℂ) * y)‖ =
      Real.exp (-(xiPoissonCutHeight g * y.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem differentiableOn_xiPoissonCutTwist (g σ : ℝ) :
    DifferentiableOn ℂ (xiPoissonCutTwist g σ) {y : ℂ | y.im < σ} := by
  intro y hy
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    have hlt : y.im < σ := hy
    linarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => xiPoissonCutTraceC g ((σ : ℂ) + z * I)) y := by
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => (σ : ℂ) + z * I) y := by fun_prop
    exact (differentiableAt_xiPoissonCutTraceC hre).comp y hcomp
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (I * (xiPoissonCutHeight g : ℂ) * z)) y := by fun_prop
  exact ((h1.mul h2)).differentiableWithinAt

theorem norm_xiPoissonCutTwist_le {g σ : ℝ} (hσ : 0 < σ) {y : ℂ} (hy : y.im ≤ 0) :
    ‖xiPoissonCutTwist g σ y‖ ≤
      xiPoissonCutTraceReal g σ *
        Real.exp ((1 / 2 + xiPoissonCutHeight g) * ‖y‖) := by
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    linarith
  have hreEq : ((σ : ℂ) + y * I).re = σ - y.im := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    ring
  have himEq : ((σ : ℂ) + y * I).im = y.re := by
    simp [Complex.mul_im]
  have hΘ := norm_xiPoissonCutTraceC_le (g := g) (τ := (σ : ℂ) + y * I) hre
  rw [himEq, hreEq] at hΘ
  have hmono : xiPoissonCutTraceReal g (σ - y.im) ≤ xiPoissonCutTraceReal g σ := by
    have h := xiPoissonCutTraceReal_antitone (g := g) (σ := σ) (v := -y.im) hσ (by linarith)
    have heq : σ + -y.im = σ - y.im := by ring
    rwa [heq] at h
  have hΘ' : ‖xiPoissonCutTraceC g ((σ : ℂ) + y * I)‖ ≤
      Real.exp (|y.re| / 2) * xiPoissonCutTraceReal g σ := by
    refine hΘ.trans ?_
    exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  rw [xiPoissonCutTwist, norm_mul, norm_exp_cutTwist]
  have hb1 : |y.re| / 2 ≤ ‖y‖ / 2 := by
    have := Complex.abs_re_le_norm y
    linarith
  have hb2 : -(xiPoissonCutHeight g * y.im) ≤ xiPoissonCutHeight g * ‖y‖ := by
    have him : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    have h1 : -y.im ≤ ‖y‖ := le_trans (neg_le_abs _) him
    nlinarith [xiPoissonCutHeight_nonneg g]
  calc ‖xiPoissonCutTraceC g ((σ : ℂ) + y * I)‖ * Real.exp (-(xiPoissonCutHeight g * y.im))
      ≤ (Real.exp (|y.re| / 2) * xiPoissonCutTraceReal g σ) *
          Real.exp (xiPoissonCutHeight g * ‖y‖) := by
        refine mul_le_mul hΘ' (Real.exp_le_exp.mpr hb2) (Real.exp_pos _).le ?_
        exact mul_nonneg (Real.exp_pos _).le (xiPoissonCutTraceReal_nonneg g σ)
    _ ≤ xiPoissonCutTraceReal g σ * Real.exp ((1 / 2 + xiPoissonCutHeight g) * ‖y‖) := by
        rw [mul_comm (Real.exp (|y.re| / 2)), mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
        · nlinarith [hb1]
        · exact xiPoissonCutTraceReal_nonneg g σ

theorem norm_xiPoissonCutTwist_imaginary_ray {g σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : x ≤ 0) :
    ‖xiPoissonCutTwist g σ ((x : ℂ) * I)‖ ≤ xiPoissonCutTraceReal g σ := by
  have harg : (σ : ℂ) + ((x : ℂ) * I) * I = ((σ - x : ℝ) : ℂ) := by
    have hxx : ((x : ℂ) * I) * I = -(x : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]; ring
    rw [hxx]
    push_cast
    ring
  have hre : 0 < (((σ - x : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hΘ := norm_xiPoissonCutTraceC_le (g := g) (τ := ((σ - x : ℝ) : ℂ)) hre
  simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_div, Real.exp_zero,
    one_mul] at hΘ
  have htw : ‖Complex.exp (I * (xiPoissonCutHeight g : ℂ) * ((x : ℂ) * I))‖ =
      Real.exp (-(xiPoissonCutHeight g * x)) := by
    rw [norm_exp_cutTwist]
    congr 2
    simp
  rw [xiPoissonCutTwist, norm_mul, harg, htw]
  have hkey := exp_cutHeight_mul_xiPoissonCutTraceReal_le (g := g) hσ (v := -x) (by linarith)
  have hrw : σ + -x = σ - x := by ring
  rw [hrw] at hkey
  have hexp : Real.exp (-(xiPoissonCutHeight g * x)) =
      Real.exp (xiPoissonCutHeight g * -x) := by congr 1; ring
  rw [hexp, mul_comm]
  refine le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) hkey

theorem norm_xiPoissonCutTwist_real_ray {g σ C : ℝ}
    (hline : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) (x : ℝ) :
    ‖xiPoissonCutTwist g σ ((x : ℝ) : ℂ)‖ ≤ C := by
  rw [xiPoissonCutTwist, norm_mul, norm_exp_cutTwist]
  simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact hline x

/-- **Phragmén--Lindelöf for a cut divisor.** -/
theorem norm_xiPoissonCutTwist_le_of_line_bound {g σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {y : ℂ} (hy : y.im ≤ 0) :
    ‖xiPoissonCutTwist g σ y‖ ≤ max C (xiPoissonCutTraceReal g σ) := by
  have hdiff := differentiableOn_xiPoissonCutTwist g σ
  have hsub : ∀ s t : Set ℝ, closure (s ×ℂ t) ⊆ {z : ℂ | z.im < σ} →
      DiffContOnCl ℂ (xiPoissonCutTwist g σ) (s ×ℂ t) := by
    intro s t hsu
    exact ⟨hdiff.mono (subset_closure.trans hsu), (hdiff.mono hsu).continuousOn⟩
  have hclos : ∀ s : Set ℝ, closure (s ×ℂ Set.Iio 0) ⊆ {z : ℂ | z.im < σ} := by
    intro s z hz
    rw [Complex.closure_reProdIm, closure_Iio] at hz
    have h := (Complex.mem_reProdIm.mp hz).2
    simp only [Set.mem_Iic] at h
    simp only [Set.mem_setOf_eq]
    linarith
  have hO : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≤ 0) →
      (xiPoissonCutTwist g σ) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        (fun z => Real.exp ((1 / 2 + xiPoissonCutHeight g) * ‖z‖ ^ (1 : ℝ))) := by
    intro S hS
    refine isBigO_iff.mpr ⟨xiPoissonCutTraceReal g σ, ?_⟩
    rw [eventually_inf_principal]
    filter_upwards with z hz
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact norm_xiPoissonCutTwist_le hσ (hS z hz)
  have hgrow : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≤ 0) →
      ∃ c < (2 : ℝ), ∃ B, (xiPoissonCutTwist g σ) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        fun z => Real.exp (B * ‖z‖ ^ c) :=
    fun S hS => ⟨1, by norm_num, 1 / 2 + xiPoissonCutHeight g, hO S hS⟩
  have hrealRay : ∀ x : ℝ,
      ‖xiPoissonCutTwist g σ ((x : ℝ) : ℂ)‖ ≤ max C (xiPoissonCutTraceReal g σ) :=
    fun x => le_trans (norm_xiPoissonCutTwist_real_ray hline x) (le_max_left _ _)
  rcases le_or_gt y.re 0 with hcase | hcase
  · refine PhragmenLindelof.quadrant_III
      (hsub (Set.Iio 0) (Set.Iio 0) (hclos (Set.Iio 0)))
      (hgrow (Set.Iio 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (norm_xiPoissonCutTwist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase hy
  · refine PhragmenLindelof.quadrant_IV
      (hsub (Set.Ioi 0) (Set.Iio 0) (hclos (Set.Ioi 0)))
      (hgrow (Set.Ioi 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (norm_xiPoissonCutTwist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase.le hy

/-- **Half-plane decay for a cut divisor.** -/
theorem norm_xiPoissonCutTraceC_le_of_line_bound {g σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖xiPoissonCutTraceC g ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {t : ℂ} (ht : σ ≤ t.re) :
    ‖xiPoissonCutTraceC g t‖ ≤
      max C (xiPoissonCutTraceReal g σ) *
        Real.exp (-(xiPoissonCutHeight g * (t.re - σ))) := by
  set y : ℂ := -I * (t - (σ : ℂ)) with hy
  have hyim : y.im = σ - t.re := by
    rw [hy]
    simp [Complex.mul_im]
  have hyle : y.im ≤ 0 := by rw [hyim]; linarith
  have harg : (σ : ℂ) + y * I = t := by
    rw [hy]
    have hxx : (-I * (t - (σ : ℂ))) * I = t - (σ : ℂ) := by
      rw [mul_comm (-I) _, mul_assoc]
      simp [Complex.I_mul_I]
    rw [hxx]
    ring
  have hpl := norm_xiPoissonCutTwist_le_of_line_bound hσ hline hyle
  rw [xiPoissonCutTwist, harg, norm_mul, norm_exp_cutTwist, hyim] at hpl
  have hexp : Real.exp (-(xiPoissonCutHeight g * (σ - t.re))) =
      Real.exp (xiPoissonCutHeight g * (t.re - σ)) := by congr 1; ring
  rw [hexp] at hpl
  rw [← le_div_iff₀ (Real.exp_pos _)] at hpl
  refine le_trans hpl (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

end

end RHTower
