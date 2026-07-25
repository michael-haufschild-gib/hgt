import GaloisForLFunctions.HTGeometry.AbstractSpectralFamily
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Half-plane decay for an abstract spectral family

The Phragmén--Lindelöf step over an arbitrary index type.  Twisting the trace by the family's least
height makes both boundary rays of the lower quadrants bounded, and the order-one envelope supplies
the `∃ c < 2` growth condition, so boundedness on one vertical line upgrades to decay at the
least-height rate on the whole half-plane.
-/

open Complex Filter Asymptotics
open scoped BigOperators

namespace HTGeometry

namespace AbstractSpectralFamily

noncomputable section

variable {ι : Type*} [Nonempty ι] (F : AbstractSpectralFamily ι)

/-- An index of least height. -/
def bottomIndex : ι :=
  Classical.choose (F.exists_min_re_of_nonempty (s := (Set.univ : Set ι))
    ⟨Classical.arbitrary ι, trivial⟩)

theorem bottomIndex_min (i : ι) : (F.pt F.bottomIndex).re ≤ (F.pt i).re :=
  (Classical.choose_spec (F.exists_min_re_of_nonempty (s := (Set.univ : Set ι))
    ⟨Classical.arbitrary ι, trivial⟩)).2 i trivial

/-- The least height of the family. -/
def bottomHeight : ℝ := (F.pt F.bottomIndex).re

theorem bottomHeight_le (i : ι) : F.bottomHeight ≤ (F.pt i).re := F.bottomIndex_min i

theorem bottomHeight_pos : 0 < F.bottomHeight := lt_of_lt_of_le F.base_pos (F.base_le _)

theorem exp_bottomHeight_mul_traceReal_le {σ : ℝ} (hσ : 0 < σ) {v : ℝ} (hv : 0 ≤ v) :
    Real.exp (F.bottomHeight * v) * F.traceReal (σ + v) ≤ F.traceReal σ := by
  have hterm : ∀ i : ι,
      Real.exp (F.bottomHeight * v) * F.weight (σ + v) i ≤ F.weight σ i := by
    intro i
    rw [weight, weight, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [F.bottomHeight_le i, hv]
  calc Real.exp (F.bottomHeight * v) * F.traceReal (σ + v)
      = ∑' i : ι, Real.exp (F.bottomHeight * v) * F.weight (σ + v) i := by
        rw [traceReal, tsum_mul_left]
    _ ≤ ∑' i : ι, F.weight σ i :=
        Summable.tsum_le_tsum hterm ((F.summable_weight (by linarith)).mul_left _)
          (F.summable_weight hσ)
    _ = F.traceReal σ := rfl

/-- The least-height twist of the trace. -/
def twist (σ : ℝ) (y : ℂ) : ℂ :=
  F.traceC ((σ : ℂ) + y * I) * Complex.exp (I * (F.bottomHeight : ℂ) * y)

theorem norm_exp_twist (y : ℂ) :
    ‖Complex.exp (I * (F.bottomHeight : ℂ) * y)‖ = Real.exp (-(F.bottomHeight * y.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem differentiableOn_twist (σ : ℝ) :
    DifferentiableOn ℂ (F.twist σ) {y : ℂ | y.im < σ} := by
  intro y hy
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    have hlt : y.im < σ := hy
    linarith
  have h1 : DifferentiableAt ℂ (fun z : ℂ => F.traceC ((σ : ℂ) + z * I)) y := by
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => (σ : ℂ) + z * I) y := by fun_prop
    exact (F.differentiableAt_traceC hre).comp y hcomp
  have h2 : DifferentiableAt ℂ
      (fun z : ℂ => Complex.exp (I * (F.bottomHeight : ℂ) * z)) y := by fun_prop
  exact ((h1.mul h2)).differentiableWithinAt

theorem norm_twist_le {σ : ℝ} (hσ : 0 < σ) {y : ℂ} (hy : y.im ≤ 0) :
    ‖F.twist σ y‖ ≤ F.traceReal σ * Real.exp ((1 / 2 + F.bottomHeight) * ‖y‖) := by
  have hre : 0 < ((σ : ℂ) + y * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    linarith
  have hreEq : ((σ : ℂ) + y * I).re = σ - y.im := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub]
    ring
  have himEq : ((σ : ℂ) + y * I).im = y.re := by simp [Complex.mul_im]
  have hΘ := F.norm_traceC_le hre
  rw [himEq, hreEq] at hΘ
  have hmono : F.traceReal (σ - y.im) ≤ F.traceReal σ := by
    have h := F.traceReal_antitone (σ := σ) (v := -y.im) hσ (by linarith)
    have heq : σ + -y.im = σ - y.im := by ring
    rwa [heq] at h
  have hΘ' : ‖F.traceC ((σ : ℂ) + y * I)‖ ≤ Real.exp (|y.re| / 2) * F.traceReal σ :=
    hΘ.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le)
  rw [twist, norm_mul, F.norm_exp_twist]
  have hb1 : |y.re| / 2 ≤ ‖y‖ / 2 := by
    have := Complex.abs_re_le_norm y
    linarith
  have hb2 : -(F.bottomHeight * y.im) ≤ F.bottomHeight * ‖y‖ := by
    have him : |y.im| ≤ ‖y‖ := Complex.abs_im_le_norm y
    have h1 : -y.im ≤ ‖y‖ := le_trans (neg_le_abs _) him
    nlinarith [F.bottomHeight_pos]
  calc ‖F.traceC ((σ : ℂ) + y * I)‖ * Real.exp (-(F.bottomHeight * y.im))
      ≤ (Real.exp (|y.re| / 2) * F.traceReal σ) * Real.exp (F.bottomHeight * ‖y‖) := by
        refine mul_le_mul hΘ' (Real.exp_le_exp.mpr hb2) (Real.exp_pos _).le ?_
        exact mul_nonneg (Real.exp_pos _).le (F.traceReal_nonneg σ)
    _ ≤ F.traceReal σ * Real.exp ((1 / 2 + F.bottomHeight) * ‖y‖) := by
        rw [mul_comm (Real.exp (|y.re| / 2)), mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (F.traceReal_nonneg σ)
        nlinarith [hb1]

theorem norm_twist_imaginary_ray {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : x ≤ 0) :
    ‖F.twist σ ((x : ℂ) * I)‖ ≤ F.traceReal σ := by
  have harg : (σ : ℂ) + ((x : ℂ) * I) * I = ((σ - x : ℝ) : ℂ) := by
    have hxx : ((x : ℂ) * I) * I = -(x : ℂ) := by rw [mul_assoc, Complex.I_mul_I]; ring
    rw [hxx]; push_cast; ring
  have hre : 0 < (((σ - x : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]; linarith
  have hΘ := F.norm_traceC_le hre
  simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_div, Real.exp_zero,
    one_mul] at hΘ
  have htw : ‖Complex.exp (I * (F.bottomHeight : ℂ) * ((x : ℂ) * I))‖ =
      Real.exp (-(F.bottomHeight * x)) := by
    rw [F.norm_exp_twist]
    congr 2
    simp
  rw [twist, norm_mul, harg, htw]
  have hkey := F.exp_bottomHeight_mul_traceReal_le hσ (v := -x) (by linarith)
  rw [show σ + -x = σ - x from by ring] at hkey
  rw [show Real.exp (-(F.bottomHeight * x)) = Real.exp (F.bottomHeight * -x) from by
    congr 1; ring, mul_comm]
  exact le_trans (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _).le) hkey

theorem norm_twist_real_ray {σ C : ℝ}
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) (x : ℝ) :
    ‖F.twist σ ((x : ℝ) : ℂ)‖ ≤ C := by
  rw [twist, norm_mul, F.norm_exp_twist]
  simp only [Complex.ofReal_im, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact hline x

/-- **Phragmén--Lindelöf for an abstract spectral family.** -/
theorem norm_twist_le_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {y : ℂ} (hy : y.im ≤ 0) :
    ‖F.twist σ y‖ ≤ max C (F.traceReal σ) := by
  have hsub : ∀ s t : Set ℝ, closure (s ×ℂ t) ⊆ {z : ℂ | z.im < σ} →
      DiffContOnCl ℂ (F.twist σ) (s ×ℂ t) := fun s t hsu =>
    ⟨(F.differentiableOn_twist σ).mono (subset_closure.trans hsu),
      ((F.differentiableOn_twist σ).mono hsu).continuousOn⟩
  have hclos : ∀ s : Set ℝ, closure (s ×ℂ Set.Iio 0) ⊆ {z : ℂ | z.im < σ} := by
    intro s z hz
    rw [Complex.closure_reProdIm, closure_Iio] at hz
    have h := (Complex.mem_reProdIm.mp hz).2
    simp only [Set.mem_Iic] at h
    simp only [Set.mem_setOf_eq]
    linarith
  have hgrow : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≤ 0) →
      ∃ c < (2 : ℝ), ∃ B, (F.twist σ) =O[Bornology.cobounded ℂ ⊓ 𝓟 S]
        fun z => Real.exp (B * ‖z‖ ^ c) := by
    intro S hS
    refine ⟨1, by norm_num, 1 / 2 + F.bottomHeight, isBigO_iff.mpr ⟨F.traceReal σ, ?_⟩⟩
    rw [eventually_inf_principal]
    filter_upwards with z hz
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact F.norm_twist_le hσ (hS z hz)
  have hrealRay : ∀ x : ℝ, ‖F.twist σ ((x : ℝ) : ℂ)‖ ≤ max C (F.traceReal σ) :=
    fun x => le_trans (F.norm_twist_real_ray hline x) (le_max_left _ _)
  rcases le_or_gt y.re 0 with hcase | hcase
  · exact PhragmenLindelof.quadrant_III
      (hsub (Set.Iio 0) (Set.Iio 0) (hclos (Set.Iio 0)))
      (hgrow (Set.Iio 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (F.norm_twist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase hy
  · exact PhragmenLindelof.quadrant_IV
      (hsub (Set.Ioi 0) (Set.Iio 0) (hclos (Set.Ioi 0)))
      (hgrow (Set.Ioi 0 ×ℂ Set.Iio 0)
        (fun z hz => (Set.mem_Iio.mp (Complex.mem_reProdIm.mp hz).2).le))
      (fun x _ => hrealRay x)
      (fun x hx => le_trans (F.norm_twist_imaginary_ray hσ hx) (le_max_right _ _))
      hcase.le hy

/-- **Half-plane decay for an abstract spectral family.** -/
theorem norm_traceC_le_of_line_bound {σ C : ℝ} (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖F.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C)
    {t : ℂ} (ht : σ ≤ t.re) :
    ‖F.traceC t‖ ≤ max C (F.traceReal σ) * Real.exp (-(F.bottomHeight * (t.re - σ))) := by
  set y : ℂ := -I * (t - (σ : ℂ)) with hy
  have hyim : y.im = σ - t.re := by rw [hy]; simp [Complex.mul_im]
  have hyle : y.im ≤ 0 := by rw [hyim]; linarith
  have harg : (σ : ℂ) + y * I = t := by
    rw [hy]
    have hxx : (-I * (t - (σ : ℂ))) * I = t - (σ : ℂ) := by
      rw [mul_comm (-I) _, mul_assoc]
      simp [Complex.I_mul_I]
    rw [hxx]; ring
  have hpl := F.norm_twist_le_of_line_bound hσ hline hyle
  rw [twist, harg, norm_mul, F.norm_exp_twist, hyim] at hpl
  rw [show Real.exp (-(F.bottomHeight * (σ - t.re))) =
      Real.exp (F.bottomHeight * (t.re - σ)) from by congr 1; ring] at hpl
  rw [← le_div_iff₀ (Real.exp_pos _)] at hpl
  refine le_trans hpl (le_of_eq ?_)
  rw [Real.exp_neg]
  field_simp

end

end AbstractSpectralFamily

end HTGeometry
