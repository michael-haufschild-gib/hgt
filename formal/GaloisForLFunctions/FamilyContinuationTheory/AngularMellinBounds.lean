import GaloisForLFunctions.FamilyContinuationTheory.AngularMellinTransform

/-! # Mellin continuation and height bounds for angular profiles

The angular Mellin identity extends to the right half-plane. One Gamma recurrence
bounds its quotient with polynomial degree independent of angular weight, yielding
rapid vertical decay and Mellin inversion on every positive line.
-/

noncomputable section
open Complex MeasureTheory Set Filter Asymptotics
open scoped Classical SchwartzMap Topology

namespace GaloisForLFunctions.FamilyContinuationTheory
open MetaplecticMobiusDescent.CubicEisenstein
open MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open MetaplecticMobiusDescent.CubicEisenstein.ProbeRadialMellin

/-- The polynomial height degree of the angular Gamma quotient is independent of the
angular weight. A single recurrence reduces it to the shifted Gamma-pair bound. -/
theorem angular_gamma_quotient_strip (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ d : ℕ, ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      ‖Complex.Gamma (((σ : ℂ) + t * Complex.I) + n) /
        Complex.Gamma (1 - ((σ : ℂ) + t * Complex.I) + n)‖ ≤
        C * (1 + |t|) ^ d := by
  obtain ⟨A, hA⟩ := exists_nat_gt hi
  refine ⟨2 * A + 2, ?_⟩
  intro n
  obtain ⟨C, hC, hb⟩ := Gamma_pair_strip_bound ((n : ℝ) + 1)
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) A
  refine ⟨C / lo, div_pos hC hlo, ?_⟩
  intro σ hσ t
  have hσ0 : 0 < σ := hlo.trans_le hσ.1
  let z : ℂ := (σ : ℂ) + t * Complex.I
  have hzre : z.re = σ := by dsimp [z]; simp
  have hzn : z + n ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re, hzre]
    positivity
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  change ‖Complex.Gamma (((n : ℝ) + 1 : ℝ) + z) /
    Complex.Gamma (((n : ℝ) + 1 : ℝ) - z)‖ ≤ _ at hh
  rw [show (((n : ℝ) + 1 : ℝ) : ℂ) + z = (z + n) + 1 by push_cast; ring,
    show (((n : ℝ) + 1 : ℝ) : ℂ) - z = 1 - z + n by push_cast; ring,
    Complex.Gamma_add_one _ hzn, mul_div_assoc, norm_mul] at hh
  have hnorm : lo ≤ ‖z + n‖ := by
    apply le_trans ?_ (Complex.re_le_norm (z + n))
    simp only [Complex.add_re, Complex.natCast_re, hzre]
    linarith [hσ.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa only [z, mul_comm] using hh'

theorem angular_mellin_differentiable (k : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) :
    DifferentiableOn ℂ (mellin (paperAngularFourier k W)) {z | 0 < z.re} := by
  intro z hz
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((paperAngularFourier_continuous k W hW).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (paperAngularFourier_isBigO_top k W hW A) hA
    (paperAngularFourier_isBigO_zero k W hW) hz).differentiableWithinAt

/-- Analytic continuation extends the angular Mellin identity over the entire right
half-plane. Reciprocal Gamma removes the apparent denominator singularities. -/
theorem angular_mellin_identity_right (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) (z : ℂ) (hz : 0 < z.re) :
    mellin (paperAngularFourier (2 * n) W) z =
      ((paperConstant : ℂ) ^ (1 - 2 * z) * Complex.Gamma (z + n) /
        Complex.Gamma (1 - z + n)) * mellin W (1 - z) := by
  let D : Set ℂ := {z | 0 < z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant : ℂ) ^ (1 - 2 * z) * Complex.Gamma (z + n) /
      Complex.Gamma (1 - z + n)) * mellin W (1 - z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperAngularFourier (2 * n) W)) D :=
    (angular_mellin_differentiable (2 * n) W hW).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant : ℂ) ^ (1 - 2 * z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := (Gamma_differentiableAt_of_re_pos (w + n) (by
      simp only [Complex.add_re, Complex.natCast_re]
      exact add_pos_of_pos_of_nonneg hw (Nat.cast_nonneg n))).comp w
        (differentiableAt_id.add_const (n : ℂ))
    have h3 := (Complex.differentiable_one_div_Gamma (1 - w + n)).comp w
      ((differentiableAt_const _ |>.sub differentiableAt_id).add_const (n : ℂ))
    have h4 := (compact_source_mellin_differentiable W (1 / 2) 2 (by norm_num) hW
      (W.smooth ⊤) (1 - w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using!
      (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperAngularFourier (2 * n) W) =ᶠ[𝓝 (1 / 2 : ℂ)] G := by
    have hstrip : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact angular_mellin_gamma n W hW w hw.1
      (by linarith [hw.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

/-- Arbitrary Mellin height decay holds on every closed strip in the right half-plane. -/
theorem angular_mellin_strip_decay (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2)
    (lo hi : ℝ) (hlo : 0 < lo) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ N * ‖mellin (paperAngularFourier (2 * n) W) ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨d, hg⟩ := angular_gamma_quotient_strip lo hi hlo
  obtain ⟨Cg, hCg, hg⟩ := hg n
  obtain ⟨Cw, hCw, hw⟩ := compact_source_mellin_strip_decay W (1 / 2) 2
    (by norm_num) hW (W.smooth ⊤) (1 - hi) (1 - lo) (d + N)
  have hc : Continuous (fun σ : ℝ => paperConstant ^ (1 - 2 * σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B| + 1
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨Cp * Cg * Cw, by positivity, ?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant : ℂ) ^ (1 - 2 * ((σ : ℂ) + t * Complex.I))‖ ≤ Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2 : ℂ).re = 2 by rfl, show (2 : ℂ).im = 0 by rfl,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans
      (by change B ≤ |B| + 1; linarith [le_abs_self B])
  have hwb := hw (1 - σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1 - σ : ℝ) : ℂ) + (-t : ℝ) * Complex.I =
    1 - ((σ : ℂ) + t * Complex.I) by push_cast; ring] at hwb
  rw [angular_mellin_identity_right n W hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1 + |t|) ^ N * (Cp * (Cg * (1 + |t|) ^ d) *
        ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp * Cg) * ((1 + |t|) ^ (d + N) *
        ‖mellin W (1 - ((σ : ℂ) + t * Complex.I))‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

theorem angular_mellin_vertical_integrable (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2) (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (paperAngularFourier (2 * n) W)) σ := by
  obtain ⟨C, hC, hb⟩ := angular_mellin_strip_decay n W hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ =>
      mellin (paperAngularFourier (2 * n) W) ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hm := (angular_mellin_differentiable (2 * n) W hW).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
    apply (hm _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using weighted_two_to_cauchy
      (norm_nonneg _) t (hb σ ⟨le_rfl, le_rfl⟩ t)

/-- Mellin inversion for every even angular trace-Fourier profile on every positive line. -/
theorem angular_mellin_inversion (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Icc (1 / 2 : ℝ) 2)
    (σ x : ℝ) (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ (mellin (paperAngularFourier (2 * n) W)) x =
      paperAngularFourier (2 * n) W x :=
  mellinInv_mellin_eq σ (paperAngularFourier (2 * n) W) hx
    (paperAngularFourier_mellin_convergent (2 * n) W hW σ hσ)
    (angular_mellin_vertical_integrable n W hW σ hσ)
    (paperAngularFourier_continuous (2 * n) W hW).continuousAt

end GaloisForLFunctions.FamilyContinuationTheory
