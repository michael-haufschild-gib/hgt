import GaloisForLFunctions.RHTower.ChiPhysicalStationaryKernel
import GaloisForLFunctions.RHTower.BagPhysicalWindowGram

/-!
# Physical mass of the complete moving-chi product

A pointwise logarithmic lower bound and the source chi curvature theorem control
physical mass without expanding the product into grades. Every factor, product
frequency, and cross term remains present. The source height window supplies its
own derivative variation and positive mass. No phase independence or frequency
support bound is assumed. Normalized affine factors retain an energy-scale lower
bound. This does not provide the separate signed self-target error estimate.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped BigOperators
namespace RHTower
open GaloisForLFunctions.RHTower


private theorem factor_exp_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    Real.exp (2 * z.re - 25 * ‖z‖ ^ 2) ≤ ‖1 + z‖ ^ 2 := by
  have hr := Complex.abs_re_le_norm z
  have hn := norm_nonneg z
  have hnear := norm_sub_norm_le (1 : ℂ) (-z)
  simp only [norm_one, norm_neg, sub_neg_eq_add] at hnear
  have hx : (1 / 4 : ℝ) ≤ ‖1 + z‖ ^ 2 := by nlinarith [norm_nonneg (1 + z)]
  have hid : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  have hrlo : -‖z‖ ≤ z.re := (abs_le.mp hr).1
  have hrhi : z.re ≤ ‖z‖ := (abs_le.mp hr).2
  have hzsq : ‖z‖ ^ 2 ≤ ‖z‖ / 2 := by nlinarith
  have hdiff : |‖1 + z‖ ^ 2 - 1| ≤ (5 / 2 : ℝ) * ‖z‖ := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdiffsq : (‖1 + z‖ ^ 2 - 1) ^ 2 ≤ (25 / 4 : ℝ) * ‖z‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
    nlinarith only [hh, sq_abs (‖1 + z‖ ^ 2 - 1)]
  have hxpos : 0 < ‖1 + z‖ ^ 2 := by linarith
  have hdef : (‖1 + z‖ ^ 2 - 1) ^ 2 / ‖1 + z‖ ^ 2 ≤ 25 * ‖z‖ ^ 2 := by
    apply (div_le_iff₀ hxpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg ‖z‖)]
  have halg : 1 - (‖1 + z‖ ^ 2)⁻¹ =
      (‖1 + z‖ ^ 2 - 1) - (‖1 + z‖ ^ 2 - 1) ^ 2 / ‖1 + z‖ ^ 2 := by
    field_simp [(show ‖1 + z‖ ≠ 0 by intro h; rw [h] at hxpos; norm_num at hxpos)]
    ring
  apply (Real.le_log_iff_exp_le hxpos).mp
  have hh := Real.one_sub_inv_le_log_of_pos hxpos
  rw [halg] at hh
  nlinarith

/-- The actual physical window has a uniform first-grade chi mean estimate. -/
theorem exists_physicalWindow_chi_firstMean :
    ∃ B : ℝ, 0 < B ∧ ∀ T : ℝ, 4 ≤ T → ∀ ω : ℝ,
      ‖∫ t in T..2 * T, (bagPhysicalHeightWindow (t / T) : ℂ) *
        (zetaChi (linePt t) * Complex.exp (((ω * t : ℝ) : ℂ) * I))‖ ≤ B * Real.sqrt T := by
  obtain ⟨C, hC, hvar⟩ := exists_physicalWindow_variation
  refine ⟨60 * C, by positivity, ?_⟩
  intro T hT ω
  have hT0 : 0 < T := by linarith
  obtain ⟨hder, hint, hb⟩ := hvar T hT0
  have hh := norm_integral_complexAmplitude_mul_zetaChi_line_mul_exp_le hT ω
    (fun t _ => hder t) hint
  have hs : 6 / Real.sqrt (1 / (100 * T)) = 60 * Real.sqrt T := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
    norm_num [div_div, div_eq_mul_inv]
    ring
  rw [hs] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 60 * Real.sqrt T by positivity)])

/-- The literal moving-chi product, retaining every grade and every product frequency. -/
def chiProductResonator {ι : Type*} (S : Finset ι) (u : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∏ j ∈ S, (1 + u j * (zetaChi (linePt t) * Complex.exp (((freq j * t : ℝ) : ℂ) * I)))

private theorem continuous_chiProductResonator {ι : Type*}
    (S : Finset ι) (u : ι → ℂ) (freq : ι → ℝ) :
    Continuous (chiProductResonator S u freq) := by
  unfold chiProductResonator
  exact continuous_finsetProd S (fun j _ => continuous_const.add
    (continuous_const.mul (continuous_zetaChiCriticalTwistIntegrand (freq j))))

private theorem product_exp_lower {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ j ∈ S, ‖z j‖ ≤ 1 / 2) :
    Real.exp (2 * (∑ j ∈ S, z j).re - 25 * ∑ j ∈ S, ‖z j‖ ^ 2) ≤
      ‖∏ j ∈ S, (1 + z j)‖ ^ 2 := by
  calc
    _ = ∏ j ∈ S, Real.exp (2 * (z j).re - 25 * ‖z j‖ ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Complex.re_sum, Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ ∏ j ∈ S, ‖1 + z j‖ ^ 2 := Finset.prod_le_prod
      (fun j _ => (Real.exp_pos _).le) (fun j hj => factor_exp_lower (hz j hj))
    _ = _ := by rw [norm_prod, Finset.prod_pow]

private theorem physicalWindow_mass {T : ℝ} (hT : 0 < T) :
    (∫ t in T..2 * T, bagPhysicalHeightWindow (t / T)) = T * bagPhysicalHeightMass := by
  rw [intervalIntegral.integral_comp_div _ hT.ne']
  simp only [div_self hT.ne', mul_div_cancel_right₀ _ hT.ne', smul_eq_mul, bagPhysicalHeightMass]

private theorem exp_tangent (a x : ℝ) :
    Real.exp a * (1 + x - a) ≤ Real.exp x := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - a)) (Real.exp_pos a).le
  rw [← Real.exp_add] at hh
  convert hh using 1 <;> congr 1 <;> ring

/-- Uniform physical mass for the whole chi-bearing product. No bound on degree or frequency
support, phase-independence premise, or truncation of product terms is needed. -/
theorem exists_chiProductResonator_physical_mass_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (u : ι → ℂ) (freq : ι → ℝ),
      (∀ j ∈ S, ‖u j‖ ≤ 1 / 2) →
      T * bagPhysicalHeightMass *
          Real.exp (-25 * (∑ j ∈ S, ‖u j‖ ^ 2) -
            C * (∑ j ∈ S, ‖u j‖) / Real.sqrt T) ≤
        ∫ t in T..2 * T, bagPhysicalHeightWindow (t / T) *
          ‖chiProductResonator S u freq t‖ ^ 2 := by
  obtain ⟨B, hB, hmean⟩ := exists_physicalWindow_chi_firstMean
  refine ⟨2 * B / bagPhysicalHeightMass, div_pos (mul_pos (by norm_num) hB) bagPhysicalHeightMass_pos, ?_⟩
  intro T hT ι S u freq hu
  have hT0 : 0 < T := by linarith
  let W : ℝ → ℝ := fun t => bagPhysicalHeightWindow (t / T)
  let f : ι → ℝ → ℂ := fun j t =>
    zetaChi (linePt t) * Complex.exp (((freq j * t : ℝ) : ℂ) * I)
  let F : ℝ → ℂ := fun t => ∑ j ∈ S, u j * f j t
  let E : ℝ := ∑ j ∈ S, ‖u j‖ ^ 2
  let L : ℝ := ∑ j ∈ S, ‖u j‖
  let M : ℝ := T * bagPhysicalHeightMass
  have hM : 0 < M := mul_pos hT0 bagPhysicalHeightMass_pos
  have hW : Continuous W := bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const T)
  have hf (j : ι) : Continuous (f j) := continuous_zetaChiCriticalTwistIntegrand (freq j)
  have hF : Continuous F := continuous_finsetSum S (fun j _ => continuous_const.mul (hf j))
  have hcW : Continuous (fun t => (W t : ℂ)) := Complex.continuous_ofReal.comp hW
  have hWF : Continuous (fun t => (W t : ℂ) * F t) := hcW.mul hF
  have hterm (j : ι) : IntervalIntegrable (fun t => u j * ((W t : ℂ) * f j t)) volume T (2 * T) :=
    (continuous_const.mul (hcW.mul (hf j))).intervalIntegrable T (2 * T)
  have hFmean : ‖∫ t in T..2 * T, (W t : ℂ) * F t‖ ≤ B * Real.sqrt T * L := by
    have heq : (∫ t in T..2 * T, (W t : ℂ) * F t) =
        ∑ j ∈ S, u j * ∫ t in T..2 * T, (W t : ℂ) * f j t := by
      calc
        _ = ∫ t in T..2 * T, ∑ j ∈ S, u j * ((W t : ℂ) * f j t) := by
          apply intervalIntegral.integral_congr
          intro t _
          dsimp only [F]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_finsetSum (fun j _ => hterm j)]
          simp_rw [intervalIntegral.integral_const_mul]
    rw [heq]
    calc
      _ ≤ ∑ j ∈ S, ‖u j‖ * ‖∫ t in T..2 * T, (W t : ℂ) * f j t‖ := by
        simpa only [norm_mul] using norm_sum_le S (fun j => u j * ∫ t in T..2 * T, (W t : ℂ) * f j t)
      _ ≤ ∑ j ∈ S, ‖u j‖ * (B * Real.sqrt T) := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hmean T hT (freq j)) (norm_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; dsimp only [L]; ring
  have hWmass : (∫ t in T..2 * T, W t) = M := physicalWindow_mass hT0
  have hR : (∫ t in T..2 * T, W t * (F t).re) =
      (∫ t in T..2 * T, (W t : ℂ) * F t).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.reCLM_apply] using Complex.reCLM.intervalIntegral_comp_comm
        (hWF.intervalIntegrable T (2 * T))
  have hRlower : -(B * Real.sqrt T * L) ≤ ∫ t in T..2 * T, W t * (F t).re := by
    rw [hR]
    have hh := (abs_le.mp (Complex.abs_re_le_norm
      (∫ t in T..2 * T, (W t : ℂ) * F t))).1
    linarith
  let a : ℝ := -25 * E - 2 * B * Real.sqrt T * L / M
  have hpoint (t : ℝ) : Real.exp (2 * (F t).re - 25 * E) ≤
      ‖chiProductResonator S u freq t‖ ^ 2 := by
    have hnorm (j : ι) : ‖u j * f j t‖ = ‖u j‖ := by
      simp only [f, norm_mul, norm_zetaChi_line, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hh := product_exp_lower S (fun j => u j * f j t)
      (fun j hj => by rw [hnorm]; exact hu j hj)
    simpa only [hnorm, F, E, chiProductResonator, f] using hh
  have hmono :
      (∫ t in T..2 * T, W t * (Real.exp a * (1 + (2 * (F t).re - 25 * E) - a))) ≤
      ∫ t in T..2 * T, W t * ‖chiProductResonator S u freq t‖ ^ 2 := by
    apply intervalIntegral.integral_mono_on (show T ≤ 2 * T by linarith)
      ((hW.mul (continuous_const.mul ((continuous_const.add
        ((continuous_const.mul (Complex.continuous_re.comp hF)).sub continuous_const)).sub continuous_const))).intervalIntegrable _ _)
      ((hW.mul ((continuous_chiProductResonator S u freq).norm.pow 2)).intervalIntegrable _ _)
    intro t _
    exact mul_le_mul_of_nonneg_left ((exp_tangent a _).trans (hpoint t))
      bagPhysicalHeightWindow.nonneg
  have heval :
      (∫ t in T..2 * T, W t * (Real.exp a * (1 + (2 * (F t).re - 25 * E) - a))) =
      Real.exp a * ((1 - 25 * E - a) * M +
        2 * ∫ t in T..2 * T, W t * (F t).re) := by
    have hiA : IntervalIntegrable (fun t => (1 - 25 * E - a) * W t) volume T (2 * T) :=
      (continuous_const.mul hW).intervalIntegrable T (2 * T)
    have hiB : IntervalIntegrable (fun t => 2 * (W t * (F t).re)) volume T (2 * T) :=
      (continuous_const.mul (hW.mul (Complex.continuous_re.comp hF))).intervalIntegrable T (2 * T)
    calc
      _ = ∫ t in T..2 * T,
          Real.exp a * ((1 - 25 * E - a) * W t + 2 * (W t * (F t).re)) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hiA hiB,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hWmass]
  have halg : (1 - 25 * E - a) * M = M + 2 * B * Real.sqrt T * L := by
    dsimp only [a]
    field_simp
    ring
  rw [heval, halg] at hmono
  have hlow : M * Real.exp a ≤ ∫ t in T..2 * T, W t * ‖chiProductResonator S u freq t‖ ^ 2 := by
    have hbracket : M ≤ M + 2 * B * Real.sqrt T * L +
        2 * ∫ t in T..2 * T, W t * (F t).re := by linarith only [hRlower]
    calc
      _ = Real.exp a * M := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hbracket (Real.exp_pos a).le
      _ ≤ _ := hmono
  have ha : a = -25 * E - (2 * B / bagPhysicalHeightMass) * L / Real.sqrt T := by
    dsimp only [a, M]
    have hsq := Real.sq_sqrt hT0.le
    have hspos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
    field_simp [hspos.ne', hT0.ne', bagPhysicalHeightMass_pos.ne']
    ring_nf
    rw [hsq]
  rw [ha] at hlow
  exact hlow
/-- Normalizing each affine factor still leaves source-derived physical mass, uniformly
in the number and size of the frequencies. -/
theorem exists_chiProductResonator_normalized_physical_mass_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ {ι : Type} (S : Finset ι) (u : ι → ℂ) (freq : ι → ℝ),
      (∀ j ∈ S, ‖u j‖ ≤ 1 / 2) →
      T * bagPhysicalHeightMass *
          Real.exp (-26 * (∑ j ∈ S, ‖u j‖ ^ 2) -
            C * (∑ j ∈ S, ‖u j‖) / Real.sqrt T) ≤
        (∫ t in T..2 * T, bagPhysicalHeightWindow (t / T) *
          ‖chiProductResonator S u freq t‖ ^ 2) /
          ∏ j ∈ S, (1 + ‖u j‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_chiProductResonator_physical_mass_lower
  refine ⟨C, hC, ?_⟩
  intro T hT ι S u freq hu
  have hT0 : 0 < T := by linarith
  have hQ : 0 < ∏ j ∈ S, (1 + ‖u j‖ ^ 2) :=
    Finset.prod_pos (fun j _ => by positivity)
  have hQbound : (∏ j ∈ S, (1 + ‖u j‖ ^ 2)) ≤
      Real.exp (∑ j ∈ S, ‖u j‖ ^ 2) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun j _ => by positivity)
    intro j _
    simpa only [add_comm] using Real.add_one_le_exp (‖u j‖ ^ 2)
  apply (le_div_iff₀ hQ).mpr
  calc
    _ ≤ (T * bagPhysicalHeightMass *
          Real.exp (-26 * (∑ j ∈ S, ‖u j‖ ^ 2) -
            C * (∑ j ∈ S, ‖u j‖) / Real.sqrt T)) *
          Real.exp (∑ j ∈ S, ‖u j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hQbound
        (mul_nonneg (mul_nonneg hT0.le bagPhysicalHeightMass_pos.le) (Real.exp_pos _).le)
    _ = T * bagPhysicalHeightMass *
          Real.exp (-25 * (∑ j ∈ S, ‖u j‖ ^ 2) -
            C * (∑ j ∈ S, ‖u j‖) / Real.sqrt T) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hb T hT S u freq hu

end RHTower
