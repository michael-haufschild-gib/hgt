import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockBorelFlattening
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Set MeasureTheory
open scoped ENNReal
noncomputable section

private def hgt_history_hinge_mass (k : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in 0..t, k x
private def hgt_history_hinge_measure (k : ℝ → ℝ) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (deriv k 0) • Measure.dirac 0 +
    (volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (deriv (deriv k) x))
private def hgt_history_hinge_age (k : ℝ → ℝ) (t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 t)).withDensity
    (fun s => ENNReal.ofReal (k (t-s) / hgt_history_hinge_mass k t))
private def hgt_history_hinge_cap (h w : ℝ) : ℝ :=
  w * min h w - (min h w)^2 / 2

private theorem hgt_history_hinge_derivatives {k : ℝ → ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) :
    Differentiable ℝ k ∧ Continuous (deriv k) ∧
      Differentiable ℝ (deriv k) ∧ Continuous (deriv (deriv k)) := by
  have hk1 : ContDiff ℝ (1 : ℕ∞) (deriv k) := hk.deriv'
  exact ⟨hk.differentiable (by norm_num), hk.continuous_deriv (by norm_num),
    hk.differentiable_deriv_two, hk1.continuous_deriv_one⟩

private theorem hgt_history_hinge_deriv_lower {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (ht : 0 ≤ t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    ∀ x ∈ Icc 0 t, deriv k 0 ≤ deriv k x := by
  have hd := hgt_history_hinge_derivatives hk
  have hm : MonotoneOn (deriv k) (Icc 0 t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hd.2.1.continuousOn
      hd.2.2.1.differentiableOn (fun x hx => hc x (interior_subset hx))
  intro x hx
  exact hm ⟨le_rfl, ht⟩ hx hx.1

private theorem hgt_history_hinge_linear_lower {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0) (ht : 0 ≤ t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    ∀ x ∈ Icc 0 t, deriv k 0 * x ≤ k x := by
  have hd := hgt_history_hinge_derivatives hk
  have hl := hgt_history_hinge_deriv_lower hk ht hc
  intro x hx
  have h := (convex_Icc 0 t).mul_sub_le_image_sub_of_le_deriv
    hk.continuous.continuousOn hd.1.differentiableOn
    (fun y hy => hl y (interior_subset hy)) 0 ⟨le_rfl, ht⟩ x hx hx.1
  simpa [hk0] using h

private theorem hgt_history_hinge_guards {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    0 < deriv k t ∧ 0 < k t ∧ 0 < hgt_history_hinge_mass k t ∧
      0 < k t / deriv k t ∧ k t / deriv k t ≤ t := by
  have hd := hgt_history_hinge_derivatives hk
  have hl := hgt_history_hinge_deriv_lower hk ht.le hc
  have hklo := hgt_history_hinge_linear_lower hk hk0 ht.le hc
  have hdt : 0 < deriv k t := lt_of_lt_of_le hb (hl t ⟨ht.le, le_rfl⟩)
  have hkt : 0 < k t := lt_of_lt_of_le (mul_pos hb ht) (hklo t ⟨ht.le, le_rfl⟩)
  have hmass : deriv k 0 * t^2 / 2 ≤ hgt_history_hinge_mass k t := by
    have hh := intervalIntegral.integral_mono_on ht.le
      ((continuous_const.mul continuous_id).intervalIntegrable (μ := volume) 0 t)
      (hk.continuous.intervalIntegrable 0 t) hklo
    dsimp only [Pi.mul_apply, id_eq] at hh
    rw [show (fun u : ℝ => deriv k 0 * u) = (fun u : ℝ => u * deriv k 0) by ext u; ring,
      intervalIntegral.integral_mul_const, integral_id] at hh
    dsimp [hgt_history_hinge_mass]
    nlinarith [hh]
  have hmpos : 0 < hgt_history_hinge_mass k t :=
    lt_of_lt_of_le (by positivity) hmass
  have hm : MonotoneOn (deriv k) (Icc 0 t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hd.2.1.continuousOn
      hd.2.2.1.differentiableOn (fun x hx => hc x (interior_subset hx))
  have hi : (∫ x in 0..t, deriv k x) ≤ t * deriv k t := by
    have hh := intervalIntegral.integral_mono_on ht.le
      (hd.2.1.intervalIntegrable 0 t) ((continuous_const : Continuous (fun _ : ℝ => deriv k t)).intervalIntegrable (μ := volume) 0 t)
      (fun x hx => hm hx ⟨ht.le, le_rfl⟩ hx.2)
    simpa [mul_comm] using hh
  have he : (∫ x in 0..t, deriv k x) = k t := by
    simpa [hk0] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hd.1 x).hasDerivAt) (hd.2.1.intervalIntegrable 0 t)
  exact ⟨hdt, hkt, hmpos, div_pos hkt hdt,
    (div_le_iff₀ hdt).2 (by simpa [he, mul_comm] using hi)⟩

private theorem hgt_history_hinge_linear_ibp {k : ℝ → ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (a t : ℝ) :
    (∫ x in a..t, (t-x) * deriv (deriv k) x) =
      -(t-a) * deriv k a + k t - k a := by
  have hd := hgt_history_hinge_derivatives hk
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => t-x) (u' := fun _ => (-1 : ℝ))
    (v := deriv k) (v' := deriv (deriv k))
    (by fun_prop) hd.2.1.continuousOn
    (fun x _ => by convert (hasDerivAt_const x t).sub (hasDerivAt_id x) using 1 <;> first | rfl | simp)
    (fun x _ => (hd.2.2.1 x).hasDerivAt)
    (continuous_const.intervalIntegrable a t) (hd.2.2.2.intervalIntegrable a t)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc a t) => (hd.1 x).hasDerivAt)
    (hd.2.1.intervalIntegrable a t)
  simp only [sub_self, zero_mul, zero_sub, neg_mul, intervalIntegral.integral_neg, one_mul, he] at h
  calc _ = _ := h
       _ = _ := by ring

private theorem hgt_history_hinge_square_ibp {k : ℝ → ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (a t : ℝ) :
    (∫ x in a..t, (t-x)^2 / 2 * deriv (deriv k) x) =
      -(t-a)^2 / 2 * deriv k a - (t-a) * k a + ∫ x in a..t, k x := by
  have hd := hgt_history_hinge_derivatives hk
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => (t-x)^2/2) (u' := fun x => -(t-x))
    (v := deriv k) (v' := deriv (deriv k))
    (by fun_prop) hd.2.1.continuousOn
    (fun x _ => by
      convert (((hasDerivAt_const x t).sub (hasDerivAt_id x)).pow 2).div_const 2 using 1
      all_goals first | rfl | (simp only [Pi.sub_apply, id_eq]; ring))
    (fun x _ => (hd.2.2.1 x).hasDerivAt)
    (by apply Continuous.intervalIntegrable; fun_prop) (hd.2.2.2.intervalIntegrable a t)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun x : ℝ => t-x) (u' := fun _ => (-1 : ℝ)) (v := k) (v' := deriv k)
    (by fun_prop) hk.continuous.continuousOn
    (fun x _ => by convert (hasDerivAt_const x t).sub (hasDerivAt_id x) using 1 <;> first | rfl | simp)
    (fun x _ => (hd.1 x).hasDerivAt)
    (continuous_const.intervalIntegrable a t) (hd.2.1.intervalIntegrable a t)
  simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_div, zero_mul, zero_sub] at h h2
  rw [show (fun x => -(t-x) * deriv k x) = (fun x => -((t-x)*deriv k x)) by ext x; ring,
    intervalIntegral.integral_neg, h2] at h
  simp only [neg_mul, one_mul, intervalIntegral.integral_neg] at h
  calc _ = _ := h
       _ = _ := by ring

private theorem hgt_history_hinge_representation {k : ℝ → ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0) (x : ℝ) :
    k x = deriv k 0 * x + ∫ r in 0..x, (x-r)*deriv (deriv k) r := by
  have h := hgt_history_hinge_linear_ibp hk 0 x
  simp only [sub_zero, hk0] at h
  linarith

private theorem hgt_history_hinge_icc_integral (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x in Icc 0 t, f x) = ∫ x in 0..t, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht]

private theorem hgt_history_hinge_density_admissions {g : ℝ → ℝ} {t : ℝ}
    (hg : Continuous g) (hgn : ∀ x ∈ Icc 0 t, 0 ≤ g x) (ht : 0 ≤ t) :
    IsFiniteMeasure ((volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (g x))) ∧
    ∀ f : ℝ → ℝ, Continuous f →
      Integrable f ((volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (g x))) ∧
      (∫ x, f x ∂(volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (g x))) =
        ∫ x in 0..t, g x * f x := by
  have hgi : Integrable g (volume.restrict (Icc 0 t)) := hg.continuousOn.integrableOn_Icc
  have hfinite := isFiniteMeasure_withDensity_ofReal hgi.hasFiniteIntegral
  refine ⟨hfinite, ?_⟩
  intro f hf
  have hraw : Integrable (fun x => g x * f x) (volume.restrict (Icc 0 t)) :=
    (hg.mul hf).continuousOn.integrableOn_Icc
  have hconv : (fun x => (ENNReal.ofReal (g x)).toReal • f x) =ᵐ[volume.restrict (Icc 0 t)]
      (fun x => g x * f x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [ENNReal.toReal_ofReal (hgn x hx), smul_eq_mul]
  have hi : Integrable f ((volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (g x))) :=
    (integrable_withDensity_iff_integrable_smul' hg.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).2 (hraw.congr hconv.symm)
  refine ⟨hi, ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hg.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  exact (integral_congr_ae hconv).trans (hgt_history_hinge_icc_integral _ ht)

private theorem hgt_history_hinge_density_support (g : ℝ → ℝ) (t : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 t)).withDensity (fun x => ENNReal.ofReal (g x)), x ∈ Icc 0 t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Icc)

private theorem hgt_history_hinge_admissions {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hb : 0 ≤ deriv k 0) (ht : 0 ≤ t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    IsFiniteMeasure (hgt_history_hinge_measure k t) ∧
    (∀ᵐ x ∂hgt_history_hinge_measure k t, x ∈ Icc 0 t) ∧
    ∀ f : ℝ → ℝ, Continuous f →
      Integrable f (hgt_history_hinge_measure k t) ∧
      (∫ x, f x ∂hgt_history_hinge_measure k t) =
        deriv k 0 * f 0 + ∫ x in 0..t, deriv (deriv k) x * f x := by
  have hd := hgt_history_hinge_derivatives hk
  have ha := hgt_history_hinge_density_admissions hd.2.2.2 hc ht
  haveI := ha.1
  haveI : IsFiniteMeasure (ENNReal.ofReal (deriv k 0) • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite (by simp)
  refine ⟨by dsimp [hgt_history_hinge_measure]; infer_instance, ?_, ?_⟩
  · apply ae_add_measure_iff.2
    refine ⟨Measure.ae_smul_measure ?_ _, hgt_history_hinge_density_support _ _⟩
    simpa using (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩)
  · intro f hf
    have hdir : Integrable f (ENNReal.ofReal (deriv k 0) • Measure.dirac 0) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have hden := ha.2 f hf
    refine ⟨hdir.add_measure hden.1, ?_⟩
    rw [hgt_history_hinge_measure, integral_add_measure hdir hden.1,
      integral_smul_measure, integral_dirac, hden.2, smul_eq_mul]
    rw [ENNReal.toReal_ofReal hb]

private theorem hgt_history_hinge_moments {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0) (hb : 0 ≤ deriv k 0)
    (ht : 0 ≤ t) (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    (hgt_history_hinge_measure k t).real univ = deriv k t ∧
    (∫ r, t-r ∂hgt_history_hinge_measure k t) = k t ∧
    (∫ r, (t-r)^2/2 ∂hgt_history_hinge_measure k t) = hgt_history_hinge_mass k t := by
  have ha := hgt_history_hinge_admissions hk hb ht hc
  haveI := ha.1
  have hd := hgt_history_hinge_derivatives hk
  have h0 := (ha.2.2 (fun _ => 1) continuous_const).2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc 0 t) => (hd.2.2.1 x).hasDerivAt)
    (hd.2.2.2.intervalIntegrable 0 t)
  have h1 := (ha.2.2 (fun r => t-r) (by fun_prop)).2
  have h2 := (ha.2.2 (fun r => (t-r)^2/2) (by fun_prop)).2
  have he1 := hgt_history_hinge_linear_ibp hk 0 t
  have he2 := hgt_history_hinge_square_ibp hk 0 t
  simp only [sub_zero, hk0, mul_zero] at he1 he2
  simp only [integral_const, smul_eq_mul, mul_one, he] at h0
  simp only [sub_zero] at h1 h2
  rw [show (fun x => deriv (deriv k) x * (t-x)) =
    (fun x => (t-x) * deriv (deriv k) x) by ext x; ring, he1] at h1
  rw [show (fun x => deriv (deriv k) x * ((t-x)^2/2)) =
    (fun x => (t-x)^2/2 * deriv (deriv k) x) by ext x; ring, he2] at h2
  refine ⟨by linarith, by linarith, ?_⟩
  dsimp [hgt_history_hinge_mass]
  linarith

private theorem hgt_history_hinge_age_admissions {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    IsFiniteMeasure (hgt_history_hinge_age k t) ∧
    (∀ᵐ s ∂hgt_history_hinge_age k t, s ∈ Icc 0 t) ∧
    ∀ f : ℝ → ℝ, Continuous f → Integrable f (hgt_history_hinge_age k t) ∧
      (∫ s, f s ∂hgt_history_hinge_age k t) =
        (∫ s in 0..t, k (t-s) * f s) / hgt_history_hinge_mass k t := by
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hlo := hgt_history_hinge_linear_lower hk hk0 ht.le hc
  have hkn : ∀ s ∈ Icc 0 t, 0 ≤ k (t-s) := by
    intro s hs
    have h := hlo (t-s) ⟨sub_nonneg.2 hs.2, by linarith [hs.1]⟩
    exact le_trans (mul_nonneg hb.le (sub_nonneg.2 hs.2)) h
  have hdensity : Continuous (fun s => k (t-s) / hgt_history_hinge_mass k t) :=
    (hk.continuous.comp (by fun_prop)).div_const _
  have hd := hgt_history_hinge_density_admissions hdensity
    (fun s hs => div_nonneg (hkn s hs) hg.2.2.1.le) ht.le
  refine ⟨hd.1, hgt_history_hinge_density_support _ _, ?_⟩
  intro f hf
  have h := hd.2 f hf
  refine ⟨h.1, ?_⟩
  rw [hgt_history_hinge_age, h.2]
  simp only [div_eq_mul_inv]
  rw [show (fun s => k (t-s) * (hgt_history_hinge_mass k t)⁻¹ * f s) =
    (fun s => (k (t-s) * f s) * (hgt_history_hinge_mass k t)⁻¹) by ext s; ring,
    intervalIntegral.integral_mul_const]

private theorem hgt_history_hinge_age_probability {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    IsProbabilityMeasure (hgt_history_hinge_age k t) ∧
      NullSingletonClass (hgt_history_hinge_age k t) := by
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have ha := hgt_history_hinge_age_admissions hk hk0 hb ht hc
  haveI := ha.1
  have h := (ha.2.2 (fun _ => 1) continuous_const).2
  simp only [integral_const, smul_eq_mul, mul_one] at h
  have he : (∫ s in 0..t, k (t-s)) = hgt_history_hinge_mass k t := by
    simp [hgt_history_hinge_mass, intervalIntegral.integral_comp_sub_left]
  rw [he, div_self hg.2.2.1.ne'] at h
  refine ⟨isProbabilityMeasure_iff_real.2 h, ?_⟩
  dsimp [hgt_history_hinge_age]
  infer_instance

private theorem hgt_history_hinge_age_cutoff {k : ℝ → ℝ} {t h : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t) (hh : 0 ≤ h)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    (hgt_history_hinge_age k t).real (Icc 0 h) =
      (∫ s in 0..min h t, k (t-s)) / hgt_history_hinge_mass k t := by
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hlo := hgt_history_hinge_linear_lower hk hk0 ht.le hc
  have hcset : Icc 0 h ∩ Icc 0 t = Icc 0 (min h t) := by
    ext x
    simp only [mem_inter_iff, mem_Icc, le_min_iff]
    tauto
  have he : (hgt_history_hinge_age k t).restrict (Icc 0 h) =
      (volume.restrict (Icc 0 (min h t))).withDensity
        (fun s => ENNReal.ofReal (k (t-s) / hgt_history_hinge_mass k t)) := by
    rw [hgt_history_hinge_age, restrict_withDensity measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, hcset]
  have hn : ∀ s ∈ Icc 0 (min h t), 0 ≤ k (t-s) / hgt_history_hinge_mass k t := by
    intro s hs
    have hs' : 0 ≤ t-s := sub_nonneg.2 (le_trans hs.2 (min_le_right _ _))
    have h := hlo (t-s) ⟨hs', by linarith [hs.1]⟩
    exact div_nonneg (le_trans (mul_nonneg hb.le hs') h) hg.2.2.1.le
  have hd := hgt_history_hinge_density_admissions
    ((hk.continuous.comp (by fun_prop)).div_const (hgt_history_hinge_mass k t)) hn
    (le_min hh ht.le)
  haveI := hd.1
  have hp := (hd.2 (fun _ => 1) continuous_const).2
  have hi : (hgt_history_hinge_age k t).real (Icc 0 h) =
      ∫ s, (1 : ℝ) ∂(hgt_history_hinge_age k t).restrict (Icc 0 h) := by
    simp [integral_const]
  dsimp only [Function.comp_apply] at hp
  rw [he, hp] at hi
  calc _ = _ := hi
       _ = _ := by simp [div_eq_mul_inv, intervalIntegral.integral_mul_const]

private theorem hgt_history_hinge_cap_continuous (h : ℝ) :
    Continuous (fun r : ℝ => hgt_history_hinge_cap h (r)) := by
  dsimp [hgt_history_hinge_cap]
  fun_prop

private theorem hgt_history_hinge_cap_curvature {k : ℝ → ℝ} {t h : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hh : 0 ≤ h) (hht : h ≤ t) :
    (∫ r in 0..t, hgt_history_hinge_cap h (t-r) * deriv (deriv k) r) =
      hgt_history_hinge_mass k t - hgt_history_hinge_mass k (t-h) -
        deriv k 0 * (t*h-h^2/2) := by
  have hd := hgt_history_hinge_derivatives hk
  let a := t-h
  have ha : 0 ≤ a := sub_nonneg.2 hht
  have hat : a ≤ t := by dsimp [a]; linarith
  have hcap : Continuous (fun r : ℝ => hgt_history_hinge_cap h (t-r) * deriv (deriv k) r) :=
    ((hgt_history_hinge_cap_continuous h).comp (by fun_prop)).mul hd.2.2.2
  have hsq : Continuous (fun r : ℝ => (t-r)^2/2 * deriv (deriv k) r) := by fun_prop
  have hasq : Continuous (fun r : ℝ => (a-r)^2/2 * deriv (deriv k) r) := by fun_prop
  have hp := intervalIntegral.integral_add_adjacent_intervals
    (hcap.intervalIntegrable (μ := volume) 0 a) (hcap.intervalIntegrable (μ := volume) a t)
  have hq := intervalIntegral.integral_add_adjacent_intervals
    (hsq.intervalIntegrable (μ := volume) 0 a) (hsq.intervalIntegrable (μ := volume) a t)
  have hhead : (∫ r in 0..a, hgt_history_hinge_cap h (t-r) * deriv (deriv k) r) =
      (∫ r in 0..a, (t-r)^2/2 * deriv (deriv k) r) -
        ∫ r in 0..a, (a-r)^2/2 * deriv (deriv k) r := by
    rw [← intervalIntegral.integral_sub (hsq.intervalIntegrable 0 a) (hasq.intervalIntegrable 0 a)]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc 0 a := by simpa [uIcc_of_le ha] using hr
    have hw : h ≤ t-r := by dsimp [a] at hr'; linarith [hr'.2]
    dsimp only [hgt_history_hinge_cap]
    rw [min_eq_left hw]
    dsimp [a]
    ring
  have htail : (∫ r in a..t, hgt_history_hinge_cap h (t-r) * deriv (deriv k) r) =
      ∫ r in a..t, (t-r)^2/2 * deriv (deriv k) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a t := by simpa [uIcc_of_le hat] using hr
    have hw : t-r ≤ h := by dsimp [a] at hr'; linarith [hr'.1]
    dsimp only [hgt_history_hinge_cap]
    rw [min_eq_right hw]
    ring
  have he := hgt_history_hinge_square_ibp hk 0 t
  have he' := hgt_history_hinge_square_ibp hk 0 a
  simp only [sub_zero, hk0, mul_zero] at he he'
  rw [hhead, htail] at hp
  dsimp [hgt_history_hinge_mass, a] at he' ⊢
  nlinarith [he, he', hq]

private theorem hgt_history_hinge_cap_identity {k : ℝ → ℝ} {t h : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t) (hh : 0 ≤ h)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    Integrable (fun r => hgt_history_hinge_cap h (t-r)) (hgt_history_hinge_measure k t) ∧
      (∫ r, hgt_history_hinge_cap h (t-r) ∂hgt_history_hinge_measure k t) =
        hgt_history_hinge_mass k t * (hgt_history_hinge_age k t).real (Icc 0 h) := by
  have ha := hgt_history_hinge_admissions hk hb.le ht.le hc
  have hcap := ha.2.2 (fun r => hgt_history_hinge_cap h (t-r))
    ((hgt_history_hinge_cap_continuous h).comp (by fun_prop))
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  refine ⟨hcap.1, ?_⟩
  rw [hgt_history_hinge_age_cutoff hk hk0 hb ht hh hc,
    ← mul_div_assoc, mul_div_cancel_left₀ _ hg.2.2.1.ne']
  by_cases hht : h ≤ t
  · rw [min_eq_left hht]
    have he := hgt_history_hinge_cap_curvature hk hk0 hh hht
    have hsub := intervalIntegral.integral_add_adjacent_intervals
      (hk.continuous.intervalIntegrable (μ := volume) 0 (t-h))
      (hk.continuous.intervalIntegrable (μ := volume) (t-h) t)
    have href : (∫ s in 0..h, k (t-s)) = ∫ s in (t-h)..t, k s := by
      simp only [intervalIntegral.integral_comp_sub_left, sub_zero]
    rw [show (fun x => deriv (deriv k) x * hgt_history_hinge_cap h (t-x)) =
      (fun x => hgt_history_hinge_cap h (t-x) * deriv (deriv k) x) by ext x; ring,
      he, sub_zero, hgt_history_hinge_cap, min_eq_left hht] at hcap
    rw [href]
    dsimp [hgt_history_hinge_mass] at hcap
    linarith
  · have hth : t ≤ h := le_of_not_ge hht
    rw [min_eq_right hth]
    have hm := (hgt_history_hinge_moments hk hk0 hb.le ht.le hc).2.2
    have hs := ha.2.1
    have he : (∫ r, hgt_history_hinge_cap h (t-r) ∂hgt_history_hinge_measure k t) =
        ∫ r, (t-r)^2/2 ∂hgt_history_hinge_measure k t := by
      apply integral_congr_ae
      filter_upwards [hs] with r hr
      rw [hgt_history_hinge_cap, min_eq_right (by linarith [hr.1])]
      ring
    rw [he, hm]
    simp [hgt_history_hinge_mass, intervalIntegral.integral_comp_sub_left]

end


/-! Complete actual-source derivatives, origin, curvature and strict cubic defect.
Coefficients retain both factorials and normalized full raw theta moments. -/

open Filter Topology Set
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "K2" => deriv (deriv (deriv liEvenCrossActualClockBorelKernel))
local notation "nu" => thetaCuspNormalizedEvenMoment
local notation "b" => (thetaCuspNormalizedEvenMoment 1 / 2)
local notation "A" => (fun t : ℝ => liEvenCrossActualClockBorelKernel t - 1)

private def hgt_history_source_term (m j : ℕ) (t : ℝ) : ℝ :=
  liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
    t^(2*j-m)

private def hgt_history_source_series (m : ℕ) (t : ℝ) : ℝ := ∑' j, hgt_history_source_term m j t

private theorem hgt_history_source_coefficient_le_inverse_factorial (j : ℕ) :
    liEvenCrossActualClockBorelCoefficient j ≤ ((j.factorial : ℝ))⁻¹ := by
  have hp : (32/303 : ℝ)^j ≤ 1 := by
    simpa using pow_le_pow_left₀ (by norm_num : 0 ≤ (32/303 : ℝ))
      (by norm_num : (32/303 : ℝ) ≤ 1) j
  calc
    liEvenCrossActualClockBorelCoefficient j ≤
        (32/303 : ℝ)^j/(j.factorial : ℝ) := liEvenCrossActualClockBorelCoefficient_le j
    _ ≤ 1/(j.factorial : ℝ) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := one_div _

private theorem hgt_history_source_term_bound (m j : ℕ) {t T : ℝ}
    (hT : 1 ≤ T) (ht : |t| ≤ T) :
    ‖hgt_history_source_term m j t‖ ≤ (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j) := by
  have hd : ((2*j).descFactorial m : ℝ) ≤ (2:ℝ)^m*(j:ℝ)^m := by
    calc
      ((2*j).descFactorial m : ℝ) ≤ (((2*j : ℕ) : ℝ))^m := by
        exact_mod_cast Nat.descFactorial_le_pow (2*j) m
      _ = _ := by push_cast; rw [mul_pow]
  have hp : |t|^(2*j-m) ≤ T^(2*j) :=
    (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  have hc := (liEvenCrossActualClockBorelCoefficient_pos j).le
  rw [hgt_history_source_term, norm_mul, norm_mul, Real.norm_eq_abs,
    abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j),
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), norm_pow, Real.norm_eq_abs]
  calc
    liEvenCrossActualClockBorelCoefficient j * ((2*j).descFactorial m : ℝ) *
        |t|^(2*j-m) ≤
      (liEvenCrossActualClockBorelCoefficient j*((2:ℝ)^m*(j:ℝ)^m))*T^(2*j) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd
        (liEvenCrossActualClockBorelCoefficient_pos j).le) hp
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem hgt_history_source_envelope_summable (m : ℕ) {T : ℝ} (_hT : 0 ≤ T) :
    Summable (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
      liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
  have hc (j : ℕ) : ‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖ ≤
      ((j.factorial : ℝ))⁻¹ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j)]
      using hgt_history_source_coefficient_le_inverse_factorial j
  have hs := GaloisForLFunctions.HTGeometry.summable_pow_mul_of_factorial_decay
    hc m (sq_nonneg T)
  have he : (fun j : ℕ => (2:ℝ)^m*((j:ℝ)^m*
        (‖(liEvenCrossActualClockBorelCoefficient j : ℂ)‖*(T^2)^j))) =
      (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
        liEvenCrossActualClockBorelCoefficient j*T^(2*j)) := by
    funext j
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j), ← pow_mul]
    ring
  rw [← he]
  exact hs.mul_left _

private theorem hgt_history_source_norm_summable (m : ℕ) (t : ℝ) :
    Summable (fun j => ‖hgt_history_source_term m j t‖) := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => hgt_history_source_term_bound m j hT (by dsimp [T]; linarith))
    (hgt_history_source_envelope_summable m (by linarith))

private theorem hgt_history_source_summable (m : ℕ) (t : ℝ) : Summable (fun j => hgt_history_source_term m j t) :=
  (hgt_history_source_norm_summable m t).of_norm

private theorem hgt_history_source_term_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (hgt_history_source_term m j) (hgt_history_source_term (m+1) j t) t := by
  have he : 2*j-(m+1) = 2*j-m-1 := by omega
  convert (((hasDerivAt_id t).pow (2*j-m)).const_mul
    (liEvenCrossActualClockBorelCoefficient j*((2*j).descFactorial m : ℝ))) using 1 <;>
    first | rfl | (simp only [hgt_history_source_term, Nat.descFactorial_succ, Nat.cast_mul,
      id_eq, mul_one, he]; ring)

private theorem hgt_history_source_series_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (hgt_history_source_series m) (hgt_history_source_series (m+1) t) t := by
  let T := |t|+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  exact hasDerivAt_tsum_of_isPreconnected
    (hgt_history_source_envelope_summable (m+1) (by linarith)) Metric.isOpen_ball
    (convex_ball (0:ℝ) T).isPreconnected
    (fun j y _ => hgt_history_source_term_hasDerivAt m j y)
    (fun j y hy => hgt_history_source_term_bound (m+1) j hT
      (le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)))
    (by simp [Metric.mem_ball, T]; positivity) (hgt_history_source_summable m 0)
    (by simp [Metric.mem_ball, T])

private theorem hgt_history_source_series_zero : hgt_history_source_series 0 = liEvenCrossActualClockBorelKernel := by
  funext t
  unfold hgt_history_source_series liEvenCrossActualClockBorelKernel
  apply tsum_congr
  intro j
  simp [hgt_history_source_term, liEvenCrossActualClockBorelTerm_eq_coefficient_mul]

private theorem hgt_history_source_iteratedDeriv (m : ℕ) :
    iteratedDeriv m liEvenCrossActualClockBorelKernel = hgt_history_source_series m := by
  induction m with
  | zero => simpa using hgt_history_source_series_zero.symm
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hgt_history_source_series_hasDerivAt m t).deriv

private theorem hgt_history_source_first_deriv : deriv liEvenCrossActualClockBorelKernel = hgt_history_source_series 1 := by
  rw [← iteratedDeriv_one, hgt_history_source_iteratedDeriv]

private theorem hgt_history_source_hasDerivAt_iterated (m : ℕ) (t : ℝ) :
    HasDerivAt (iteratedDeriv m B) (iteratedDeriv (m+1) B t) t := by
  rw [hgt_history_source_iteratedDeriv m, hgt_history_source_iteratedDeriv (m+1)]
  exact hgt_history_source_series_hasDerivAt m t

private theorem hgt_history_source_continuous_iterated (m : ℕ) : Continuous (iteratedDeriv m B) :=
  continuous_iff_continuousAt.mpr (fun t => (hgt_history_source_hasDerivAt_iterated m t).continuousAt)

private theorem hgt_history_source_compact_uniform (m : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    TendstoUniformlyOn
      (fun N : ℕ => fun t : ℝ => ∑ j ∈ Finset.range N, hgt_history_source_term m j t)
      (hgt_history_source_series m) atTop (Icc (-T) T) := by
  exact tendstoUniformlyOn_tsum_nat
    (hgt_history_source_envelope_summable m (by linarith))
    (fun j t ht => hgt_history_source_term_bound m j hT (abs_le.mpr ht))

private theorem hgt_history_source_two : iteratedDeriv 2 B = K1 := by
  rw [show (2 : ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem hgt_history_source_three : iteratedDeriv 3 B = K2 := by
  rw [show (3 : ℕ) = 2+1 from rfl, iteratedDeriv_succ, hgt_history_source_two]

private theorem hgt_history_source_derivative_series (m : ℕ) (t : ℝ) :
    Summable (fun j => ‖hgt_history_source_term m j t‖) ∧
    HasSum (fun j => hgt_history_source_term m j t) (iteratedDeriv m B t) := by
  rw [hgt_history_source_iteratedDeriv]
  exact ⟨hgt_history_source_norm_summable m t,
    (hgt_history_source_summable m t).hasSum⟩

private theorem hgt_history_source_hasDerivAt_B (t : ℝ) : HasDerivAt B (K t) t := by
  simpa only [Nat.zero_add, iteratedDeriv_zero, iteratedDeriv_one] using
    hgt_history_source_hasDerivAt_iterated 0 t

private theorem hgt_history_source_hasDerivAt_K (t : ℝ) : HasDerivAt K (K1 t) t := by
  simpa only [show (1:ℕ)+1=2 from rfl, iteratedDeriv_one, hgt_history_source_two] using
    hgt_history_source_hasDerivAt_iterated 1 t

private theorem hgt_history_source_hasDerivAt_K1 (t : ℝ) : HasDerivAt K1 (K2 t) t := by
  simpa only [show (2:ℕ)+1=3 from rfl, hgt_history_source_two, hgt_history_source_three] using
    hgt_history_source_hasDerivAt_iterated 2 t

private theorem hgt_history_source_contDiff_K : ContDiff ℝ (⊤ : ℕ∞) K := by
  simpa only [Function.iterate_one] using
    contDiff_liEvenCrossActualClockBorelKernel.iterate_deriv 1

private theorem hgt_history_source_contDiff_K1 : ContDiff ℝ (⊤ : ℕ∞) K1 := by
  simpa only [Function.iterate_one] using hgt_history_source_contDiff_K.iterate_deriv 1

private theorem hgt_history_source_contDiff_K2 : ContDiff ℝ (⊤ : ℕ∞) K2 := by
  simpa only [Function.iterate_one] using hgt_history_source_contDiff_K1.iterate_deriv 1

private theorem hgt_history_source_origin :
    K 0 = 0 ∧ K1 0 = b ∧ b = normalizedPrimeArchMoment 0 / 2 ∧ 0 < b := by
  refine ⟨liEvenCrossActualClockBorelCorrection_origin.1, ?_, ?_, ?_⟩
  · simpa only [hgt_history_source_two] using
      liEvenCrossActualClockBorelCorrection_origin.2.2.1
  · rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  · exact div_pos (thetaCuspNormalizedEvenMoment_pos 1) (by norm_num)

private theorem hgt_history_source_excess_zero : A 0 = 0 := by
  simp

private theorem hgt_history_source_term_nonneg (m j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hgt_history_source_term m j t := by
  unfold hgt_history_source_term
  exact mul_nonneg (mul_nonneg (liEvenCrossActualClockBorelCoefficient_pos j).le
    (Nat.cast_nonneg _)) (pow_nonneg ht _)

private theorem hgt_history_source_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ iteratedDeriv m B t := by
  rw [hgt_history_source_iteratedDeriv]
  exact tsum_nonneg (fun j => hgt_history_source_term_nonneg m j ht)

private theorem hgt_history_source_K1_lower {t : ℝ} (ht : 0 ≤ t) : b ≤ K1 t := by
  have hs := (hgt_history_source_derivative_series 2 t).2
  have h := hs.summable.le_tsum 1 (fun j _ => hgt_history_source_term_nonneg 2 j ht)
  rw [hgt_history_source_two] at hs
  have he : hgt_history_source_term 2 1 t = b := by
    norm_num [hgt_history_source_term, liEvenCrossActualClockBorelCoefficient]
    ring
  exact he.symm.trans_le (h.trans_eq hs.tsum_eq)

private theorem hgt_history_source_K2_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ K2 t := by
  simpa only [hgt_history_source_three] using hgt_history_source_nonneg 3 ht

private theorem hgt_history_source_curvature :
    (∀ t : ℝ, 0 ≤ t → b ≤ K1 t ∧ 0 ≤ K2 t) ∧ MonotoneOn K1 (Ici 0) := by
  refine ⟨fun t ht => ⟨hgt_history_source_K1_lower ht,
    hgt_history_source_K2_nonneg ht⟩, ?_⟩
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ))
    hgt_history_source_contDiff_K1.continuous.continuousOn
    (fun t _ => (hgt_history_source_hasDerivAt_K1 t).differentiableAt.differentiableWithinAt)
  intro t ht
  rw [interior_Ici] at ht
  exact hgt_history_source_K2_nonneg (le_of_lt ht)

private theorem hgt_history_source_excess_pos {t : ℝ} (ht : 0 < t) : 0 < A t := by
  have h := (summable_liEvenCrossActualClockBorelTerm t).sum_le_tsum
    ({0, 1} : Finset ℕ) (fun j _ => liEvenCrossActualClockBorelTerm_nonneg t j)
  have hl : 1 + liEvenCrossActualClockBorelCoefficient 1*t^2 ≤ B t := by
    simpa [liEvenCrossActualClockBorelKernel,
      liEvenCrossActualClockBorelTerm_eq_coefficient_mul] using h
  have hp : 0 < liEvenCrossActualClockBorelCoefficient 1*t^2 := by
    have hc := liEvenCrossActualClockBorelCoefficient_pos 1
    positivity
  linarith

private def hgt_history_source_defectTerm (j : ℕ) (t : ℝ) : ℝ :=
  t*hgt_history_source_term 2 j t-hgt_history_source_term 1 j t

private theorem hgt_history_source_defect_series (t : ℝ) :
    Summable (fun j => ‖hgt_history_source_defectTerm j t‖) ∧
    HasSum (fun j => hgt_history_source_defectTerm j t) (t*K1 t-K t) := by
  have h2 := (hgt_history_source_derivative_series 2 t).2
  have h1 := (hgt_history_source_derivative_series 1 t).2
  rw [hgt_history_source_two] at h2
  rw [iteratedDeriv_one] at h1
  have hs := (h2.mul_left t).sub h1
  exact ⟨hs.summable.norm, hs⟩

private theorem hgt_history_source_defect_coefficient {j : ℕ} (hj : 0 < j) (t : ℝ) :
    hgt_history_source_defectTerm j t =
      ((2*j:ℝ)-2)*hgt_history_source_term 1 j t := by
  have he : 2*j-2+1 = 2*j-1 := by omega
  have hp : t^(2*j-1) = t*t^(2*j-2) := by
    rw [← he, pow_succ]
    ring
  unfold hgt_history_source_defectTerm hgt_history_source_term
  simp only [Nat.cast_descFactorial_two, Nat.descFactorial_one,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [hp]
  ring

private theorem hgt_history_source_defect_nonneg (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ hgt_history_source_defectTerm j t := by
  by_cases hj : j = 0
  · simp [hj, hgt_history_source_defectTerm, hgt_history_source_term]
  · rw [hgt_history_source_defect_coefficient (Nat.pos_of_ne_zero hj)]
    have hc : 0 ≤ (2*j:ℝ)-2 := by
      have h : (1:ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      linarith
    exact mul_nonneg hc (hgt_history_source_term_nonneg 1 j ht)

private theorem hgt_history_source_defect_second (t : ℝ) :
    hgt_history_source_defectTerm 2 t = nu 2*t^3/72 := by
  norm_num [hgt_history_source_defectTerm, hgt_history_source_term,
    liEvenCrossActualClockBorelCoefficient]
  ring

private theorem hgt_history_source_cubic_defect {t : ℝ} (ht : 0 ≤ t) :
    nu 2*t^3/72 ≤ t*K1 t-K t := by
  have hs := (hgt_history_source_defect_series t).2
  have h := hs.summable.le_tsum 2 (fun j _ => hgt_history_source_defect_nonneg j ht)
  rw [hgt_history_source_defect_second] at h
  exact h.trans_eq hs.tsum_eq

private theorem hgt_history_source_strict_defect {t : ℝ} (ht : 0 < t) :
    0 < t*K1 t-K t := by
  have hp : 0 < nu 2*t^3/72 := by
    have hn := thetaCuspNormalizedEvenMoment_pos 2
    positivity
  exact hp.trans_le (hgt_history_source_cubic_defect ht.le)

private theorem hgt_history_source_geometry {t : ℝ} (ht : 0 < t) :
    0 < A t ∧ 0 < K1 t ∧
    0 < K t/K1 t ∧ K t/K1 t < t ∧
    0 < K t/(4*K1 t) ∧ K t/(4*K1 t) < t/4 := by
  have hK := liEvenCrossActualClockBorel_deriv_pos ht
  have hK1 : 0 < K1 t := hgt_history_source_origin.2.2.2.trans_le
    (hgt_history_source_K1_lower ht.le)
  have hd := hgt_history_source_strict_defect ht
  refine ⟨hgt_history_source_excess_pos ht, hK1, div_pos hK hK1, ?_,
    div_pos hK (by positivity), ?_⟩
  · exact (div_lt_iff₀ hK1).2 (by linarith)
  · apply (div_lt_iff₀ (show 0 < 4*K1 t by positivity)).2
    nlinarith

end
end RHTower


namespace RHTower
noncomputable section

private def hgt_history_scalar_cap (h w : ℝ) : ℝ :=
  w * min h w - (min h w)^2 / 2

private def hgt_history_scalar_residual (mLen alpha w : ℝ) : ℝ :=
  (2*alpha-alpha^2)*w^2/2 - hgt_history_scalar_cap (alpha*mLen) w -
    alpha*mLen*(1-alpha)*(w-mLen)

private theorem hgt_history_scalar_upper {mLen alpha w : ℝ}
    (h : alpha*mLen ≤ w) :
    hgt_history_scalar_residual mLen alpha w =
      (2*alpha-alpha^2)*(w-mLen)^2/2 := by
  simp only [hgt_history_scalar_residual, hgt_history_scalar_cap, min_eq_left h]
  ring

private theorem hgt_history_scalar_lower {mLen alpha w : ℝ}
    (h : w ≤ alpha*mLen) :
    hgt_history_scalar_residual mLen alpha w =
      -(1-alpha)^2*w^2/2 - alpha*(1-alpha)*mLen*w +
        alpha*(1-alpha)*mLen^2 := by
  simp only [hgt_history_scalar_residual, hgt_history_scalar_cap, min_eq_right h]
  ring

private theorem hgt_history_scalar_ceiling_pos {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) : 0 < 2*alpha-alpha^2 := by
  have htwo : 0 < 2-alpha := by linarith
  nlinarith [mul_pos ha htwo]

private theorem hgt_history_scalar_lower_pos {mLen alpha w : ℝ}
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hw : 0 ≤ w) (h : w ≤ alpha*mLen) :
    0 < hgt_history_scalar_residual mLen alpha w := by
  have hq : 0 < 1-alpha := by linarith
  have hq0 : 0 ≤ 1-alpha := by linarith
  have hm0 : 0 ≤ mLen := by linarith
  have ha0 : 0 ≤ alpha := by linarith
  have hsq : 0 ≤ (alpha*mLen)^2-w^2 := by
    nlinarith [mul_self_le_mul_self hw h]
  have hd : 0 ≤ alpha*mLen-w := by linarith
  have hfirst : 0 ≤ (1-alpha)^2*((alpha*mLen)^2-w^2)/2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) hsq) (by norm_num)
  have hsecond : 0 ≤ alpha*(1-alpha)*mLen*(alpha*mLen-w) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha0 hq0) hm0) hd
  have hgap : 0 < mLen-alpha*mLen := by nlinarith [mul_pos hm hq]
  have hc : 0 < 2*alpha-alpha^2 :=
    hgt_history_scalar_ceiling_pos ha (by linarith)
  have hlast : 0 < (2*alpha-alpha^2)*(mLen-alpha*mLen)^2/2 :=
    div_pos (mul_pos hc (sq_pos_of_pos hgap)) (by norm_num)
  have heq : hgt_history_scalar_residual mLen alpha w =
      (1-alpha)^2*((alpha*mLen)^2-w^2)/2 +
      alpha*(1-alpha)*mLen*(alpha*mLen-w) +
      (2*alpha-alpha^2)*(mLen-alpha*mLen)^2/2 := by
    rw [hgt_history_scalar_lower h]
    ring
  rw [heq]
  linarith

private theorem hgt_history_scalar_upper_zero {mLen alpha w : ℝ}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (h : alpha*mLen ≤ w) :
    hgt_history_scalar_residual mLen alpha w = 0 ↔ w = mLen := by
  rw [hgt_history_scalar_upper h]
  have hc := hgt_history_scalar_ceiling_pos ha ha1
  constructor
  · intro hz
    by_contra hne
    have hs : 0 < (w-mLen)^2 := by
      apply lt_of_le_of_ne (sq_nonneg _)
      intro heq
      have hzero : w-mLen = 0 := sq_eq_zero_iff.mp heq.symm
      apply hne
      linarith
    nlinarith [mul_pos hc hs]
  · intro heq
    rw [heq]
    ring

private theorem hgt_history_scalar_nonneg {mLen alpha w : ℝ}
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hw : 0 ≤ w) :
    0 ≤ hgt_history_scalar_residual mLen alpha w ∧
      (hgt_history_scalar_residual mLen alpha w = 0 ↔
        if alpha < 1 then w = mLen else w ≤ mLen) := by
  by_cases hupper : alpha*mLen ≤ w
  · constructor
    · rw [hgt_history_scalar_upper hupper]
      have hc0 : 0 ≤ 2*alpha-alpha^2 := by
        have := hgt_history_scalar_ceiling_pos ha ha1
        linarith
      exact div_nonneg (mul_nonneg hc0 (sq_nonneg _)) (by norm_num)
    · rw [hgt_history_scalar_upper_zero ha ha1 hupper]
      by_cases hlt : alpha < 1
      · simp only [if_pos hlt]
      · have heq : alpha = 1 := by linarith
        rw [if_neg hlt]
        constructor
        · intro h; linarith
        · intro h
          rw [heq] at hupper
          nlinarith
  · have hlower : w ≤ alpha*mLen := by linarith
    by_cases hlt : alpha < 1
    · have hp := hgt_history_scalar_lower_pos hm ha hlt hw hlower
      constructor
      · linarith
      · rw [if_pos hlt]
        constructor
        · intro hz; exfalso; linarith
        · intro heq
          exfalso
          have hq : 0 < 1-alpha := by linarith
          nlinarith [mul_pos hm hq]
    · have heq : alpha = 1 := by linarith
      have hz : hgt_history_scalar_residual mLen alpha w = 0 := by
        rw [hgt_history_scalar_lower hlower, heq]
        ring
      constructor
      · rw [hz]
      · rw [if_neg hlt]
        constructor
        · intro _
          rw [heq] at hlower
          nlinarith
        · intro _; exact hz

private def hgt_history_scalar_quarter (h w : ℝ) : ℝ :=
  7*w^2/32 - hgt_history_scalar_cap h w - 3*h/4*(w-4*h)

private theorem hgt_history_scalar_quarter_eq (h w : ℝ) :
    hgt_history_scalar_quarter h w =
      hgt_history_scalar_residual (4*h) (1/4) w := by
  unfold hgt_history_scalar_quarter hgt_history_scalar_residual
  have hmul : (1/4:ℝ)*(4*h) = h := by ring
  rw [hmul]
  ring

private theorem hgt_history_scalar_quarter_nonneg {h w : ℝ}
    (hh : 0 < h) (hw : 0 ≤ w) :
    0 ≤ hgt_history_scalar_quarter h w ∧
      (hgt_history_scalar_quarter h w = 0 ↔ w = 4*h) := by
  rw [hgt_history_scalar_quarter_eq]
  have ha : (1/4:ℝ) < 1 := by norm_num
  simpa only [if_pos ha] using
    hgt_history_scalar_nonneg (mLen := 4*h) (alpha := (1/4:ℝ))
      (by linarith) (by norm_num) (by norm_num) hw

private theorem hgt_history_scalar_quarter_lower {h w : ℝ}
    (hh : 0 < h) (hw : 0 ≤ w) (hwh : w ≤ h) :
    63*h^2/32 ≤ hgt_history_scalar_quarter h w := by
  have hsq : w^2 ≤ h^2 := by nlinarith [mul_self_le_mul_self hw hwh]
  have hprod : 0 ≤ h*(h-w) := mul_nonneg (by linarith) (by linarith)
  have heq : hgt_history_scalar_quarter h w = 3*h^2-3*h*w/4-9*w^2/32 := by
    simp only [hgt_history_scalar_quarter, hgt_history_scalar_cap, min_eq_right hwh]
    ring
  rw [heq]
  nlinarith

end
end RHTower


/-! Right-origin limits for the slope scale and capped history fractions. -/
open Filter Topology Set
namespace RHTower
noncomputable section

private theorem hgt_history_origin_slope {K : ℝ → ℝ} {b : ℝ}
    (hK0 : K 0 = 0) (hK : HasDerivAt K b 0) :
    Tendsto (fun t : ℝ => K t / t) (𝓝[Ioi 0] 0) (𝓝 b) := by
  simpa only [zero_add, hK0, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm]
    using hK.tendsto_slope_zero_right

private theorem hgt_history_origin_excess {A K : ℝ → ℝ} {b : ℝ}
    (hA0 : A 0 = 0) (hK0 : K 0 = 0) (hAc : Continuous A)
    (hA : ∀ t : ℝ, HasDerivAt A (K t) t) (hK : HasDerivAt K b 0) :
    Tendsto (fun t : ℝ => A t / t^2) (𝓝[Ioi 0] 0) (𝓝 (b/2)) := by
  have hratio : Tendsto (fun t : ℝ => K t / (2*t))
      (𝓝[Ioi 0] 0) (𝓝 (b/2)) := by
    convert (hgt_history_origin_slope hK0 hK).div_const 2 using 1
    funext t
    ring
  exact HasDerivAt.lhopital_zero_right_on_Ico (b := 1) (by norm_num)
    (fun t _ => hA t)
    (fun t _ => by
      simpa using (hasDerivAt_id t).fun_pow 2)
    hAc.continuousOn (continuous_id.pow 2).continuousOn
    (fun t ht => by nlinarith [ht.1]) hA0 (by norm_num) hratio

private theorem hgt_history_origin_scale {K K1 : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hK0 : K 0 = 0) (hK : HasDerivAt K b 0)
    (hK1c : ContinuousAt K1 0) (hK10 : K1 0 = b) :
    Tendsto (fun t : ℝ => (K t / K1 t) / t)
      (𝓝[Ioi 0] 0) (𝓝 1) ∧
    Tendsto (fun t : ℝ => (K t / (4*K1 t)) / t)
      (𝓝[Ioi 0] 0) (𝓝 (1/4 : ℝ)) := by
  have h1 : Tendsto K1 (𝓝[Ioi 0] 0) (𝓝 b) := by
    simpa only [hK10] using hK1c.tendsto.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun t : ℝ => (K t / K1 t) / t)
      (𝓝[Ioi 0] 0) (𝓝 1) := by
    convert (hgt_history_origin_slope hK0 hK).div h1 (ne_of_gt hb) using 1
    · funext t
      change K t / K1 t / t = K t / t / K1 t
      ring
    · simp [ne_of_gt hb]
  refine ⟨hm, ?_⟩
  convert hm.div_const 4 using 1
  funext t
  ring

private def hgt_history_origin_quadratic (A : ℝ → ℝ) (c u : ℝ) : ℝ :=
  if u = 0 then c else A u / u^2

private theorem hgt_history_origin_quadratic_limit {A : ℝ → ℝ} {c : ℝ}
    (hA : Tendsto (fun t : ℝ => A t / t^2) (𝓝[Ioi 0] 0) (𝓝 c)) :
    Tendsto (hgt_history_origin_quadratic A c) (𝓝[Ici 0] 0) (𝓝 c) := by
  have hs : Ici (0 : ℝ) = insert 0 (Ioi 0) := by
    ext x
    simp only [mem_Ici, mem_insert_iff, mem_Ioi]
    constructor
    · intro hx
      by_cases he : x = 0
      · exact Or.inl he
      · right
        exact lt_of_le_of_ne hx (Ne.symm he)
    · rintro (rfl | hx)
      · exact le_rfl
      · exact hx.le
  rw [hs, nhdsWithin_insert, Filter.tendsto_sup]
  constructor
  · simpa [hgt_history_origin_quadratic] using
      (Filter.tendsto_pure_pure (hgt_history_origin_quadratic A c) 0).mono_right
        (pure_le_nhds _)
  · apply hA.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Ioi] at ht
    simp only [hgt_history_origin_quadratic, if_neg (ne_of_gt ht)]

private theorem hgt_history_origin_remainder {A u : ℝ → ℝ} {c r : ℝ}
    (hA0 : A 0 = 0) (hc : c ≠ 0)
    (hA : Tendsto (fun t : ℝ => A t / t^2) (𝓝[Ioi 0] 0) (𝓝 c))
    (hu : Tendsto u (𝓝[Ioi 0] 0) (𝓝 0))
    (hupos : ∀ᶠ t : ℝ in 𝓝[Ioi 0] 0, 0 ≤ u t)
    (hr : Tendsto (fun t : ℝ => u t / t) (𝓝[Ioi 0] 0) (𝓝 r)) :
    Tendsto (fun t : ℝ => A (u t) / A t) (𝓝[Ioi 0] 0) (𝓝 (r^2)) := by
  have huclosed : Tendsto u (𝓝[Ioi 0] 0) (𝓝[Ici 0] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, hupos⟩
  have hq := (hgt_history_origin_quadratic_limit hA).comp huclosed
  have hv : Tendsto (fun t : ℝ =>
      hgt_history_origin_quadratic A c (u t) * (u t / t)^2 / (A t / t^2))
      (𝓝[Ioi 0] 0) (𝓝 (r^2)) := by
    convert (hq.mul (hr.pow 2)).div hA hc using 1
    · rfl
    · field_simp
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  by_cases hu0 : u t = 0
  · simp [hgt_history_origin_quadratic, hu0, hA0]
  · by_cases hAt : A t = 0
    · simp [hAt]
    · simp only [hgt_history_origin_quadratic, if_neg hu0]
      field_simp

private theorem hgt_history_origin_cap_ratio {m : ℝ → ℝ}
    (hm : Tendsto (fun t : ℝ => m t / t) (𝓝[Ioi 0] 0) (𝓝 1))
    (alpha : ℝ) :
    Tendsto (fun t : ℝ => (t - min (alpha*m t) t) / t)
      (𝓝[Ioi 0] 0) (𝓝 (1 - min alpha 1)) := by
  have hv : Tendsto (fun t : ℝ => 1-min (alpha*(m t/t)) 1)
      (𝓝[Ioi 0] 0) (𝓝 (1-min alpha 1)) := by
    simpa only [mul_one] using ((hm.const_mul alpha).min tendsto_const_nhds).const_sub 1
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simp only [sub_div, ← min_div_div_right (le_of_lt ht),
    div_self (ne_of_gt ht), mul_div_assoc]

private theorem hgt_history_origin_cap_zero {m : ℝ → ℝ}
    (hm : Tendsto (fun t : ℝ => m t / t) (𝓝[Ioi 0] 0) (𝓝 1))
    (alpha : ℝ) :
    Tendsto (fun t : ℝ => t - min (alpha*m t) t) (𝓝[Ioi 0] 0) (𝓝 0) := by
  have hv : Tendsto (fun t : ℝ => ((t-min (alpha*m t) t)/t)*t)
      (𝓝[Ioi 0] 0) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using (hgt_history_origin_cap_ratio hm alpha).mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun t : ℝ => t) (𝓝[Ioi 0] 0) (𝓝 0))
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  field_simp [ne_of_gt ht]

private theorem hgt_history_origin_fraction {A m : ℝ → ℝ} {c : ℝ}
    (hA0 : A 0 = 0) (hc : c ≠ 0)
    (hApos : ∀ t : ℝ, 0 < t → 0 < A t)
    (hA : Tendsto (fun t : ℝ => A t / t^2) (𝓝[Ioi 0] 0) (𝓝 c))
    (hm : Tendsto (fun t : ℝ => m t / t) (𝓝[Ioi 0] 0) (𝓝 1))
    (alpha : ℝ) :
    Tendsto (fun t : ℝ => (A t - A (t - min (alpha*m t) t)) / A t)
      (𝓝[Ioi 0] 0) (𝓝 (if alpha ≤ 1 then 2*alpha-alpha^2 else 1)) := by
  have hupos : ∀ᶠ t : ℝ in 𝓝[Ioi 0] 0, 0 ≤ t-min (alpha*m t) t := by
    filter_upwards with t
    exact sub_nonneg.mpr (min_le_right _ _)
  have hr := hgt_history_origin_remainder hA0 hc hA
    (hgt_history_origin_cap_zero hm alpha) hupos (hgt_history_origin_cap_ratio hm alpha)
  have hcval : 1-(1-min alpha 1)^2 =
      (if alpha ≤ 1 then 2*alpha-alpha^2 else 1) := by
    by_cases ha : alpha ≤ 1
    · rw [if_pos ha, min_eq_left ha]
      ring
    · rw [if_neg ha, min_eq_right (by linarith : 1 ≤ alpha)]
      norm_num
  rw [← hcval]
  apply (hr.const_sub 1).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [sub_div, div_self (ne_of_gt (hApos t ht))]

private theorem hgt_history_origin_eventually_cap {m : ℝ → ℝ} {alpha : ℝ}
    (ha : 1 < alpha)
    (hm : Tendsto (fun t : ℝ => m t / t) (𝓝[Ioi 0] 0) (𝓝 1)) :
    ∀ᶠ t : ℝ in 𝓝[Ioi 0] 0, t < alpha*m t := by
  have hv : Tendsto (fun t : ℝ => alpha*(m t/t))
      (𝓝[Ioi 0] 0) (𝓝 alpha) := by simpa only [mul_one] using hm.const_mul alpha
  filter_upwards [(tendsto_order.mp hv).1 1 ha, self_mem_nhdsWithin] with t hgt ht
  change 0 < t at ht
  have hp : 0 < (alpha*(m t/t)-1)*t := mul_pos (by linarith) ht
  have he : (alpha*(m t/t)-1)*t = alpha*m t-t := by
    field_simp [ne_of_gt ht]
  rw [he] at hp
  linarith

private theorem hgt_history_origin_eventually_one {U m : ℝ → ℝ} {alpha : ℝ}
    (ha : 1 < alpha)
    (hm : Tendsto (fun t : ℝ => m t / t) (𝓝[Ioi 0] 0) (𝓝 1))
    (hU : ∀ t : ℝ, 0 < t → t ≤ alpha*m t → U t = 1) :
    ∀ᶠ t : ℝ in 𝓝[Ioi 0] 0, U t = 1 := by
  filter_upwards [hgt_history_origin_eventually_cap ha hm, self_mem_nhdsWithin] with t hc ht
  exact hU t ht hc.le

private theorem hgt_history_origin_ceiling {U : ℝ → ℝ} {c : ℝ}
    (hlim : Tendsto U (𝓝[Ioi 0] 0) (𝓝 c))
    (hbound : ∀ t : ℝ, 0 < t → U t ≤ c) (gamma : ℝ) :
    (∀ t : ℝ, 0 < t → U t ≤ gamma) ↔ c ≤ gamma := by
  constructor
  · intro h
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall h)
  · intro h t ht
    exact (hbound t ht).trans h

end
end RHTower

section
open MeasureTheory Set intervalIntegral Filter Topology
namespace RHTower
noncomputable section

private def hgt_history_age_dividedPower (n : ℕ) (t : ℝ) : ℝ := t^n/(n.factorial:ℝ)
@[fun_prop] private theorem hgt_history_age_continuous_dividedPower (n : ℕ) : Continuous (hgt_history_age_dividedPower n) := by
  unfold hgt_history_age_dividedPower
  fun_prop
private theorem hgt_history_age_dividedPower_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (hgt_history_age_dividedPower (n+1)) (hgt_history_age_dividedPower n t) t := by
  have h := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
  convert h using 1 <;> try rfl
  simp only [hgt_history_age_dividedPower, id_eq, Nat.add_sub_cancel, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp
private theorem hgt_history_age_integral_dividedPower_convolution (p q : ℕ) (t : ℝ) :
    ∫ s in 0..t, hgt_history_age_dividedPower p s * hgt_history_age_dividedPower q (t-s) =
      hgt_history_age_dividedPower (p+q+1) t := by
  induction q generalizing p with
  | zero =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=0) (b:=t) (fun x _ => hgt_history_age_dividedPower_deriv p x)
      (by exact (by fun_prop : Continuous (hgt_history_age_dividedPower p)).intervalIntegrable 0 t)
    simpa [hgt_history_age_dividedPower] using h
  | succ q ih =>
    have hu : ∀ x, HasDerivAt (fun s => hgt_history_age_dividedPower (q+1) (t-s))
        (-hgt_history_age_dividedPower q (t-x)) x := by
      intro x
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (hgt_history_age_dividedPower_deriv q (t-x)).comp x
          ((hasDerivAt_const x t).sub (hasDerivAt_id x))
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a:=0) (b:=t)
      (u:=fun s => hgt_history_age_dividedPower (q+1) (t-s)) (v:=hgt_history_age_dividedPower (p+1))
      (u':=fun s => -hgt_history_age_dividedPower q (t-s)) (v':=hgt_history_age_dividedPower p)
      (by fun_prop) (by fun_prop) (fun x _ => hu x)
      (fun x _ => hgt_history_age_dividedPower_deriv p x)
      ((by fun_prop : Continuous fun s => -hgt_history_age_dividedPower q (t-s)).intervalIntegrable 0 t)
      ((by fun_prop : Continuous (hgt_history_age_dividedPower p)).intervalIntegrable 0 t)
    simp only [hgt_history_age_dividedPower, sub_self, zero_pow (Nat.succ_ne_zero _), zero_div,
      zero_mul, mul_zero, sub_zero, zero_sub] at h
    have hn : (fun x : ℝ => -(hgt_history_age_dividedPower q (t-x)) * hgt_history_age_dividedPower (p+1) x) =
        (fun x => -(hgt_history_age_dividedPower q (t-x) * hgt_history_age_dividedPower (p+1) x)) := by
      funext x
      ring
    change (∫x in 0..t, hgt_history_age_dividedPower (q+1) (t-x)*hgt_history_age_dividedPower p x) =
      -(∫x in 0..t, -(hgt_history_age_dividedPower q (t-x))*hgt_history_age_dividedPower (p+1) x) at h
    rw [hn, intervalIntegral.integral_neg, neg_neg] at h
    calc
      (∫s in 0..t, hgt_history_age_dividedPower p s * hgt_history_age_dividedPower (q+1) (t-s)) =
          ∫s in 0..t, hgt_history_age_dividedPower (q+1) (t-s)*hgt_history_age_dividedPower p s := by
        congr 1
        funext s
        ring
      _ = ∫s in 0..t, hgt_history_age_dividedPower q (t-s)*hgt_history_age_dividedPower (p+1) s := h
      _ = ∫s in 0..t, hgt_history_age_dividedPower (p+1) s * hgt_history_age_dividedPower q (t-s) := by
        congr 1
        funext s
        ring
      _ = hgt_history_age_dividedPower (p+q+1+1) t := by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (p+1)

private def hgt_history_age_term (n j : ℕ) (t s : ℝ) : ℝ :=
  hgt_history_source_term 1 (j+1) (t-s) * s^n

private theorem hgt_history_age_shifted_hasSum (x : ℝ) :
    HasSum (fun j => hgt_history_source_term 1 (j+1) x)
      (deriv liEvenCrossActualClockBorelKernel x) := by
  have h := (hgt_history_source_derivative_series 1 x).2
  rw [iteratedDeriv_one] at h
  simpa [hgt_history_source_term] using (hasSum_nat_add_iff' 1).mpr h

private theorem hgt_history_age_term_hasSum (n : ℕ) (t s : ℝ) :
    HasSum (fun j => hgt_history_age_term n j t s)
      (deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) :=
  (hgt_history_age_shifted_hasSum (t-s)).mul_right (s^n)

private theorem hgt_history_age_power_beta (p q : ℕ) (t : ℝ) :
    (∫ s in 0..t, s^p * (t-s)^q) =
      (p.factorial : ℝ) * (q.factorial : ℝ) *
        t^(p+q+1) / ((p+q+1).factorial : ℝ) := by
  calc
    (∫ s in 0..t, s^p * (t-s)^q) =
        ((p.factorial : ℝ) * (q.factorial : ℝ)) *
          ∫ s in 0..t, hgt_history_age_dividedPower p s *
            hgt_history_age_dividedPower q (t-s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      unfold hgt_history_age_dividedPower
      field_simp
    _ = _ := by
      rw [hgt_history_age_integral_dividedPower_convolution]
      unfold hgt_history_age_dividedPower
      ring

private theorem hgt_history_age_term_integral (n j : ℕ) (t : ℝ) :
    (∫ s in 0..t, hgt_history_age_term n j t s) =
      (n.factorial : ℝ) * thetaCuspNormalizedEvenMoment (j+1) *
        t^(2*(j+1)+n) /
          (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)) := by
  have hp : 2*(j+1)-1 = 2*j+1 := by omega
  have hn : n+(2*j+1)+1 = 2*(j+1)+n := by omega
  have hf : (((2*(j+1)).factorial : ℕ) : ℝ) =
      (2*(j+1) : ℝ) * ((2*j+1).factorial : ℝ) := by
    rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  calc
    (∫ s in 0..t, hgt_history_age_term n j t s) =
        (liEvenCrossActualClockBorelCoefficient (j+1) * (2*(j+1) : ℝ)) *
          ∫ s in 0..t, s^n * (t-s)^(2*j+1) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hgt_history_age_term, hgt_history_source_term, Nat.descFactorial_one,
        Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, hp]
      ring
    _ = _ := by
      rw [hgt_history_age_power_beta, hn]
      unfold liEvenCrossActualClockBorelCoefficient
      field_simp
      rw [hf]
      ring

private theorem hgt_history_age_integrated_series (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s : ℝ => deriv liEvenCrossActualClockBorelKernel (t-s) * s^n)
      volume 0 t ∧
    HasSum (fun j => ∫ s in 0..t, hgt_history_age_term n j t s)
      (∫ s in 0..t, deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) := by
  let T : ℝ := t+1
  have hT : 1 ≤ T := by dsimp [T]; linarith
  let G : ℕ → ℝ := fun j =>
    ((2 : ℝ)^1 * ((j+1 : ℕ) : ℝ)^1 *
      liEvenCrossActualClockBorelCoefficient (j+1) * T^(2*(j+1))) * T^n
  have hG : Summable G := by
    exact ((summable_nat_add_iff 1).mpr
      (hgt_history_source_envelope_summable 1 (show 0 ≤ T by linarith))).mul_right (T^n)
  have hcont : Continuous (fun s : ℝ => deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) :=
    (hgt_history_source_contDiff_K.continuous.comp (by fun_prop)).mul (by fun_prop)
  refine ⟨hcont.intervalIntegrable 0 t, ?_⟩
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ => G j)
  · intro j
    apply Continuous.aestronglyMeasurable
    unfold hgt_history_age_term hgt_history_source_term
    fun_prop
  · intro j
    filter_upwards with s hs
    have hs' : s ∈ Icc 0 t := by
      rw [uIoc_of_le ht] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hst : |t-s| ≤ T := by
      rw [abs_of_nonneg (by linarith [hs'.2])]
      dsimp [T]
      linarith [hs'.1]
    have hsp : s^n ≤ T^n := pow_le_pow_left₀ hs'.1 (by dsimp [T]; linarith [hs'.2]) n
    rw [hgt_history_age_term, norm_mul, norm_pow]
    rw [show ‖s‖ = s by rw [Real.norm_eq_abs, abs_of_nonneg hs'.1]]
    have hc := (liEvenCrossActualClockBorelCoefficient_pos (j+1)).le
    have hT0 : 0 ≤ T := by linarith
    exact mul_le_mul (hgt_history_source_term_bound 1 (j+1) hT hst) hsp
      (pow_nonneg hs'.1 n) (by positivity)
  · filter_upwards with s _
    exact hG
  · exact intervalIntegrable_const
  · filter_upwards with s _
    exact hgt_history_age_term_hasSum n t s

private theorem hgt_history_age_beta_series (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun j => (n.factorial : ℝ) * thetaCuspNormalizedEvenMoment (j+1) *
      t^(2*(j+1)+n) /
        (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)))
      (∫ s in 0..t, deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) := by
  exact (hgt_history_age_integrated_series n ht).2.congr_fun
    (fun j => (hgt_history_age_term_integral n j t).symm)

private theorem hgt_history_age_base_series (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun j => ‖thetaCuspNormalizedEvenMoment (j+1) * t^(2*(j+1)+n) /
      (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ))‖) ∧
    HasSum (fun j => thetaCuspNormalizedEvenMoment (j+1) * t^(2*(j+1)+n) /
      (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)))
      ((∫ s in 0..t, deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) /
        (n.factorial : ℝ)) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : HasSum (fun j => thetaCuspNormalizedEvenMoment (j+1) * t^(2*(j+1)+n) /
      (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)))
      ((∫ s in 0..t, deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) /
        (n.factorial : ℝ)) := by
    have hraw := (hgt_history_age_beta_series n ht).mul_right (n.factorial : ℝ)⁻¹
    have hnew := hraw.congr_fun (g := fun j =>
      thetaCuspNormalizedEvenMoment (j+1) * t^(2*(j+1)+n) /
        (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)))
      (by intro j; field_simp)
    simpa only [div_eq_mul_inv] using hnew
  exact ⟨hs.summable.norm, hs⟩

private theorem hgt_history_age_integral_eq (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, deriv liEvenCrossActualClockBorelKernel (t-s) * s^n) =
      (n.factorial : ℝ) * ∑' j, thetaCuspNormalizedEvenMoment (j+1) * t^(2*(j+1)+n) /
        (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ)) := by
  rw [(hgt_history_age_base_series n ht).2.tsum_eq]
  field_simp

end
end RHTower
end

namespace RHTower

private theorem hgt_history_rigidity_residual_continuous (mLen alpha t : ℝ) :
    Continuous (fun r => hgt_history_scalar_residual mLen alpha (t-r)) := by
  unfold hgt_history_scalar_residual hgt_history_scalar_cap
  fun_prop

private theorem hgt_history_rigidity_mean_correction {k : ℝ → ℝ} {t mLen : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (hm : mLen = k t / deriv k t) :
    (∫ r, t-r-mLen ∂hgt_history_hinge_measure k t) = 0 := by
  have ha := hgt_history_hinge_admissions hk hb.le ht.le hc
  have mom := hgt_history_hinge_moments hk hk0 hb.le ht.le hc
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hlag := (ha.2.2 (fun r => t-r) (by fun_prop)).1
  have hconst := (ha.2.2 (fun _ => mLen) continuous_const).1
  rw [integral_sub hlag hconst, mom.2.1, integral_const, smul_eq_mul, mom.1, hm,
    mul_comm (deriv k t), div_mul_cancel₀ _ hg.1.ne', sub_self]

private theorem hgt_history_rigidity_residual_integral {k : ℝ → ℝ} {t mLen alpha : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (hm : mLen = k t / deriv k t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    (∫ r, hgt_history_scalar_residual mLen alpha (t-r)
      ∂hgt_history_hinge_measure k t) =
    (2*alpha-alpha^2)*hgt_history_hinge_mass k t - ∫ s in 0..alpha*mLen, k (t-s) := by
  have adm := hgt_history_hinge_admissions hk hb.le ht.le hc
  have mom := hgt_history_hinge_moments hk hk0 hb.le ht.le hc
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hmpos : 0 < mLen := by rw [hm]; exact hg.2.2.2.1
  have hmt : mLen ≤ t := by rw [hm]; exact hg.2.2.2.2
  have hh : 0 ≤ alpha*mLen := (mul_pos ha hmpos).le
  have hht : alpha*mLen ≤ t := (mul_le_of_le_one_left hmpos.le ha1).trans hmt
  have hi1 := (adm.2.2 (fun r => (2*alpha-alpha^2)*((t-r)^2/2)) (by fun_prop)).1
  have hi2 := (adm.2.2 (fun r => hgt_history_scalar_cap (alpha*mLen) (t-r))
    (by unfold hgt_history_scalar_cap; fun_prop)).1
  have hi3 := (adm.2.2 (fun r => alpha*mLen*(1-alpha)*(t-r-mLen)) (by fun_prop)).1
  have hcap := (hgt_history_hinge_cap_identity hk hk0 hb ht hh hc).2
  rw [hgt_history_hinge_age_cutoff hk hk0 hb ht hh hc, min_eq_left hht,
    ← mul_div_assoc, mul_div_cancel_left₀ _ hg.2.2.1.ne'] at hcap
  have heq : (fun r => hgt_history_scalar_residual mLen alpha (t-r)) =
      (fun r => (2*alpha-alpha^2)*((t-r)^2/2) -
        hgt_history_scalar_cap (alpha*mLen) (t-r) - alpha*mLen*(1-alpha)*(t-r-mLen)) := by
    ext r
    unfold hgt_history_scalar_residual
    ring
  have hdiff := integral_sub (hi1.sub hi2) hi3
  dsimp only [Pi.sub_apply] at hdiff
  rw [heq, hdiff, integral_sub hi1 hi2,
    integral_const_mul, integral_const_mul, mom.2.2,
    hgt_history_rigidity_mean_correction hk hk0 hb ht hc hm, mul_zero, sub_zero]
  simpa only [hgt_history_scalar_cap, hgt_history_hinge_cap] using
    congrArg (fun x => (2*alpha-alpha^2)*hgt_history_hinge_mass k t-x) hcap

private theorem hgt_history_rigidity_origin_reserve {k : ℝ → ℝ} {t mLen alpha : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hb : 0 ≤ deriv k 0) (ht : 0 ≤ t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    deriv k 0 * hgt_history_scalar_residual mLen alpha t ≤
      (∫ r, hgt_history_scalar_residual mLen alpha (t-r)
        ∂hgt_history_hinge_measure k t) := by
  have adm := hgt_history_hinge_admissions hk hb ht hc
  rw [(adm.2.2 _ (hgt_history_rigidity_residual_continuous mLen alpha t)).2, sub_zero]
  have hn : 0 ≤ ∫ r in 0..t, deriv (deriv k) r *
      hgt_history_scalar_residual mLen alpha (t-r) := by
    apply intervalIntegral.integral_nonneg ht
    intro r hr
    exact mul_nonneg (hc r hr) (hgt_history_scalar_nonneg hm ha ha1 (by linarith [hr.2])).1
  linarith

private theorem hgt_history_rigidity_equal_mean {k : ℝ → ℝ} {t alpha : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (he : (∫ s in 0..alpha*(k t / deriv k t), k (t-s)) /
      hgt_history_hinge_mass k t = 2*alpha-alpha^2) :
    k t / deriv k t = t := by
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hr := hgt_history_rigidity_residual_integral hk hk0 hb ht hc rfl ha ha1
  have hn := (div_eq_iff hg.2.2.1.ne').mp he
  rw [hn] at hr
  have hz : (∫ r, hgt_history_scalar_residual (k t / deriv k t) alpha (t-r)
      ∂hgt_history_hinge_measure k t) = 0 := by linarith
  have hres := hgt_history_rigidity_origin_reserve hk hb.le ht.le hc hg.2.2.2.1 ha ha1
  rw [hz] at hres
  have hupper : alpha*(k t / deriv k t) ≤ t :=
    (mul_le_of_le_one_left hg.2.2.2.1.le ha1).trans hg.2.2.2.2
  have hnon := (hgt_history_scalar_nonneg hg.2.2.2.1 ha ha1 ht.le).1
  have hez : hgt_history_scalar_residual (k t / deriv k t) alpha t = 0 := by
    nlinarith
  exact ((hgt_history_scalar_upper_zero ha ha1 hupper).mp hez).symm

private theorem hgt_history_rigidity_mean_linear {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (he : k t = t*deriv k t) :
    ∀ x ∈ Icc 0 t, k x = deriv k 0*x := by
  have hd := hgt_history_hinge_derivatives hk
  have hmon : MonotoneOn (deriv k) (Icc 0 t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hd.2.1.continuousOn
      hd.2.2.1.differentiableOn (fun x hx => hc x (interior_subset hx))
  have hint : (∫ x in 0..t, deriv k x) = k t := by
    simpa [hk0] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (hd.1 x).hasDerivAt) (hd.2.1.intervalIntegrable 0 t)
  have hb : deriv k 0 = deriv k t := by
    have hle := hmon ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
    apply le_antisymm hle
    by_contra hn
    have hlt : deriv k 0 < deriv k t := lt_of_not_ge hn
    have hstrict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      ht hd.2.1.continuousOn (continuous_const.continuousOn)
      (fun x hx => hmon ⟨hx.1.le, hx.2⟩ ⟨ht.le, le_rfl⟩ hx.2)
      ⟨0, ⟨le_rfl, ht.le⟩, hlt⟩
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, hint, he] at hstrict
    exact (lt_irrefl _ hstrict)
  have hdconst : ∀ x ∈ Icc 0 t, deriv k x = deriv k 0 := by
    intro x hx
    apply le_antisymm
    · rw [hb]
      exact hmon hx ⟨ht.le, le_rfl⟩ hx.2
    · exact hmon ⟨le_rfl, ht.le⟩ hx hx.1
  intro x hx
  have hxint : (∫ y in 0..x, deriv k y) = k x := by
    simpa [hk0] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => (hd.1 y).hasDerivAt) (hd.2.1.intervalIntegrable 0 x)
  have hsame : (∫ y in 0..x, deriv k y) = ∫ y in 0..x, deriv k 0 := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyc : y ∈ Icc 0 x := by simpa only [uIcc_of_le hx.1] using hy
    exact hdconst y ⟨hyc.1, hyc.2.trans hx.2⟩
  rw [hxint, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hsame
  simpa [mul_comm] using hsame

private theorem hgt_history_rigidity_linear_deriv {k : ℝ → ℝ} {t : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (ht : 0 < t)
    (he : ∀ x ∈ Icc 0 t, k x = deriv k 0*x) : deriv k t = deriv k 0 := by
  have hd := hgt_history_hinge_derivatives hk
  have hlinear : HasDerivWithinAt k (deriv k 0) (Icc 0 t) t :=
    (hasDerivAt_const_mul (deriv k 0) (x := t)).hasDerivWithinAt.congr_of_mem he
      ⟨ht.le, le_rfl⟩
  exact UniqueDiffWithinAt.eq_deriv (Icc 0 t) (uniqueDiffOn_Icc ht t ⟨ht.le, le_rfl⟩)
    (hd.1 t).hasDerivAt.hasDerivWithinAt hlinear

private theorem hgt_history_rigidity_linear_fraction {k : ℝ → ℝ} {t alpha : ℝ}
    (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (ht : 0 < t)
    (hc : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (he : ∀ x ∈ Icc 0 t, k x = deriv k 0*x) :
    (∫ s in 0..alpha*(k t / deriv k t), k (t-s)) /
      hgt_history_hinge_mass k t = 2*alpha-alpha^2 := by
  have hd := hgt_history_rigidity_linear_deriv hk ht he
  have hg := hgt_history_hinge_guards hk hk0 hb ht hc
  have hm : k t / deriv k t = t := by
    rw [hd, he t ⟨ht.le, le_rfl⟩, mul_div_cancel_left₀ _ hb.ne']
  have hmass : hgt_history_hinge_mass k t = deriv k 0*t^2/2 := by
    unfold hgt_history_hinge_mass
    have hi : (∫ x in 0..t, k x) = ∫ x in 0..t, deriv k 0*x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact he x (by simpa only [uIcc_of_le ht.le] using hx)
    rw [hi, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hcut : 0 ≤ alpha*t := (mul_pos ha ht).le
  have hcutle : alpha*t ≤ t := mul_le_of_le_one_left ht.le ha1
  have hnum : (∫ s in 0..alpha*t, k (t-s)) =
      deriv k 0*(t*(alpha*t)-(alpha*t)^2/2) := by
    rw [intervalIntegral.integral_comp_sub_left, sub_zero]
    have hi : (∫ s in (t-alpha*t)..t, k s) =
        ∫ s in (t-alpha*t)..t, deriv k 0*s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hst : s ∈ Icc (t-alpha*t) t := by
        simpa only [uIcc_of_le (by linarith : t-alpha*t ≤ t)] using hs
      exact he s ⟨by linarith [hst.1], hst.2⟩
    rw [hi, intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hm, hnum, hmass]
  field_simp [hb.ne', ht.ne']

private theorem hgt_history_rigidity_slope (k : ℝ → ℝ) {alpha t : ℝ}
    (ht : 0 < t) (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0)
    (hcurv : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    let h := alpha*(k t / deriv k t)
    let mass := ∫ x in 0..t, k x
    ((∫ s in 0..h, k (t-s))/mass = 2*alpha-alpha^2 ↔
      ∀ x ∈ Icc 0 t, k x = deriv k 0*x) := by
  dsimp only
  constructor
  · intro he
    have hg := hgt_history_hinge_guards hk hk0 hb ht hcurv
    have hm := hgt_history_rigidity_equal_mean hk hk0 hb ht hcurv ha ha1 he
    apply hgt_history_rigidity_mean_linear hk hk0 ht hcurv
    have hmul := (div_eq_iff hg.1.ne').mp hm
    simpa [mul_comm] using hmul
  · intro he
    exact hgt_history_rigidity_linear_fraction hk hk0 hb ht hcurv ha ha1 he

private theorem hgt_history_rigidity_quarter (k : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0)
    (hcurv : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    let h := k t/(4*deriv k t)
    let mass := ∫ x in 0..t, k x
    ((∫ s in 0..h, k (t-s))/mass = 7/16 ↔
      ∀ x ∈ Icc 0 t, k x = deriv k 0*x) := by
  have hs := hgt_history_rigidity_slope k ht hk hk0 hb hcurv
    (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)
  dsimp only at hs ⊢
  have hh : (1/4:ℝ)*(k t/deriv k t) = k t/(4*deriv k t) := by ring
  rw [hh] at hs
  have hc : 2*(1/4:ℝ)-(1/4:ℝ)^2 = 7/16 := by norm_num
  rw [hc] at hs
  exact hs

end RHTower

open Set MeasureTheory
namespace RHTower
noncomputable section

private theorem hgt_history_zero_mean {μ : Measure ℝ} [IsFiniteMeasure μ]
    {W : ℝ → ℝ} {mLen : ℝ} (hW : Integrable W μ)
    (hle : ∀ᵐ x ∂μ, W x ≤ mLen)
    (hmean : (∫ x, W x ∂μ) = mLen * μ.real univ) :
    ∀ᵐ x ∂μ, W x = mLen := by
  have hi : Integrable (fun x => mLen - W x) μ := (integrable_const mLen).sub hW
  have hn : 0 ≤ᵐ[μ] (fun x => mLen - W x) := by
    filter_upwards [hle] with x hx
    exact sub_nonneg.mpr hx
  have he : (∫ x, mLen - W x ∂μ) = 0 := by
    rw [integral_sub (integrable_const mLen) hW, integral_const, smul_eq_mul, hmean]
    ring
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp he
  filter_upwards [hz] with x hx
  change mLen - W x = 0 at hx
  linarith

private theorem hgt_history_zero_residual_nonneg {μ : Measure ℝ}
    {W : ℝ → ℝ} {mLen alpha : ℝ}
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hW : ∀ᵐ x ∂μ, 0 ≤ W x) :
    0 ≤ᵐ[μ] (fun x => hgt_history_scalar_residual mLen alpha (W x)) := by
  filter_upwards [hW] with x hx
  exact (hgt_history_scalar_nonneg hm ha ha1 hx).1

private theorem hgt_history_zero_residual_iff {μ : Measure ℝ} [IsFiniteMeasure μ]
    {W : ℝ → ℝ} {mLen alpha : ℝ}
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hW : Integrable W μ) (hWn : ∀ᵐ x ∂μ, 0 ≤ W x)
    (hR : Integrable (fun x => hgt_history_scalar_residual mLen alpha (W x)) μ)
    (hmean : (∫ x, W x ∂μ) = mLen * μ.real univ) :
    (∫ x, hgt_history_scalar_residual mLen alpha (W x) ∂μ) = 0 ↔
      ∀ᵐ x ∂μ, W x = mLen := by
  have hn := hgt_history_zero_residual_nonneg hm ha ha1 hWn
  rw [integral_eq_zero_iff_of_nonneg_ae hn hR]
  constructor
  · intro hz
    by_cases hal : alpha < 1
    · filter_upwards [hz, hWn] with x hx hxn
      have he := (hgt_history_scalar_nonneg hm ha ha1 hxn).2.mp hx
      simpa only [if_pos hal] using he
    · have hle : ∀ᵐ x ∂μ, W x ≤ mLen := by
        filter_upwards [hz, hWn] with x hx hxn
        have he := (hgt_history_scalar_nonneg hm ha ha1 hxn).2.mp hx
        simpa only [if_neg hal] using he
      exact hgt_history_zero_mean hW hle hmean
  · intro he
    filter_upwards [he] with x hx
    change hgt_history_scalar_residual mLen alpha (W x) = 0
    rw [hx]
    apply (hgt_history_scalar_nonneg hm ha ha1 hm.le).2.mpr
    split_ifs <;> simp

end
end RHTower

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators Interval
namespace RHTower
noncomputable section
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "K2" => deriv (deriv (deriv liEvenCrossActualClockBorelKernel))
local notation "nu" => thetaCuspNormalizedEvenMoment

def liEvenCrossActualClockHistoryExcess (t : ℝ) : ℝ := B t - 1
def liEvenCrossActualClockHistoryOriginSlope : ℝ := nu 1 / 2
def liEvenCrossActualClockHistoryScale (t : ℝ) : ℝ := K t / (4 * K1 t)
def liEvenCrossActualClockHistoryAgeMeasure (t : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 t)).withDensity
    (fun s => ENNReal.ofReal (K (t-s) / liEvenCrossActualClockHistoryExcess t))
def liEvenCrossActualClockHistoryHingeMeasure (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal liEvenCrossActualClockHistoryOriginSlope • Measure.dirac 0 +
    (volume.restrict (Icc 0 t)).withDensity (fun r => ENNReal.ofReal (K2 r))
def liEvenCrossActualClockHistoryCappedHinge (h w : ℝ) : ℝ :=
  w * min h w - (min h w)^2 / 2
def liEvenCrossActualClockHistoryResidual (h w : ℝ) : ℝ :=
  7*w^2/32 - liEvenCrossActualClockHistoryCappedHinge h w - 3*h/4 * (w-4*h)

local notation "A" => liEvenCrossActualClockHistoryExcess
local notation "b" => liEvenCrossActualClockHistoryOriginSlope
local notation "e" => liEvenCrossActualClockHistoryScale
local notation "Q" => liEvenCrossActualClockHistoryAgeMeasure
local notation "kap" => liEvenCrossActualClockHistoryHingeMeasure
local notation "fH" => liEvenCrossActualClockHistoryCappedHinge
local notation "RH" => liEvenCrossActualClockHistoryResidual

private theorem hgt_history_assembly_smooth : ContDiff ℝ (2 : ℕ∞) K :=
  hgt_history_source_contDiff_K.of_le (by exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
private theorem hgt_history_assembly_curv {t : ℝ} :
    ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv K) x := by
  intro x hx
  exact hgt_history_source_K2_nonneg hx.1
private theorem hgt_history_assembly_mass (t : ℝ) : hgt_history_hinge_mass K t = A t := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) («b» := t) (fun x _ => hgt_history_source_hasDerivAt_B x)
    (hgt_history_source_contDiff_K.continuous.intervalIntegrable 0 t)
  simpa [hgt_history_hinge_mass, liEvenCrossActualClockHistoryExcess] using hi
private theorem hgt_history_assembly_hinge (t : ℝ) : hgt_history_hinge_measure K t = kap t := by
  unfold hgt_history_hinge_measure liEvenCrossActualClockHistoryHingeMeasure
  rw [hgt_history_source_origin.2.1]
  rfl
private theorem hgt_history_assembly_bpos : 0 < K1 0 := by
  rw [hgt_history_source_origin.2.1]
  exact hgt_history_source_origin.2.2.2
private theorem hgt_history_assembly_age (t : ℝ) : hgt_history_hinge_age K t = Q t := by
  simp only [hgt_history_hinge_age, liEvenCrossActualClockHistoryAgeMeasure, hgt_history_assembly_mass]

theorem liEvenCrossActualClockHistory_origin :
    K 0 = 0 ∧ K1 0 = b ∧ b = normalizedPrimeArchMoment 0 / 2 ∧ 0 < b :=
  hgt_history_source_origin
theorem liEvenCrossActualClockHistory_geometry {t : ℝ} (ht : 0 < t) :
    0 < A t ∧ 0 < K1 t ∧ 0 < e t ∧ e t < t/4 := by
  have h := hgt_history_source_geometry ht
  exact ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
theorem liEvenCrossActualClockHistoryHinge_admission {t : ℝ} (ht : 0 < t) :
    IsFiniteMeasure (kap t) ∧ (∀ᵐ r ∂kap t, r ∈ Icc 0 t) ∧
      (∀ f : ℝ → ℝ, Continuous f → Integrable f (kap t)) := by
  have h := hgt_history_hinge_admissions hgt_history_assembly_smooth
    hgt_history_assembly_bpos.le ht.le hgt_history_assembly_curv
  rw [hgt_history_assembly_hinge] at h
  exact ⟨h.1, h.2.1, fun f hf => (h.2.2 f hf).1⟩
theorem liEvenCrossActualClockHistoryHinge_moments {t : ℝ} (ht : 0 < t) :
    Integrable (fun r => t-r) (kap t) ∧ Integrable (fun r => (t-r)^2/2) (kap t) ∧
    (kap t).real univ = K1 t ∧ (∫ r, t-r ∂kap t) = K t ∧
      (∫ r, (t-r)^2/2 ∂kap t) = A t := by
  have h := hgt_history_hinge_moments hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos.le
    ht.le hgt_history_assembly_curv
  rw [hgt_history_assembly_hinge, hgt_history_assembly_mass] at h
  have ha := liEvenCrossActualClockHistoryHinge_admission ht
  exact ⟨ha.2.2 _ (by fun_prop), ha.2.2 _ (by fun_prop), h⟩
theorem liEvenCrossActualClockHistoryAge_admission {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (Q t) ∧ (∀ᵐ s ∂Q t, s ∈ Icc 0 t) ∧
      (∀ n : ℕ, Integrable (fun s : ℝ => s^n) (Q t)) := by
  have hp := hgt_history_hinge_age_probability hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hgt_history_assembly_curv
  have ha := hgt_history_hinge_age_admissions hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hgt_history_assembly_curv
  rw [hgt_history_assembly_age] at hp ha
  exact ⟨hp.1, ha.2.1, fun n => (ha.2.2 _ (by fun_prop)).1⟩

/-- `∫ f dQ_t = (∫_0^t K(t-s) f(s) ds)/A(t)` for every continuous test `f`. -/
theorem liEvenCrossActualClockHistoryAge_integral {t : ℝ} (ht : 0 < t)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (Q t) ∧ (∫ s, f s ∂Q t) = (∫ s in 0..t, K (t-s)*f s) / A t := by
  have h := hgt_history_hinge_age_admissions hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hgt_history_assembly_curv
  rw [hgt_history_assembly_age, hgt_history_assembly_mass] at h
  exact h.2.2 f hf
theorem liEvenCrossActualClockHistoryAge_moment {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ s, s^n ∂Q t) = (n.factorial : ℝ) / A t *
      (∑' j : ℕ, nu (j+1) * t^(2*(j+1)+n) /
        (((2*(j+1)).factorial : ℝ) * ((2*(j+1)+n).factorial : ℝ))) := by
  rw [(liEvenCrossActualClockHistoryAge_integral ht _ (by fun_prop)).2, hgt_history_age_integral_eq n ht.le]
  ring
/-- `Q_t[0,h] = (A(t) - A(t - min h t))/A(t)` for `h ≥ 0`. -/
theorem liEvenCrossActualClockHistoryAge_Icc_zero {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    (Q t).real (Icc 0 h) = (A t - A (t-min h t)) / A t := by
  have hcut := hgt_history_hinge_age_cutoff hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hh hgt_history_assembly_curv
  rw [hgt_history_assembly_age, hgt_history_assembly_mass,
    intervalIntegral.integral_comp_sub_left, sub_zero] at hcut
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := t-min h t) («b» := t) (fun x _ => hgt_history_source_hasDerivAt_B x)
    (hgt_history_source_contDiff_K.continuous.intervalIntegrable _ _)
  rw [hi] at hcut
  simpa [liEvenCrossActualClockHistoryExcess] using hcut
theorem liEvenCrossActualClockHistoryAge_recent_eq {t : ℝ} (ht : 0 < t) :
    (Q t).real (Icc 0 (e t)) = (A t - A (t-e t)) / A t := by
  have hg := liEvenCrossActualClockHistory_geometry ht
  have he : e t ≤ t := by linarith [hg.2.2.2]
  simpa only [min_eq_left he] using liEvenCrossActualClockHistoryAge_Icc_zero ht hg.2.2.1.le

private theorem hgt_history_assembly_cap {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Integrable (fun r => fH h (t-r)) (kap t) ∧
      A t * (Q t).real (Icc 0 h) = ∫ r, fH h (t-r) ∂kap t := by
  have h := hgt_history_hinge_cap_identity hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hh hgt_history_assembly_curv
  rw [hgt_history_assembly_hinge, hgt_history_assembly_age, hgt_history_assembly_mass] at h
  exact ⟨h.1, h.2.symm⟩
theorem liEvenCrossActualClockHistoryHinge_recent {t : ℝ} (ht : 0 < t) :
    Integrable (fun r => fH (e t) (t-r)) (kap t) ∧
      A t * (Q t).real (Icc 0 (e t)) = ∫ r, fH (e t) (t-r) ∂kap t :=
  hgt_history_assembly_cap ht (liEvenCrossActualClockHistory_geometry ht).2.2.1.le

local notation "m" => (fun t : ℝ => K t / K1 t)
private def hgt_history_assembly_fraction (alpha t : ℝ) : ℝ := (Q t).real (Icc 0 (alpha*m t))
private theorem hgt_history_assembly_mean {t : ℝ} (ht : 0 < t) :
    (∫ r, t-r ∂kap t) = m t * (kap t).real univ := by
  have h := liEvenCrossActualClockHistoryHinge_moments ht
  rw [h.2.2.1, h.2.2.2.1, div_mul_cancel₀ _ (liEvenCrossActualClockHistory_geometry ht).2.1.ne']
private theorem hgt_history_assembly_m_geometry {t : ℝ} (ht : 0 < t) :
    0 < m t ∧ m t < t ∧ m t = 4*e t := by
  have h := hgt_history_source_geometry ht
  exact ⟨h.2.2.1, h.2.2.2.1, by unfold liEvenCrossActualClockHistoryScale; ring⟩
private theorem hgt_history_assembly_slope_residual {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    Integrable (fun r => hgt_history_scalar_residual (m t) alpha (t-r)) (kap t) ∧
    A t * (2*alpha-alpha^2 - hgt_history_assembly_fraction alpha t) =
      ∫ r, hgt_history_scalar_residual (m t) alpha (t-r) ∂kap t := by
  have hg := hgt_history_assembly_m_geometry ht
  have hcap : alpha*m t ≤ t := (mul_le_of_le_one_left hg.1.le ha1).trans hg.2.1.le
  have hi := (liEvenCrossActualClockHistoryHinge_admission ht).2.2 _
    (hgt_history_rigidity_residual_continuous (m t) alpha t)
  have hr := hgt_history_rigidity_residual_integral hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht hgt_history_assembly_curv rfl ha ha1
  rw [hgt_history_assembly_hinge, hgt_history_assembly_mass] at hr
  have hf := hgt_history_hinge_age_cutoff hgt_history_assembly_smooth
    liEvenCrossActualClockHistory_origin.1 hgt_history_assembly_bpos
    ht (mul_pos ha hg.1).le hgt_history_assembly_curv
  rw [hgt_history_assembly_age, hgt_history_assembly_mass, min_eq_left hcap] at hf
  refine ⟨hi, ?_⟩
  unfold hgt_history_assembly_fraction
  rw [hf, hr]
  field_simp [(liEvenCrossActualClockHistory_geometry ht).1.ne']
private theorem hgt_history_assembly_slope_eq {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    hgt_history_assembly_fraction alpha t = 2*alpha-alpha^2 ↔
      (∀ᵐ r ∂kap t, t-r = m t) := by
  haveI := (liEvenCrossActualClockHistoryHinge_admission ht).1
  have hi := liEvenCrossActualClockHistoryHinge_moments ht
  have hs := hgt_history_assembly_slope_residual ht ha ha1
  have hn : ∀ᵐ r ∂kap t, 0 ≤ t-r := by
    filter_upwards [(liEvenCrossActualClockHistoryHinge_admission ht).2.1] with r hr
    exact sub_nonneg.mpr hr.2
  have he := hgt_history_zero_residual_iff (hgt_history_assembly_m_geometry ht).1
    ha ha1 hi.1 hn hs.1 (hgt_history_assembly_mean ht)
  rw [← hs.2] at he
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  constructor
  · intro h; apply he.mp; rw [h]; ring
  · intro h
    have hz := he.mpr h
    have hc : 2*alpha-alpha^2 - hgt_history_assembly_fraction alpha t = 0 :=
      (mul_eq_zero.mp hz).resolve_left hA.ne'
    linarith
private theorem hgt_history_assembly_outside {t h : ℝ}
    (ht : 0 < t) (hh : 0 ≤ h) (hht : h ≤ t) :
    (Q t).real (Ioc h t) = 1 - (Q t).real (Icc 0 h) := by
  haveI := (liEvenCrossActualClockHistoryAge_admission ht).1
  have hf : (Q t).real (Icc 0 t) = 1 := by
    have he : Icc 0 t =ᵐ[Q t] (univ : Set ℝ) := by
      filter_upwards [(liEvenCrossActualClockHistoryAge_admission ht).2.1] with s hs
      exact propext ⟨fun _ => Set.mem_univ s, fun _ => hs⟩
    rw [measureReal_congr he, probReal_univ]
  have hd : Disjoint (Icc 0 h) (Ioc h t) := by
    apply Set.disjoint_left.mpr
    intro s hs hr
    exact not_lt_of_ge hs.2 hr.1
  have he : Icc 0 h ∪ Ioc h t = Icc 0 t := by
    ext s
    constructor
    · rintro (hs | hs)
      · exact ⟨hs.1, hs.2.trans hht⟩
      · exact ⟨hh.trans hs.1.le, hs.2⟩
    · intro hs
      by_cases hsh : s ≤ h
      · exact Or.inl ⟨hs.1, hsh⟩
      · exact Or.inr ⟨lt_of_not_ge hsh, hs.2⟩
  rw [← he, measureReal_union hd measurableSet_Ioc] at hf
  linarith
private theorem hgt_history_assembly_slope_reserve {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    let d := b*(2*alpha-alpha^2)*(t-m t)^2/(2*A t)
    hgt_history_assembly_fraction alpha t ≤ 2*alpha-alpha^2-d ∧ 0 < d ∧
    hgt_history_assembly_fraction alpha t < 2*alpha-alpha^2 ∧
    1-(2*alpha-alpha^2)+d ≤ (Q t).real (Ioc (alpha*m t) t) ∧
    1-(2*alpha-alpha^2) < (Q t).real (Ioc (alpha*m t) t) := by
  dsimp only
  have hg := hgt_history_assembly_m_geometry ht
  have hA := (liEvenCrossActualClockHistory_geometry ht).1
  have hb := liEvenCrossActualClockHistory_origin.2.2.2
  have hc := hgt_history_scalar_ceiling_pos ha ha1
  have hgap : 0 < t-m t := sub_pos.mpr hg.2.1
  have hcap : alpha*m t ≤ t := (mul_le_of_le_one_left hg.1.le ha1).trans hg.2.1.le
  have hr := hgt_history_rigidity_origin_reserve hgt_history_assembly_smooth hgt_history_assembly_bpos.le ht.le
    hgt_history_assembly_curv hg.1 ha ha1
  rw [hgt_history_assembly_hinge, hgt_history_source_origin.2.1, hgt_history_scalar_upper hcap] at hr
  have hs := (hgt_history_assembly_slope_residual ht ha ha1).2
  rw [← hs] at hr
  change b*((2*alpha-alpha^2)*(t-m t)^2/2) ≤
    A t*(2*alpha-alpha^2-hgt_history_assembly_fraction alpha t) at hr
  let d := b*(2*alpha-alpha^2)*(t-m t)^2/(2*A t)
  have hd : 0 < d := by dsimp [d]; positivity
  have he : A t*d = b*(2*alpha-alpha^2)*(t-m t)^2/2 := by
    dsimp [d]; field_simp
  have hu : hgt_history_assembly_fraction alpha t ≤ 2*alpha-alpha^2-d := by
    by_contra hnot
    have hgap' : 0 < hgt_history_assembly_fraction alpha t - (2*alpha-alpha^2-d) := by linarith
    have hprod := mul_pos hA hgap'
    nlinarith [hr, he, hprod]
  have hstrict : hgt_history_assembly_fraction alpha t < 2*alpha-alpha^2 := by linarith
  have ho := hgt_history_assembly_outside ht (mul_pos ha hg.1).le hcap
  change hgt_history_assembly_fraction alpha t ≤ 2*alpha-alpha^2-d ∧ _
  refine ⟨hu, hd, hstrict, ?_, ?_⟩
  · rw [ho]; change 1-(2*alpha-alpha^2)+d ≤ 1-hgt_history_assembly_fraction alpha t; linarith
  · rw [ho]; change 1-(2*alpha-alpha^2) < 1-hgt_history_assembly_fraction alpha t; linarith
private theorem hgt_history_assembly_quarter_fraction (t : ℝ) :
    hgt_history_assembly_fraction (1/4) t = (Q t).real (Icc 0 (e t)) := by
  have he : (1/4:ℝ)*m t = e t := by unfold liEvenCrossActualClockHistoryScale; ring
  simp only [hgt_history_assembly_fraction, he]
private theorem hgt_history_assembly_quarter_residual (t w : ℝ) :
    hgt_history_scalar_residual (m t) (1/4) w = RH (e t) w := by
  have he : (1/4:ℝ)*m t = e t := by unfold liEvenCrossActualClockHistoryScale; ring
  unfold hgt_history_scalar_residual liEvenCrossActualClockHistoryResidual
    liEvenCrossActualClockHistoryCappedHinge hgt_history_scalar_cap
  rw [he]
  unfold liEvenCrossActualClockHistoryScale
  ring
private theorem hgt_history_assembly_quarter_deficit (t : ℝ) :
    b*(2*(1/4:ℝ)-(1/4:ℝ)^2)*(t-m t)^2/(2*A t) =
      7*b*(t-4*e t)^2/(32*A t) := by
  unfold liEvenCrossActualClockHistoryScale
  ring
private theorem hgt_history_assembly_origin_A :
    Tendsto (fun t : ℝ => A t/t^2) (𝓝[Ioi 0] 0) (𝓝 (b/2)) := by
  apply hgt_history_origin_excess hgt_history_source_excess_zero hgt_history_source_origin.1
    (contDiff_liEvenCrossActualClockBorelKernel.continuous.sub continuous_const)
    (fun t => (hgt_history_source_hasDerivAt_B t).sub_const 1)
  simpa only [hgt_history_source_origin.2.1, liEvenCrossActualClockHistoryOriginSlope] using
    hgt_history_source_hasDerivAt_K 0
private theorem hgt_history_assembly_origin_scale :
    Tendsto (fun t : ℝ => m t/t) (𝓝[Ioi 0] 0) (𝓝 1) ∧
      Tendsto (fun t : ℝ => e t/t) (𝓝[Ioi 0] 0) (𝓝 (1/4 : ℝ)) := by
  apply hgt_history_origin_scale hgt_history_source_origin.2.2.2 hgt_history_source_origin.1
    (by simpa only [hgt_history_source_origin.2.1] using hgt_history_source_hasDerivAt_K 0)
    hgt_history_source_contDiff_K1.continuous.continuousAt hgt_history_source_origin.2.1
private theorem hgt_history_assembly_origin_fraction {alpha : ℝ} (ha : 0 ≤ alpha) :
    Tendsto (fun t : ℝ => hgt_history_assembly_fraction alpha t) (𝓝[Ioi 0] 0)
      (𝓝 (if alpha ≤ 1 then 2*alpha-alpha^2 else 1)) := by
  have hv := hgt_history_origin_fraction hgt_history_source_excess_zero
    (ne_of_gt (show 0 < b/2 from div_pos liEvenCrossActualClockHistory_origin.2.2.2 (by norm_num)))
    (fun t ht => (liEvenCrossActualClockHistory_geometry ht).1)
    hgt_history_assembly_origin_A hgt_history_assembly_origin_scale.1 alpha
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  exact (liEvenCrossActualClockHistoryAge_Icc_zero ht (mul_nonneg ha (hgt_history_assembly_m_geometry ht).1.le)).symm

theorem liEvenCrossActualClockHistoryResidual_nonneg {h w : ℝ}
    (hh : 0 < h) (hw : 0 ≤ w) : 0 ≤ RH h w ∧ (RH h w = 0 ↔ w = 4*h) :=
  hgt_history_scalar_quarter_nonneg hh hw
theorem liEvenCrossActualClockHistory_residual {t : ℝ} (ht : 0 < t) :
    Integrable (fun r => RH (e t) (t-r)) (kap t) ∧
      A t * (7/16 - (Q t).real (Icc 0 (e t))) = ∫ r, RH (e t) (t-r) ∂kap t := by
  simpa only [hgt_history_assembly_quarter_residual, hgt_history_assembly_quarter_fraction,
    show 2*(1/4:ℝ)-(1/4:ℝ)^2=7/16 by norm_num] using
    hgt_history_assembly_slope_residual ht (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)
theorem liEvenCrossActualClockHistory_recent_eq_iff {t : ℝ} (ht : 0 < t) :
    (Q t).real (Icc 0 (e t)) = 7/16 ↔ (∀ᵐ r ∂kap t, t-r = 4*e t) := by
  simpa only [hgt_history_assembly_quarter_fraction,
    show m t=4*e t from (hgt_history_assembly_m_geometry ht).2.2,
    show 2*(1/4:ℝ)-(1/4:ℝ)^2=7/16 by norm_num] using
    hgt_history_assembly_slope_eq ht (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)
theorem liEvenCrossActualClockHistory_class_rigidity (k : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0 = 0)
    (hb : 0 < deriv k 0) (hcurv : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x) :
    let h := k t / (4 * deriv k t)
    let mass := ∫ x in 0..t, k x
    ((∫ s in 0..h, k (t-s)) / mass = 7/16 ↔ ∀ x ∈ Icc 0 t, k x = deriv k 0*x) :=
  hgt_history_rigidity_quarter k ht hk hk0 hb hcurv
theorem liEvenCrossActualClockHistory_recent_atom_deficit {t : ℝ} (ht : 0 < t) :
    (Q t).real (Icc 0 (e t)) ≤ 7/16 - 7*b*(t-4*e t)^2/(32*A t) := by
  have h := (hgt_history_assembly_slope_reserve ht (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)).1
  rw [hgt_history_assembly_quarter_deficit, hgt_history_assembly_quarter_fraction] at h
  norm_num at h
  exact h
theorem liEvenCrossActualClockHistory_recent_lt {t : ℝ} (ht : 0 < t) :
    (Q t).real (Icc 0 (e t)) < 7/16 := by
  simpa only [hgt_history_assembly_quarter_fraction,
    show 2*(1/4:ℝ)-(1/4:ℝ)^2=7/16 by norm_num] using
    (hgt_history_assembly_slope_reserve ht (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)).2.2.1
theorem liEvenCrossActualClockHistory_outside_atom_reserve {t : ℝ} (ht : 0 < t) :
    9/16 + 7*b*(t-4*e t)^2/(32*A t) ≤ (Q t).real (Ioc (e t) t) := by
  have h := (hgt_history_assembly_slope_reserve ht (alpha := (1/4:ℝ)) (by norm_num) (by norm_num)).2.2.2.1
  have he : (1/4:ℝ)*m t=e t := by unfold liEvenCrossActualClockHistoryScale; ring
  simpa only [he, hgt_history_assembly_quarter_deficit,
    show 1-(2*(1/4:ℝ)-(1/4:ℝ)^2)=9/16 by norm_num] using h
theorem tendsto_liEvenCrossActualClockHistoryExcess_div_sq :
    Tendsto (fun t : ℝ => A t/t^2) (𝓝[Ioi 0] 0) (𝓝 (b/2)) := hgt_history_assembly_origin_A
theorem tendsto_liEvenCrossActualClockHistoryScale_div :
    Tendsto (fun t : ℝ => e t/t) (𝓝[Ioi 0] 0) (𝓝 (1/4 : ℝ)) := hgt_history_assembly_origin_scale.2
theorem tendsto_liEvenCrossActualClockHistory_recent :
    Tendsto (fun t : ℝ => (Q t).real (Icc 0 (e t))) (𝓝[Ioi 0] 0) (𝓝 (7/16 : ℝ)) := by
  simpa only [hgt_history_assembly_quarter_fraction, if_pos (by norm_num : (1/4:ℝ) ≤ 1),
    show 2*(1/4:ℝ)-(1/4:ℝ)^2=7/16 by norm_num] using
    hgt_history_assembly_origin_fraction (alpha := (1/4:ℝ)) (by norm_num)
theorem liEvenCrossActualClockHistory_recent_ceiling_iff (gamma : ℝ) :
    (∀ t : ℝ, 0 < t → (Q t).real (Icc 0 (e t)) ≤ gamma) ↔ 7/16 ≤ gamma := by
  exact hgt_history_origin_ceiling tendsto_liEvenCrossActualClockHistory_recent
    (fun t ht => (liEvenCrossActualClockHistory_recent_lt ht).le) gamma
theorem liEvenCrossActualClockHistory_source_curvature :
    (∀ t : ℝ, 0 ≤ t → b ≤ K1 t ∧ 0 ≤ K2 t) ∧ MonotoneOn K1 (Ici 0) := hgt_history_source_curvature

def liEvenCrossActualClockHistorySlopeLength (t : ℝ) : ℝ := K t / K1 t
def liEvenCrossActualClockHistorySlopeFraction (alpha t : ℝ) : ℝ :=
  (Q t).real (Icc 0 (alpha*liEvenCrossActualClockHistorySlopeLength t))
def liEvenCrossActualClockHistorySlopeCeiling (alpha : ℝ) : ℝ :=
  if alpha ≤ 1 then 2*alpha-alpha^2 else 1
def liEvenCrossActualClockHistorySlopeResidual (mLen alpha w : ℝ) : ℝ :=
  (2*alpha-alpha^2)*w^2/2 - fH (alpha*mLen) w - alpha*mLen*(1-alpha)*(w-mLen)
local notation "U" => liEvenCrossActualClockHistorySlopeFraction
local notation "C" => liEvenCrossActualClockHistorySlopeCeiling
local notation "RS" => liEvenCrossActualClockHistorySlopeResidual

theorem liEvenCrossActualClockHistoryHinge_capped {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Integrable (fun r => fH h (t-r)) (kap t) ∧ A t*(Q t).real (Icc 0 h) = ∫ r, fH h (t-r) ∂kap t :=
  hgt_history_assembly_cap ht hh
theorem liEvenCrossActualClockHistorySlopeResidual_nonneg {mLen alpha w : ℝ}
    (hm : 0 < mLen) (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hw : 0 ≤ w) :
    0 ≤ RS mLen alpha w ∧ (RS mLen alpha w = 0 ↔ if alpha < 1 then w=mLen else w ≤ mLen) :=
  hgt_history_scalar_nonneg hm ha ha1 hw
theorem liEvenCrossActualClockHistory_slope_residual {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    Integrable (fun r => RS (liEvenCrossActualClockHistorySlopeLength t) alpha (t-r)) (kap t) ∧
      A t*(C alpha-U alpha t) = ∫ r, RS (liEvenCrossActualClockHistorySlopeLength t) alpha (t-r) ∂kap t := by
  simpa only [liEvenCrossActualClockHistorySlopeCeiling, if_pos ha1,
    liEvenCrossActualClockHistorySlopeFraction, liEvenCrossActualClockHistorySlopeLength,
    liEvenCrossActualClockHistorySlopeResidual, liEvenCrossActualClockHistoryCappedHinge,
    hgt_history_assembly_fraction, hgt_history_scalar_residual, hgt_history_scalar_cap] using
    hgt_history_assembly_slope_residual ht ha ha1
theorem liEvenCrossActualClockHistory_slope_eq_iff {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    U alpha t=C alpha ↔ (∀ᵐ r ∂kap t, t-r=liEvenCrossActualClockHistorySlopeLength t) := by
  simpa only [liEvenCrossActualClockHistorySlopeCeiling, if_pos ha1,
    liEvenCrossActualClockHistorySlopeFraction, liEvenCrossActualClockHistorySlopeLength,
    hgt_history_assembly_fraction] using
    hgt_history_assembly_slope_eq ht ha ha1
theorem liEvenCrossActualClockHistory_slope_class_rigidity (k : ℝ → ℝ) {alpha t : ℝ}
    (ht : 0 < t) (hk : ContDiff ℝ (2 : ℕ∞) k) (hk0 : k 0=0)
    (hb : 0 < deriv k 0) (hcurv : ∀ x ∈ Icc 0 t, 0 ≤ deriv (deriv k) x)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    let h := alpha*(k t/deriv k t)
    let mass := ∫ x in 0..t, k x
    ((∫ s in 0..h, k (t-s))/mass=2*alpha-alpha^2 ↔ ∀ x ∈ Icc 0 t, k x=deriv k 0*x) :=
  hgt_history_rigidity_slope k ht hk hk0 hb hcurv ha ha1
theorem liEvenCrossActualClockHistory_slope_atom_reserve {alpha t : ℝ}
    (ht : 0 < t) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    let d := b*C alpha*(t-liEvenCrossActualClockHistorySlopeLength t)^2/(2*A t)
    U alpha t ≤ C alpha-d ∧ 0 < d ∧ U alpha t<C alpha ∧
      1-C alpha+d ≤ (Q t).real (Ioc (alpha*liEvenCrossActualClockHistorySlopeLength t) t) ∧
      1-C alpha < (Q t).real (Ioc (alpha*liEvenCrossActualClockHistorySlopeLength t) t) := by
  simpa only [liEvenCrossActualClockHistorySlopeCeiling, if_pos ha1,
    liEvenCrossActualClockHistorySlopeFraction, liEvenCrossActualClockHistorySlopeLength,
    hgt_history_assembly_fraction] using
    hgt_history_assembly_slope_reserve ht ha ha1
private theorem hgt_history_assembly_whole_cap {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) (hht : t ≤ h) :
    (Q t).real (Icc 0 h)=1 := by
  rw [liEvenCrossActualClockHistoryAge_Icc_zero ht hh, min_eq_right hht]
  have hz : A 0 = 0 := hgt_history_source_excess_zero
  rw [sub_self, hz, sub_zero,
    div_self (liEvenCrossActualClockHistory_geometry ht).1.ne']
theorem liEvenCrossActualClockHistory_slope_endpoints {t : ℝ} (ht : 0 < t) :
    U 0 t=0 ∧ (∀ alpha : ℝ, 0 ≤ alpha → t ≤ alpha*liEvenCrossActualClockHistorySlopeLength t → U alpha t=1) := by
  constructor
  · change (Q t).real (Icc 0 (0*m t))=0
    rw [zero_mul, liEvenCrossActualClockHistoryAge_Icc_zero ht le_rfl]
    simp only [min_eq_left ht.le, sub_zero, sub_self, zero_div]
  · intro alpha ha hc
    exact hgt_history_assembly_whole_cap ht
      (mul_nonneg ha (hgt_history_assembly_m_geometry ht).1.le) hc
theorem tendsto_liEvenCrossActualClockHistory_slope_fraction {alpha : ℝ} (ha : 0 ≤ alpha) :
    Tendsto (fun t : ℝ => U alpha t) (𝓝[Ioi 0] 0) (𝓝 (C alpha)) :=
  hgt_history_assembly_origin_fraction ha
private theorem hgt_history_assembly_slope_bound {alpha t : ℝ} (ht : 0 < t) (ha : 0 ≤ alpha) :
    U alpha t ≤ C alpha := by
  by_cases hz : alpha=0
  · rw [hz, (liEvenCrossActualClockHistory_slope_endpoints ht).1]
    norm_num [liEvenCrossActualClockHistorySlopeCeiling]
  · have hpos : 0 < alpha := lt_of_le_of_ne ha (Ne.symm hz)
    by_cases ha1 : alpha ≤ 1
    · exact (liEvenCrossActualClockHistory_slope_atom_reserve ht hpos ha1).2.2.1.le
    · haveI := (liEvenCrossActualClockHistoryAge_admission ht).1
      rw [liEvenCrossActualClockHistorySlopeCeiling, if_neg ha1]
      exact (measureReal_mono (subset_univ _) : (Q t).real _ ≤ (Q t).real univ).trans_eq probReal_univ
theorem liEvenCrossActualClockHistory_slope_ceiling_iff {alpha : ℝ}
    (ha : 0 ≤ alpha) (gamma : ℝ) :
    (∀ t : ℝ, 0 < t → U alpha t ≤ gamma) ↔ C alpha ≤ gamma :=
  hgt_history_origin_ceiling (tendsto_liEvenCrossActualClockHistory_slope_fraction ha)
    (fun _t ht => hgt_history_assembly_slope_bound ht ha) gamma
theorem liEvenCrossActualClockHistory_slope_eventually_one {alpha : ℝ} (ha : 1 < alpha) :
    ∀ᶠ t : ℝ in 𝓝[Ioi 0] 0, U alpha t=1 := by
  exact hgt_history_origin_eventually_one ha hgt_history_assembly_origin_scale.1
    (fun t ht hc => (liEvenCrossActualClockHistory_slope_endpoints ht).2 alpha (by linarith) hc)

end
end RHTower
