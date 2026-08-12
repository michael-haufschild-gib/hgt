import GaloisForLFunctions.RHTower.SuzukiCanonicalArithmeticMellin
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Local `L²` regularity of Suzuki's canonical source kernel

Suzuki (2012), Lemma 4.2 uses the sharp local estimate
`h_ω(x) ≪ |x - n|^(ω - 1)` at the finitely many singular points `n`.  This file proves the
analytic input at the level of Suzuki's literal beta kernel.  The threshold is exact:
after squaring, the endpoint exponent is `2 * (ω - 1)`, integrable precisely when `ω > 1 / 2`.

The incomplete-beta term is handled from its printed integral, not replaced by a bounded proxy.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

/-- Translation of the sharp endpoint criterion `p > -1` to an interval ending at `1`. -/
theorem integrableOn_one_sub_rpow_Ioc {delta p : ℝ}
    (hdelta : delta < 1) (hp : -1 < p) :
    IntegrableOn (fun x : ℝ => (1 - x) ^ p) (Ioc delta 1) := by
  have hr : IntervalIntegrable (fun u : ℝ => u ^ p) volume 0 (1 - delta) :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hc := (hr.comp_sub_left 1).symm
  have hc' : IntervalIntegrable (fun x : ℝ => (1 - x) ^ p) volume delta 1 := by
    convert hc using 1 <;> ring
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hdelta.le).mp hc'

/-- The literal incomplete-beta integrand is integrable on every interval separated from zero. -/
theorem integrableOn_suzukiBetaIntegrand_Ioc
    {omega delta : ℝ} (homega : 0 < omega) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
        (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)) (Ioc (delta ^ 2) 1) := by
  have hpow : IntervalIntegrable
      (fun u : ℝ => (u : ℂ) ^ ((omega : ℂ) - 1)) volume 0 (1 - delta ^ 2) :=
    intervalIntegral.intervalIntegrable_cpow' (by norm_num; linarith)
  have hsing' := (hpow.comp_sub_left 1).symm
  have hsingI : IntervalIntegrable
      (fun t : ℝ => (1 - (t : ℂ)) ^ ((omega : ℂ) - 1))
      volume (delta ^ 2) 1 := by
    convert hsing' using 1 <;> push_cast <;> ring
  have hdeltasq : delta ^ 2 ≤ 1 := by nlinarith
  have hsing : IntegrableOn
      (fun t : ℝ => (1 - (t : ℂ)) ^ ((omega : ℂ) - 1))
      (Ioc (delta ^ 2) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hdeltasq).mp hsingI
  have hcont : ContinuousOn
      (fun t : ℝ => (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ))
      (Icc (delta ^ 2) 1) := by
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    refine (continuousAt_cpow_const ?_).comp Complex.continuous_ofReal.continuousAt
    exact Complex.ofReal_mem_slitPlane.2
      (by nlinarith [sq_pos_of_pos hdelta, ht.1])
  exact hsing.continuousOn_mul_of_subset hcont isCompact_Icc
    measurableSet_Ioc Ioc_subset_Icc_self

/-- Suzuki's literal incomplete-beta tail is measurable as a parameterized set integral. -/
theorem measurable_suzukiBetaTail (omega : ℝ) :
    Measurable (suzukiBetaTail omega) := by
  let F : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
      (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  rw [show suzukiBetaTail omega = fun x : ℝ =>
      ∫ t, if x ^ 2 < t ∧ t ≤ 1 then F t else 0 by
    funext x
    rw [suzukiBetaTail, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with t
    simp only [indicator, mem_Ioc, F]]
  have hjoint : Measurable fun p : ℝ × ℝ =>
      if p.1 ^ 2 < p.2 ∧ p.2 ≤ 1 then F p.2 else 0 := by
    apply Measurable.ite
    · have hsq : Measurable fun p : ℝ × ℝ => p.1 ^ 2 := by fun_prop
      have hsnd : Measurable fun p : ℝ × ℝ => p.2 := measurable_snd
      have hone : Measurable fun _p : ℝ × ℝ => (1 : ℝ) := measurable_const
      exact (measurableSet_lt hsq hsnd).inter (measurableSet_le hsnd hone)
    · exact hF.comp measurable_snd
    · fun_prop
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The literal incomplete-beta tail is uniformly bounded on every compact subinterval separated
from zero.  The bound is the norm integral of the source integrand on the fixed containing
interval. -/
theorem exists_bound_norm_suzukiBetaTail
    {omega delta : ℝ} (homega : 0 < omega) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ C : ℝ, ∀ x ∈ Icc delta 1, ‖suzukiBetaTail omega x‖ ≤ C := by
  let F : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((1 / 2 - omega : ℝ) : ℂ) *
      (1 - (t : ℂ)) ^ ((omega : ℂ) - 1)
  have hFint : IntegrableOn F (Ioc (delta ^ 2) 1) := by
    dsimp only [F]
    exact integrableOn_suzukiBetaIntegrand_Ioc homega hdelta hdelta1
  refine ⟨∫ t in Ioc (delta ^ 2) 1, ‖F t‖, ?_⟩
  intro x hx
  have hsubset : Ioc (x ^ 2) 1 ⊆ Ioc (delta ^ 2) 1 := by
    intro t ht
    have hsqx : delta ^ 2 ≤ x ^ 2 := by nlinarith [hdelta, hx.1]
    exact ⟨lt_of_le_of_lt hsqx ht.1, ht.2⟩
  calc
    ‖suzukiBetaTail omega x‖ = ‖∫ t in Ioc (x ^ 2) 1, F t‖ := by rfl
    _ ≤ ∫ t in Ioc (x ^ 2) 1, ‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (delta ^ 2) 1, ‖F t‖ :=
      setIntegral_mono_set hFint.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall hsubset)

/-- Sharp square-integrability of the singular first term in Suzuki's printed `g_ω` formula. -/
theorem integrableOn_sq_norm_suzukiPrimarySourceTerm
    {omega delta : ℝ} (homega : 1 / 2 < omega)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    IntegrableOn (fun x : ℝ =>
      ‖(x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
        (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)‖ ^ 2)
      (Ioc delta 1) := by
  let p : ℝ := 2 * (omega - 1)
  let q : ℝ → ℝ := fun x => x ^ (2 * (2 - omega)) * (1 + x) ^ p
  have hp : -1 < p := by dsimp only [p]; linarith
  have hbase : IntegrableOn (fun x : ℝ => (1 - x) ^ p) (Ioc delta 1) :=
    integrableOn_one_sub_rpow_Ioc hdelta1 hp
  have hq : ContinuousOn q (Icc delta 1) := by
    refine ContinuousOn.mul (continuousOn_of_forall_continuousAt fun x hx => ?_)
      (continuousOn_of_forall_continuousAt fun x hx => ?_)
    · exact Real.continuousAt_rpow_const x (2 * (2 - omega))
        (Or.inl (ne_of_gt (lt_of_lt_of_le hdelta hx.1)))
    · exact (Real.continuousAt_rpow_const (1 + x) p
        (Or.inl (by nlinarith [hdelta, hx.1]))).comp
          (continuousAt_const.add continuousAt_id)
  have hmodel : IntegrableOn (fun x => (1 - x) ^ p * q x) (Ioc delta 1) :=
    hbase.mul_continuousOn_of_subset hq measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self
  have hmodel' : IntegrableOn (fun x => q x * (1 - x) ^ p) (Ioc delta 1) := by
    convert hmodel using 1
    funext x
    ring
  have htargetIoo : IntegrableOn (fun x : ℝ =>
      ‖(x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
        (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)‖ ^ 2)
      (Ioo delta 1) := (hmodel'.mono_set Ioo_subset_Ioc_self).congr_fun (by
    intro x hx
    have hx0 : 0 < x := lt_trans hdelta hx.1
    have hx1 : x < 1 := hx.2
    have hxsq : 0 < 1 - x ^ 2 := by nlinarith
    have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    have hco : 1 - (x : ℂ) ^ (2 : ℕ) = ((1 - x ^ 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    change q x * (1 - x) ^ p =
      ‖(x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
        (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)‖ ^ 2
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hco,
      Complex.norm_cpow_eq_rpow_re_of_pos hxsq]
    norm_num
    dsimp only [q, p]
    rw [hfac, Real.mul_rpow (by linarith) (by linarith)]
    rw [mul_pow, mul_pow]
    rw [show (x ^ (2 - omega)) ^ 2 = x ^ (2 * (2 - omega)) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      ring,
      show ((1 - x) ^ (omega - 1)) ^ 2 = (1 - x) ^ (2 * (omega - 1)) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring,
      show ((1 + x) ^ (omega - 1)) ^ 2 = (1 + x) ^ (2 * (omega - 1)) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring]
    ring) measurableSet_Ioo
  exact htargetIoo.congr_set_ae Ioo_ae_eq_Ioc.symm

/-- The incomplete-beta correction in Suzuki's printed kernel is locally `L²` away from zero. -/
theorem memLp_suzukiBetaCorrection_local_two
    {omega delta : ℝ} (homega : 1 / 2 < omega)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    MemLp (fun x : ℝ =>
      (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) * suzukiBetaTail omega x)
      2 (volume.restrict (Ioc delta 1)) := by
  obtain ⟨C, hC⟩ := exists_bound_norm_suzukiBetaTail
    (omega := omega) (delta := delta) (by linarith) hdelta hdelta1
  let a : ℝ → ℂ := fun x => (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ)
  have haCont : ContinuousOn a (Icc delta 1) := by
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    refine (continuousAt_cpow_const ?_).comp Complex.continuous_ofReal.continuousAt
    exact Complex.ofReal_mem_slitPlane.2 (lt_of_lt_of_le hdelta hx.1)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn haCont
  have hD0 : 0 ≤ D := le_trans (norm_nonneg (a delta))
    (hD delta ⟨le_rfl, hdelta1.le⟩)
  have haMeas : Measurable a := by
    dsimp only [a]
    fun_prop
  have hmeas : Measurable fun x : ℝ => a x * suzukiBetaTail omega x :=
    haMeas.mul (measurable_suzukiBetaTail omega)
  refine MemLp.of_bound hmeas.aestronglyMeasurable (D * C) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [norm_mul]
  exact mul_le_mul (hD x ⟨hx.1.le, hx.2⟩) (hC x ⟨hx.1.le, hx.2⟩)
    (norm_nonneg _) hD0

/-- Suzuki's source-faithful totalized `g_ω` is measurable. -/
theorem measurable_suzukiSourceG (omega : ℝ) : Measurable (suzukiSourceG omega) := by
  rw [show suzukiSourceG omega = fun x : ℝ =>
      if 0 < x ∧ x < 1 then
        (2 * (Real.pi : ℂ) ^ (omega : ℂ) / Complex.Gamma (omega : ℂ)) *
          ((x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
              (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1) -
            (omega : ℂ) * (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) *
              suzukiBetaTail omega x)
      else 0 by rfl]
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  · have hprimary : Measurable fun x : ℝ =>
        (x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
          (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1) := by
      fun_prop
    have hpow : Measurable fun x : ℝ =>
        (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) := by
      fun_prop
    exact measurable_const.mul (hprimary.sub
      ((measurable_const.mul hpow).mul (measurable_suzukiBetaTail omega)))
  · fun_prop

/-- **Sharp local `L²` theorem for Suzuki's literal `g_ω`.**  This discharges the analytic
kernel input in Suzuki (2012), Lemma 4.2 at the base-kernel level, with no regularity premise and
the source's exact threshold `ω > 1 / 2`. -/
theorem memLp_suzukiSourceG_local_two
    {omega delta : ℝ} (homega : 1 / 2 < omega)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    MemLp (suzukiSourceG omega) 2 (volume.restrict (Ioc delta 1)) := by
  let A : ℝ → ℂ := fun x =>
    (x : ℂ) ^ ((2 - omega : ℝ) : ℂ) *
      (1 - (x : ℂ) ^ (2 : ℕ)) ^ ((omega : ℂ) - 1)
  let B : ℝ → ℂ := fun x =>
    (x : ℂ) ^ ((omega - 1 : ℝ) : ℂ) * suzukiBetaTail omega x
  let c : ℂ := 2 * (Real.pi : ℂ) ^ (omega : ℂ) / Complex.Gamma (omega : ℂ)
  have hAmeas : Measurable A := by
    dsimp only [A]
    fun_prop
  have hA : MemLp A 2 (volume.restrict (Ioc delta 1)) :=
    (memLp_two_iff_integrable_sq_norm hAmeas.aestronglyMeasurable).mpr
      (integrableOn_sq_norm_suzukiPrimarySourceTerm homega hdelta hdelta1)
  have hB : MemLp B 2 (volume.restrict (Ioc delta 1)) := by
    dsimp only [B]
    exact memLp_suzukiBetaCorrection_local_two homega hdelta hdelta1
  have hraw : MemLp (fun x => c * (A x - (omega : ℂ) * B x)) 2
      (volume.restrict (Ioc delta 1)) :=
    (hA.sub (hB.const_mul (omega : ℂ))).const_mul c
  refine hraw.congr_norm (measurable_suzukiSourceG omega).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne 1)] with x hx hx1
  have hx0 : 0 < x := lt_trans hdelta hx.1
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
  congr 1
  rw [suzukiSourceG, if_pos ⟨hx0, hxlt⟩]
  dsimp only [A, B, c]
  ring

end RHTower
