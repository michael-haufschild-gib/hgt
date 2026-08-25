import GaloisForLFunctions.RHTower.CriticalActivationReesSourceLaw
import GaloisForLFunctions.RHTower.CCMAnalyticShiftSpectrumRigidity
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import Mathlib.Analysis.Analytic.Order

/-!
# Rees quasianalyticity of source augmentation

An analytic source section sampled along any positive scale approaching augmentation is flat
beyond every Rees grade exactly when its analytic germ is locally zero.  Thus a nonzero
all-orders-flat boundary sector cannot be an unseen finite Taylor coefficient: it is genuinely
nonperturbative in the augmentation coordinate.

The final theorem applies this boundary law to the actual reflected prime-Wold irregular Gamma
gauge.  At positive horizontal charge its `exp (-c/a)` norm is nonzero and all-orders flat in the
boundary volume `a`, so no holomorphic augmentation germ can have those norms as its cofinal
boundary samples.
-/

open Filter Asymptotics
open GaloisForLFunctions
open scoped Topology

noncomputable section

namespace RHTower

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Infinite analytic order forces norm extinction along every scale approaching augmentation. -/
theorem analyticNormAlongScale_eventually_eq_zero_of_order_eq_top
    {l : Filter α} {a : α → ℝ} (htend : Tendsto a l (nhds 0))
    {F : ℂ → E} (hFtop : analyticOrderAt F 0 = ⊤) :
    (fun x => ‖F (a x : ℂ)‖) =ᶠ[l] 0 := by
  have haC : Tendsto (fun x => (a x : ℂ)) l (nhds 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp htend
  have hzero : ∀ᶠ z : ℂ in 𝓝 0, F z = 0 := analyticOrderAt_eq_top.mp hFtop
  filter_upwards [haC.eventually hzero] with x hx
  simp only [hx, norm_zero, Pi.zero_apply]

/-- **Analytic augmentation is quasianalytic for every positive contracting Rees scale.**
An analytic source section sampled at a positive real scale approaching augmentation is flat
beyond every Rees grade exactly when its analytic germ is locally zero. -/
theorem reesAllOrdersFlat_analyticNormAlongScale_iff
    {l : Filter α} [l.NeBot] {a : α → ℝ}
    (hpos : ∀ᶠ x in l, 0 < a x) (htend : Tendsto a l (nhds 0))
    {F : ℂ → E} (hF : AnalyticAt ℂ F 0) :
    ReesAllOrdersFlat l a (fun x => ‖F (a x : ℂ)‖) ↔
      analyticOrderAt F 0 = ⊤ := by
  constructor
  · intro hflat
    by_contra hfinite
    have horder : (analyticOrderNatAt F 0 : ℕ∞) = analyticOrderAt F 0 :=
      ENat.coe_toNat hfinite
    obtain ⟨G, hGan, hG0, hfactor⟩ :=
      (hF.analyticOrderAt_eq_natCast).mp horder.symm
    have haC : Tendsto (fun x => (a x : ℂ)) l (nhds 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp htend
    have hGlim : Tendsto (fun x => ‖G (a x : ℂ)‖) l (nhds ‖G 0‖) :=
      hGan.continuousAt.norm.tendsto.comp haC
    have hfactorAlong :
        (fun x => ‖F (a x : ℂ)‖) =ᶠ[l]
          fun x => a x ^ analyticOrderNatAt F 0 * ‖G (a x : ℂ)‖ := by
      filter_upwards [haC.eventually hfactor, hpos] with x hx hax
      rw [hx, norm_smul, norm_pow]
      simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hax]
    have hG0norm : 0 < ‖G 0‖ := norm_pos_iff.mpr hG0
    have hbound := (hflat (analyticOrderNatAt F 0)).bound (half_pos hG0norm)
    have hlower : ∀ᶠ x in l, ‖G 0‖ / 2 < ‖G (a x : ℂ)‖ :=
      hGlim.eventually (eventually_gt_nhds (half_lt_self hG0norm))
    obtain ⟨x, ⟨⟨hb, hfac⟩, hlowerx⟩, hax⟩ :=
      (((hbound.and hfactorAlong).and hlower).and hpos).exists
    have hscale : 0 < a x ^ analyticOrderNatAt F 0 := pow_pos hax _
    have hfac' :
        ‖F (a x : ℂ)‖ = a x ^ analyticOrderNatAt F 0 * ‖G (a x : ℂ)‖ := hfac
    rw [hfac'] at hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hscale,
      abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_of_pos hscale] at hb
    have hstrict := mul_lt_mul_of_pos_left hlowerx hscale
    nlinarith
  · intro htop N
    exact (isLittleO_zero (fun x => a x ^ N) l).congr'
      (analyticNormAlongScale_eventually_eq_zero_of_order_eq_top htend htop).symm
      EventuallyEq.rfl

/-- Fixed exponential augmentation is the special source coordinate used by aperture shifts. -/
theorem reesAllOrdersFlat_normedAnalyticShiftMultiplier_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → E} (hF : AnalyticAt ℂ F 0) :
    ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-q * h))
        (normedAnalyticShiftMultiplier q F) ↔
      analyticOrderAt F 0 = ⊤ := by
  have hpos : ∀ᶠ h : ℝ in atTop, 0 < Real.exp (-q * h) :=
    Eventually.of_forall fun h => Real.exp_pos _
  have htend : Tendsto (fun h : ℝ => Real.exp (-q * h)) atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_id.const_mul_atTop_of_neg (by linarith : -q < 0)
  change ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-q * h))
      (fun h => ‖F (Real.exp (-q * h) : ℂ)‖) ↔ analyticOrderAt F 0 = ⊤
  exact reesAllOrdersFlat_analyticNormAlongScale_iff hpos htend hF

/-- Scalar form of analytic fixed-shift quasianalyticity. -/
theorem reesAllOrdersFlat_analyticShiftMultiplier_iff
    {q : ℝ} (hq : 0 < q) {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-q * h))
        (analyticShiftMultiplier q F) ↔
      analyticOrderAt F 0 = ⊤ := by
  change ReesAllOrdersFlat atTop (fun h : ℝ => Real.exp (-q * h))
      (normedAnalyticShiftMultiplier q F) ↔ analyticOrderAt F 0 = ⊤
  exact reesAllOrdersFlat_normedAnalyticShiftMultiplier_iff hq hF

/-- The positive-charge reflected prime-Wold gauge cannot be the boundary trace of a holomorphic
augmentation germ.  Its nonzero `exp (-c/a)` sector is genuinely nonperturbative in boundary
volume `a`, rather than a hidden finite Taylor coefficient. -/
theorem not_exists_analyticAt_primeWoldReflectedIrregularGauge_augmentation
    {t : ℂ} (ht : 0 < t.re) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧
        (fun N => ‖F (primeWoldBoundaryVolumeBelow N : ℂ)‖) =ᶠ[atTop]
          fun N => ‖primeWoldReflectedIrregularGauge t N‖ := by
  rintro ⟨F, hF, hmatch⟩
  have hflatActual := norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat ht
  have hflatSample :
      ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (fun N => ‖F (primeWoldBoundaryVolumeBelow N : ℂ)‖) :=
    fun k => (hflatActual k).congr' hmatch.symm EventuallyEq.rfl
  have htop : analyticOrderAt F 0 = ⊤ :=
    (reesAllOrdersFlat_analyticNormAlongScale_iff
      (Eventually.of_forall primeWoldBoundaryVolumeBelow_pos)
      tendsto_primeWoldBoundaryVolumeBelow_zero hF).mp hflatSample
  have hsampleZero :
      (fun N => ‖F (primeWoldBoundaryVolumeBelow N : ℂ)‖) =ᶠ[atTop] 0 :=
    analyticNormAlongScale_eventually_eq_zero_of_order_eq_top
      tendsto_primeWoldBoundaryVolumeBelow_zero htop
  have hactualZero :
      (fun N => ‖primeWoldReflectedIrregularGauge t N‖) =ᶠ[atTop] 0 :=
    hmatch.symm.trans hsampleZero
  obtain ⟨N, hN⟩ := hactualZero.exists
  have hpositive : 0 < ‖primeWoldReflectedIrregularGauge t N‖ := by
    rw [norm_primeWoldReflectedIrregularGauge]
    exact Real.exp_pos _
  have hN' : ‖primeWoldReflectedIrregularGauge t N‖ = 0 := by simpa using hN
  rw [hN'] at hpositive
  exact (lt_irrefl 0) hpositive

end RHTower
