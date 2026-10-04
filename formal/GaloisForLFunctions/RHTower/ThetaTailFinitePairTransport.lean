import GaloisForLFunctions.RHTower.ThetaTailTransportPrimitiveFloor

/-! Exact finite-pair transport of the literal center Schur kernel. The positive
flux is integrable because its primitive has a finite limit. Thus the improper
integration by parts does not assume integrability of the new moment. -/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.ThetaFiniteTransport

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel
local notation "J" => H 0 0
local notation "p" => thetaCuspLogDecaySlope

def sourceRatio (y t : ℝ) : ℝ := k (y+t)/k t

private theorem source_hasDerivAt (t : ℝ) : HasDerivAt k (-p t*k t) t := by
  have he : deriv k t=-p t*k t := by
    have hl : iteratedDeriv 1 thetaCuspLogSource t=deriv k t/k t := by
      simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
    dsimp only [thetaCuspLogDecaySlope]
    rw [hl]
    field_simp [(thetaCuspFullSource_pos_all t).ne']
  rw [← he]
  exact thetaCuspSchwartzReal.hasDerivAt t

theorem sourceRatio_hasDerivAt (y t : ℝ) : HasDerivAt (sourceRatio y)
    (-(p (y+t)-p t)*sourceRatio y t) t := by
  have hs := (source_hasDerivAt (y+t)).comp t ((hasDerivAt_id t).const_add y)
  convert! hs.div (source_hasDerivAt t) (thetaCuspFullSource_pos_all t).ne' using 1
  dsimp only [sourceRatio,Function.comp_apply,id_eq]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

theorem sourceRatio_pos (y t : ℝ) : 0 < sourceRatio y t :=
  div_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)

theorem sourceRatio_antitone {y : ℝ} (hy : 0 < y) :
    AntitoneOn (sourceRatio y) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro t _; exact (sourceRatio_hasDerivAt y t).continuousAt.continuousWithinAt
  · intro t _; exact (sourceRatio_hasDerivAt y t).differentiableAt.differentiableWithinAt
  · intro t _
    rw [(sourceRatio_hasDerivAt y t).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sub_nonneg.mpr (monotone_thetaCuspLogDecaySlope (by linarith))))
      (sourceRatio_pos y t).le

def balanceFlux (x y t : ℝ) : ℝ := sourceRatio y t*prefixBalance x t

def positiveFlux (x y t : ℝ) : ℝ :=
  (p (y+t)-p t)*sourceRatio y t*prefixBalance x t

def packetDensity (x y t : ℝ) : ℝ :=
  J*(k (x+t)*k (y+t))-H 0 x*(k t*k (y+t))

def rawTransport (x y t : ℝ) : ℝ :=
  J*thetaTailCommonTranslationIntegrand x y t-
    H 0 x*thetaTailCommonTranslationIntegrand 0 y t-y*packetDensity x y t

theorem packetDensity_integrable (x y : ℝ) : Integrable (packetDensity x y) := by
  change Integrable (fun t => J*(k (x+t)*k (y+t))-H 0 x*(k t*k (y+t)))
  convert!
    ((ThetaJoint.correlation_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal x y).const_mul J).sub
      ((ThetaJoint.correlation_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal 0 y).const_mul (H 0 x)) using 1
  funext t
  simp only [thetaCuspSchwartzReal_apply,Pi.sub_apply,zero_add]

theorem rawTransport_integrable (x y : ℝ) : Integrable (rawTransport x y) :=
  (((integrable_thetaTailCommonTranslationIntegrand x y).const_mul J).sub
    ((integrable_thetaTailCommonTranslationIntegrand 0 y).const_mul (H 0 x))).sub
      ((packetDensity_integrable x y).const_mul y)

private theorem rawTransport_continuous (x y : ℝ) : Continuous (rawTransport x y) := by
  unfold rawTransport packetDensity thetaTailCommonTranslationIntegrand
  have hk := contDiff_thetaCuspFullSource.continuous
  fun_prop

theorem rawTransport_eq (x y t : ℝ) :
    rawTransport x y t=sourceRatio y t*balanceDensity x t := by
  unfold rawTransport packetDensity sourceRatio balanceDensity thetaTailCommonTranslationIntegrand
  simp only [zero_add]
  field_simp [(thetaCuspFullSource_pos_all t).ne']
  ring

theorem balanceFlux_hasDerivAt (x y t : ℝ) : HasDerivAt (balanceFlux x y)
    (rawTransport x y t-positiveFlux x y t) t := by
  convert! (sourceRatio_hasDerivAt y t).mul (prefixBalance_hasDerivAt x t) using 1
  rw [rawTransport_eq]
  unfold positiveFlux
  ring

theorem balanceFlux_limit (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (balanceFlux x y) atTop (𝓝 0) := by
  apply bdd_le_mul_tendsto_zero (b := 0) (B := sourceRatio y 0)
  · exact Eventually.of_forall fun t => (sourceRatio_pos y t).le
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact sourceRatio_antitone hy (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  · exact prefixBalance_limit x

theorem positiveFlux_nonneg {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (ht : 0 < t) :
    0 ≤ positiveFlux x y t := by
  apply mul_nonneg
    (mul_nonneg (sub_nonneg.mpr (monotone_thetaCuspLogDecaySlope (by linarith)))
      (sourceRatio_pos y t).le)
    (prefixBalance_pos hx ht).le

private def fluxPrimitive (x y t : ℝ) : ℝ :=
  (∫ s in 0..t, rawTransport x y s)-balanceFlux x y t

private theorem fluxPrimitive_hasDerivAt (x y t : ℝ) :
    HasDerivAt (fluxPrimitive x y) (positiveFlux x y t) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (a := 0)
    (rawTransport_integrable x y).intervalIntegrable
    ((rawTransport_continuous x y).stronglyMeasurableAtFilter volume (𝓝 t))
    (rawTransport_continuous x y).continuousAt
  convert! hi.sub (balanceFlux_hasDerivAt x y t) using 1
  ring

private theorem fluxPrimitive_limit (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Tendsto (fluxPrimitive x y) atTop (𝓝 (∫ s in Ioi 0, rawTransport x y s)) := by
  have hi := intervalIntegral_tendsto_integral_Ioi 0
    (rawTransport_integrable x y).integrableOn tendsto_id
  change Tendsto (fun t => (∫ s in 0..t, rawTransport x y s)-balanceFlux x y t)
    atTop (𝓝 (∫ s in Ioi 0, rawTransport x y s))
  simpa only [id_eq,sub_zero] using hi.sub (balanceFlux_limit x hy)

/-- Integrability of the new positive flux follows from its actual finite primitive. -/
theorem positiveFlux_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (positiveFlux x y) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun t _ => fluxPrimitive_hasDerivAt x y t)
    (fun _ ht => positiveFlux_nonneg hx hy ht) (fluxPrimitive_limit x hy)

theorem integral_positiveFlux {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioi 0, positiveFlux x y t)=∫ t in Ioi 0, rawTransport x y t := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => fluxPrimitive_hasDerivAt x y t)
    (fun t ht => positiveFlux_nonneg hx hy ht) (fluxPrimitive_limit x hy)
  simpa only [fluxPrimitive,intervalIntegral.integral_same,balanceFlux,
    prefixBalance_zero,mul_zero,sub_zero] using h

def transportMoment (x y t : ℝ) : ℝ :=
  normalizedPacket x t+(p (y+t)-p t)/y*transportPrimitive x t

def transportDensity (x y t : ℝ) : ℝ :=
  k (x+t)*k (y+t)/(k x*k y)*transportMoment x y t

private theorem center_ne : J ≠ 0 := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact (ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0).ne'

theorem transportDensity_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    transportDensity x y t=(positiveFlux x y t+y*packetDensity x y t)/(J*x*y*k x*k y) := by
  unfold transportDensity transportMoment normalizedPacket transportPrimitive
    positiveFlux sourceRatio packetDensity
  field_simp [hx.ne',hy.ne',center_ne,(thetaCuspFullSource_pos_all t).ne',
    (thetaCuspFullSource_pos_all (x+t)).ne',(thetaCuspFullSource_pos_all x).ne',
    (thetaCuspFullSource_pos_all y).ne']
  ring

theorem transportDensity_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (transportDensity x y) (Ioi 0) := by
  have he := funext (transportDensity_eq hx hy)
  rw [he]
  exact ((positiveFlux_integrable hx hy).add
    ((packetDensity_integrable x y).const_mul y).integrableOn).div_const _

private theorem kernel_integral (x y : ℝ) :
    (∫ t in Ioi 0, thetaTailCommonTranslationIntegrand x y t)=H x y := by
  simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 x y).symm

/-- Exact finite-pair center Schur transport, including the signed packet term. -/
theorem integral_transportDensity {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in Ioi 0, transportDensity x y t)=
      (H x y-H 0 x*H 0 y/J)/(x*y*k x*k y) := by
  rw [funext (transportDensity_eq hx hy),integral_div,
    integral_add (positiveFlux_integrable hx hy)
      ((packetDensity_integrable x y).const_mul y).integrableOn,
    integral_positiveFlux hx hy]
  have hu : Integrable (fun t => J*thetaTailCommonTranslationIntegrand x y t-
      H 0 x*thetaTailCommonTranslationIntegrand 0 y t) := by
    convert! ((integrable_thetaTailCommonTranslationIntegrand x y).const_mul J).sub
      ((integrable_thetaTailCommonTranslationIntegrand 0 y).const_mul (H 0 x)) using 1
  unfold rawTransport
  rw [integral_sub hu.integrableOn
    ((packetDensity_integrable x y).const_mul y).integrableOn,
    integral_sub ((integrable_thetaTailCommonTranslationIntegrand x y).const_mul J).integrableOn
      ((integrable_thetaTailCommonTranslationIntegrand 0 y).const_mul (H 0 x)).integrableOn,
    integral_const_mul,integral_const_mul,kernel_integral,kernel_integral]
  field_simp [center_ne,hx.ne',hy.ne',
    (thetaCuspFullSource_pos_all x).ne',(thetaCuspFullSource_pos_all y).ne']
  ring

end RHTower.ThetaFiniteTransport
