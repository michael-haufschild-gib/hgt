import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.LandauTailSignObstruction
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheUnheatedStateIsTheSumOfItsZeroModes
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTransformOfTheStateConvergesExactlyRightOfTheTransportedZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheAveragedStateHasAMeanSquareAtTheExactRate
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionMoments

/-!
# Shifted zero pairings on the half-plane of square moments

Synthesize the state at a depth between its zeros and the shifted sampling line.
An imaginary shift modulates the testing vector without changing its square mass.
At the midpoint depth both vectors use exactly the moment of the state under test.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def tiltedRay (F : ℝ → ℝ) (v : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (v*(t:ℂ))*(F (-t):ℂ)

private theorem memLp_tiltedRay {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (v : ℂ)
    (hv : 2*v.re < 17-2*zetaZeroAbscissa) : MemLp (tiltedRay F v) 2 halfLineLaplaceMeasure := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hm : Measurable (tiltedRay F v) :=
    (by fun_prop : Measurable fun t : ℝ => Complex.exp (v*(t:ℂ))).mul
      (Complex.measurable_ofReal.comp (hd.meas.comp measurable_neg))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hi := (integrable_sq_mul_exp_of_lt_decayRate hW ht hF hv).comp_neg
  apply hi.integrableOn.congr (Eventually.of_forall fun t => ?_)
  change F (-t)^2 * Real.exp (-(2*v.re*(-t))) = ‖Complex.exp (v*(t:ℂ))*(F (-t):ℂ)‖^2
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,norm_cexp_mul_ofReal,
    sq (Real.exp _),← Real.exp_add]
  rw [mul_comm]
  congr 2
  ring

/-- Shifting a feature reading translates the argument of the physical Laplace transform. -/
private theorem inner_feature_tiltedRay {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0)
    (v : ℂ) (hv : MemLp (tiltedRay F v) 2 halfLineLaplaceMeasure) (p : ℂ) (hp : 0 < p.re) :
    inner ℂ (halfLineLaplaceFeature p hp) (hv.toLp _) = negativeHalfLineLaplace (cx F) (p-v) := by
  rw [← halfLineLaplaceTransform,halfLineLaplaceTransform_eq_laplaceRay,
    negativeHalfLineLaplace_eq_laplaceRay_reflect (cx F) (fun u hu => by simp [cx,hsupp u hu])]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with t h
  change (hv.toLp _) t * expRay p t = (F (-t):ℂ) * expRay (p-v) t
  rw [h]
  unfold tiltedRay expRay
  rw [mul_right_comm,← Complex.exp_add,mul_comm _ (F (-t):ℂ)]
  congr 2
  ring

/-- The unheated expansion at every depth strictly to the right of the zeros.
Its Hilbert sum is the physical state tilted by the difference from depth eight. -/
theorem criticalState_hasSum_zero_modes_at_depth {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ}
    (hs : zetaZeroAbscissa-1/2 < s) :
    ∃ D : HalfLineLaplaceL2,
      HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) •
        zeroRayFeature s q ((re_centredZero_le_abscissa q).trans_lt hs)) D ∧
      (D : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure] fun t =>
        -(criticalAliasCoefficient W₀:ℂ) * Complex.exp (((8-s:ℝ):ℂ)*(t:ℂ)) * (F (-t):ℂ) := by
  let b : ℂ := ((8-s:ℝ):ℂ)
  let a : ℂ := criticalAliasCoefficient W₀
  have hb : 2*b.re < 17-2*zetaZeroAbscissa := by dsimp [b]; linarith
  have hD := memLp_tiltedRay hW ht hF b hb
  let D := hD.toLp _
  obtain ⟨U,hU⟩ := criticalState_summable_zeroRayFeature hW ht hF (Function.Embedding.refl XiZeroCopy)
    hs re_centredZero_le_abscissa
  have hphys : U = (-a) • D := by
    apply halfLine_eq_of_feature_readings
    intro p hp
    have hline : zetaZeroAbscissa-1/2-8 < (p-b).re := by
      simp only [b,Complex.sub_re,Complex.ofReal_re]; linarith
    have h := criticalState_hasSum_starEquation_right_of_zeros (sub_nonneg.mpr half_le_zetaZeroAbscissa)
      re_centredZero_le_abscissa hW ht hF hline
    have e : p-b+8 = p+(s:ℂ) := by dsimp only [b]; push_cast; ring
    rw [e] at h
    have hread := hU.mapL (innerSL ℂ (halfLineLaplaceFeature p hp))
    have hscalar : HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        (p+(s:ℂ)-centredZero q)⁻¹) (inner ℂ (halfLineLaplaceFeature p hp) U) := by
      refine hread.congr_fun (fun q => ?_)
      symm
      change inner ℂ _ (_ • zeroRayFeature s q _) = _
      rw [inner_smul_right,inner_zeroRayFeature]
      rfl
    rw [inner_smul_right,show inner ℂ (halfLineLaplaceFeature p hp) D =
      negativeHalfLineLaplace (cx F) (p-b) from inner_feature_tiltedRay
        (criticalHalfLineEnergyDomain_of_groundState hF).support b hD p hp,hscalar.unique h]
    ring
  refine ⟨U,hU,?_⟩
  rw [hphys]
  filter_upwards [Lp.coeFn_smul (-a) D,hD.coeFn_toLp] with t ht hval
  change ((-a) • D) t = _
  change D t = tiltedRay F b t at hval
  rw [ht,Pi.smul_apply,smul_eq_mul,hval]
  unfold tiltedRay
  exact (mul_assoc ..).symm

/-- Pairing a tilted real profile against a single zero exponential is one shifted sample. -/
private theorem inner_tiltedRay_mode {F : ℝ → ℝ} (hsupp : ∀ u, 0 ≤ u → F u = 0) (v : ℂ)
    (hv : MemLp (tiltedRay F v) 2 halfLineLaplaceMeasure) (s : ℝ) (q : XiZeroCopy)
    (hq : (centredZero q).re < s) :
    inner ℂ (hv.toLp _) (zeroRayFeature s q hq) =
      negativeHalfLineLaplace (cx F) ((s:ℂ)-centredZero q-star v) := by
  let p := (s:ℂ)-star (centredZero q)
  have hp : 0 < p.re := by simp [p]; linarith
  change inner ℂ (hv.toLp _) (halfLineLaplaceFeature p hp) = _
  rw [← inner_conj_symm,inner_feature_tiltedRay hsupp v hv p hp]
  change (starRingEnd ℂ) (negativeHalfLineLaplace (fun u => (F u:ℂ)) (p-v)) = _
  rw [← negativeHalfLineLaplace_real_conj]
  congr 1
  simp [p]

/-- The absolutely convergent complex shifted zero pairing is the square-moment
transform on its entire open half-plane of convergence. -/
theorem criticalState_hasSum_shifted_zeroPairing_moment_halfPlane {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {w : ℂ}
    (hw : w.re < 9-2*zetaZeroAbscissa) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx F) (-centredZero q-w))
      (-(criticalAliasCoefficient W₀:ℂ) * negativeHalfLineLaplace (cx (fun u => F u ^ 2)) (-(8+w))) := by
  let s := (8-w.re)/2
  let v := star (w+(s:ℂ))
  have hs : zetaZeroAbscissa-1/2 < s := by dsimp [s]; linarith
  have hv := memLp_tiltedRay hW ht hF v (by simp [v,s]; linarith)
  obtain ⟨D,hD,hval⟩ := criticalState_hasSum_zero_modes_at_depth hW ht hF hs
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hpair : HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx F) (-centredZero q-w)) (inner ℂ (hv.toLp _) D) := by
    refine (hD.mapL (innerSL ℂ (hv.toLp _))).congr_fun fun q => ?_
    symm
    change inner ℂ _ (_ • zeroRayFeature s q _) = _
    rw [inner_smul_right,inner_tiltedRay_mode hd.support]
    have e : (s:ℂ)-centredZero q-star v = -centredZero q-w := by simp only [v,star_star]; ring
    rw [e]
  have hsq : ∀ u, 0 ≤ u → cx (fun u => F u ^ 2) u = 0 := fun u hu => by simp [cx,hd.support u hu]
  suffices he : inner ℂ (hv.toLp _) D =
      -(criticalAliasCoefficient W₀:ℂ)*negativeHalfLineLaplace (cx fun u => F u ^ 2) (-(8+w)) by
    rw [← he]; exact hpair
  rw [L2.inner_def,negativeHalfLineLaplace_eq_laplaceRay_reflect _ hsq,laplaceRay,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp,hval] with t h1 h2
  rw [RCLike.inner_apply,h1,h2]
  simp only [tiltedRay,map_mul,Complex.conj_ofReal,← Complex.exp_conj,v,Complex.star_def,Complex.conj_conj,
    cx,Complex.ofReal_pow,expRay,neg_mul,neg_neg]
  have e : (((8-s:ℝ):ℂ)*(t:ℂ)) + (w+(s:ℂ))*(t:ℂ) = (8+w)*(t:ℂ) := by push_cast; ring
  rw [← e,Complex.exp_add]
  ring

#print axioms criticalState_hasSum_zero_modes_at_depth
#print axioms criticalState_hasSum_shifted_zeroPairing_moment_halfPlane


/-- The unheated zero pairing with complex translation of the second transform. -/
def unheatedShiftedZeroPairing (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
    negativeHalfLineLaplace (cx F) (-centredZero q-w)

private theorem square_laplace_integrable {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {σ : ℝ}
    (hσ : 2*zetaZeroAbscissa-17 < σ) :
    Integrable fun u => F u ^ 2 * Real.exp (σ*u) := by
  simpa only [neg_mul,neg_neg] using
    integrable_sq_mul_exp_of_lt_decayRate hW ht hF (b := -σ) (by linarith)

/-- The shifted series defines a holomorphic function on every strict moment line. -/
theorem criticalState_analyticOnNhd_shiftedZeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    AnalyticOnNhd ℂ (unheatedShiftedZeroPairing F) {w : ℂ | w.re < 9-2*zetaZeroAbscissa} := by
  let b := 2*zetaZeroAbscissa-17
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hsupp (u : ℝ) (hu : 0 ≤ u) : (F u)^2 = 0 := by simp [hd.support u hu]
  have hdiff := differentiableOn_laplace_of_abs (hd.meas.pow_const 2) hsupp (κ := b)
    (fun σ hσ => by simpa only [abs_pow,sq_abs] using square_laplace_integrable hW ht hF hσ)
  intro w hw
  have hx : b < (-(8+w)).re := by change w.re < _ at hw; dsimp [b]; linarith
  have h1 := hdiff.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx)
  have ha : AnalyticAt ℂ (fun z : ℂ => -(8+z)) w := by fun_prop
  have hcomp : AnalyticAt ℂ ((negativeHalfLineLaplace (cx fun u => F u ^ 2)) ∘ (fun z : ℂ => -(8+z))) w :=
    AnalyticAt.comp (f := fun z : ℂ => -(8+z)) h1 ha
  have hh : AnalyticAt ℂ (fun z : ℂ => -(criticalAliasCoefficient W₀:ℂ) *
      negativeHalfLineLaplace (cx fun u => F u ^ 2) (-(8+z))) w :=
    analyticAt_const.mul hcomp
  apply hh.congr
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw] with z hz
  exact (criticalState_hasSum_shifted_zeroPairing_moment_halfPlane hW ht hF hz).tsum_eq.symm

open GaloisForLFunctions.RHTower (IsAbscissa laplaceReal false_of_analyticAt_abscissa)

private theorem square_tail_abscissa {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    IsAbscissa (tailMeasure (fun u => F u ^ 2) 0) (2*zetaZeroAbscissa-17) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hm := laplaceMass_tailMeasure_ne_top_iff (hd.meas.pow_const 2) (show (0:ℝ) ≤ 0 from le_rfl)
    (Eventually.of_forall fun u => sq_nonneg (F u))
  constructor
  · intro σ hσ
    exact (hm σ).mpr (square_laplace_integrable hW ht hF hσ).integrableOn
  · intro σ hσ
    by_contra hfin
    have hi := (hm σ).mp hfin
    have hall := hi.integrable_of_forall_notMem_eq_zero (fun u hu => by
      have hnon : 0 ≤ u := by simpa using hu
      simp [hd.support u hnon])
    apply not_integrable_sq_mul_exp_of_decayRate_lt hW ht hF (b := -σ) (by linarith)
    simpa only [neg_mul,neg_neg] using hall

private theorem pairing_real_tail {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {σ : ℝ} (hσ : 2*zetaZeroAbscissa-17 < σ) :
    unheatedShiftedZeroPairing F ((-8-σ:ℝ):ℂ) =
      -(criticalAliasCoefficient W₀:ℂ) * (laplaceReal (tailMeasure (fun u => F u ^ 2) 0) σ:ℂ) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hh := (criticalState_hasSum_shifted_zeroPairing_moment_halfPlane hW ht hF
    (w := ((-8-σ:ℝ):ℂ)) (by simp only [Complex.ofReal_re]; linarith)).tsum_eq
  rw [show -(8+((-8-σ:ℝ):ℂ)) = (σ:ℂ) by push_cast; ring,negativeHalfLineLaplace_ofReal] at hh
  rw [laplaceReal_tailMeasure (hd.meas.pow_const 2) le_rfl (Eventually.of_forall fun u => sq_nonneg (F u)),
    neg_zero,setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [hd.support u (not_lt.mp hu)]; simp)]
  exact hh

/-- From a real centre the shifted zero pairing extends to a disk exactly up to the
distance to its first real square-moment singularity, even for an unattained zero abscissa. -/
theorem criticalState_shiftedZeroPairing_exact_disk {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {c r : ℝ} (hc : c < 9-2*zetaZeroAbscissa) :
    (∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball (c:ℂ) r) ∧
      ∀ x : ℝ, (x:ℂ) ∈ Metric.ball (c:ℂ) r → x < 9-2*zetaZeroAbscissa →
        G x = unheatedShiftedZeroPairing F x) ↔ r ≤ 9-2*zetaZeroAbscissa-c := by
  let B := 9-2*zetaZeroAbscissa
  let b := 2*zetaZeroAbscissa-17
  constructor
  · rintro ⟨G,hG,hagree⟩
    by_contra! hr
    let δ := r-(B-c)
    have hδ : 0 < δ := sub_pos.mpr hr
    have hbc : dist (B:ℂ) (c:ℂ) = B-c := by
      rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hc)]
    have hmap (z : ℂ) (hz : z ∈ Metric.ball (b:ℂ) δ) : -8-z ∈ Metric.ball (c:ℂ) r := by
      have he : -8-z-(B:ℂ) = -(z-(b:ℂ)) := by dsimp only [B,b]; push_cast; ring
      have hd : dist (-8-z) (B:ℂ) = dist z (b:ℂ) := by rw [dist_eq_norm,he,norm_neg,dist_eq_norm]
      have hh := dist_triangle (-8-z) (B:ℂ) (c:ℂ)
      rw [hd,hbc] at hh
      change dist z (b:ℂ) < r-(B-c) at hz
      exact hh.trans_lt (by linarith)
    let a : ℂ := criticalAliasCoefficient W₀
    have ha : -a ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne')
    apply false_of_analyticAt_abscissa (square_tail_abscissa hW ht hF) hδ
      (Φ := fun z : ℂ => G (-8-z)/(-a))
    · intro z hz
      exact ((hG _ (hmap z hz)).comp (by fun_prop : AnalyticAt ℂ (fun p : ℂ => -8-p) z)).div
        analyticAt_const ha
    · intro σ hσlo hσhi
      have hmem : (σ:ℂ) ∈ Metric.ball (b:ℂ) δ := by
        rw [Metric.mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hσlo)]
        linarith
      have hcst : ((-8-σ:ℝ):ℂ) = -8-(σ:ℂ) := by push_cast; rfl
      have harg := hmap _ hmem
      rw [← hcst] at harg
      have hx : -8-σ < B := by dsimp only [b,B] at *; linarith
      change G (-8-(σ:ℂ))/(-a) = _
      rw [← hcst,hagree _ harg hx,pairing_real_tail hW ht hF hσlo]
      exact mul_div_cancel_left₀ _ ha
  · intro hr
    refine ⟨unheatedShiftedZeroPairing F,?_,fun _ _ _ => rfl⟩
    apply (criticalState_analyticOnNhd_shiftedZeroPairing hW ht hF).mono
    intro z hz
    have hh := Complex.re_le_norm (z-(c:ℂ))
    rw [Complex.sub_re,Complex.ofReal_re] at hh
    rw [Metric.mem_ball,dist_eq_norm] at hz
    change z.re < 9-2*zetaZeroAbscissa
    linarith

#print axioms criticalState_analyticOnNhd_shiftedZeroPairing
#print axioms criticalState_shiftedZeroPairing_exact_disk

end GaloisForLFunctions.ExclusionOfTheCriticalState
