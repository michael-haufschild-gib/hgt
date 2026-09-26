import GaloisForLFunctions.HTGeometry.MellinBoundaryFinitePart
import GaloisForLFunctions.HTGeometry.SecantEnergyBoundary
import GaloisForLFunctions.RHTower.XiPoissonProgression
import GaloisForLFunctions.RHTower.ThetaCuspSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Geometric theta tangent boundary energy

The full theta source has a logarithmically divergent geometric tangent energy, an explicit finite part, and unbounded finite secant energy near the origin.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
namespace RHTower.ThetaGeometricBoundaryAudit

lemma sourceSquare_integrable : Integrable (fun t : ℝ => thetaCuspFullSource t^2) := by
  have h : Integrable (fun t : ℝ => thetaCuspFullSource t*thetaCuspFullSource t) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
      thetaCuspSchwartzReal thetaCuspSchwartzReal).integrable
  simpa only [pow_two] using h

lemma source_times_derivative_integrable :
    Integrable (fun t : ℝ => thetaCuspFullSource t*deriv thetaCuspFullSource t) := by
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
    thetaCuspSchwartzReal (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)).integrable

lemma weighted_derivative_square_integrable :
    Integrable (fun t : ℝ => t*(deriv thetaCuspFullSource t)^2) := by
  let d := SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal
  let g := SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) d d
  have hg := g.integrable_pow_mul volume 1
  change Integrable (fun t : ℝ => ‖t‖^1*‖deriv thetaCuspFullSource t*
    deriv thetaCuspFullSource t‖) at hg
  have hnorm : Integrable (fun t : ℝ => ‖t*(deriv thetaCuspFullSource t)^2‖) := by
    simpa only [pow_one, norm_mul, pow_two] using hg
  apply (integrable_norm_iff ?_).mp hnorm
  have hc : Continuous (fun t : ℝ => deriv thetaCuspFullSource t) := d.continuous
  exact (continuous_id.mul (hc.pow 2)).aestronglyMeasurable

lemma source_times_derivative_tail (x : ℝ) :
    (∫ t in Ioi x, thetaCuspFullSource t*deriv thetaCuspFullSource t) =
      -thetaCuspFullSource x^2/2 := by
  have hder (t : ℝ) : HasDerivAt (fun t => thetaCuspFullSource t^2/2)
      (thetaCuspFullSource t*deriv thetaCuspFullSource t) t := by
    have hphi : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource t) t :=
      thetaCuspSchwartzReal.hasDerivAt t
    have h := (hphi.pow 2).div_const 2
    convert! h using 1
    ring
  have ht : Tendsto thetaCuspFullSource atTop (𝓝 0) :=
    thetaCuspSchwartzReal.tendsto_cocompact.mono_left atTop_le_cocompact
  have hlim : Tendsto (fun t => thetaCuspFullSource t^2/2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div] using (ht.pow 2).div_const 2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hder t) source_times_derivative_integrable.integrableOn hlim (a := x)
  simpa only [zero_sub, neg_div] using h

lemma source_inverse_tail_finitePart_tendsto :
    Tendsto (fun x => (∫ t in Ioi x, thetaCuspFullSource t^2/t)-
      thetaCuspFullSource 0^2*Real.log (1/x)) (𝓝[>] 0)
      (𝓝 ((∫ t in (0:ℝ)..1, dslope (fun t => thetaCuspFullSource t^2) 0 t)+
        (∫ t in Ioi (1:ℝ), thetaCuspFullSource t^2/t))) :=
  GaloisForLFunctions.HTGeometry.MellinBoundary.inverseTail_finitePart_tendsto
    (thetaCuspSchwartzReal.continuous.pow 2)
    ((thetaCuspSchwartzReal.hasDerivAt 0).pow 2).differentiableAt sourceSquare_integrable

lemma source_inverse_tail_log_ratio_tendsto :
    Tendsto (fun x => (∫ t in Ioi x, thetaCuspFullSource t^2/t)/Real.log (1/x))
      (𝓝[>] 0) (𝓝 (thetaCuspFullSource 0^2)) :=
  GaloisForLFunctions.HTGeometry.MellinBoundary.inverseTail_log_ratio_tendsto
    (thetaCuspSchwartzReal.continuous.pow 2)
    ((thetaCuspSchwartzReal.hasDerivAt 0).pow 2).differentiableAt sourceSquare_integrable

/-- Derivative of the square-root weighted source at a positive argument. -/
def geometricTangent (x : ℝ) : ℝ :=
  thetaCuspFullSource x/(2*Real.sqrt x)+Real.sqrt x*deriv thetaCuspFullSource x

lemma geometricTangent_sq {x : ℝ} (hx : 0 < x) :
    geometricTangent x^2 = thetaCuspFullSource x^2/(4*x)+
      thetaCuspFullSource x*deriv thetaCuspFullSource x+
      x*(deriv thetaCuspFullSource x)^2 := by
  have hs : (Real.sqrt x)^2 = x := Real.sq_sqrt hx.le
  have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold geometricTangent
  field_simp
  rw [hs]
  ring

lemma source_inverse_tail_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => thetaCuspFullSource t^2/t) (Ioi x) :=
  GaloisForLFunctions.HTGeometry.MellinBoundary.integrableOn_div_id
    (thetaCuspSchwartzReal.continuous.pow 2) sourceSquare_integrable hx

lemma geometricTangent_sq_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => geometricTangent t^2) (Ioi x) := by
  have h1 := (source_inverse_tail_integrable hx).div_const 4
  have h2 := source_times_derivative_integrable.integrableOn (s := Ioi x)
  have h3 := weighted_derivative_square_integrable.integrableOn (s := Ioi x)
  apply ((h1.add h2).add h3).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [Pi.add_apply]
  rw [geometricTangent_sq (hx.trans ht)]
  simp only [div_div, mul_comm t (4:ℝ)]

lemma geometricTangent_energy_eq {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi x, geometricTangent t^2) =
      (∫ t in Ioi x, thetaCuspFullSource t^2/t)/4-
      thetaCuspFullSource x^2/2+(∫ t in Ioi x, t*(deriv thetaCuspFullSource t)^2) := by
  have h1 := (source_inverse_tail_integrable hx).div_const 4
  have h2 := source_times_derivative_integrable.integrableOn (s := Ioi x)
  have h3 := weighted_derivative_square_integrable.integrableOn (s := Ioi x)
  calc
    _ = ∫ t in Ioi x, (thetaCuspFullSource t^2/t)/4+
        thetaCuspFullSource t*deriv thetaCuspFullSource t+
        t*(deriv thetaCuspFullSource t)^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [geometricTangent_sq (hx.trans ht)]
      simp only [div_div, mul_comm t (4:ℝ)]
    _ = _ := by
      have hadd := integral_add (h1.add h2) h3
      dsimp only [Pi.add_apply] at hadd
      rw [hadd]
      have hadd2 := integral_add h1 h2
      rw [hadd2, integral_div, source_times_derivative_tail]
      ring

lemma continuous_tail {f : ℝ → ℝ} (hi : Integrable f) :
    Continuous (fun x => ∫ t in Ioi x, f t) := by
  have hc : Continuous (fun x => (∫ t in Ioi (0:ℝ), f t)-(∫ t in (0:ℝ)..x, f t)) :=
    continuous_const.sub (hi.continuous_primitive 0)
  apply hc.congr
  intro x
  have h := intervalIntegral.integral_interval_add_Ioi
    (hi.integrableOn (s := Ioi (0:ℝ))) (hi.integrableOn (s := Ioi x))
  linarith only [h]

/-- The finite remainder after subtracting the singular geometric energy. -/
def geometricTangentFinitePart : ℝ :=
  ((∫ t in (0:ℝ)..1, dslope (fun t => thetaCuspFullSource t^2) 0 t)+
    (∫ t in Ioi (1:ℝ), thetaCuspFullSource t^2/t))/4-
    thetaCuspFullSource 0^2/2+(∫ t in Ioi (0:ℝ), t*(deriv thetaCuspFullSource t)^2)

lemma geometricTangent_energy_finitePart_tendsto :
    Tendsto (fun x => (∫ t in Ioi x, geometricTangent t^2)-
      (thetaCuspFullSource 0^2/4)*Real.log (1/x)) (𝓝[>] 0)
      (𝓝 geometricTangentFinitePart) := by
  have hsource : Tendsto (fun x => thetaCuspFullSource x^2/2) (𝓝[>] 0)
      (𝓝 (thetaCuspFullSource 0^2/2)) :=
    ((thetaCuspSchwartzReal.continuous.pow 2).div_const 2).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have htail : Tendsto (fun x => ∫ t in Ioi x, t*(deriv thetaCuspFullSource t)^2)
      (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), t*(deriv thetaCuspFullSource t)^2)) :=
    (continuous_tail weighted_derivative_square_integrable).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have h := ((source_inverse_tail_finitePart_tendsto.div_const 4).sub hsource).add htail
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [geometricTangent_energy_eq hx]
  ring

lemma geometricTangent_energy_log_ratio_tendsto :
    Tendsto (fun x => (∫ t in Ioi x, geometricTangent t^2)/Real.log (1/x))
      (𝓝[>] 0) (𝓝 (thetaCuspFullSource 0^2/4)) := by
  have hsmall := geometricTangent_energy_finitePart_tendsto.div_atTop
    GaloisForLFunctions.HTGeometry.MellinBoundary.log_inv_tendsto
  have hlim := (show Tendsto (fun _ : ℝ => thetaCuspFullSource 0^2/4)
    (𝓝[>] 0) (𝓝 (thetaCuspFullSource 0^2/4)) from tendsto_const_nhds).add hsmall
  rw [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [GaloisForLFunctions.HTGeometry.MellinBoundary.log_inv_tendsto.eventually
    (eventually_gt_atTop (0:ℝ))] with x hx
  field_simp [hx.ne']
  ring

lemma hasDerivAt_sqrt_source {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => Real.sqrt t*thetaCuspFullSource t) (geometricTangent x) x := by
  have hphi : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource x) x :=
    thetaCuspSchwartzReal.hasDerivAt x
  convert! (Real.hasDerivAt_sqrt hx.ne').mul hphi using 1
  unfold geometricTangent
  ring

lemma geometricTangent_energy_tendsto_atTop :
    Tendsto (fun x => ∫ t in Ioi x, geometricTangent t^2) (𝓝[>] 0) atTop := by
  have hc : 0 < thetaCuspFullSource 0^2/4 :=
    div_pos (sq_pos_of_pos thetaCuspFullSource_pos_zero) (by norm_num)
  have h := geometricTangent_energy_log_ratio_tendsto.pos_mul_atTop hc
    GaloisForLFunctions.HTGeometry.MellinBoundary.log_inv_tendsto
  apply h.congr'
  filter_upwards [GaloisForLFunctions.HTGeometry.MellinBoundary.log_inv_tendsto.eventually
    (eventually_gt_atTop (0:ℝ))] with x hx
  exact div_mul_cancel₀ _ hx.ne'

lemma not_integrable_geometricTangent_sq :
    ¬IntegrableOn (fun t => geometricTangent t^2) (Ioi 0) := by
  intro hi
  have hbound : ∀ᶠ x in 𝓝[>] (0:ℝ),
      (∫ t in Ioi x, geometricTangent t^2) ≤ ∫ t in Ioi (0:ℝ), geometricTangent t^2 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact setIntegral_mono_set hi (Eventually.of_forall fun t => sq_nonneg _)
      (Eventually.of_forall fun t ht => hx.trans ht)
  obtain ⟨x, hle, hgt⟩ := (hbound.and
    (geometricTangent_energy_tendsto_atTop.eventually_gt_atTop
      (∫ t in Ioi (0:ℝ), geometricTangent t^2))).exists
  exact (not_lt_of_ge hle) hgt

lemma not_memLp_geometricTangent :
    ¬MemLp geometricTangent 2 (volume.restrict (Ioi 0)) := by
  intro hm
  apply not_integrable_geometricTangent_sq
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [IntegrableOn, Real.norm_eq_abs, sq_abs] using hi

lemma sqrt_source_sq_integrable :
    Integrable (fun t => (Real.sqrt t*thetaCuspFullSource t)^2) := by
  let g := SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ)
    thetaCuspSchwartzReal thetaCuspSchwartzReal
  have hg := g.integrable_pow_mul volume 1
  change Integrable (fun t : ℝ => ‖t‖^1*‖thetaCuspFullSource t*thetaCuspFullSource t‖) at hg
  apply hg.mono' ((Real.continuous_sqrt.mul thetaCuspSchwartzReal.continuous).pow 2).aestronglyMeasurable
  filter_upwards [] with t
  change ‖(Real.sqrt t*thetaCuspFullSource t)^2‖ ≤
    ‖t‖^1*‖thetaCuspFullSource t*thetaCuspFullSource t‖
  rw [norm_pow, norm_mul, mul_pow, pow_one, ← pow_two, norm_pow,
    Real.norm_eq_abs (Real.sqrt t), abs_of_nonneg (Real.sqrt_nonneg t), Real.norm_eq_abs t]
  by_cases ht : 0 ≤ t
  · rw [Real.sq_sqrt ht, abs_of_nonneg ht]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht), zero_pow (by decide : 2 ≠ 0), zero_mul]
    positivity

lemma exists_large_geometric_secant (C : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h ∈ Ioo 0 δ, C < ∫ t in Ioi (0:ℝ),
      ((Real.sqrt (t+h)*thetaCuspFullSource (t+h)-
        Real.sqrt t*thetaCuspFullSource t)/h)^2 :=
  GaloisForLFunctions.HTGeometry.SecantBoundary.exists_large_secant
    (Real.continuous_sqrt.mul thetaCuspSchwartzReal.continuous)
    sqrt_source_sq_integrable (fun _ ht => hasDerivAt_sqrt_source ht)
    not_integrable_geometricTangent_sq C hδ

end RHTower.ThetaGeometricBoundaryAudit
