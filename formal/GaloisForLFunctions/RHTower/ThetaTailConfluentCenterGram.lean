import GaloisForLFunctions.RHTower.ThetaTwoNodePortTransversality
import GaloisForLFunctions.RHTower.ThetaGeometricBoundaryEnergy
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The actual center confluent Gram entry has a strictly positive source current.
This supplies the nondegenerate denominator for coalescing-node projection limits. -/

noncomputable section
open MeasureTheory Filter Topology Set
namespace RHTower.ThetaConfluent
open ThetaGeometricBoundaryAudit

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) :
    weighted f t = t*f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private theorem weighted_product_integrable (f g : SchwartzMap ℝ ℝ) :
    Integrable (fun t : ℝ => t*f t*g t) := by
  have h : Integrable (fun t : ℝ => weighted f t*g t) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (weighted f) g).integrable
  simpa only [weighted_apply] using h

private theorem weighted_product_zero (f g : SchwartzMap ℝ ℝ) :
    Tendsto (fun t : ℝ => t*f t*g t) atTop (𝓝 0) := by
  have h := ((weighted f).tendsto_cocompact.mono_left atTop_le_cocompact).mul
    (g.tendsto_cocompact.mono_left atTop_le_cocompact)
  simpa only [weighted_apply, mul_zero] using h

private theorem source_hasDerivAt (t : ℝ) :
    HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource t) t :=
  thetaCuspSchwartzReal.hasDerivAt t

private theorem source_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv thetaCuspFullSource) (deriv (deriv thetaCuspFullSource) t) t :=
  (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal).hasDerivAt t

private theorem source_deriv_eq (t : ℝ) :
    deriv thetaCuspFullSource t = -thetaCuspLogDecaySlope t*thetaCuspFullSource t := by
  have h : iteratedDeriv 1 thetaCuspLogSource t =
      deriv thetaCuspFullSource t/thetaCuspFullSource t := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource t).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all t).ne']

private theorem slope_hasDerivAt (t : ℝ) :
    HasDerivAt thetaCuspLogDecaySlope (-iteratedDeriv 2 thetaCuspLogSource t) t :=
  (hasDerivAt_iteratedDeriv_thetaCuspLogSource 1 t).neg

private theorem source_second_eq (t : ℝ) :
    deriv (deriv thetaCuspFullSource) t =
      (thetaCuspLogDecaySlope t^2+iteratedDeriv 2 thetaCuspLogSource t)*thetaCuspFullSource t := by
  have he : deriv thetaCuspFullSource =
      fun t => -thetaCuspLogDecaySlope t*thetaCuspFullSource t := funext source_deriv_eq
  have h := ((slope_hasDerivAt t).neg.mul (source_hasDerivAt t)).deriv
  change deriv (fun t => -thetaCuspLogDecaySlope t*thetaCuspFullSource t) t =
    - -iteratedDeriv 2 thetaCuspLogSource t*thetaCuspFullSource t+
      -thetaCuspLogDecaySlope t*deriv thetaCuspFullSource t at h
  rw [← he, source_deriv_eq] at h
  rw [h]
  ring

private theorem slope_zero : thetaCuspLogDecaySlope 0 = 0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩, neg_zero]

/-- Strict convexity of the actual decay slope supplies the confluent current sign. -/
theorem slope_current_pos {t : ℝ} (ht : 0 < t) :
    0 < -t*iteratedDeriv 2 thetaCuspLogSource t-thetaCuspLogDecaySlope t := by
  have h := ThetaPort.strictConvexOn_slope.slope_lt_of_hasDerivAt
    (show (0:ℝ) ∈ Ici 0 by simp) ht.le ht (slope_hasDerivAt t)
  simp only [slope, slope_zero, sub_zero, smul_eq_mul, inv_mul_eq_div] at h
  change (thetaCuspLogDecaySlope t-0)/t < -iteratedDeriv 2 thetaCuspLogSource t at h
  rw [sub_zero] at h
  have h' := (div_lt_iff₀ ht).mp h
  nlinarith only [h']

/-- Weighted derivative mass of the literal source. -/
def derivativeMass : ℝ := ∫ t in Ioi 0, t*(deriv thetaCuspFullSource t)^2

/-- The derivative-derivative entry of the full center confluent kernel. -/
def centerEntry : ℝ := 2*derivativeMass-thetaCuspFullSource 0^2

/-- A Schwartz-product expression for the positive source current. -/
def sourceCurrent (t : ℝ) : ℝ :=
  t*(deriv thetaCuspFullSource t)^2-
    t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t+
    thetaCuspFullSource t*deriv thetaCuspFullSource t

theorem sourceCurrent_eq (t : ℝ) :
    sourceCurrent t =
      (-t*iteratedDeriv 2 thetaCuspLogSource t-thetaCuspLogDecaySlope t)*thetaCuspFullSource t^2 := by
  dsimp only [sourceCurrent]
  rw [source_second_eq, source_deriv_eq]
  ring

theorem sourceCurrent_pos {t : ℝ} (ht : 0 < t) : 0 < sourceCurrent t := by
  rw [sourceCurrent_eq]
  exact mul_pos (slope_current_pos ht) (sq_pos_of_pos (thetaCuspFullSource_pos_all t))

private theorem weighted_second_integrable :
    Integrable (fun t => t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t) :=
  weighted_product_integrable thetaCuspSchwartzReal
    (SchwartzMap.derivCLM ℝ ℝ (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal))

theorem sourceCurrent_integrable : Integrable sourceCurrent :=
  (weighted_derivative_square_integrable.sub weighted_second_integrable).add
    source_times_derivative_integrable

/-- Integration by parts retains the endpoint source square exactly. -/
theorem weighted_second_integral :
    (∫ t in Ioi 0, t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t) =
      thetaCuspFullSource 0^2/2-derivativeMass := by
  let b : ℝ → ℝ := fun t => thetaCuspFullSource t*deriv thetaCuspFullSource t+
    t*(deriv thetaCuspFullSource t)^2+
    t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t
  have hd (t : ℝ) : HasDerivAt
      (fun t => t*thetaCuspFullSource t*deriv thetaCuspFullSource t) (b t) t := by
    convert! ((hasDerivAt_id t).mul (source_hasDerivAt t)).mul
      (source_deriv_hasDerivAt t) using 1
    simp only [b, Pi.mul_apply, id_eq]
    ring
  have hi : Integrable b := (source_times_derivative_integrable.add
    weighted_derivative_square_integrable).add weighted_second_integrable
  have hb := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (fun t _ => hd t) hi.integrableOn
    (weighted_product_zero thetaCuspSchwartzReal
      (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal))
  simp only [b, zero_mul, zero_sub, neg_zero] at hb
  have hiab : Integrable (fun t => thetaCuspFullSource t*deriv thetaCuspFullSource t+
      t*(deriv thetaCuspFullSource t)^2) :=
    source_times_derivative_integrable.add weighted_derivative_square_integrable
  rw [integral_add hiab.integrableOn weighted_second_integrable.integrableOn,
    integral_add source_times_derivative_integrable.integrableOn
      weighted_derivative_square_integrable.integrableOn,
    source_times_derivative_tail] at hb
  change -thetaCuspFullSource 0^2/2+derivativeMass+
    (∫ t in Ioi 0, t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t) = 0 at hb
  linarith

/-- Exact positive-current representation of the actual center confluent entry. -/
theorem centerEntry_eq_integral : centerEntry = ∫ t in Ioi 0, sourceCurrent t := by
  unfold sourceCurrent
  have hisub : Integrable (fun t => t*(deriv thetaCuspFullSource t)^2-
      t*thetaCuspFullSource t*deriv (deriv thetaCuspFullSource) t) :=
    weighted_derivative_square_integrable.sub weighted_second_integrable
  rw [integral_add hisub.integrableOn source_times_derivative_integrable.integrableOn,
    integral_sub weighted_derivative_square_integrable.integrableOn weighted_second_integrable.integrableOn,
    weighted_second_integral, source_times_derivative_tail]
  dsimp only [centerEntry, derivativeMass]
  ring

/-- Nondegeneracy at the actual center, without an assumed projection or RH sign. -/
theorem centerEntry_pos : 0 < centerEntry := by
  rw [centerEntry_eq_integral]
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ sourceCurrent t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (sourceCurrent_pos ht).le
  apply (integral_pos_iff_support_of_nonneg_ae hnn sourceCurrent_integrable.integrableOn).mpr
  have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioi 0) := by
    simp only [Measure.restrict_apply measurableSet_Ioi, inter_self, Real.volume_Ioi,
      ENNReal.zero_lt_top]
  exact lt_of_lt_of_le hm (measure_mono fun t ht => (sourceCurrent_pos ht).ne')

end RHTower.ThetaConfluent
