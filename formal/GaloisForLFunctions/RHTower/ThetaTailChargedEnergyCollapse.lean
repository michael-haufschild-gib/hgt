import GaloisForLFunctions.RHTower.ThetaCuspChargedSourceMeanSquare
import GaloisForLFunctions.RHTower.ThetaTailReflectedCauchyObstruction
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Charged-cusp collapse of the complete theta tail energy

The compact `N^9` source bound and a uniform integrable tail prove that the
actual Hermitian diagonal is little-o of the squared boundary source. Any
positive source comparison must therefore have a divergent charged boundary
rate. Every analytic scalar feature dominated on a real tail vanishes relative
to the complete source at this cusp.

These are unconditional source-specific boundary laws. Positivity of the
unsubtracted kernel and RH remain unresolved.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower.ThetaCuspBoundaryAudit
open DominatedL2Sections

/-- Compact integral collapse plus a fixed integrable tail controls total mass. -/
private theorem integral_Ioi_tendsto_zero_of_compact
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hi : ∀ N, 0 < N → IntegrableOn (f N) (Ioi 0))
    (hg : IntegrableOn g (Ioi 0))
    (hdom : ∀ N, 0 < N → ∀ s, 0 < s → 0 ≤ f N s ∧ f N s ≤ g s)
    (hhead : ∀ S : ℝ, 0 ≤ S →
      Tendsto (fun N => ∫ s in (0:ℝ)..S, f N s) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ s in Ioi (0:ℝ), f N s) atTop (𝓝 0) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact ha.trans_le (setIntegral_nonneg measurableSet_Ioi (fun s hs => (hdom N hN s hs).1))
  · intro e he
    have ht : Tendsto (fun S : ℝ => ∫ s in Ioi S, g s) atTop (𝓝 0) :=
      tendsto_integral_Ioi_zero tendsto_id
    obtain ⟨S, hS, htail⟩ := ((eventually_ge_atTop (0:ℝ)).and
      (ht.eventually (gt_mem_nhds (half_pos he)))).exists
    filter_upwards [eventually_gt_atTop (0:ℕ),
      (hhead S hS).eventually (gt_mem_nhds (half_pos he))] with N hN hsmall
    have htailN : (∫ s in Ioi S, f N s) ≤ ∫ s in Ioi S, g s := by
      apply setIntegral_mono_on ((hi N hN).mono_set (Ioi_subset_Ioi hS))
        (hg.mono_set (Ioi_subset_Ioi hS)) measurableSet_Ioi
      intro s hs
      exact (hdom N hN s (hS.trans_lt hs)).2
    rw [← intervalIntegral.integral_interval_add_Ioi (hi N hN)
      ((hi N hN).mono_set (Ioi_subset_Ioi hS))]
    linarith only [hsmall, htail, htailN]

/-- The normalized actual diagonal density, before integration. -/
def chargedEnergyDensity (N : ℕ) (s : ℝ) : ℝ :=
  4*((chargedPoint (1/(N:ℝ)^2)).re+s)*
    ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2/(N:ℝ)^10

private theorem chargedEnergyDensity_integrable (N : ℕ) (hN : 0 < N) :
    IntegrableOn (chargedEnergyDensity N) (Ioi 0) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  exact (completeThetaSource.integrable_weighted_source_norm
    (chargedPoint_mem_strip (by positivity))).div_const _

private theorem chargedEnergyDensity_nonneg (N : ℕ) (hN : 0 < N)
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ chargedEnergyDensity N s := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 < 1/(N:ℝ)^2 := by positivity
  have hp1 : 1/(N:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hN1)
  have hr := (chargedPoint_re_bounds hp hp1).1
  unfold chargedEnergyDensity
  positivity

private theorem chargedEnergyDensity_le (N : ℕ) (hN : 0 < N)
    {s : ℝ} (hs : 0 ≤ s) :
    chargedEnergyDensity N s ≤ 12*486^2*Real.exp (-(1/2)*s) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 < 1/(N:ℝ)^2 := by positivity
  have hp1 : 1/(N:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hN1)
  have hr := (chargedPoint_re_bounds hp hp1).2
  have hsq : ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2 ≤
      486^2*(N:ℝ)^10*Real.exp (-s) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (chargedPoint_source_horizontal_upper N hN s) 2
    rw [mul_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul] at h
    simp only [Nat.cast_ofNat] at h
    simpa only [show 2*(-s/2) = -s by ring] using h
  have hlin : 1+s ≤ 3*Real.exp (s/2) := by
    have h1 := Real.add_one_le_exp (s/2)
    have h0 := Real.one_le_exp (show 0 ≤ s/2 by positivity)
    linarith only [h1, h0]
  unfold chargedEnergyDensity
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (N:ℝ)^10)).mpr
  calc
    _ ≤ 4*(1+s)*(486^2*(N:ℝ)^10*Real.exp (-s)) :=
      mul_le_mul (by linarith only [hr]) hsq (sq_nonneg _) (by positivity)
    _ ≤ 4*(3*Real.exp (s/2))*(486^2*(N:ℝ)^10*Real.exp (-s)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlin (by norm_num)) (by positivity)
    _ = _ := by
      rw [show 4*(3*Real.exp (s/2))*(486^2*(N:ℝ)^10*Real.exp (-s)) =
        12*486^2*(N:ℝ)^10*(Real.exp (s/2)*Real.exp (-s)) by ring,
        ← Real.exp_add, show s/2 + -s = -(1/2)*s by ring]
      ring

private theorem chargedEnergyDensity_compact_tendsto {S : ℝ} (hS : 0 ≤ S) :
    Tendsto (fun N => ∫ s in (0:ℝ)..S, chargedEnergyDensity N s) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := chargedSource_compact_integral_le hS
  have hmajor : Tendsto (fun N : ℕ => (4*(1+S)*B)/(N:ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact intervalIntegral.integral_nonneg hS (fun s hs => chargedEnergyDensity_nonneg N hN hs.1)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have hp : 0 < 1/(N:ℝ)^2 := by positivity
    have hp1 : 1/(N:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hN1)
    have hr := (chargedPoint_re_bounds hp hp1).2
    have hcont : ContinuousOn (fun s : ℝ => thetaCuspStripSource
        (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))) (uIcc 0 S) := by
      apply differentiableOn_thetaCuspStripSource.continuousOn.comp (by fun_prop)
      intro s hs
      simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero]
        using chargedPoint_mem_strip hp
    have hnorm : IntervalIntegrable (fun s : ℝ =>
        ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2) volume 0 S :=
      (hcont.norm.pow 2).intervalIntegrable
    have hd : IntervalIntegrable (chargedEnergyDensity N) volume 0 S := by
      apply ContinuousOn.intervalIntegrable
      unfold chargedEnergyDensity
      exact ((continuousOn_const.mul (continuousOn_const.add continuousOn_id)).mul
        (hcont.norm.pow 2)).div_const _
    calc
      _ ≤ ∫ s in (0:ℝ)..S, (4*(1+S)/(N:ℝ)^10)*
          ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2 := by
        apply intervalIntegral.integral_mono_on hS hd (hnorm.const_mul _)
        intro s hs
        unfold chargedEnergyDensity
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by linarith only [hr, hs.2]) (by positivity))
          (sq_nonneg _)
      _ = (4*(1+S)/(N:ℝ)^10)*(∫ s in (0:ℝ)..S,
          ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (4*(1+S)/(N:ℝ)^10)*(B*(N:ℝ)^9) :=
        mul_le_mul_of_nonneg_left (hb N hN) (by positivity)
      _ = _ := by field_simp

/-- Charged-cusp diagonal energy is little-o of `N^10`. -/
theorem chargedPoint_kernel_diagonal_normalized_tendsto :
    Tendsto (fun N : ℕ =>
      (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
        (chargedPoint (1/(N:ℝ)^2))).re/(N:ℝ)^10) atTop (𝓝 0) := by
  have h := integral_Ioi_tendsto_zero_of_compact chargedEnergyDensity
    (fun s => 12*486^2*Real.exp (-(1/2)*s)) chargedEnergyDensity_integrable
    ((integrableOn_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0) (0:ℝ)).const_mul _)
    (fun N hN s hs => ⟨chargedEnergyDensity_nonneg N hN hs.le,
      chargedEnergyDensity_le N hN hs.le⟩)
    (fun S hS => chargedEnergyDensity_compact_tendsto hS)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  rw [completeThetaSource.realization_diagonal_integral (chargedPoint_mem_strip (by positivity))]
  unfold chargedEnergyDensity
  rw [integral_div]
  rfl


/-- Positivity here follows from the exact weighted source integral. -/
theorem chargedPoint_kernel_diagonal_nonneg (N : ℕ) (hN : 0 < N) :
    0 ≤ (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
      (chargedPoint (1/(N:ℝ)^2))).re := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 < 1/(N:ℝ)^2 := by positivity
  have hp1 : 1/(N:ℝ)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hN1)
  have hr := (chargedPoint_re_bounds hp hp1).1
  rw [completeThetaSource.realization_diagonal_integral (chargedPoint_mem_strip hp)]
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  change 0 ≤ 4*((chargedPoint (1/(N:ℝ)^2)).re+s)*
    ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ))‖^2
  exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hr hs.le)) (sq_nonneg _)

/-- The boundary source is nonzero at every point of the charged sequence. -/
theorem chargedPoint_source_norm_pos (N : ℕ) (hN : 0 < N) :
    0 < ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖ := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  exact lt_of_lt_of_le (by positivity) (chargedPoint_source_lower N hN)

/-- C10: the actual tail diagonal collapses relative to the charged boundary source. -/
theorem chargedPoint_kernel_source_ratio_tendsto :
    Tendsto (fun N : ℕ =>
      (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
        (chargedPoint (1/(N:ℝ)^2))).re /
      ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2) atTop (𝓝 0) := by
  let A := 12*Real.pi^2*Real.exp (-4*Real.pi)
  have hA : 0 < A := by dsimp [A]; positivity
  have ht := chargedPoint_kernel_diagonal_normalized_tendsto.div_const (A^2)
  simp only [zero_div] at ht
  refine squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact div_nonneg (chargedPoint_kernel_diagonal_nonneg N hN) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hl := chargedPoint_source_lower N hN
    change A*(N:ℝ)^5 ≤ _ at hl
    have hl2 : A^2*(N:ℝ)^10 ≤
        ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 := by
      simpa only [mul_pow, ← pow_mul] using
        pow_le_pow_left₀ (by positivity : 0 ≤ A*(N:ℝ)^5) hl 2
    calc
      _ ≤ (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
          (chargedPoint (1/(N:ℝ)^2))).re/(A^2*(N:ℝ)^10) :=
        div_le_div_of_nonneg_left (chargedPoint_kernel_diagonal_nonneg N hN)
          (by positivity) hl2
      _ = _ := by ring


/-- A valid positive source comparison forces its charged boundary rate to diverge. -/
theorem chargedPoint_comparison_rate_tendsto_atTop {c : ℝ} (hc : 0 < c)
    (u : ℕ → ℝ)
    (hcomp : ∀ᶠ N : ℕ in atTop,
      c*‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2 ≤
        u N*(completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
          (chargedPoint (1/(N:ℝ)^2))).re) :
    Tendsto u atTop atTop := by
  let r : ℕ → ℝ := fun N =>
    (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
      (chargedPoint (1/(N:ℝ)^2))).re /
      ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2
  have hbound : ∀ᶠ N : ℕ in atTop, 0 < r N ∧ c/(r N) ≤ u N := by
    filter_upwards [hcomp, eventually_gt_atTop (0:ℕ)] with N hcompN hN
    have hp := sq_pos_of_pos (chargedPoint_source_norm_pos N hN)
    have hr0 : 0 ≤ r N := div_nonneg (chargedPoint_kernel_diagonal_nonneg N hN) hp.le
    have hcr : c ≤ u N*r N := by
      apply (le_div_iff₀ hp).mpr hcompN |>.trans_eq
      dsimp [r]
      ring
    have hr : 0 < r N := lt_of_le_of_ne hr0 (by
      intro he
      rw [← he, mul_zero] at hcr
      exact (not_le_of_gt hc) hcr)
    exact ⟨hr, (div_le_iff₀ hr).mpr hcr⟩
  have ht : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨chargedPoint_kernel_source_ratio_tendsto,
      hbound.mono (fun N hN => hN.1)⟩
  have hi : Tendsto (fun N => c/(r N)) atTop atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using
      ht.inv_tendsto_nhdsGT_zero.const_mul_atTop hc
  exact tendsto_atTop_mono' atTop (hbound.mono (fun N hN => hN.2)) hi


/-- Every analytic feature dominated by the actual kernel on a real tail must
vanish relative to the complete source at the charged cusp. -/
theorem scalar_comparison_charged_boundary_vanishing (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f thetaCuspStrip) {c : ℝ} (hc : 0 < c) (a : ℝ)
    (hpack : ∀ (S : Finset (Complex.ofReal '' Ioi a))
      (d : (Complex.ofReal '' Ioi a) → ℂ),
      2*c*‖∑ i ∈ S, d i*f i.val‖^2 ≤
        (∑ i ∈ S, ∑ j ∈ S,
          star (d j)*d i*((2*thetaTailFirstMomentKernel i.val.re j.val.re:ℝ):ℂ)).re) :
    Tendsto (fun N : ℕ => f (chargedPoint (1/(N:ℝ)^2)) /
      thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))) atTop (𝓝 0) := by
  let F : ℕ → ℂ := fun N => f (chargedPoint (1/(N:ℝ)^2)) /
    thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))
  have ht := chargedPoint_kernel_source_ratio_tendsto.div_const (2*c)
  simp only [zero_div] at ht
  have hsquare : Tendsto (fun N => ‖F N‖^2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _) ?_ ht
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    have hNr : (0:ℝ) < N := by exact_mod_cast hN
    have hp := sq_pos_of_pos (chargedPoint_source_norm_pos N hN)
    have hbound := scalar_boundary_admissibility f hf c a hpack
      (chargedPoint_mem_strip (show 0 < 1/(N:ℝ)^2 by positivity))
    have hb' : ‖f (chargedPoint (1/(N:ℝ)^2))‖^2 ≤
        (completeThetaSource.realization.kernel (chargedPoint (1/(N:ℝ)^2))
          (chargedPoint (1/(N:ℝ)^2))).re/(2*c) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
      exact (mul_comm _ _).trans_le hbound
    have hdiv := div_le_div_of_nonneg_right hb' hp.le
    dsimp [F]
    rw [norm_div, div_pow]
    exact hdiv.trans_eq (by rw [div_div, div_div, mul_comm (2*c)])
  have hnorm : Tendsto (fun N => ‖F N‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsquare.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

private theorem chargedPoint_re_uniform_lower (eps : ℝ) :
    Real.log 2/2 ≤ (chargedPoint eps).re := by
  have hlo : (2:ℝ) ≤ ‖(eps:ℂ)+2*Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((eps:ℂ)+2*Complex.I)
  simp only [chargedPoint, Complex.div_ofNat_re, Complex.log_re]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by norm_num) hlo) (by norm_num)

/-- The normalized horizontal source section converges strongly in weighted L². -/
theorem chargedPoint_weighted_source_energy_tendsto :
    Tendsto (fun N : ℕ => ∫ s : ℝ in Ioi 0, (1+s)*
      ‖thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2)+(s:ℂ)) /
        thetaCuspStripSource (chargedPoint (1/(N:ℝ)^2))‖^2) atTop (𝓝 0) := by
  let r := Real.log 2/2
  let C := 1+r⁻¹
  have hr : 0 < r := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hC : 0 ≤ C := add_nonneg (by norm_num) (inv_pos.mpr hr).le
  have ht := chargedPoint_kernel_source_ratio_tendsto.const_mul C
  simp only [mul_zero] at ht
  refine squeeze_zero' (Eventually.of_forall fun N =>
    setIntegral_nonneg measurableSet_Ioi (fun s hs => mul_nonneg (add_nonneg (by norm_num) hs.le)
      (sq_nonneg _))) ?_ ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  let z := chargedPoint (1/(N:ℝ)^2)
  let d := ‖thetaCuspStripSource z‖^2
  let f : ℝ → ℝ := fun s => (1+s)*‖thetaCuspStripSource (z+(s:ℂ))/thetaCuspStripSource z‖^2
  let g : ℝ → ℝ := fun s => 4*(z.re+s)*‖thetaCuspStripSource (z+(s:ℂ))‖^2/d
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hz : z ∈ thetaCuspStrip := chargedPoint_mem_strip (by positivity)
  have hd : 0 < d := sq_pos_of_pos (chargedPoint_source_norm_pos N hN)
  have hzr : r ≤ z.re := chargedPoint_re_uniform_lower _
  have hz0 : 0 ≤ z.re := hr.le.trans hzr
  have hbound (s : ℝ) (hs : 0 < s) : f s ≤ C*g s := by
    have hscale : 1 ≤ r⁻¹*z.re := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hr).mpr (by simpa using hzr)
    have hweight : 1+s ≤ C*(z.re+s) := by
      calc
        1+s ≤ r⁻¹*z.re+s := add_le_add hscale le_rfl
        _ ≤ (1+r⁻¹)*z.re+(1+r⁻¹)*s := add_le_add
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hz0)
          (le_mul_of_one_le_left hs.le
            (le_add_of_nonneg_right (inv_nonneg.mpr hr.le)))
        _ = _ := (mul_add _ _ _).symm
    have hweight4 : 1+s ≤ C*(4*(z.re+s)) := hweight.trans (by
      apply mul_le_mul_of_nonneg_left _ hC
      have hzplus : 0 ≤ z.re+s := add_nonneg hz0 hs.le
      linarith only [hzplus])
    dsimp [f, g]
    rw [norm_div, div_pow]
    change (1+s)*(‖thetaCuspStripSource (z+(s:ℂ))‖^2/d) ≤ _
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hweight4
      (div_nonneg (sq_nonneg ‖thetaCuspStripSource (z+(s:ℂ))‖) hd.le)
  have hg : IntegrableOn g (Ioi 0) :=
    (completeThetaSource.integrable_weighted_source_norm hz).div_const d
  have hfc : ContinuousOn f (Ioi 0) := by
    have hphi : ContinuousOn (fun s : ℝ => thetaCuspStripSource (z+(s:ℂ))) (Ioi 0) := by
      apply differentiableOn_thetaCuspStripSource.continuousOn.comp (by fun_prop)
      intro s hs
      simpa only [thetaCuspStrip, mem_setOf_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz
    exact (continuousOn_const.add continuousOn_id).mul ((hphi.div_const _).norm.pow 2)
  have hf : IntegrableOn f (Ioi 0) := (hg.const_mul C).mono'
    (hfc.aestronglyMeasurable measurableSet_Ioi) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hf0 : 0 ≤ f s := mul_nonneg (add_nonneg (by norm_num) hs.le) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hf0]
      exact hbound s hs)
  calc
    _ = ∫ s in Ioi (0:ℝ), f s := rfl
    _ ≤ ∫ s in Ioi (0:ℝ), C*g s :=
      setIntegral_mono_on hf (hg.const_mul C) measurableSet_Ioi hbound
    _ = C*((completeThetaSource.realization.kernel z z).re/d) := by
      rw [integral_const_mul, completeThetaSource.realization_diagonal_integral hz]
      dsimp [g]
      rw [integral_div]
      rfl
    _ = _ := rfl


end RHTower.ThetaCuspBoundaryAudit
