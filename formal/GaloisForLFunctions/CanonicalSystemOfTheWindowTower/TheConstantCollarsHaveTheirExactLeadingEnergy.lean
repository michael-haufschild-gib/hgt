import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheConstantCollarsReadTheWeilTraces

/-!
# The exact leading energy of the two constant collars

The full two-collar floor and the matching upper estimate place the energy
of every fixed linear combination between two logarithmic bounds. The
bounded crossing terms therefore disappear after normalization.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy
namespace WeilHilbertBeforeContact

/-- Scalar multiples of an interval source retain its interval support. -/
private theorem intervalSource_smul_support (α : ℂ) (lo hi : ℝ) :
    ∀ᵐ x ∂volume, x ∉ Icc lo hi →
      (α • logarithmicIntervalSource lo hi : RealLineL2) x = 0 := by
  filter_upwards [Lp.coeFn_smul α (logarithmicIntervalSource lo hi),
    logarithmicIntervalSource_coeFn lo hi] with x hs hx hout
  rw [hs, Pi.smul_apply, hx, indicator_of_notMem (fun hin => hout ⟨hin.1.le, hin.2⟩),
    smul_zero]

/-- The complete Weil form has the sharp logarithmic lower energy for a
weighted pair of constant collars in a fixed enclosing aperture. -/
theorem constantCollar_pair_energy_lower {a c : PrecontactAperture}
    (hac : a.1.1 ≤ c.1.1) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (l r : WeilHilbertBeforeContact c)
    (hl : ccmArchimedeanFormEmbedding c.1 (toForm c l) =
      logarithmicIntervalSource (-a.1.1-h) (-a.1.1))
    (hr : ccmArchimedeanFormEmbedding c.1 (toForm c r) =
      logarithmicIntervalSource a.1.1 (a.1.1+h)) (α β : ℂ) :
    h*(Real.log (1/h)-weilTwoCollarEnergyError a c)*(‖α‖^2+‖β‖^2) ≤
      ‖α • l+β • r‖^2 := by
  have hl' : ccmArchimedeanFormEmbedding c.1 (toForm c (α • l)) =
      α • logarithmicIntervalSource (-a.1.1-h) (-a.1.1) := by rw [map_smul, map_smul, hl]
  have hr' : ccmArchimedeanFormEmbedding c.1 (toForm c (β • r)) =
      β • logarithmicIntervalSource a.1.1 (a.1.1+h) := by rw [map_smul, map_smul, hr]
  have hls : ∀ᵐ x ∂volume, x ∉ Icc (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding c.1 (toForm c (α • l)) x = 0 := by
    rw [hl']; exact intervalSource_smul_support α _ _
  have hrs : ∀ᵐ x ∂volume, x ∉ Icc a.1.1 (a.1.1+h) →
      ccmArchimedeanFormEmbedding c.1 (toForm c (β • r)) x = 0 := by
    rw [hr']; exact intervalSource_smul_support β _ _
  have hmassL : ‖ccmArchimedeanFormToAperture c.1 (toForm c (α • l))‖^2 = ‖α‖^2*h := by
    change ‖ccmArchimedeanFormEmbedding c.1 (toForm c (α • l))‖^2 = _
    rw [hl', norm_smul, mul_pow, norm_logarithmicIntervalSource_sq (by linarith only [hh])]
    congr 1
    ring
  have hmassR : ‖ccmArchimedeanFormToAperture c.1 (toForm c (β • r))‖^2 = ‖β‖^2*h := by
    change ‖ccmArchimedeanFormEmbedding c.1 (toForm c (β • r))‖^2 = _
    rw [hr', norm_smul, mul_pow, norm_logarithmicIntervalSource_sq (by linarith only [hh]),
      add_sub_cancel_left]
  have hf := twoCollar_energy_floor hac hh hh1 (0 : WeilHilbertBeforeContact a)
    (α • l) (β • r) hls hrs
  rw [hmassL, hmassR, map_zero, add_zero, add_comm (β • r)] at hf
  convert hf using 1 <;> ring

/-- The same fixed lower error controls every smaller enlarged window. -/
theorem constantCollar_pair_energy_lower_in_enclosure {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (l r : WeilHilbertBeforeContact b)
    (hl : ccmArchimedeanFormEmbedding b.1 (toForm b l) =
      logarithmicIntervalSource (-a.1.1-h) (-a.1.1))
    (hr : ccmArchimedeanFormEmbedding b.1 (toForm b r) =
      logarithmicIntervalSource a.1.1 (a.1.1+h)) (α β : ℂ) :
    h*(Real.log (1/h)-weilTwoCollarEnergyError a c)*(‖α‖^2+‖β‖^2) ≤
      ‖α • l+β • r‖^2 := by
  have he (u : WeilHilbertBeforeContact b) :
      ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc u)) =
        ccmArchimedeanFormEmbedding b.1 (toForm b u) := by
    rw [toForm_inclusion]
    exact ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hbc (toForm b u))
  have hf := constantCollar_pair_energy_lower (hab.trans hbc) hh hh1
    (inclusion hbc l) (inclusion hbc r) ((he l).trans hl) ((he r).trans hr) α β
  simpa only [← map_smul, ← map_add, (inclusion hbc).norm_map] using hf

/-- Every admitted constant collar pair has the same normalized leading
quadratic energy, uniformly over the intermediate aperture. -/
theorem eventually_constantCollar_energy_lt {a c : PrecontactAperture}
    (α β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1)
      (l r : WeilHilbertBeforeContact b),
      ccmArchimedeanFormEmbedding b.1 (toForm b l) =
        logarithmicIntervalSource (-a.1.1-h) (-a.1.1) →
      ccmArchimedeanFormEmbedding b.1 (toForm b r) =
        logarithmicIntervalSource a.1.1 (a.1.1+h) →
      |‖(Real.sqrt (Real.log (1/h)) : ℂ)⁻¹ • (α • l+β • r)‖^2/h-
        (‖α‖^2+‖β‖^2)| < ε := by
  let L : ℝ → ℝ := fun h => Real.log (1/h)
  let S := ‖α‖^2+‖β‖^2
  let D := 3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1
  let E := weilTwoCollarEnergyError a c
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [L, one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have he (d : ℝ) : Tendsto (fun h => d/L h) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hL).const_mul d
  have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
  have hl : Tendsto (fun h => (1-E/L h)*S) (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    simpa only [sub_zero, one_mul] using (hOne.sub (he E)).mul_const S
  have hu : Tendsto (fun h => (1+D/L h)*S) (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    simpa only [add_zero, one_mul] using (hOne.add (he D)).mul_const S
  filter_upwards [hl.eventually (Ioi_mem_nhds (sub_lt_self S hε)),
    hu.eventually (Iio_mem_nhds (show S < S+ε from by linarith only [hε])), self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with h hlo hup hh hh1
  change 0 < h at hh
  intro b hab hbc l r hlr hrr
  have hLp : 0 < L h := Real.log_pos ((one_lt_div hh).mpr hh1)
  have hs : 0 < Real.sqrt (L h) := Real.sqrt_pos.mpr hLp
  let v := α • l+β • r
  let w := (Real.sqrt (L h) : ℂ)⁻¹ • v
  have hn : ‖w‖^2/h = ‖v‖^2/(h*L h) := by
    dsimp only [w]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs, mul_pow, inv_pow, Real.sq_sqrt hLp.le]
    ring
  have hf := constantCollar_pair_energy_lower_in_enclosure hab hbc hh hh1.le l r hlr hrr α β
  have hc := constantCollar_pair_energy_upper_in_enclosure hbc a.1.2 hh hh1.le l r hlr hrr α β
  have hlow : (1-E/L h)*S ≤ ‖w‖^2/h := by
    rw [hn]
    calc
      _ = (h*(L h-E)*S)/(h*L h) := by field_simp [hh.ne', hLp.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hf (mul_nonneg hh.le hLp.le)
  have hupp : ‖w‖^2/h ≤ (1+D/L h)*S := by
    rw [hn]
    have hc' : ‖v‖^2 ≤ h*(L h+D)*S := by
      convert hc using 1 <;> dsimp only [v, L, D, S] <;> ring
    calc
      _ ≤ (h*(L h+D)*S)/(h*L h) := div_le_div_of_nonneg_right hc' (mul_nonneg hh.le hLp.le)
      _ = _ := by field_simp [hh.ne', hLp.ne']
  change |‖w‖^2/h-S| < ε
  exact abs_lt.mpr ⟨by linarith only [hlo, hlow], by linarith only [hup, hupp]⟩

#print axioms constantCollar_pair_energy_lower_in_enclosure
#print axioms eventually_constantCollar_energy_lt
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
