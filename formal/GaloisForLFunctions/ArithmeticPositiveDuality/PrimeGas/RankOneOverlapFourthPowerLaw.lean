import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SurvivingExponentAndOverlapDivisor

/-!
# Krein heat-drop Mellin bridge, UV-regularized rank-one fourth-power equivalence, and high-shell obstruction at left-strip zeros

At any open-strip zero of the complex dyadic overlap integral
`∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0`, we analyze how vanishing of the integral
transfers to fourth-power trace bounds across conserving rank-one omissions `v : MissingWave`:

1. **Exact Krein spectral heat-drop Mellin bridge (`bandHeatDrop`, `bandHeatDrop_bounds`,
   `mellin_bandHeatDrop_eq`, `integral_mul_bandHeatDrop_eq_traceLoss`,
   `jointSurvivingPartition_eq_dyadicOverlap_sub_heatDrop`)**:
   Every `b : SpectralBand r` defines a nonnegative spectral heat drop `bandHeatDrop b u` on
   `(0, ∞)` satisfying the Pauli/interlacing ceiling `0 ≤ bandHeatDrop b u ≤ r * exp(-u)` (so at
   rank one, `0 ≤ bandHeatDrop b u ≤ exp(-u) ≤ 1`), with exact Mellin transform
   `∫_{u > 0} u^{s-1} bandHeatDrop(b, u) = Γ(s) relativePartition(b, s)` (`Re s > 0`), exact first
   moment `∫_{u > 0} u · bandHeatDrop(b, u) = traceLoss(projected P)`, and exact identity
   `jointSurvivingPartition b s = (∫ dyadicOverlapContrast / u) / (C^{s/2}(1 - 2^{1-s})Γ(s))
     - ((2^s - 1)/Γ(s)) ∫ u^{s-1} bandHeatDrop(b, u)`.

2. **Sharp bathtub moment inequality and UV-regularized rank-one fourth-power equivalence
   (`bathtub_moment_bound`, `jointSurviving_bathtub_bound_of_integral_eq_zero`,
   `uvRegularRankOne_of_half_le_re`, `uvRegularRankOne_fourthPower_iff_integral_eq_zero`)**:
   Whenever the dyadic overlap integral vanishes (`0 < Re s < 1`), rearrangement on `(0, ∞)` yields
   `‖jointSurvivingPartition b_v s‖^{2 / Re s} ≤ 2 (‖2^s - 1‖ / (Re s · ‖Γ(s)‖))^{2 / Re s} lineLoss v`.
   On every UV-regularized rank-one conserving class `uvRegularRankOne s hs0 Λ` (`Λ > 0`, which
   still accumulates at `hotEdge 1` with arbitrarily small positive `lineLoss`), vanishing of the
   dyadic overlap integral is **necessary and sufficient** (`↔`) for the fourth-power bound
   `‖jointSurvivingPartition b_v s‖^4 ≤ K · lineLoss v.val` across all `0 < Re s < 1` (including
   `0 < Re s < 1/2` and `|Im s| > 84.5`), while `uvRegularRankOne s hs0 1` holds universally on
   `1/2 ≤ Re s ≤ 2`.

3. **Unconditional high-shell obstruction on `0 < Re s < 1/2` and reflection closure above `84.5`
   (`blockSpectrum_fourthPower_ratio_of_integral_eq_zero`,
   `tendsto_blockSpectrum_fourthPower_ratio_atTop_of_integral_eq_zero`,
   `exists_missingWave_fourthPower_violation_of_re_lt_half`,
   `rankOne_fourthPower_from_integral_iff_integral_ne_zero`,
   `rh_iff_rankOne_fourthPower_at_left_dyadicOverlap_zeros_above_eightyFour_and_half`)**:
   When the UV cap is removed on `0 < Re s < 1/2`, even under vanishing of the dyadic overlap
   integral, single-shell deletions `blockSpectrum N 1 ∈ closure(physicalSpectra 1)` satisfy
   `‖jointSurvivingPartition(blockSpectrum N 1, s)‖^4 / traceLoss_N = ‖2^s - 1‖^4 (N+1)^{2 - 4 Re s} → +∞`.
   Hence at every `0 < Re s < 1/2`, unconstrained `MissingWave` unconditionally violates every
   fourth-power bound (`0 < lineLoss v.val < ε`), making the integral-to-fourth-power implication
   at each left-strip candidate above `84.5` pointwise equivalent to nonvanishing of the integral
   there, and globally equivalent (via left-zero exponent exclusion + functional reflection) to
   `RiemannHypothesis`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter MeasureTheory Set Topology
open InverseSpectrum.ShellMixing
open AntipodalSpectrum AntipodalSpectrum.ComplementaryHalves
open scoped ComplexConjugate Topology

/-! ### Part 1: Krein spectral heat drop and exact Mellin–overlap bridge -/

/-- Single-shell heat drop `exp(-u / occupationWeight n) - exp(-u / b_n)` for `b : SpectralBand r`. -/
def bandHeatDropTerm {r : ℕ} (b : SpectralBand r) (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-((occupationWeight n)⁻¹ * u)) - Real.exp (-(((b n).val)⁻¹ * u))

/-- Total Krein spectral heat drop `∑' n, bandHeatDropTerm b n u` on `(0, ∞)`. -/
def bandHeatDrop {r : ℕ} (b : SpectralBand r) (u : ℝ) : ℝ :=
  ∑' n : ℕ, bandHeatDropTerm b n u

private theorem inv_occupationWeight_eq (n : ℕ) :
    (occupationWeight n)⁻¹ = (n : ℝ) + 1 := by
  rw [occupationWeight_eq, inv_inv]

private theorem bandHeatDropTerm_nonneg_and_le_edge {r : ℕ} (b : SpectralBand r) (n : ℕ)
    {u : ℝ} (hu : 0 < u) :
    0 ≤ bandHeatDropTerm b n u ∧
      bandHeatDropTerm b n u ≤
        Real.exp (-((occupationWeight n)⁻¹ * u)) -
          Real.exp (-((occupationWeight (n + r))⁻¹ * u)) := by
  have hb_pos : 0 < (b n).val := band_pos b n
  have hocc_r_pos : 0 < occupationWeight (n + r) := occupationWeight_pos (n + r)
  have hinv_lo : (occupationWeight n)⁻¹ ≤ ((b n).val)⁻¹ :=
    inv_anti₀ hb_pos (b n).property.2
  have hinv_hi : ((b n).val)⁻¹ ≤ (occupationWeight (n + r))⁻¹ :=
    inv_anti₀ hocc_r_pos (b n).property.1
  unfold bandHeatDropTerm
  refine ⟨sub_nonneg.mpr ?_, sub_le_sub_left ?_ _⟩
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem hasSum_edge_heatDrop (r : ℕ) {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ =>
      Real.exp (-((occupationWeight n)⁻¹ * u)) -
        Real.exp (-((occupationWeight (n + r))⁻¹ * u)))
      (∑ j ∈ Finset.range r, Real.exp (-((occupationWeight j)⁻¹ * u))) := by
  let a : ℕ → ℝ := fun n => Real.exp (-((occupationWeight n)⁻¹ * u))
  have ha : Antitone a := by
    intro i j hij
    dsimp only [a]
    apply Real.exp_le_exp.mpr
    have hinv : (occupationWeight i)⁻¹ ≤ (occupationWeight j)⁻¹ :=
      inv_anti₀ (occupationWeight_pos j) (occupationWeight_antitone hij)
    nlinarith
  have h0 : Tendsto a atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => -(((n : ℝ) + 1) * u)) atTop atBot := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact tendsto_neg_atTop_atBot.comp (h1.atTop_mul_const hu)
    refine (Real.tendsto_exp_atBot.comp hlin).congr fun n => ?_
    dsimp only [Function.comp_apply, a]
    rw [inv_occupationWeight_eq]
  exact hasSum_shift_drop ha h0 r

/-- **Summability, nonnegativity, and Pauli/interlacing ceiling of `bandHeatDrop`:**
for every `b : SpectralBand r` and `u > 0`, `bandHeatDropTerm b · u` is summable and
`0 ≤ bandHeatDrop b u ≤ ∑_{j < r} exp(-(j + 1) u) ≤ r * exp(-u)`. -/
theorem bandHeatDrop_bounds {r : ℕ} (b : SpectralBand r) {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => bandHeatDropTerm b n u) ∧
      0 ≤ bandHeatDrop b u ∧
      bandHeatDrop b u ≤ ∑ j ∈ Finset.range r, Real.exp (-(((j : ℝ) + 1) * u)) ∧
      bandHeatDrop b u ≤ (r : ℝ) * Real.exp (-u) := by
  have hedge := hasSum_edge_heatDrop r hu
  have hsum : Summable (fun n : ℕ => bandHeatDropTerm b n u) :=
    Summable.of_nonneg_of_le (fun n => (bandHeatDropTerm_nonneg_and_le_edge b n hu).1)
      (fun n => (bandHeatDropTerm_nonneg_and_le_edge b n hu).2) hedge.summable
  have hnn : 0 ≤ bandHeatDrop b u :=
    tsum_nonneg fun n => (bandHeatDropTerm_nonneg_and_le_edge b n hu).1
  have hle_sum : bandHeatDrop b u ≤
      ∑ j ∈ Finset.range r, Real.exp (-(((j : ℝ) + 1) * u)) := by
    have h := hasSum_le (fun n => (bandHeatDropTerm_nonneg_and_le_edge b n hu).2)
      hsum.hasSum hedge
    refine h.trans_eq ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inv_occupationWeight_eq]
  have hsum_le : (∑ j ∈ Finset.range r, Real.exp (-(((j : ℝ) + 1) * u))) ≤
      (r : ℝ) * Real.exp (-u) := by
    calc (∑ j ∈ Finset.range r, Real.exp (-(((j : ℝ) + 1) * u)))
        ≤ ∑ _j ∈ Finset.range r, Real.exp (-u) := by
          refine Finset.sum_le_sum fun j _ => Real.exp_le_exp.mpr ?_
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
      _ = (r : ℝ) * Real.exp (-u) := by simp
  exact ⟨hsum, hnn, hle_sum, hle_sum.trans hsum_le⟩

private theorem measurable_bandHeatDrop {r : ℕ} (b : SpectralBand r) :
    Measurable (bandHeatDrop b) := by
  unfold bandHeatDrop bandHeatDropTerm
  exact Measurable.tsum fun _ => (by fun_prop : Continuous _).measurable

private theorem integrableOn_exp_neg_mul_rpow_local {α q : ℝ} (hα : 0 < α) (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => Real.exp (-α * u) * u ^ (q - 1)) (Ioi 0) := by
  have hG : IntegrableOn (fun v : ℝ => Real.exp (-v) * v ^ (q - 1)) (Ioi (α * 0)) := by
    rw [mul_zero]
    exact Real.GammaIntegral_convergent hq
  have hcomp := (integrableOn_Ioi_comp_mul_left_iff
    (fun v : ℝ => Real.exp (-v) * v ^ (q - 1)) 0 hα).mpr hG
  have hpow_pos : 0 < α ^ (q - 1) := Real.rpow_pos_of_pos hα _
  refine IntegrableOn.congr_fun (hcomp.const_mul (α ^ (q - 1))⁻¹) (fun u hu => ?_)
    measurableSet_Ioi
  rw [Real.mul_rpow hα.le (le_of_lt hu), neg_mul]
  field_simp [hpow_pos.ne']

private theorem integral_cpow_mul_exp_inv_eq {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * (Real.exp (-(x⁻¹ * u)) : ℂ)) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - 1) * (Real.exp (-(x⁻¹ * u)) : ℂ)) =
        Complex.Gamma s * (x : ℂ) ^ s := by
  set p : ℝ := x⁻¹
  have hp : 0 < p := inv_pos.mpr hx
  refine ⟨?_, ?_⟩
  · have hG := Complex.GammaIntegral_convergent hs
    rw [← mul_zero p, ← integrableOn_Ioi_comp_mul_left_iff _ _ hp] at hG
    refine IntegrableOn.congr_fun (hG.const_mul (1 / (p : ℂ) ^ (s - 1)))
      (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
    simp only [Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg hp.le hu.le]
    have hne : (p : ℂ) ^ (s - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.mpr hp.ne')
    calc (1 / (p : ℂ) ^ (s - 1)) *
            ((Real.exp (-(p * u)) : ℂ) * ((p : ℂ) ^ (s - 1) * (u : ℂ) ^ (s - 1)))
        = ((p : ℂ) ^ (s - 1))⁻¹ * (p : ℂ) ^ (s - 1) *
            ((u : ℂ) ^ (s - 1) * (Real.exp (-(p * u)) : ℂ)) := by
          rw [one_div]; ring
      _ = (u : ℂ) ^ (s - 1) * (Real.exp (-(p * u)) : ℂ) := by
          rw [inv_mul_cancel₀ hne, one_mul]
  · have hI := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hp
    have hcongr : EqOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * (Real.exp (-(p * u)) : ℂ))
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * Complex.exp (-((p : ℂ) * (t : ℂ)))) (Ioi 0) := by
      intro u _
      dsimp only
      rw [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    have hx_inv : (1 : ℂ) / (p : ℂ) = (x : ℂ) := by
      dsimp only [p]
      rw [Complex.ofReal_inv, one_div, inv_inv]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hI, hx_inv, mul_comm]

private theorem integral_rpow_mul_bandHeatDropTerm_eq {r : ℕ} (b : SpectralBand r) (n : ℕ)
    {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => u ^ (σ - 1) * bandHeatDropTerm b n u) (Ioi 0) ∧
      (∫ u : ℝ in Ioi 0, u ^ (σ - 1) * bandHeatDropTerm b n u) =
        Real.Gamma σ * spectralDrop (powerResponse ⟨σ, hσ⟩) b n := by
  have h1_pos : 0 < (occupationWeight n)⁻¹ := inv_pos.mpr (occupationWeight_pos n)
  have h2_pos : 0 < ((b n).val)⁻¹ := inv_pos.mpr (band_pos b n)
  have hint1 : IntegrableOn (fun u : ℝ => u ^ (σ - 1) * Real.exp (-((occupationWeight n)⁻¹ * u)))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_exp_neg_mul_rpow_local h1_pos hσ) (fun u _ => ?_)
      measurableSet_Ioi
    rw [neg_mul]; ring
  have hint2 : IntegrableOn (fun u : ℝ => u ^ (σ - 1) * Real.exp (-(((b n).val)⁻¹ * u)))
      (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_exp_neg_mul_rpow_local h2_pos hσ) (fun u _ => ?_)
      measurableSet_Ioi
    rw [neg_mul]; ring
  have hsub : IntegrableOn (fun u : ℝ => u ^ (σ - 1) * bandHeatDropTerm b n u) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hint1.sub hint2) (fun u _ => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]
    unfold bandHeatDropTerm; ring
  refine ⟨hsub, ?_⟩
  have hI1 : (∫ u : ℝ in Ioi 0, u ^ (σ - 1) * Real.exp (-((occupationWeight n)⁻¹ * u))) =
      occupationWeight n ^ σ * Real.Gamma σ := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hσ h1_pos, one_div, inv_inv]
  have hI2 : (∫ u : ℝ in Ioi 0, u ^ (σ - 1) * Real.exp (-(((b n).val)⁻¹ * u))) =
      (b n).val ^ σ * Real.Gamma σ := by
    rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hσ h2_pos, one_div, inv_inv]
  have hcongr : EqOn (fun u : ℝ => u ^ (σ - 1) * bandHeatDropTerm b n u)
      (fun u : ℝ => u ^ (σ - 1) * Real.exp (-((occupationWeight n)⁻¹ * u)) -
        u ^ (σ - 1) * Real.exp (-(((b n).val)⁻¹ * u))) (Ioi 0) := by
    intro u _; unfold bandHeatDropTerm; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub hint1 hint2, hI1, hI2]
  unfold spectralDrop powerResponse
  dsimp only
  ring

/-- Real power-moment integrability of `bandHeatDrop` on `(0, ∞)` for every `σ > 0`. -/
theorem integrableOn_rpow_mul_bandHeatDrop {r : ℕ} (b : SpectralBand r) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun u : ℝ => u ^ (σ - 1) * bandHeatDrop b u) (Ioi 0) := by
  have hdom : IntegrableOn (fun u : ℝ => (r : ℝ) * (Real.exp (-u) * u ^ (σ - 1))) (Ioi 0) :=
    (Real.GammaIntegral_convergent hσ).const_mul (r : ℝ)
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ (σ - 1) * bandHeatDrop b u)
      (volume.restrict (Ioi 0)) := by
    have h1 : AEStronglyMeasurable (fun u : ℝ => u ^ (σ - 1)) (volume.restrict (Ioi 0)) :=
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).aestronglyMeasurable
        measurableSet_Ioi
    exact h1.mul (measurable_bandHeatDrop b).aestronglyMeasurable
  refine hdom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := hu
  obtain ⟨_, hnn, _, hub⟩ := bandHeatDrop_bounds b hu0
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu0.le _) hnn)]
  calc u ^ (σ - 1) * bandHeatDrop b u
      ≤ u ^ (σ - 1) * ((r : ℝ) * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left hub (Real.rpow_nonneg hu0.le _)
    _ = (r : ℝ) * (Real.exp (-u) * u ^ (σ - 1)) := by ring

/-- **Exact Mellin transform of the Krein spectral heat drop:**
for every `b : SpectralBand r` and `s` with `0 < Re s`, `u ↦ (u : ℂ)^{s-1} • bandHeatDrop b u` is
integrable on `(0, ∞)` and integrates to `Complex.Gamma s * relativePartition b s`. -/
theorem mellin_bandHeatDrop_eq {r : ℕ} (b : SpectralBand r) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun u : ℝ => (bandHeatDrop b u : ℂ)) s ∧
      mellin (fun u : ℝ => (bandHeatDrop b u : ℂ)) s =
        Complex.Gamma s * relativePartition b s := by
  have hmc : MellinConvergent (fun u : ℝ => (bandHeatDrop b u : ℂ)) s := by
    have hdom := integrableOn_rpow_mul_bandHeatDrop b hs
    have hmeas : AEStronglyMeasurable
        (fun u : ℝ => (u : ℂ) ^ (s - 1) • (bandHeatDrop b u : ℂ))
        (volume.restrict (Ioi 0)) := by
      have h1 : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ (s - 1))
          (volume.restrict (Ioi 0)) :=
        (continuousOn_of_forall_continuousAt fun x hx =>
          Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))).aestronglyMeasurable
          measurableSet_Ioi
      exact h1.smul (Complex.continuous_ofReal.measurable.comp
        (measurable_bandHeatDrop b)).aestronglyMeasurable
    refine hdom.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re,
      Complex.one_re, Complex.norm_real, Real.norm_of_nonneg (bandHeatDrop_bounds b hu0).2.1]
  refine ⟨hmc, ?_⟩
  let F : ℕ → ℝ → ℂ := fun n u => (u : ℂ) ^ (s - 1) * (bandHeatDropTerm b n u : ℂ)
  have hF_int : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    have h1 := (integral_cpow_mul_exp_inv_eq hs (occupationWeight_pos n)).1
    have h2 := (integral_cpow_mul_exp_inv_eq hs (band_pos b n)).1
    refine IntegrableOn.congr_fun (h1.sub h2) (fun u _ => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply, F, bandHeatDropTerm]
    push_cast; ring
  have hF_val : ∀ n : ℕ, (∫ u : ℝ in Ioi 0, F n u) = Complex.Gamma s * complexDrop b n s := by
    intro n
    have h1 := integral_cpow_mul_exp_inv_eq hs (occupationWeight_pos n)
    have h2 := integral_cpow_mul_exp_inv_eq hs (band_pos b n)
    have hcongr : EqOn (F n)
        (fun u : ℝ => (u : ℂ) ^ (s - 1) * (Real.exp (-((occupationWeight n)⁻¹ * u)) : ℂ) -
          (u : ℂ) ^ (s - 1) * (Real.exp (-(((b n).val)⁻¹ * u)) : ℂ)) (Ioi 0) := by
      intro u _; dsimp only [F, bandHeatDropTerm]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub h1.1 h2.1, h1.2, h2.2]
    unfold complexDrop
    ring
  have hF_norm_sum : Summable (fun n : ℕ => ∫ u : ℝ in Ioi 0, ‖F n u‖) := by
    have hbase := (summable_spectralDrop (powerResponse ⟨s.re, hs⟩) b).mul_left (Real.Gamma s.re)
    refine hbase.congr fun n => ?_
    rw [← (integral_rpow_mul_bandHeatDropTerm_eq b n hs).2]
    refine (setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_).symm
    have hu0 : 0 < u := hu
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
      Complex.norm_real,
      Real.norm_of_nonneg (bandHeatDropTerm_nonneg_and_le_edge b n hu0).1]
  have hhas := hasSum_integral_of_summable_integral_norm hF_int hF_norm_sum
  have htsum_eq : (∫ u : ℝ in Ioi 0, ∑' n : ℕ, F n u) =
      mellin (fun u : ℝ => (bandHeatDrop b u : ℂ)) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    dsimp only [F]
    rw [smul_eq_mul, tsum_mul_left, ← Complex.ofReal_tsum]
    rfl
  rw [htsum_eq] at hhas
  simp_rw [hF_val] at hhas
  have hrp : HasSum (fun n : ℕ => Complex.Gamma s * complexDrop b n s)
      (Complex.Gamma s * relativePartition b s) :=
    (summable_complexDrop b hs).hasSum.mul_left (Complex.Gamma s)
  exact hhas.unique hrp

/-- **First-moment identity for the fourth-trace loss:**
for every `b : SpectralBand r`, `∫_{u > 0} u · bandHeatDrop b u = relativeReading quadraticResponse b`,
and for every positive conserving omission `(P, hd, hc)`, this first moment equals
`traceLoss (projected P)`. -/
theorem integral_mul_bandHeatDrop_eq_traceLoss {r : ℕ} (P : Projection) (hd : MissingDimension P r)
    (hc : Conserving (projected P)) :
    (∫ u : ℝ in Ioi 0, u * bandHeatDrop (physicalSpectrum P hd hc) u) =
      traceLoss (projected P) := by
  let b := physicalSpectrum P hd hc
  have hm := (mellin_bandHeatDrop_eq b (s := 2) (by norm_num)).2
  have hG2 : Complex.Gamma 2 = 1 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero,
      Complex.Gamma_one, mul_one]
  rw [hG2, one_mul, partition_at_two b, quadratic_physicalReading P hd hc] at hm
  have hint_c : (∫ u : ℝ in Ioi 0, ((u * bandHeatDrop b u : ℝ) : ℂ)) =
      mellin (fun u : ℝ => (bandHeatDrop b u : ℂ)) 2 := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one, smul_eq_mul, Complex.ofReal_mul]
  have heq_c := hint_c.trans hm
  rw [integral_complex_ofReal] at heq_c
  exact Complex.ofReal_injective heq_c

/-- **Exact Mellin–overlap decomposition of `jointSurvivingPartition`:**
for every `b : SpectralBand r` and `s` with `0 < Re s` and `Re s ≠ 1`,
`jointSurvivingPartition b s` equals the normalized `dyadicOverlapContrast` integral minus
`((2^s - 1) / Γ(s)) ∫_{u > 0} u^{s-1} bandHeatDrop b u`. -/
theorem jointSurvivingPartition_eq_dyadicOverlap_sub_heatDrop
    (t : ExceptionalTime) (j : ℕ) {r : ℕ} (b : SpectralBand r)
    {s : ℂ} (hs0 : 0 < s.re) (hs_re : s.re ≠ 1) :
    jointSurvivingPartition b s =
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) /
          (((tailRadix t j).val : ℂ) ^ (s / 2) * (1 - (2 : ℂ) ^ (1 - s)) * Complex.Gamma s) -
        (((2 : ℂ) ^ s - 1) / Complex.Gamma s) *
          ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - 1) • (bandHeatDrop b u : ℂ) := by
  have hs1 : s ≠ 1 := fun he => hs_re (by rw [he, Complex.one_re])
  have hC_ne : ((tailRadix t j).val : ℂ) ^ (s / 2) ≠ 0 := by
    have hC0 : ((tailRadix t j).val : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (tailRadix t j).pos.ne'
    rw [Complex.cpow_def_of_ne_zero hC0]
    exact Complex.exp_ne_zero _
  have h2_ne : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    intro h0
    have heq : (2 : ℂ) ^ (1 - s) = 1 := (sub_eq_zero.mp h0).symm
    have hnorm := congrArg norm heq
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, norm_one] at hnorm
    have hexp0 : (1 - s).re = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hlt).ne hnorm
      · exact (Real.one_lt_rpow one_lt_two hgt).ne' hnorm
    rw [Complex.sub_re, Complex.one_re] at hexp0
    exact hs_re (sub_eq_zero.mp hexp0).symm
  have hG_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hpre_ne : ((tailRadix t j).val : ℂ) ^ (s / 2) * (1 - (2 : ℂ) ^ (1 - s)) *
      Complex.Gamma s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hC_ne h2_ne) hG_ne
  rw [integral_dyadicOverlapContrast_div_eq t j hs0 hs1,
    mul_div_cancel_left₀ _ hpre_ne,
    show (∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - 1) • (bandHeatDrop b u : ℂ)) =
      mellin (fun u : ℝ => (bandHeatDrop b u : ℂ)) s from rfl,
    (mellin_bandHeatDrop_eq b hs0).2,
    jointSurvivingPartition_eq_continued_sub]
  field_simp [hG_ne]

/-! ### Part 2: Bathtub moment inequality and UV-regularized rank-one fourth-power equivalence -/

/-- **Sharp bathtub moment inequality on `(0, ∞)`:**
for `0 < σ < 2`, `M > 0`, and any `h : ℝ → ℝ` with `0 ≤ h(u) ≤ M` on `(0, ∞)`,
`∫_{u > 0} u^{σ-1} h(u) ≤ (M^{1 - σ/2} / σ) (2 ∫_{u > 0} u h(u))^{σ/2}`. -/
theorem bathtub_moment_bound {σ M : ℝ} (hσ0 : 0 < σ) (hσ2 : σ < 2) (hM : 0 < M)
    {h : ℝ → ℝ} (hint_σ : IntegrableOn (fun u : ℝ => u ^ (σ - 1) * h u) (Ioi 0))
    (hint_1 : IntegrableOn (fun u : ℝ => u * h u) (Ioi 0))
    (h_bounds : ∀ u : ℝ, 0 < u → 0 ≤ h u ∧ h u ≤ M) :
    (∫ u : ℝ in Ioi 0, u ^ (σ - 1) * h u) ≤
      (M ^ (1 - σ / 2) / σ) * (2 * ∫ u : ℝ in Ioi 0, u * h u) ^ (σ / 2) := by
  set Δ : ℝ := ∫ u : ℝ in Ioi 0, u * h u
  have h_uh_nn : 0 ≤ᵐ[volume.restrict (Ioi 0)] (fun u : ℝ => u * h u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (le_of_lt hu) (h_bounds u hu).1
  have hΔ_nn : 0 ≤ Δ := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (le_of_lt hu) (h_bounds u hu).1
  rcases eq_or_lt_of_le hΔ_nn with hΔ0 | hΔ_pos
  · have hae0 : (fun u : ℝ => u * h u) =ᵐ[volume.restrict (Ioi 0)] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae h_uh_nn hint_1).mp hΔ0.symm
    have hae_σ : (fun u : ℝ => u ^ (σ - 1) * h u) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hae0] with u hu huh0
      have hu_ne : u ≠ 0 := (ne_of_gt hu)
      have hh0 : h u = 0 := (mul_eq_zero.mp huh0).resolve_left hu_ne
      simp [hh0]
    rw [integral_eq_zero_of_ae hae_σ, ← hΔ0, mul_zero,
      Real.zero_rpow (half_pos hσ0).ne', mul_zero]
  · set T : ℝ := Real.sqrt (2 * Δ / M)
    have hT : 0 < T := Real.sqrt_pos.mpr (div_pos (mul_pos two_pos hΔ_pos) hM)
    have hT_sq : T ^ 2 = 2 * Δ / M :=
      Real.sq_sqrt (div_nonneg (mul_nonneg zero_le_two hΔ_pos.le) hM.le)
    let ind : ℝ → ℝ := (Ioc 0 T).indicator (fun u => (u ^ (σ - 1) - T ^ (σ - 2) * u) * M)
    have hi1 : IntervalIntegrable (fun u : ℝ => u ^ (σ - 1)) volume 0 T :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < σ - 1)
    have hi2 : IntervalIntegrable (fun u : ℝ => T ^ (σ - 2) * u) volume 0 T :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 T
    have hind_Ioc : IntegrableOn (fun u : ℝ => (u ^ (σ - 1) - T ^ (σ - 2) * u) * M) (Ioc 0 T) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp (hi1.sub hi2)).mul_const M
    have hind_int : IntegrableOn ind (Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc]
      rwa [IntegrableOn, Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    have hpt : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
        u ^ (σ - 1) * h u - T ^ (σ - 2) * (u * h u) ≤ ind u := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      obtain ⟨hh_nn, hh_le⟩ := h_bounds u hu0
      have hu_pow : u ^ (σ - 1) = u ^ (σ - 2) * u := by
        rw [show σ - 1 = (σ - 2) + 1 by ring, Real.rpow_add_one hu0.ne']
      by_cases huT : u ≤ T
      · have hmem : u ∈ Ioc 0 T := ⟨hu0, huT⟩
        dsimp only [ind]
        rw [indicator_of_mem hmem]
        have hpow_ge : T ^ (σ - 2) ≤ u ^ (σ - 2) :=
          Real.rpow_le_rpow_of_nonpos hu0 huT (by linarith)
        have hdiff_nn : 0 ≤ u ^ (σ - 1) - T ^ (σ - 2) * u := by
          rw [hu_pow]; nlinarith
        calc u ^ (σ - 1) * h u - T ^ (σ - 2) * (u * h u)
            = (u ^ (σ - 1) - T ^ (σ - 2) * u) * h u := by ring
          _ ≤ (u ^ (σ - 1) - T ^ (σ - 2) * u) * M :=
              mul_le_mul_of_nonneg_left hh_le hdiff_nn
      · have hnot : u ∉ Ioc 0 T := fun hm => huT hm.2
        have hTu : T < u := lt_of_not_ge huT
        dsimp only [ind]
        rw [indicator_of_notMem hnot]
        have hpow_le : u ^ (σ - 2) ≤ T ^ (σ - 2) :=
          Real.rpow_le_rpow_of_nonpos hT hTu.le (by linarith)
        have hdiff_np : u ^ (σ - 1) - T ^ (σ - 2) * u ≤ 0 := by
          rw [hu_pow]; nlinarith
        calc u ^ (σ - 1) * h u - T ^ (σ - 2) * (u * h u)
            = (u ^ (σ - 1) - T ^ (σ - 2) * u) * h u := by ring
          _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdiff_np hh_nn
    have hint_lhs : IntegrableOn
        (fun u : ℝ => u ^ (σ - 1) * h u - T ^ (σ - 2) * (u * h u)) (Ioi 0) :=
      hint_σ.sub (hint_1.const_mul _)
    have hmono := integral_mono_ae hint_lhs hind_int hpt
    rw [integral_sub hint_σ (hint_1.const_mul _), integral_const_mul] at hmono
    have hind_eval : (∫ u : ℝ in Ioi 0, ind u) = (T ^ σ / σ - T ^ σ / 2) * M := by
      dsimp only [ind]
      have hid_eval : (∫ u : ℝ in 0..T, u) = (T ^ 2 - 0 ^ 2) / 2 := by
        simpa only [pow_one, Nat.cast_one, show (1 : ℝ) + 1 = 2 by norm_num] using
          (integral_pow 1 (a := 0) (b := T))
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self,
        integral_mul_const, ← intervalIntegral.integral_of_le hT.le,
        intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : -1 < σ - 1)),
        hid_eval,
        show σ - 1 + 1 = σ by ring, Real.zero_rpow hσ0.ne', sub_zero]
      have hT_split : T ^ (σ - 2) * ((T ^ 2 - 0 ^ 2) / 2) = T ^ σ / 2 := by
        have h1 : T ^ (σ - 2) * T ^ 2 = T ^ σ := by
          rw [← Real.rpow_natCast T 2, ← Real.rpow_add hT, Nat.cast_ofNat]
          congr 1; ring
        calc T ^ (σ - 2) * ((T ^ 2 - 0 ^ 2) / 2)
            = (T ^ (σ - 2) * T ^ 2) / 2 := by ring
          _ = T ^ σ / 2 := by rw [h1]
      rw [hT_split]
    rw [hind_eval] at hmono
    have hT_Δ : T ^ (σ - 2) * Δ = M * (T ^ σ / 2) := by
      have hΔ_eq : Δ = M * T ^ 2 / 2 := by
        field_simp [hM.ne'] at hT_sq ⊢
        linarith
      have h1 : T ^ (σ - 2) * T ^ 2 = T ^ σ := by
        rw [← Real.rpow_natCast T 2, ← Real.rpow_add hT, Nat.cast_ofNat]
        congr 1; ring
      rw [hΔ_eq]
      calc T ^ (σ - 2) * (M * T ^ 2 / 2)
          = M * ((T ^ (σ - 2) * T ^ 2) / 2) := by ring
        _ = M * (T ^ σ / 2) := by rw [h1]
    have hstep : (∫ u : ℝ in Ioi 0, u ^ (σ - 1) * h u) ≤ M * T ^ σ / σ := by
      have hsum : T ^ (σ - 2) * Δ + (T ^ σ / σ - T ^ σ / 2) * M = M * T ^ σ / σ := by
        rw [hT_Δ]; ring
      linarith
    have hT_rpow : M * T ^ σ = M ^ (1 - σ / 2) * (2 * Δ) ^ (σ / 2) := by
      have hsqrt : T ^ σ = (2 * Δ / M) ^ (σ / 2) := by
        dsimp only [T]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg (mul_nonneg zero_le_two hΔ_pos.le) hM.le)]
        congr 1; ring
      rw [hsqrt, Real.div_rpow (mul_nonneg zero_le_two hΔ_pos.le) hM.le,
        div_eq_mul_inv, ← Real.rpow_neg hM.le]
      calc M * ((2 * Δ) ^ (σ / 2) * M ^ (-(σ / 2)))
          = (M ^ (1 : ℝ) * M ^ (-(σ / 2))) * (2 * Δ) ^ (σ / 2) := by
            rw [Real.rpow_one]; ring
        _ = M ^ (1 - σ / 2) * (2 * Δ) ^ (σ / 2) := by
            rw [← Real.rpow_add hM, sub_eq_add_neg]
    rwa [hT_rpow, mul_div_right_comm] at hstep

/-- Canonical spectral band `SpectralBand 1` attached to a conserving rank-one missing wave `v`. -/
def missingWaveSpectrum (v : MissingWave) : SpectralBand 1 :=
  physicalSpectrum (omitLine v.val)
    ((missingDimension_one_iff _).mpr ⟨v.val, missingWave_ne_zero v, rfl⟩)
    ((nonzero_line_conserves_iff v.val).mpr v.property).2

theorem relativeReading_quadratic_missingWaveSpectrum (v : MissingWave) :
    relativeReading quadraticResponse (missingWaveSpectrum v) = lineLoss v.val :=
  (quadratic_physicalReading _ _ _).trans (traceLoss_omitLine v.val)

/-- **Sharp surviving-partition power bound deduced directly from vanishing of the dyadic overlap
integral:** if `0 < Re s < 1` and `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0`, then every
conserving rank-one omission `v : MissingWave` satisfies
`‖jointSurvivingPartition(missingWaveSpectrum v, s)‖^{2 / Re s}
  ≤ 2 * (‖2^s - 1‖ / (Re s · ‖Γ(s)‖))^{2 / Re s} * lineLoss v.val`. -/
theorem jointSurviving_bathtub_bound_of_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0)
    (v : MissingWave) :
    ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ (2 / s.re) ≤
      2 * (‖(2 : ℂ) ^ s - 1‖ / (s.re * ‖Complex.Gamma s‖)) ^ (2 / s.re) *
        lineLoss v.val := by
  let b := missingWaveSpectrum v
  have hdecomp := jointSurvivingPartition_eq_dyadicOverlap_sub_heatDrop t j b hs0 hs1.ne
  rw [hint0, zero_div, zero_sub] at hdecomp
  have hG_pos : 0 < ‖Complex.Gamma s‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hs0)
  have hint_norm : ‖∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - 1) • (bandHeatDrop b u : ℂ)‖ ≤
      ∫ u : ℝ in Ioi 0, u ^ (s.re - 1) * bandHeatDrop b u := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 < u := hu
    rw [smul_eq_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re,
      Complex.one_re, Complex.norm_real, Real.norm_of_nonneg (bandHeatDrop_bounds b hu0).2.1]
  have h1_int : IntegrableOn (fun u : ℝ => u * bandHeatDrop b u) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_rpow_mul_bandHeatDrop b (σ := 2) (by norm_num))
      (fun u _ => ?_) measurableSet_Ioi
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have h1_val : (∫ u : ℝ in Ioi 0, u * bandHeatDrop b u) = lineLoss v.val := by
    exact (integral_mul_bandHeatDrop_eq_traceLoss (omitLine v.val) _ _).trans
      (traceLoss_omitLine v.val)
  have hbath := bathtub_moment_bound hs0 (by linarith : s.re < 2) zero_lt_one
    (integrableOn_rpow_mul_bandHeatDrop b hs0) h1_int (fun u hu => by
      obtain ⟨_, hnn, _, hub⟩ := bandHeatDrop_bounds b hu
      refine ⟨hnn, ?_⟩
      rw [Nat.cast_one, one_mul] at hub
      exact hub.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le)))
  rw [Real.one_rpow, one_div, h1_val] at hbath
  have hnorm_le : ‖jointSurvivingPartition b s‖ ≤
      (‖(2 : ℂ) ^ s - 1‖ / (s.re * ‖Complex.Gamma s‖)) *
        (2 * lineLoss v.val) ^ (s.re / 2) := by
    rw [hdecomp, norm_neg, norm_mul, norm_div]
    calc (‖(2 : ℂ) ^ s - 1‖ / ‖Complex.Gamma s‖) *
            ‖∫ u : ℝ in Ioi 0, (u : ℂ) ^ (s - 1) • (bandHeatDrop b u : ℂ)‖
        ≤ (‖(2 : ℂ) ^ s - 1‖ / ‖Complex.Gamma s‖) *
            (s.re⁻¹ * (2 * lineLoss v.val) ^ (s.re / 2)) :=
          mul_le_mul_of_nonneg_left (hint_norm.trans hbath) (by positivity)
      _ = (‖(2 : ℂ) ^ s - 1‖ / (s.re * ‖Complex.Gamma s‖)) *
            (2 * lineLoss v.val) ^ (s.re / 2) := by
          field_simp [hs0.ne', hG_pos.ne']
  have hloss_nn : 0 ≤ 2 * lineLoss v.val :=
    mul_nonneg zero_le_two (line_loss_bounds v).1.le
  have hexp_pos : 0 < 2 / s.re := div_pos two_pos hs0
  have hrpow := Real.rpow_le_rpow (norm_nonneg _) hnorm_le hexp_pos.le
  have hpow_cancel : ((2 * lineLoss v.val) ^ (s.re / 2)) ^ (2 / s.re) = 2 * lineLoss v.val := by
    rw [← Real.rpow_mul hloss_nn, show (s.re / 2) * (2 / s.re) = 1 by field_simp [hs0.ne'],
      Real.rpow_one]
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hloss_nn _), hpow_cancel] at hrpow
  linarith

/-- UV-regularized conserving rank-one class at parameter `s` and UV budget `Λ`: missing waves
whose temperature-`Re s` spectral drop has fourth power controlled by `Λ * lineLoss v.val`. -/
def uvRegularRankOne (s : ℂ) (hs0 : 0 < s.re) (Λ : ℝ) (v : MissingWave) : Prop :=
  relativeReading (powerResponse ⟨s.re, hs0⟩) (missingWaveSpectrum v) ^ 4 ≤
    Λ * lineLoss v.val

/-- On `1 / 2 ≤ Re s ≤ 2`, **every** conserving rank-one missing wave belongs to
`uvRegularRankOne s hs0 1` with universal constant `Λ = 1`. -/
theorem uvRegularRankOne_of_half_le_re {s : ℂ} (hs0 : 0 < s.re) (hlo : 1 / 2 ≤ s.re)
    (hhi : s.re ≤ 2) (v : MissingWave) :
    uvRegularRankOne s hs0 1 v := by
  unfold uvRegularRankOne
  rw [one_mul]
  let β : GibbsExponent := ⟨s.re, hs0⟩
  let q : Ici (1 : ℝ) := ⟨2 / s.re, (one_le_div hs0).mpr hhi⟩
  have hscaled : (scaledExponent β q).val = 2 := by
    change s.re * (2 / s.re) = 2
    field_simp [hs0.ne']
  let b := missingWaveSpectrum v
  have hcost := detector_power_transfer β q (hotEdge 1) b
  rw [reference_error_eq_reading, reference_error_eq_reading,
    reading_at_two b _ hscaled, Nat.cast_one, Real.one_rpow, one_mul,
    relativeReading_quadratic_missingWaveSpectrum] at hcost
  have hrd_bounds := relativeReading_bounds (powerResponse β) b
  have hhead_one : relativeHead (powerResponse β) 1 = 1 := by
    rw [relativeHead, Finset.sum_range_one, occupationWeight_zero]
    change (1 : ℝ) ^ s.re - (0 : ℝ) ^ s.re = 1
    rw [Real.one_rpow, Real.zero_rpow hs0.ne', sub_zero]
  rw [hhead_one] at hrd_bounds
  have hq_le4 : (2 / s.re : ℝ) ≤ 4 := (div_le_iff₀ hs0).mpr (by linarith)
  have hpow_le : relativeReading (powerResponse β) b ^ (4 : ℝ) ≤
      relativeReading (powerResponse β) b ^ (2 / s.re) :=
    Real.rpow_le_rpow_of_exponent_ge' hrd_bounds.1 hrd_bounds.2 (div_nonneg zero_le_two hs0.le)
      hq_le4
  simpa only [Real.rpow_ofNat] using hpow_le.trans hcost

/-- **Exact rank-one fourth-power equivalence on UV-regularized conserving omissions:**
throughout the entire open strip `0 < Re s < 1` (including `0 < Re s < 1 / 2` and `|Im s| > 84.5`)
and for every UV budget `Λ > 0`, a fourth-power bound across `uvRegularRankOne s hs0 Λ` holds
**if and only if** the dyadic overlap integral `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u`
vanishes. -/
theorem uvRegularRankOne_fourthPower_iff_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (∃ K : ℝ, ∀ v : MissingWave, uvRegularRankOne s hs0 Λ v →
      ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0 := by
  constructor
  · rintro ⟨K, hK⟩
    rw [continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne]
    by_contra hcs
    let β : GibbsExponent := ⟨s.re, hs0⟩
    -- Along `τ ↑ 1⁻`, ground-state attenuations have arbitrarily small positive loss,
    -- satisfy the strict UV-regularity inequality `< Λ * loss`, and keep `jointSurvivingPartition`
    -- bounded away from `0`.
    have hτ_int : ∀ᶠ τ : ℝ in 𝓝[<] 1, 0 < τ ∧ τ < 1 := by
      have hx : Tendsto (fun τ : ℝ => τ) (𝓝[<] 1) (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      exact (hx.eventually_const_lt zero_lt_one).and self_mem_nhdsWithin
    have hx1 : Tendsto (fun τ : ℝ => τ) (𝓝[<] 1) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hloss0 : Tendsto (fun τ : ℝ => 1 - τ ^ 2) (𝓝[<] 1) (𝓝 0) := by
      simpa only [one_pow, sub_self] using (hx1.pow 2).const_sub 1
    have hc_pow : Tendsto (fun τ : ℝ => (τ : ℂ) ^ s) (𝓝[<] 1) (𝓝 1) := by
      have hc := (Complex.continuousAt_ofReal_cpow_const 1 s (Or.inr one_ne_zero)).tendsto.comp hx1
      simpa only [Function.comp_def, Complex.ofReal_one, Complex.one_cpow] using hc
    have hjsp_lim : Tendsto (fun τ : ℝ =>
        ‖continued s - ((2 : ℂ) ^ s - 1) * (1 - (τ : ℂ) ^ s)‖ ^ 4)
        (𝓝[<] 1) (𝓝 (‖continued s‖ ^ 4)) := by
      have h1 : Tendsto (fun τ : ℝ =>
          continued s - ((2 : ℂ) ^ s - 1) * (1 - (τ : ℂ) ^ s))
          (𝓝[<] 1) (𝓝 (continued s)) := by
        simpa only [sub_self, mul_zero, sub_zero] using
          tendsto_const_nhds.sub ((hc_pow.const_sub 1).const_mul ((2 : ℂ) ^ s - 1))
      exact (h1.norm.pow 4)
    have hpos_lim : 0 < ‖continued s‖ ^ 4 := pow_pos (norm_pos_iff.mpr hcs) 4
    have hev_uv : ∀ᶠ τ : ℝ in 𝓝[<] 1, (1 - τ ^ 2) ^ 4 < Λ * (1 - τ ^ 2) := by
      have hcube0 : Tendsto (fun τ : ℝ => (1 - τ ^ 2) ^ 3) (𝓝[<] 1) (𝓝 0) := by
        simpa only [zero_pow (by norm_num : 3 ≠ 0)] using hloss0.pow 3
      filter_upwards [hτ_int, hcube0.eventually (gt_mem_nhds hΛ)] with τ hτ hcube
      have hd_pos : 0 < 1 - τ ^ 2 := by nlinarith [hτ.1, hτ.2]
      have hmul := mul_lt_mul_of_pos_right hcube hd_pos
      nlinarith
    have hev_viol : ∀ᶠ τ : ℝ in 𝓝[<] 1,
        K * (1 - τ ^ 2) < ‖continued s - ((2 : ℂ) ^ s - 1) * (1 - (τ : ℂ) ^ s)‖ ^ 4 := by
      have hK0 : Tendsto (fun τ : ℝ => K * (1 - τ ^ 2)) (𝓝[<] 1) (𝓝 0) := by
        simpa only [mul_zero] using hloss0.const_mul K
      have hmid := (hK0.eventually (gt_mem_nhds (half_pos hpos_lim))).and
        (hjsp_lim.eventually (lt_mem_nhds (half_lt_self hpos_lim)))
      filter_upwards [hmid] with τ ⟨h1, h2⟩
      linarith
    obtain ⟨τ, hτ_bounds, huv_τ, hviol_τ⟩ := (hτ_int.and (hev_uv.and hev_viol)).exists
    obtain ⟨b₀, hb₀_cl, hb₀_eq⟩ := exists_ground_attenuation 0 ⟨τ, hτ_bounds.1, hτ_bounds.2.le⟩
    have hb₀_q : relativeReading quadraticResponse b₀ = 1 - τ ^ 2 := by
      have h := hb₀_eq (z := 2) (by norm_num)
      rw [partition_at_two, show (τ : ℂ) ^ (2 : ℂ) = ((τ ^ 2 : ℝ) : ℂ) by
        rw [Complex.ofReal_pow, ← Complex.cpow_natCast]; rfl,
        ← Complex.ofReal_one, ← Complex.ofReal_sub] at h
      exact (Complex.ofReal_injective h).symm |> Eq.symm
    have hb₀_β : relativeReading (powerResponse β) b₀ = 1 - τ ^ s.re := by
      have h := hb₀_eq (z := (s.re : ℂ)) (by simpa using hs0)
      have hrp := relativePartition_real b₀ β
      dsimp only [β] at hrp
      rw [hrp, ← Complex.ofReal_cpow hτ_bounds.1.le, ← Complex.ofReal_one,
        ← Complex.ofReal_sub] at h
      exact Complex.ofReal_injective h
    have hb₀_β_le_q : relativeReading (powerResponse β) b₀ ≤
        relativeReading quadraticResponse b₀ := by
      rw [hb₀_β, hb₀_q]
      have hle : τ ^ (2 : ℝ) ≤ τ ^ s.re :=
        Real.rpow_le_rpow_of_exponent_ge hτ_bounds.1 hτ_bounds.2.le (by linarith)
      rw [Real.rpow_two] at hle
      linarith
    have hb₀_uv : relativeReading (powerResponse β) b₀ ^ 4 <
        Λ * relativeReading quadraticResponse b₀ := by
      have hnn := (relativeReading_bounds (powerResponse β) b₀).1
      have hp4 : relativeReading (powerResponse β) b₀ ^ 4 ≤
          relativeReading quadraticResponse b₀ ^ 4 :=
        pow_le_pow_left₀ hnn hb₀_β_le_q 4
      rw [hb₀_q] at hp4 ⊢
      exact hp4.trans_lt huv_τ
    have hb₀_viol : K * relativeReading quadraticResponse b₀ <
        ‖jointSurvivingPartition b₀ s‖ ^ 4 := by
      rw [hb₀_q, jointSurvivingPartition_eq_continued_sub, hb₀_eq hs0]
      exact hviol_τ
    have hcont_jsp4 : Continuous (fun b : SpectralBand 1 => ‖jointSurvivingPartition b s‖ ^ 4) := by
      have hc1 : Continuous (fun b : SpectralBand 1 => jointSurvivingPartition b s) := by
        simp_rw [jointSurvivingPartition_eq_continued_sub]
        exact Continuous.sub continuous_const (continuous_const.mul
          (continuous_relativePartition_spectrum hs0 1))
      exact hc1.norm.pow 4
    let U : Set (SpectralBand 1) :=
      {b | relativeReading (powerResponse β) b ^ 4 < Λ * relativeReading quadraticResponse b ∧
        K * relativeReading quadraticResponse b < ‖jointSurvivingPartition b s‖ ^ 4}
    have hU_open : IsOpen U :=
      (isOpen_lt ((continuous_relativeReading (powerResponse β) 1).pow 4)
        (continuous_const.mul (continuous_relativeReading quadraticResponse 1))).inter
      (isOpen_lt (continuous_const.mul (continuous_relativeReading quadraticResponse 1))
        hcont_jsp4)
    obtain ⟨b_phys, hb_U, ⟨P, hd, hc, rfl⟩⟩ :=
      mem_closure_iff.mp hb₀_cl U hU_open ⟨hb₀_uv, hb₀_viol⟩
    obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
    let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
    have hspec_eq : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
    rw [hspec_eq] at hb_U
    have huv_v : uvRegularRankOne s hs0 Λ v := by
      unfold uvRegularRankOne
      rw [← relativeReading_quadratic_missingWaveSpectrum]
      exact hb_U.1.le
    have hviol_v := hb_U.2
    rw [relativeReading_quadratic_missingWaveSpectrum] at hviol_v
    exact (hK v huv_v).not_gt hviol_v
  · intro hint0
    have hcs : continued s = 0 :=
      (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
    refine ⟨‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * Λ, fun v huv => ?_⟩
    let b := missingWaveSpectrum v
    let β : GibbsExponent := ⟨s.re, hs0⟩
    have hrp := relativePartition_norm_le b β le_rfl
    have hjsp_norm : ‖jointSurvivingPartition b s‖ ≤
        ‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * relativeReading (powerResponse β) b) := by
      rw [jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left hrp (norm_nonneg _)
    have hp4 := pow_le_pow_left₀ (norm_nonneg _) hjsp_norm 4
    calc ‖jointSurvivingPartition b s‖ ^ 4
        ≤ (‖(2 : ℂ) ^ s - 1‖ * ((‖s‖ / s.re) * relativeReading (powerResponse β) b)) ^ 4 := hp4
      _ = ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 *
            relativeReading (powerResponse β) b ^ 4 := by ring
      _ ≤ ‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * (Λ * lineLoss v.val) :=
          mul_le_mul_of_nonneg_left huv (by positivity)
      _ = (‖(2 : ℂ) ^ s - 1‖ ^ 4 * (‖s‖ / s.re) ^ 4 * Λ) * lineLoss v.val := by ring

/-! ### Part 3: Unconditional high-shell obstruction on `0 < Re s < 1/2` and reflection closure above `84.5` -/

/-- **Exact fourth-power-to-loss ratio on `blockSpectrum N 1` under vanishing of the dyadic
overlap integral:** for `0 < Re s < 1` with `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0`,
`‖jointSurvivingPartition(blockSpectrum N 1, s)‖^4 / relativeReading quadraticResponse (blockSpectrum N 1)
  = ‖2^s - 1‖^4 * (N + 1)^{2 - 4 Re s}`. -/
theorem blockSpectrum_fourthPower_ratio_of_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0) (N : ℕ) :
    ‖jointSurvivingPartition (blockSpectrum N 1) s‖ ^ 4 /
        relativeReading quadraticResponse (blockSpectrum N 1) =
      ‖(2 : ℂ) ^ s - 1‖ ^ 4 * ((N : ℝ) + 1) ^ (2 - 4 * s.re) := by
  have hcs : continued s = 0 :=
    (continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mp hint0
  have hn_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hrp : relativePartition (blockSpectrum N 1) s = (occupationWeight N : ℂ) ^ s := by
    simpa only [Finset.range_one, Finset.sum_singleton, Nat.add_zero] using
      relativePartition_block N 1 hs0
  have hqr : relativeReading quadraticResponse (blockSpectrum N 1) = occupationWeight N ^ 2 := by
    have h : relativePartition (blockSpectrum N 1) 2 =
        (occupationWeight N : ℂ) ^ (2 : ℂ) := by
      simpa only [Finset.range_one, Finset.sum_singleton, Nat.add_zero] using
        relativePartition_block N 1 (z := 2) (by norm_num)
    rw [partition_at_two, show (occupationWeight N : ℂ) ^ (2 : ℂ) =
      ((occupationWeight N ^ 2 : ℝ) : ℂ) by
        rw [Complex.ofReal_pow, ← Complex.cpow_natCast]; rfl] at h
    exact Complex.ofReal_injective h
  rw [jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul, hrp,
    Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos N), mul_pow, hqr,
    occupationWeight_eq]
  have h1 : ((((N : ℝ) + 1)⁻¹) ^ s.re) ^ 4 = ((N : ℝ) + 1) ^ (-4 * s.re) := by
    rw [Real.inv_rpow hn_pos.le, ← Real.rpow_neg hn_pos.le, ← Real.rpow_natCast _ 4,
      ← Real.rpow_mul hn_pos.le, Nat.cast_ofNat]
    congr 1; ring
  have h2 : (((N : ℝ) + 1)⁻¹ ^ 2)⁻¹ = ((N : ℝ) + 1) ^ (2 : ℝ) := by
    rw [inv_pow, inv_inv, Real.rpow_two]
  rw [h1, div_eq_mul_inv, h2, mul_assoc, ← Real.rpow_add hn_pos]
  congr 2; ring

/-- **UV blow-up of the fourth-power ratio on `0 < Re s < 1 / 2` even when the dyadic overlap
integral vanishes:** as `N → ∞`, the single-shell deletion ratio on `blockSpectrum N 1` tends to
`+∞`. -/
theorem tendsto_blockSpectrum_fourthPower_ratio_atTop_of_integral_eq_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    (hint0 : (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0) :
    Tendsto (fun N : ℕ =>
      ‖jointSurvivingPartition (blockSpectrum N 1) s‖ ^ 4 /
        relativeReading quadraticResponse (blockSpectrum N 1)) atTop atTop := by
  have hs1 : s.re < 1 := by linarith
  have hf_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := (ComplementaryHalves.factor_zero_iff s).mp h0
    exact hs0.ne' ((congrArg Complex.re hk).trans (ComplementaryHalves.frequency_re k))
  have hf_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ ^ 4 := pow_pos (norm_pos_iff.mpr hf_ne) 4
  have hexp_pos : 0 < 2 - 4 * s.re := by linarith
  have hlin : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hrpow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (2 - 4 * s.re)) atTop atTop :=
    (tendsto_rpow_atTop hexp_pos).comp hlin
  refine (hrpow.const_mul_atTop hf_pos).congr fun N => ?_
  exact (blockSpectrum_fourthPower_ratio_of_integral_eq_zero t j hs0 hs1 hint0 N).symm

/-- **Unconditional rank-one fourth-power violation at every point in `0 < Re s < 1 / 2`:**
without any hypothesis on `ζ(s)`, for every `s` with `0 < Re s < 1 / 2`, every `K : ℝ`, and every
`ε > 0`, there exists a conserving rank-one missing wave `v : MissingWave` with
`0 < lineLoss v.val < ε` and `K * lineLoss v.val < ‖jointSurvivingPartition (missingWaveSpectrum v) s‖^4`. -/
theorem exists_missingWave_fourthPower_violation_of_re_lt_half
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : MissingWave,
      0 < lineLoss v.val ∧ lineLoss v.val < ε ∧
      K * lineLoss v.val < ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 := by
  by_cases hcs : continued s = 0
  · have hf_ne : (2 : ℂ) ^ s - 1 ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (ComplementaryHalves.factor_zero_iff s).mp h0
      exact hs0.ne' ((congrArg Complex.re hk).trans (ComplementaryHalves.frequency_re k))
    have hf4_pos : 0 < ‖(2 : ℂ) ^ s - 1‖ ^ 4 := pow_pos (norm_pos_iff.mpr hf_ne) 4
    obtain ⟨P, hd, hc, hloss_pos, hloss_lt, hviol⟩ :=
      exists_small_trace_violation 0 hs0 ⟨4, by norm_num⟩ (by dsimp only; linarith)
        (K / (‖(2 : ℂ) ^ s - 1‖ ^ 4)) hε
    obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
    let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
    have hspec_eq : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
    have htr_eq : traceLoss (projected (omitLine w)) = lineLoss v.val := traceLoss_omitLine w
    refine ⟨v, htr_eq ▸ hloss_pos, htr_eq ▸ hloss_lt, ?_⟩
    rw [← hspec_eq, jointSurvivingPartition_eq_continued_sub, hcs, zero_sub, norm_neg, norm_mul,
      mul_pow]
    dsimp only at hviol
    rw [Real.rpow_ofNat, htr_eq, div_mul_eq_mul_div, div_lt_iff₀' hf4_pos] at hviol
    exact hviol
  · obtain ⟨P, hd, hc, hloss_pos, hloss_lt, hviol⟩ :=
      exists_small_trace_jointSurviving_violation 0 hs0 hcs (p := 4) (by norm_num) K hε
    obtain ⟨w, hw_ne, rfl⟩ := (missingDimension_one_iff P).mp hd
    let v : MissingWave := ⟨w, (nonzero_line_conserves_iff w).mp ⟨hw_ne, hc⟩⟩
    have hspec_eq : physicalSpectrum (omitLine w) hd hc = missingWaveSpectrum v := rfl
    have htr_eq : traceLoss (projected (omitLine w)) = lineLoss v.val := traceLoss_omitLine w
    rw [hspec_eq, Real.rpow_ofNat, htr_eq] at hviol
    exact ⟨v, htr_eq ▸ hloss_pos, htr_eq ▸ hloss_lt, hviol⟩

/-- **Pointwise logical reduction at each left-strip candidate:**
at every `s` with `0 < Re s < 1 / 2`, deducing a fourth-power bound across all conserving rank-one
missing waves from `∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u = 0` is pointwise equivalent to
`∫_{u > 0} dyadicOverlapContrast(t, j, s, u) / u ≠ 0` (`continued s ≠ 0`). -/
theorem rankOne_fourthPower_from_integral_iff_integral_ne_zero
    (t : ExceptionalTime) (j : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    (((∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0) →
      ∃ K : ℝ, ∀ v : MissingWave,
        ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val) ↔
      (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) ≠ 0 := by
  constructor
  · intro himp hint0
    obtain ⟨K, hK⟩ := himp hint0
    obtain ⟨v, _, _, hviol⟩ :=
      exists_missingWave_fourthPower_violation_of_re_lt_half hs0 hhi K zero_lt_one
    exact (hK v).not_gt hviol
  · exact fun hne hint0 => (hne hint0).elim

/-- **Complete left-zero exclusion and functional-reflection equivalence above Bohman height `84.5`:**
quantifying the rank-one fourth-power bound over candidate left-strip zeros of the dyadic overlap
integral in `{3001 / 24000 ≤ Re s < 1 / 2 ∧ 169 / 2 < |Im s|}` excludes all left-strip zeros by the
surviving-exponent classification and excludes all right-strip zeros by functional reflection
`w ↔ 1 - w`, giving an unconditional equivalence with `RiemannHypothesis`. -/
theorem rh_iff_rankOne_fourthPower_at_left_dyadicOverlap_zeros_above_eightyFour_and_half
    (t : ExceptionalTime) (j : ℕ) :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
        (∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0 →
        ∃ K : ℝ, ∀ v : MissingWave,
          ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val) ∧
    (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 169 / 2 < |s.im| →
      ((∫ u : ℝ in Ioi 0, dyadicOverlapContrast t j s u / (u : ℂ)) = 0 →
        ∃ K : ℝ, ∀ v : MissingWave,
          ‖jointSurvivingPartition (missingWaveSpectrum v) s‖ ^ 4 ≤ K * lineLoss v.val) →
      continued s ≠ 0 ∧ continued (1 - s) ≠ 0) := by
  refine ⟨?_, fun s hlo hhi _ himp => ?_⟩
  · rw [(rh_iff_surviving_exponent_four_at_dyadicOverlap_zeros_above_eightyFour_and_half t j 0).2]
    refine forall₄_congr fun s hlo hhi _ => imp_congr_right fun _ => ?_
    have hs0 : 0 < s.re := by linarith
    constructor
    · intro h4
      obtain ⟨_, hge⟩ := (mem_jointSurvivingTracePowers_four_iff 0 hs0).mp h4
      linarith
    · rintro ⟨K, hK⟩
      obtain ⟨v, _, _, hviol⟩ :=
        exists_missingWave_fourthPower_violation_of_re_lt_half hs0 hhi K zero_lt_one
      exact (hK v).not_gt hviol |> False.elim
  · have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hne_int := (rankOne_fourthPower_from_integral_iff_integral_ne_zero t j hs0 hhi).mp himp
    have hcs_ne : continued s ≠ 0 := fun hcs =>
      hne_int ((continued_eq_zero_iff_integral_dyadicOverlapContrast_eq_zero t j hs0 hs1.ne).mpr hcs)
    have h1s_pos : 0 < (1 - s).re := by simp; linarith
    have h1s_lt1 : (1 - s).re < 1 := by simp; linarith
    refine ⟨hcs_ne, fun hc1s => hcs_ne ?_⟩
    have hζ1s : riemannZeta (1 - s) = 0 :=
      (ComplementaryHalves.positive_zero_iff ⟨1 - s, h1s_pos⟩).mp hc1s
    have hζs : riemannZeta s = 0 := by
      have h := _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hζ1s h1s_pos h1s_lt1
      simpa only [sub_sub_cancel] using h
    exact (ComplementaryHalves.positive_zero_iff ⟨s, hs0⟩).mpr hζs

#print axioms bandHeatDrop_bounds
#print axioms integrableOn_rpow_mul_bandHeatDrop
#print axioms mellin_bandHeatDrop_eq
#print axioms integral_mul_bandHeatDrop_eq_traceLoss
#print axioms jointSurvivingPartition_eq_dyadicOverlap_sub_heatDrop
#print axioms bathtub_moment_bound
#print axioms jointSurviving_bathtub_bound_of_integral_eq_zero
#print axioms uvRegularRankOne_of_half_le_re
#print axioms uvRegularRankOne_fourthPower_iff_integral_eq_zero
#print axioms blockSpectrum_fourthPower_ratio_of_integral_eq_zero
#print axioms tendsto_blockSpectrum_fourthPower_ratio_atTop_of_integral_eq_zero
#print axioms exists_missingWave_fourthPower_violation_of_re_lt_half
#print axioms rankOne_fourthPower_from_integral_iff_integral_ne_zero
#print axioms rh_iff_rankOne_fourthPower_at_left_dyadicOverlap_zeros_above_eightyFour_and_half

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
