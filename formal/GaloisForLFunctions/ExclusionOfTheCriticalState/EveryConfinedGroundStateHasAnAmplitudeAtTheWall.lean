import GaloisForLFunctions.ExclusionOfTheCriticalState.BoundedProfilesDecreasingTowardsTheWallLieInTheEnergyDomain
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateAndThePrimeSideHaveExactLogarithmicLawsAtTheWall

/-!
# Every confined ground state has an amplitude at the wall

Let `F` be a minimizer of the confined half-line form at a ratio `R > 0`, and let
`L_F(k) = ∫_{v>k} F(−v)/v dv` be its logarithmic moment left of `−k`.

**Theorem** (`halfLineEnergyMinimizer_exists_wallAmplitude`). There is a real number `ℓ` with

  `L_F(k) / √log(1/k) → 2ℓ` as `k → 0⁺`,  `√log(1/|u|) F(u) → ℓ` essentially as `u → 0⁻`.

The ratio is arbitrary: the statement concerns the ground state of the confined form at every
confinement, not only the critical one, and it uses no property of the zeros.

Mechanism. The barrier `A/√log(1/|u|)` on a collar `(−k, 0)`, completed by a ramp, lies above `F`
as soon as `A √log(1/k) ≥ L_F(k)/2 + K + 13|A|` (`halfLineEnergyMinimizer_exists_wall_barrier`):
the cutoff Lévy operators take the value `√log(1/k) + O(1)` on the inverse root logarithm, and the
part of `F` left of the collar acts on the collar through `L_F(k)/2 + O(1)`
(`abs_exterior_sub_half_wallLogMoment_le`). Conversely a bound `F ≤ S/√log(1/|u|)` on a collar
integrates to `L_F(k) ≤ L_F(k₀) + 2S(√log(1/k) − √log(1/k₀))` (`wallLogMoment_le_of_ae_le`).
The two steps bound the quotient `q(k) = L_F(k)/√log(1/k)`, and then give
`limsup q ≤ q(k) + ε` for every small `k`. The same for `−F` makes `q` a Cauchy family at `0⁺`;
the barrier with `A = ℓ ± ε` gives the essential limit.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The part of the state left of the collar -/

/-- At the lags beyond the cutoff the symmetric kernel is the Lévy density. -/
theorem symCutoffKernel_of_lt {δ s : ℝ} (hδ : 0 < δ) (hs : δ < s) :
    symCutoffKernel δ s = archLevyDensity s := by
  unfold symCutoffKernel halfLineGammaCutoffKernel
  rw [indicator_of_mem (mem_Ioi.mpr hs), indicator_of_notMem (by
    rw [mem_Ioi, not_lt]
    linarith only [hδ, hs]), add_zero]

/-- The Lévy density against the kernel of the logarithmic moment:
`|ω(s) − 1/(2(s+t))| ≤ 1/4 + (t/2) s⁻²`. -/
theorem abs_archLevyDensity_sub_half_inv_add_le {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    |archLevyDensity s - 1 / (2 * (s + t))| ≤ 1 / 4 + t / 2 * s ^ (-(2 : ℝ)) := by
  have h1 := archLevyDensity_le_half_inv_add hs
  have h2 := half_inv_sub_le_archLevyDensity hs
  have hst : 0 < s + t := by linarith only [hs, ht]
  have e : s ^ (-(2 : ℝ)) = (s ^ 2)⁻¹ := by rw [Real.rpow_neg hs.le, Real.rpow_two]
  have h3 : 1 / (2 * s) - 1 / (2 * (s + t)) = t / (2 * s * (s + t)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) (by positivity)]
    ring
  have h4 : t / (2 * s * (s + t)) ≤ t / 2 * (s ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, div_div]
    exact div_le_div_of_nonneg_left ht (by positivity)
      (by nlinarith only [mul_nonneg hs.le ht])
  have h5 : 0 ≤ t / (2 * s * (s + t)) := by positivity
  rw [e, abs_le]
  constructor <;> linarith only [h1, h2, h3, h4, h5]

/-- **The part of a bounded profile left of the collar acts through its logarithmic moment.** For
`δ ≤ t < k/2` the cutoff kernel applied to `F 1_{u ≤ −k}` at `−t` is `L_F(k)/2` up to
`‖F‖₁/4 + C/2`. -/
theorem abs_exterior_sub_half_wallLogMoment_le {F : ℝ → ℝ} (hFm : Measurable F)
    (hF1 : Integrable F) (hF2 : Integrable fun u => F u ^ 2) {C : ℝ} (hC0 : 0 ≤ C)
    (hFC : ∀ᵐ u : ℝ, |F u| ≤ C) {k δ t : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (htk : t < k / 2) :
    |lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) (-t) - wallLogMoment F k / 2| ≤
      (∫ u, |F u|) / 4 + C / 2 := by
  have ht : 0 < t := lt_of_lt_of_le hδ hδt
  have hk : 0 < k := by linarith only [ht, htk]
  have hkt : 0 < k - t := by linarith only [ht, htk]
  have hXm : Measurable ((Iic (-k)).indicator F) := hFm.indicator measurableSet_Iic
  have hX2 : Integrable fun u => (Iic (-k)).indicator F u ^ 2 := by
    refine hF2.mono' (hXm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hu : u ∈ Iic (-k)
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, zero_pow two_ne_zero]
      exact sq_nonneg _
  have hI1 : Integrable fun s => symCutoffKernel δ s * (Iic (-k)).indicator F (-t - s) :=
    integrable_symCutoffKernel_mul_translate hδ hXm hX2 (-t)
  -- the logarithmic moment as an integral over the lags
  have hdiv : IntegrableOn (fun v => F (-v) / v) (Ioi k) :=
    integrableOn_div_self (f := fun v => F (-v)) (hFm.comp measurable_neg) hF1.comp_neg hk
  have hI2 : Integrable fun s => (Ioi k).indicator (fun v => F (-v) / v) (s + t) :=
    (hdiv.integrable_indicator measurableSet_Ioi).comp_add_right t
  have hmom : wallLogMoment F k = ∫ s, (Ioi k).indicator (fun v => F (-v) / v) (s + t) := by
    rw [integral_add_right_eq_self ((Ioi k).indicator fun v => F (-v) / v) t,
      integral_indicator measurableSet_Ioi, wallLogMoment]
  have hdiff : lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) (-t) -
      wallLogMoment F k / 2 = ∫ s, (symCutoffKernel δ s * (Iic (-k)).indicator F (-t - s) -
        (Ioi k).indicator (fun v => F (-v) / v) (s + t) / 2) := by
    rw [hmom, integral_sub hI1 (hI2.div_const 2), integral_div]
    rfl
  have hFC' : ∀ᵐ s : ℝ, |F (-t - s)| ≤ C := ae_comp_const_sub hFC (-t)
  have hne : ({k - t} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr Real.volume_singleton
  have hpow : IntegrableOn (fun s : ℝ => s ^ (-(2 : ℝ))) (Ioi (k - t)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hkt
  have hg1 : Integrable fun s => |F (-t - s)| / 4 := (hF1.abs.comp_sub_left (-t)).div_const 4
  have hg2 : Integrable fun s =>
      C * (t / 2) * (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s :=
    (hpow.integrable_indicator measurableSet_Ioi).const_mul _
  have hg : Integrable fun s => |F (-t - s)| / 4 +
      C * (t / 2) * (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s := hg1.add hg2
  have hbound : ∀ᵐ s : ℝ, ‖symCutoffKernel δ s * (Iic (-k)).indicator F (-t - s) -
      (Ioi k).indicator (fun v => F (-v) / v) (s + t) / 2‖ ≤ |F (-t - s)| / 4 +
        C * (t / 2) * (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s := by
    filter_upwards [hFC', hne] with s hs hsne
    have hsne' : s ≠ k - t := fun h => hsne (mem_singleton_iff.mpr h)
    rcases lt_or_gt_of_ne hsne' with hlt | hgt
    · -- lags that stay inside the collar: both kernels vanish
      have e1 : (Iic (-k)).indicator F (-t - s) = 0 :=
        indicator_of_notMem (by
          rw [mem_Iic, not_le]
          linarith only [hlt]) _
      have e2 : (Ioi k).indicator (fun v => F (-v) / v) (s + t) = 0 :=
        indicator_of_notMem (by
          rw [mem_Ioi, not_lt]
          linarith only [hlt]) _
      have e3 : (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s = 0 :=
        indicator_of_notMem (by
          rw [mem_Ioi, not_lt]
          exact hlt.le) _
      rw [e1, e2, e3]
      simp only [mul_zero, zero_div, sub_zero, norm_zero, add_zero]
      positivity
    · have hs0 : 0 < s := lt_trans hkt hgt
      have e1 : (Iic (-k)).indicator F (-t - s) = F (-t - s) :=
        indicator_of_mem (by
          rw [mem_Iic]
          linarith only [hgt]) _
      have e2 : (Ioi k).indicator (fun v => F (-v) / v) (s + t) = F (-(s + t)) / (s + t) :=
        indicator_of_mem (by
          rw [mem_Ioi]
          linarith only [hgt]) _
      have e3 : (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s = s ^ (-(2 : ℝ)) :=
        indicator_of_mem (mem_Ioi.mpr hgt) _
      rw [e1, e2, e3, symCutoffKernel_of_lt hδ (by linarith only [hgt, hδt, htk]),
        show -(s + t) = -t - s by ring]
      have hker := abs_archLevyDensity_sub_half_inv_add_le hs0 ht.le
      have e : archLevyDensity s * F (-t - s) - F (-t - s) / (s + t) / 2 =
          (archLevyDensity s - 1 / (2 * (s + t))) * F (-t - s) := by
        rw [show (1 : ℝ) / (2 * (s + t)) = 1 / (s + t) / 2 by rw [div_div, mul_comm]]
        ring
      rw [e, Real.norm_eq_abs, abs_mul]
      have hp : 0 ≤ s ^ (-(2 : ℝ)) := Real.rpow_nonneg hs0.le _
      have h1 : |archLevyDensity s - 1 / (2 * (s + t))| * |F (-t - s)| ≤
          (1 / 4 + t / 2 * s ^ (-(2 : ℝ))) * |F (-t - s)| :=
        mul_le_mul_of_nonneg_right hker (abs_nonneg _)
      have h2 : t / 2 * s ^ (-(2 : ℝ)) * |F (-t - s)| ≤ t / 2 * s ^ (-(2 : ℝ)) * C :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg (by linarith only [ht]) hp)
      linarith only [h1, h2]
  have hgint : ∫ s, (|F (-t - s)| / 4 +
      C * (t / 2) * (Ioi (k - t)).indicator (fun s : ℝ => s ^ (-(2 : ℝ))) s) =
      (∫ u, |F u|) / 4 + C * (t / 2) * (k - t)⁻¹ := by
    rw [integral_add hg1 hg2, integral_div, integral_const_mul,
      integral_indicator measurableSet_Ioi, integral_Ioi_rpow_neg_two_eq_inv hkt,
      integral_sub_left_eq_self (fun u => |F u|) volume (-t)]
  have hfin : C * (t / 2) * (k - t)⁻¹ ≤ C / 2 := by
    have h1 : t * (k - t)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hkt]
      linarith only [htk]
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith only [hC0] : (0 : ℝ) ≤ C / 2)
    linarith only [h2]
  rw [hdiff, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hg hbound).trans (hgint.le.trans ?_)
  linarith only [hfin]

theorem wallLogMoment_neg (F : ℝ → ℝ) (k : ℝ) :
    wallLogMoment (fun u => -F u) k = -wallLogMoment F k := by
  unfold wallLogMoment
  rw [← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun v => neg_div _ _)

/-! ### The scale of the wall -/

theorem tendsto_wallRootLog_nhdsGT_zero : Tendsto wallRootLog (𝓝[>] 0) atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_log_one_div_nhdsGT_zero

/-- `∫_k^{k₀} dv / (v √log(1/v)) = 2 (√log(1/k) − √log(1/k₀))`. -/
theorem integral_inv_wallRootLog_div {k k₀ : ℝ} (hk : 0 < k) (hkk : k ≤ k₀) (hk4 : k₀ ≤ 1 / 4) :
    IntervalIntegrable (fun v => (wallRootLog v)⁻¹ / v) volume k k₀ ∧
      ∫ v in k..k₀, (wallRootLog v)⁻¹ / v = 2 * (wallRootLog k - wallRootLog k₀) := by
  have hmem : ∀ x ∈ uIcc k k₀, k ≤ x ∧ x ≤ k₀ := fun x hx => by
    rw [uIcc_of_le hkk] at hx
    exact hx
  have hd : ∀ x ∈ uIcc k k₀,
      HasDerivAt (fun v : ℝ => -2 * wallRootLog v) ((wallRootLog x)⁻¹ / x) x := by
    intro x hx
    obtain ⟨h1, h2⟩ := hmem x hx
    refine ((hasDerivAt_wallRootLog (lt_of_lt_of_le hk h1) (h2.trans hk4)).const_mul
      (-2)).congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun v => (wallRootLog v)⁻¹ / v) volume k k₀ :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx))
      (fun x hx => by
        obtain ⟨h1, _⟩ := hmem x (Ioo_subset_Icc_self hx)
        exact div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (lt_of_lt_of_le hk h1).le)
  have hI : ∫ v in k..k₀, (wallRootLog v)⁻¹ / v = -2 * wallRootLog k₀ - -2 * wallRootLog k :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  refine ⟨hint, ?_⟩
  rw [hI]
  ring

/-- **A bound on a collar integrates to a bound for the logarithmic moment.** -/
theorem wallLogMoment_le_of_ae_le {F : ℝ → ℝ} (hFm : Measurable F) (hF1 : Integrable F)
    {S k k₀ : ℝ} (hk : 0 < k) (hkk : k ≤ k₀) (hk4 : k₀ ≤ 1 / 4)
    (hS : ∀ᵐ u : ℝ, -k₀ < u → u < 0 → F u ≤ S * (wallRootLog (-u))⁻¹) :
    wallLogMoment F k ≤ wallLogMoment F k₀ + 2 * S * (wallRootLog k - wallRootLog k₀) := by
  have hint : IntegrableOn (fun v => F (-v) / v) (Ioi k) :=
    integrableOn_div_self (f := fun v => F (-v)) (hFm.comp measurable_neg) hF1.comp_neg hk
  have hint₀ : IntegrableOn (fun v => F (-v) / v) (Ioi k₀) := hint.mono_set (Ioi_subset_Ioi hkk)
  have hsplit : (∫ v in k..k₀, F (-v) / v) + ∫ v in Ioi k₀, F (-v) / v =
      ∫ v in Ioi k, F (-v) / v := intervalIntegral.integral_interval_add_Ioi hint hint₀
  obtain ⟨hgi, hgI⟩ := integral_inv_wallRootLog_div hk hkk hk4
  have hfi : IntervalIntegrable (fun v => F (-v) / v) volume k k₀ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hkk).mpr (hint.mono_set Ioc_subset_Ioi_self)
  have hS' : ∀ᵐ v : ℝ, -k₀ < -v → -v < 0 → F (-v) ≤ S * (wallRootLog (- -v))⁻¹ := ae_comp_neg hS
  have hne : ({k₀} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr Real.volume_singleton
  have hmono : ∫ v in k..k₀, F (-v) / v ≤ ∫ v in k..k₀, S * ((wallRootLog v)⁻¹ / v) := by
    refine intervalIntegral.integral_mono_ae_restrict hkk hfi (hgi.const_mul S) ?_
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hS', hne] with v hv hvne hmem
    have hv0 : 0 < v := lt_of_lt_of_le hk hmem.1
    have hvlt : v < k₀ := lt_of_le_of_ne hmem.2 fun h => hvne (mem_singleton_iff.mpr h)
    have h1 := hv (by linarith only [hvlt]) (by linarith only [hv0])
    rw [neg_neg] at h1
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 hv0.le
  rw [intervalIntegral.integral_const_mul, hgI] at hmono
  unfold wallLogMoment
  linarith only [hmono, hsplit]

/-! ### The barrier -/

/-- **The barrier at the wall.** For a minimizer at any ratio there is a constant `K` such that
on every collar `(−k, 0)`, `k ≤ 1/4`, the inequality `L_F(k)/2 + K + 13|A| ≤ A √log(1/k)` puts the
state below `A/√log(1/|u|)` on `(−k/4, 0)`. -/
theorem halfLineEnergyMinimizer_exists_wall_barrier {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℝ, 0 < k → k ≤ 1 / 4 → ∀ A : ℝ,
      wallLogMoment F k / 2 + K + 13 * |A| ≤ A * wallRootLog k →
      ∀ᵐ u : ℝ, -(k / 4) < u → u < 0 → F u ≤ A * (wallRootLog (-u))⁻¹ := by
  obtain ⟨C, M, hC0, hM0, hFC, hcomp⟩ := halfLineEnergyMinimizer_exists_wall_comparison hR hF
  have hd := hF.1
  have hI0 : 0 ≤ ∫ u, |F u| := integral_nonneg fun u => abs_nonneg _
  refine ⟨M + 1 + 4 * C + (∫ u, |F u|) / 4 + C / 2, by linarith only [hM0, hC0, hI0], ?_⟩
  intro k hk0 hk4 A hA
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = C + |A| := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact add_nonneg hC0 (abs_nonneg A)
  have hprofd := criticalHalfLineEnergyDomain_wallLogProfile hk4
  have hrampd := criticalHalfLineEnergyDomain_collarRamp hk0
  have hψd : CriticalHalfLineEnergyDomain
      (fun u => A * wallLogProfile k u + C₁ * collarRamp k u) :=
    (hprofd.const_mul A).add_const_mul hrampd C₁
  have hbd : ∀ u, |A * wallLogProfile k u| ≤ |A| := fun u => by
    rw [abs_mul, abs_of_nonneg (wallLogProfile_nonneg k u)]
    exact mul_le_of_le_one_right (abs_nonneg A) (wallLogProfile_le_one hk4 u)
  have hzero : ∀ u, u ≤ -k → A * wallLogProfile k u + C₁ * collarRamp k u = 0 := fun u hu => by
    rw [wallLogProfile_of_le hu, collarRamp_of_le hu, mul_zero, mul_zero, add_zero]
  have hB : ∀ u, |A * wallLogProfile k u + C₁ * collarRamp k u| ≤ |A| + C₁ := fun u => by
    have h1 := abs_le.mp (hbd u)
    have h2 : C₁ * collarRamp k u ≤ C₁ := mul_le_of_le_one_right hC₁0 (collarRamp_le_one k u)
    have h3 : 0 ≤ C₁ * collarRamp k u := mul_nonneg hC₁0 (collarRamp_nonneg k u)
    exact abs_le.mpr ⟨by linarith only [h1.1, h3, hC₁0], by linarith only [h1.2, h2]⟩
  have hbig : ∀ u, -k < u → u ≤ -(k / 2) →
      C ≤ A * wallLogProfile k u + C₁ * collarRamp k u := fun u hu1 hu2 => by
    have h1 := abs_le.mp (hbd u)
    rw [collarRamp_eq_one hk0 hu1 hu2, mul_one, hC₁]
    linarith only [h1.1]
  -- the barrier is a supersolution against the part of the state left of the collar
  have hsuper : ∀ δ u : ℝ, 0 < δ → δ ≤ 1 → -(k / 2) < u → u ≤ -δ →
      M + 1 ≤ cutoffLevy δ (fun u => A * wallLogProfile k u + C₁ * collarRamp k u) u -
        lineConvolution (symCutoffKernel δ) ((Iic (-k)).indicator F) u := by
    intro δ u hδ _ hu1 hu2
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, u = -t := ⟨-u, (neg_neg u).symm⟩
    have hδt : δ ≤ t := by linarith only [hu2]
    have htk : t < k / 2 := by linarith only [hu1]
    rw [cutoffLevy_linear hδ (measurable_wallLogProfile k) hprofd.sq (measurable_collarRamp k)
      hrampd.sq A C₁ (-t)]
    have h9 : |A * (cutoffLevy δ (wallLogProfile k) (-t) - wallRootLog k)| ≤ |A| * 9 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_cutoffLevy_wallLogProfile_sub_le hk4 hδ hδt htk)
        (abs_nonneg A)
    have h9' := (abs_le.mp h9).1
    have hr := mul_le_mul_of_nonneg_left (neg_four_le_cutoffLevy_collarRamp
      (by linarith only [hk4] : k ≤ 2) hδ hδt (by linarith only [htk, hk0] : t < k)) hC₁0
    have hext := (abs_le.mp (abs_exterior_sub_half_wallLogMoment_le hd.meas hd.integrable hd.sq
      hC0 hFC hδ hδt htk)).2
    linarith only [h9', hr, hext, hA, hC₁]
  have hae := hcomp k hk0 (by linarith only [hk4]) _ hψd hzero (|A| + C₁) hB hbig 1 one_pos hsuper
  filter_upwards [hae] with u hu hu1 hu2
  have h := hu (by linarith only [hu1, hk0]) hu2
  have e : A * wallLogProfile k u + C₁ * collarRamp k u = A * (wallRootLog (-u))⁻¹ := by
    rw [wallLogProfile_of_mem (by linarith only [hu1, hk0]) hu2,
      collarRamp_eq_zero hk0 hu1.le hu2, mul_zero, add_zero]
  exact h.trans e.le

/-- A limit of the logarithmic moment bounds the state from above at the wall. -/
theorem halfLineEnergyMinimizer_wall_upper_of_tendsto {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {c : ℝ}
    (hlim : Tendsto (fun k : ℝ => wallLogMoment F k / wallRootLog k) (𝓝[>] 0) (𝓝 (2 * c)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℝ, 0 < k ∧ ∀ᵐ u : ℝ, -k < u → u < 0 → F u ≤ (c + ε) * (wallRootLog (-u))⁻¹ := by
  obtain ⟨K, _, hbar⟩ := halfLineEnergyMinimizer_exists_wall_barrier hR hF
  have h1 : ∀ᶠ k : ℝ in 𝓝[>] 0, wallLogMoment F k / wallRootLog k < 2 * c + ε :=
    hlim.eventually (gt_mem_nhds (by linarith only [hε]))
  have h2 : ∀ᶠ k : ℝ in 𝓝[>] 0, 2 * (K + 13 * |c + ε|) / ε ≤ wallRootLog k :=
    tendsto_wallRootLog_nhdsGT_zero.eventually_ge_atTop _
  have h3 : ∀ᶠ k : ℝ in 𝓝[>] 0, k ∈ Ioo (0 : ℝ) (1 / 4) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨k, hk1, hk2, hk0, hk4⟩ := (h1.and (h2.and h3)).exists
  have hw : 0 < wallRootLog k := lt_of_lt_of_le one_pos (one_le_wallRootLog hk0 hk4.le)
  have hk1' : wallLogMoment F k < (2 * c + ε) * wallRootLog k := (div_lt_iff₀ hw).mp hk1
  have hk2' : 2 * (K + 13 * |c + ε|) ≤ wallRootLog k * ε := (div_le_iff₀ hε).mp hk2
  exact ⟨k / 4, by positivity,
    hbar k hk0 hk4.le (c + ε) (by linarith only [hk1', hk2'])⟩

/-! ### The logarithmic moment converges on the scale of the wall -/

/-- A minimizer is bounded above by a multiple of the inverse root logarithm on a collar. -/
theorem halfLineEnergyMinimizer_exists_ae_le_inv_wallRootLog {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ S k : ℝ, 0 ≤ S ∧ 0 < k ∧ k ≤ 1 / 4 ∧
      ∀ᵐ u : ℝ, -k < u → u < 0 → F u ≤ S * (wallRootLog (-u))⁻¹ := by
  obtain ⟨K, _, hbar⟩ := halfLineEnergyMinimizer_exists_wall_barrier hR hF
  have h2 : ∀ᶠ k : ℝ in 𝓝[>] 0, (14 : ℝ) ≤ wallRootLog k :=
    tendsto_wallRootLog_nhdsGT_zero.eventually_ge_atTop _
  have h3 : ∀ᶠ k : ℝ in 𝓝[>] 0, k ∈ Ioo (0 : ℝ) (1 / 4) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨k, hk2, hk0, hk4⟩ := (h2.and h3).exists
  refine ⟨|wallLogMoment F k / 2 + K|, k / 4, abs_nonneg _, by positivity,
    by linarith only [hk4], hbar k hk0 hk4.le _ ?_⟩
  rw [abs_abs]
  have h1 := le_abs_self (wallLogMoment F k / 2 + K)
  have h0 := mul_le_mul_of_nonneg_left hk2 (abs_nonneg (wallLogMoment F k / 2 + K))
  linarith only [h1, h0]

/-- The logarithmic moment of a minimizer is of the order of the root logarithm. -/
theorem halfLineEnergyMinimizer_exists_abs_wallLogMoment_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ G k₀ : ℝ, 0 ≤ G ∧ 0 < k₀ ∧ k₀ ≤ 1 / 4 ∧
      ∀ k : ℝ, 0 < k → k ≤ k₀ → |wallLogMoment F k| ≤ G * wallRootLog k := by
  obtain ⟨S₁, k₁, hS₁, hk₁, hk₁4, h₁⟩ := halfLineEnergyMinimizer_exists_ae_le_inv_wallRootLog hR hF
  obtain ⟨S₂, k₂, hS₂, hk₂, hk₂4, h₂⟩ :=
    halfLineEnergyMinimizer_exists_ae_le_inv_wallRootLog hR hF.neg
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℝ, k₀ = min k₁ k₂ := ⟨_, rfl⟩
  have hk₀pos : 0 < k₀ := by
    rw [hk₀]
    exact lt_min hk₁ hk₂
  have hk₀1 : k₀ ≤ k₁ := by
    rw [hk₀]
    exact min_le_left _ _
  have hk₀2 : k₀ ≤ k₂ := by
    rw [hk₀]
    exact min_le_right _ _
  have hk₀4 : k₀ ≤ 1 / 4 := hk₀1.trans hk₁4
  have h₁' : ∀ᵐ u : ℝ, -k₀ < u → u < 0 → F u ≤ S₁ * (wallRootLog (-u))⁻¹ :=
    h₁.mono fun u hu h1 h2 => hu (by linarith only [h1, hk₀1]) h2
  have h₂' : ∀ᵐ u : ℝ, -k₀ < u → u < 0 → -F u ≤ S₂ * (wallRootLog (-u))⁻¹ :=
    h₂.mono fun u hu h1 h2 => hu (by linarith only [h1, hk₀2]) h2
  refine ⟨|wallLogMoment F k₀| + 2 * S₁ + 2 * S₂, k₀, by positivity, hk₀pos, hk₀4, ?_⟩
  intro k hk hkk
  have hw := one_le_wallRootLog hk (hkk.trans hk₀4)
  have hw₀ : 0 ≤ wallRootLog k₀ := Real.sqrt_nonneg _
  have ha := wallLogMoment_le_of_ae_le hF.1.meas hF.1.integrable hk hkk hk₀4 h₁'
  have hb := wallLogMoment_le_of_ae_le hF.neg.1.meas hF.neg.1.integrable hk hkk hk₀4 h₂'
  rw [wallLogMoment_neg, wallLogMoment_neg] at hb
  have hL := abs_le.mp (le_refl |wallLogMoment F k₀|)
  have hA0 := abs_nonneg (wallLogMoment F k₀)
  have p1 := mul_nonneg hS₁ hw₀
  have p2 := mul_nonneg hS₂ hw₀
  have p3 := mul_nonneg hA0 (sub_nonneg.mpr hw)
  have p4 := mul_nonneg hS₁ (sub_nonneg.mpr hw)
  have p5 := mul_nonneg hS₂ (sub_nonneg.mpr hw)
  rw [abs_le]
  constructor <;> linarith only [ha, hb, hL.1, hL.2, p1, p2, p3, p4, p5, hS₁, hS₂]

/-- **The quotient `L_F(k)/√log(1/k)` cannot increase towards the wall.** For every small `k` its
later values exceed the value at `k` by at most `ε`. -/
theorem halfLineEnergyMinimizer_wallLogMoment_eventually_le {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) {ε : ℝ} (hε : 0 < ε) :
    ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, 0 < k → k < k₀ → ∀ᶠ k' : ℝ in 𝓝[>] 0,
      wallLogMoment F k' / wallRootLog k' ≤ wallLogMoment F k / wallRootLog k + ε := by
  obtain ⟨K, _, hbar⟩ := halfLineEnergyMinimizer_exists_wall_barrier hR hF
  obtain ⟨G, k₂, hG, hk₂, hk₂4, hGb⟩ := halfLineEnergyMinimizer_exists_abs_wallLogMoment_le hR hF
  have h1 : ∀ᶠ k : ℝ in 𝓝[>] 0, 4 * (K + 13 * (G / 2 + ε / 4)) / ε ≤ wallRootLog k :=
    tendsto_wallRootLog_nhdsGT_zero.eventually_ge_atTop _
  have h2 : ∀ᶠ k : ℝ in 𝓝[>] 0, k ∈ Ioo (0 : ℝ) k₂ := Ioo_mem_nhdsGT hk₂
  obtain ⟨k₀, hk₀W, hk₀pos, hk₀k₂⟩ := (h1.and h2).exists
  refine ⟨k₀, hk₀pos, fun k hk hkk₀ => ?_⟩
  have hk4 : k ≤ 1 / 4 := by linarith only [hkk₀, hk₀k₂, hk₂4]
  have hw1 := one_le_wallRootLog hk hk4
  have hw : 0 < wallRootLog k := lt_of_lt_of_le one_pos hw1
  have hW : 4 * (K + 13 * (G / 2 + ε / 4)) ≤ wallRootLog k * ε :=
    (div_le_iff₀ hε).mp (hk₀W.trans (wallRootLog_anti hk hkk₀.le))
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = wallLogMoment F k / wallRootLog k := ⟨_, rfl⟩
  have hqw : q * wallRootLog k = wallLogMoment F k := by
    rw [hq, div_mul_cancel₀ _ hw.ne']
  have hqG : |q| ≤ G := by
    rw [hq, abs_div, abs_of_pos hw, div_le_iff₀ hw]
    exact hGb k hk (by linarith only [hkk₀, hk₀k₂])
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = q / 2 + ε / 4 := ⟨_, rfl⟩
  have hAabs : |A| ≤ G / 2 + ε / 4 := by
    have h := abs_le.mp hqG
    rw [hAdef]
    exact abs_le.mpr ⟨by linarith only [h.1, hε], by linarith only [h.2]⟩
  have hAw : A * wallRootLog k = wallLogMoment F k / 2 + ε / 4 * wallRootLog k := by
    rw [hAdef, ← hqw]
    ring
  have hbelow := hbar k hk hk4 A (by linarith only [hAw, hAabs, hW])
  -- integrate the barrier bound from `k/4` towards the wall
  have hk4pos : 0 < k / 4 := by positivity
  have hk44 : k / 4 ≤ 1 / 4 := by linarith only [hk4, hk]
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = wallLogMoment F (k / 4) - 2 * A * wallRootLog (k / 4) :=
    ⟨_, rfl⟩
  have h3 : ∀ᶠ k' : ℝ in 𝓝[>] 0, 2 * |D| / ε ≤ wallRootLog k' :=
    tendsto_wallRootLog_nhdsGT_zero.eventually_ge_atTop _
  have h4 : ∀ᶠ k' : ℝ in 𝓝[>] 0, k' ∈ Ioo (0 : ℝ) (k / 4) := Ioo_mem_nhdsGT hk4pos
  filter_upwards [h3, h4] with k' hk'W hk'
  have hw' : 0 < wallRootLog k' :=
    lt_of_lt_of_le one_pos (one_le_wallRootLog hk'.1 (hk'.2.le.trans hk44))
  have hB := wallLogMoment_le_of_ae_le hF.1.meas hF.1.integrable hk'.1 hk'.2.le hk44 hbelow
  have hW' : 2 * |D| ≤ wallRootLog k' * ε := (div_le_iff₀ hε).mp hk'W
  have hAw' : A * wallRootLog k' = q / 2 * wallRootLog k' + ε / 4 * wallRootLog k' := by
    rw [hAdef]
    ring
  rw [← hq, div_le_iff₀ hw']
  linarith only [hB, hW', hAw', hD, le_abs_self D]

/-- **The logarithmic moment converges on the scale of the wall.** -/
theorem halfLineEnergyMinimizer_exists_tendsto_wallLogMoment {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ ℓ : ℝ, Tendsto (fun k : ℝ => wallLogMoment F k / wallRootLog k) (𝓝[>] 0) (𝓝 (2 * ℓ)) := by
  have hcauchy : Cauchy (map (fun k : ℝ => wallLogMoment F k / wallRootLog k) (𝓝[>] 0)) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨k₁, hk₁, h₁⟩ :=
      halfLineEnergyMinimizer_wallLogMoment_eventually_le hR hF (ε := ε / 3) (by positivity)
    obtain ⟨k₂, hk₂, h₂⟩ :=
      halfLineEnergyMinimizer_wallLogMoment_eventually_le hR hF.neg (ε := ε / 3) (by positivity)
    have key : ∀ a b : ℝ, a ∈ Ioo 0 (min k₁ k₂) → b ∈ Ioo 0 (min k₁ k₂) →
        wallLogMoment F b / wallRootLog b ≤ wallLogMoment F a / wallRootLog a + 2 * (ε / 3) := by
      intro a b ha hb
      have ea := h₁ a ha.1 (lt_of_lt_of_le ha.2 (min_le_left _ _))
      have eb := h₂ b hb.1 (lt_of_lt_of_le hb.2 (min_le_right _ _))
      obtain ⟨k', hk'a, hk'b⟩ := (ea.and eb).exists
      rw [wallLogMoment_neg, wallLogMoment_neg, neg_div, neg_div] at hk'b
      linarith only [hk'a, hk'b]
    refine ⟨(fun k : ℝ => wallLogMoment F k / wallRootLog k) '' Ioo 0 (min k₁ k₂),
      image_mem_map (Ioo_mem_nhdsGT (lt_min hk₁ hk₂)), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show dist (wallLogMoment F a / wallRootLog a) (wallLogMoment F b / wallRootLog b) < ε
    have h1 := key a b ha hb
    have h2 := key b a hb ha
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [h1, h2, hε]
  obtain ⟨x, hx⟩ := cauchy_map_iff_exists_tendsto.mp hcauchy
  refine ⟨x / 2, ?_⟩
  rw [show 2 * (x / 2) = x by ring]
  exact hx

/-! ### The amplitude -/

/-- **Every confined ground state has an amplitude at the wall.** For a minimizer `F` at any ratio
there is `ℓ` with `L_F(k)/√log(1/k) → 2ℓ` as `k → 0⁺` and `√log(1/|u|) F(u) → ℓ` essentially as
`u → 0⁻`. -/
theorem halfLineEnergyMinimizer_exists_wallAmplitude {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : IsHalfLineEnergyMinimizer R F) :
    ∃ ℓ : ℝ,
      Tendsto (fun k : ℝ => wallLogMoment F k / Real.sqrt (Real.log (1 / k))) (𝓝[>] 0)
        (𝓝 (2 * ℓ)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ k : ℝ, 0 < k ∧ ∀ᵐ u : ℝ, -k < u → u < 0 →
        |Real.sqrt (Real.log (1 / (-u))) * F u - ℓ| ≤ ε := by
  obtain ⟨ℓ, hℓ⟩ := halfLineEnergyMinimizer_exists_tendsto_wallLogMoment hR hF
  refine ⟨ℓ, hℓ, fun ε hε => ?_⟩
  obtain ⟨k₁, hk₁, h₁⟩ := halfLineEnergyMinimizer_wall_upper_of_tendsto hR hF hℓ hε
  have hℓ' : Tendsto (fun k : ℝ => wallLogMoment (fun u => -F u) k / wallRootLog k) (𝓝[>] 0)
      (𝓝 (2 * -ℓ)) := by
    have h := hℓ.neg
    rw [show -(2 * ℓ) = 2 * -ℓ by ring] at h
    refine h.congr fun k => ?_
    show -(wallLogMoment F k / wallRootLog k) = wallLogMoment (fun u => -F u) k / wallRootLog k
    rw [wallLogMoment_neg, neg_div]
  obtain ⟨k₂, hk₂, h₂⟩ := halfLineEnergyMinimizer_wall_upper_of_tendsto hR hF.neg hℓ' hε
  refine ⟨min (min k₁ k₂) (1 / 4), lt_min (lt_min hk₁ hk₂) (by norm_num), ?_⟩
  filter_upwards [h₁, h₂] with u hu₁ hu₂ hu hu0
  have hm1 := min_le_left (min k₁ k₂) (1 / 4 : ℝ)
  have hm2 := min_le_right (min k₁ k₂) (1 / 4 : ℝ)
  have hm3 := min_le_left k₁ k₂
  have hm4 := min_le_right k₁ k₂
  have hw0 : 0 < wallRootLog (-u) := lt_of_lt_of_le one_pos
    (one_le_wallRootLog (by linarith only [hu0]) (by linarith only [hu, hm2]))
  have ha : F u ≤ (ℓ + ε) * (wallRootLog (-u))⁻¹ := hu₁ (by linarith only [hu, hm1, hm3]) hu0
  have hb : -F u ≤ (-ℓ + ε) * (wallRootLog (-u))⁻¹ :=
    hu₂ (by linarith only [hu, hm1, hm4]) hu0
  have ha' := mul_le_mul_of_nonneg_left ha hw0.le
  have hb' := mul_le_mul_of_nonneg_left hb hw0.le
  have e1 : wallRootLog (-u) * ((ℓ + ε) * (wallRootLog (-u))⁻¹) = ℓ + ε := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hw0.ne', mul_one]
  have e2 : wallRootLog (-u) * ((-ℓ + ε) * (wallRootLog (-u))⁻¹) = -ℓ + ε := by
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ hw0.ne', mul_one]
  show |wallRootLog (-u) * F u - ℓ| ≤ ε
  rw [abs_le]
  constructor <;> linarith only [ha', hb', e1, e2]

end GaloisForLFunctions.ExclusionOfTheCriticalState
