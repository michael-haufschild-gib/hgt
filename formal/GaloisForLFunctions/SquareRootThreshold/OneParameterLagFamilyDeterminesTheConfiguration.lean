import GaloisForLFunctions.SquareRootThreshold.RealZerosCannotHideFromTheLagFamily
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# The lag family determines the configuration

For a generic width `w` the one-parameter family `f_v = κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`,
decides the critical line (`onLine_iff_lag_twoBump_nonneg_of_lt_one`). It also determines the
configuration, up to exactly the two ambiguities that real odd tests cannot see.

* **Uniqueness of exponential sums** (`eq_zero_of_tsum_cexp_eq_zero`). Let the heights of the
  exponents be locally finite. If `Σ_t q_t e^{λ_t v} = 0` for `v ≥ V`, then `q_t = 0` whenever
  `Re λ_t ≥ 0`. The exponents right of the imaginary axis die at their top poles
  (`eq_zero_of_norm_tsum_exp_le_exp`). Those on the axis die under Cesàro means
  (`eq_zero_of_tsum_exp_eq_zero_of_re_nonpos`).
* **Determination** (`symmMult_eq_of_lag_weil_eq`). `Re W(f_v, f_v) = 2 Re S(0) − 2 Re S(v)`,
  so equal lag data make `2 Re S_Z − 2 Re S_{Z'}` constant on `[V, ∞)`. The merged coefficients
  therefore agree at every exponent `z ≠ 0`; left exponents follow by reflection. At the center
  `0` the coefficient is `(m(ρ) + m(ρ̄)) h_w(γ_ρ)²` (`evenCoeff_modScaledBump_zero_eq`), so
  `m(ρ) + m(ρ̄)` agree at every `ρ ≠ ½` once `h_w` vanishes at no zero ordinate (true for all but
  countably many `w`).
* **Exactness** (`lag_weil_eq_iff_symmMult_eq`). Conversely, equal `m(ρ) + m(ρ̄)` off `½` give
  equal lag data at every lag: the exponent `0` carries `s = ½` and cancels from
  `2 Re S(0) − 2 Re S(v)`. So the family sees precisely the conjugation-symmetrized
  multiplicities off `½`. Conjugation-symmetric configurations with the same multiplicity at `½`
  are determined (`eq_of_lag_weil_eq_of_conj`); in particular so is the zero set of `ζ`
  (`eq_zetaZeroConfig_of_lag_weil_eq`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Uniqueness of exponential sums -/

/-- **Cesàro means on the imaginary axis.** If `Re λ_t ≤ 0` for all `t`,
`Σ_t |q_t| < ∞` and `Σ_t q_t e^{λ_t v} = 0` for every `v ≥ 0`, then `q_{t₁} = 0` for every
`t₁` with `Re λ_{t₁} = 0` whose exponent is unshared. -/
theorem eq_zero_of_tsum_exp_eq_zero_of_re_nonpos {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) (hre : ∀ t, (lam t).re ≤ 0) (t₁ : ι) (h₁ : (lam t₁).re = 0)
    (hinj : ∀ t, lam t = lam t₁ → t = t₁)
    (h0 : ∀ v : ℝ, 0 ≤ v → ∑' t, q t * cexp (lam t * v) = 0) : q t₁ = 0 := by
  classical
  -- the means `c_t(T) = T⁻¹ ∫_0^T e^{(λ_t − λ_{t₁})v} dv`
  set c : ι → ℝ → ℂ := fun t T => (T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, cexp ((lam t - lam t₁) * v)
    with hc
  have hexp_le : ∀ t, ∀ v : ℝ, 0 ≤ v → ‖cexp ((lam t - lam t₁) * v)‖ ≤ 1 := fun t v hv => by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have : ((lam t - lam t₁) * (v : ℂ)).re = ((lam t).re - (lam t₁).re) * v := by simp
    rw [this, h₁, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (hre t) hv
  have hc_le : ∀ t, ∀ T : ℝ, 0 < T → ‖c t T‖ ≤ 1 := fun t T hT => by
    rw [hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
      (f := fun v : ℝ => cexp ((lam t - lam t₁) * v)) fun v hv => by
        rw [Set.uIoc_of_le hT.le] at hv
        exact hexp_le t v hv.1.le
    rw [sub_zero, abs_of_pos hT, one_mul] at h
    calc T⁻¹ * ‖∫ v in (0 : ℝ)..T, cexp ((lam t - lam t₁) * v)‖ ≤ T⁻¹ * T :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hT.le)
      _ = 1 := inv_mul_cancel₀ hT.ne'
  have hc₁ : ∀ T : ℝ, 0 < T → c t₁ T = 1 := fun T hT => by
    simp only [hc, sub_self, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hT.ne')
  have hc_lim : ∀ t, t ≠ t₁ → Tendsto (c t) atTop (𝓝 0) := fun t ht => by
    have ha : lam t - lam t₁ ≠ 0 := sub_ne_zero.mpr fun h => ht (hinj t h)
    have hbound : ∀ T : ℝ, 0 < T → ‖c t T‖ ≤ 2 / ‖lam t - lam t₁‖ * T⁻¹ := fun T hT => by
      show ‖(T : ℂ)⁻¹ * ∫ v in (0 : ℝ)..T, cexp ((lam t - lam t₁) * v)‖ ≤ _
      rw [integral_exp_mul_complex ha, norm_mul, norm_div, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hT]
      have h1 : ‖cexp ((lam t - lam t₁) * T) - cexp ((lam t - lam t₁) * ((0 : ℝ) : ℂ))‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        have := hexp_le t T hT.le
        have := hexp_le t 0 le_rfl
        linarith
      rw [mul_comm]
      gcongr
    refine squeeze_zero_norm' (a := fun T => 2 / ‖lam t - lam t₁‖ * T⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact hbound T hT
    · simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2 / ‖lam t - lam t₁‖)
  -- the means of the vanishing sum vanish
  have hmean : ∀ T : ℝ, 0 < T → ∑' t, q t * c t T = 0 := fun T hT => by
    have hHas := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := volume) (a := 0) (b := T) (F := fun t (v : ℝ) => q t * cexp ((lam t - lam t₁) * v))
      (f := fun v => ∑' t, q t * cexp ((lam t - lam t₁) * v)) (fun t _ => ‖q t‖)
      (fun t => (by fun_prop : Continuous fun v : ℝ => q t * cexp ((lam t - lam t₁) * v))
        |>.aestronglyMeasurable)
      (fun t => Eventually.of_forall fun v hv => by
        rw [Set.uIoc_of_le hT.le] at hv
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hexp_le t v hv.1.le))
      (Eventually.of_forall fun _ _ => hq) intervalIntegrable_const
      (Eventually.of_forall fun v hv => by
        rw [Set.uIoc_of_le hT.le] at hv
        exact (Summable.of_norm_bounded hq fun t => by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hexp_le t v hv.1.le)).hasSum)
    have hzero : ∫ v in (0 : ℝ)..T, ∑' t, q t * cexp ((lam t - lam t₁) * v) = 0 := by
      have hpt : Set.EqOn (fun v : ℝ => ∑' t, q t * cexp ((lam t - lam t₁) * v))
          (fun _ => (0 : ℂ)) (Ioc 0 T) := fun v hv => by
        have e : ∑' t, q t * cexp ((lam t - lam t₁) * v) =
          cexp (-(lam t₁ * v)) * ∑' t, q t * cexp (lam t * v) := by
          rw [← tsum_mul_left]
          refine tsum_congr fun t => ?_
          rw [mul_left_comm, ← Complex.exp_add]
          congr 2
          ring
        show ∑' t, q t * cexp ((lam t - lam t₁) * v) = 0
        rw [e, h0 v hv.1.le, mul_zero]
      rw [intervalIntegral.integral_of_le hT.le, setIntegral_congr_fun measurableSet_Ioc hpt]
      simp
    rw [hzero] at hHas
    have hsum0 : ∑' t, q t * ∫ v in (0 : ℝ)..T, cexp ((lam t - lam t₁) * v) = 0 := by
      rw [← hHas.tsum_eq]
      exact tsum_congr fun t => (intervalIntegral.integral_const_mul (q t) _).symm
    calc ∑' t, q t * c t T
        = (T : ℂ)⁻¹ * ∑' t, q t * ∫ v in (0 : ℝ)..T, cexp ((lam t - lam t₁) * v) := by
          rw [← tsum_mul_left]
          exact tsum_congr fun t => by simp only [hc]; ring
      _ = 0 := by rw [hsum0, mul_zero]
  -- pass to the limit
  have hlim : Tendsto (fun T : ℝ => ∑' t, q t * c t T) atTop (𝓝 (q t₁)) := by
    rw [← tsum_ite_eq t₁ q]
    refine tendsto_tsum_of_dominated_convergence hq (fun t => ?_) ?_
    · by_cases ht : t = t₁
      · subst ht
        rw [if_pos rfl]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop 0] with T hT
        rw [hc₁ T hT, mul_one]
      · rw [if_neg ht]
        simpa using (hc_lim t ht).const_mul (q t)
    · filter_upwards [eventually_gt_atTop 0] with T hT t
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hc_le t T hT)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact (hmean T hT).symm))

/-- Locally finite heights are separated around every height. -/
theorem exists_sep_of_locFinite {ι : Type*} {lam : ι → ℂ}
    (hloc : ∀ γ : ℝ, {t | |(lam t).im - γ| < 1}.Finite) (γ : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ t, |(lam t).im - γ| < η → (lam t).im = γ := by
  classical
  set F := (hloc γ).toFinset with hF
  set G := insert (1 : ℝ) ((F.filter fun t => (lam t).im ≠ γ).image fun t => |(lam t).im - γ|)
    with hG
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  refine ⟨G.min' hGne, ?_, fun t hlt => ?_⟩
  · rcases Finset.mem_insert.mp (G.min'_mem hGne) with h | h
    · rw [h]; exact one_pos
    obtain ⟨t, ht, h⟩ := Finset.mem_image.mp h
    rw [← h]
    exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp ht).2)
  · by_contra hne
    have h1 : G.min' hGne ≤ 1 := G.min'_le _ (Finset.mem_insert_self _ _)
    have hmem : t ∈ F := (Set.Finite.mem_toFinset _).mpr (hlt.trans_le h1)
    have := G.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨t, Finset.mem_filter.mpr ⟨hmem, hne⟩, rfl⟩))
    linarith

/-- **Uniqueness of exponential sums.** Let `Σ_t |q_t| < ∞`, `Re λ_t ≤ A`, `λ` injective, and let
each horizontal band of height `2` contain finitely many exponents. If `Σ_t q_t e^{λ_t v} = 0`
for every `v ≥ V`, then `q_t = 0` whenever `Re λ_t ≥ 0`. -/
theorem eq_zero_of_tsum_cexp_eq_zero {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) {A : ℝ} (hA : ∀ t, (lam t).re ≤ A)
    (hinj : Function.Injective lam) (hloc : ∀ γ : ℝ, {t | |(lam t).im - γ| < 1}.Finite) {V : ℝ}
    (h0 : ∀ v : ℝ, V ≤ v → ∑' t, q t * cexp (lam t * v) = 0) {t₁ : ι}
    (h₁ : 0 ≤ (lam t₁).re) : q t₁ = 0 := by
  classical
  -- shift to `v ≥ 0`
  set W := max V 0 with hW
  have hW0 : 0 ≤ W := le_max_right _ _
  set q' : ι → ℂ := fun t => q t * cexp (lam t * W) with hq'def
  have hq' : Summable fun t => ‖q' t‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => ?_)
      (hq.mul_right (Real.exp (|A| * W)))
    rw [hq'def, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (lam t * (W : ℂ)).re = (lam t).re * W := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_right ((hA t).trans (le_abs_self A)) hW0
  have h0' : ∀ u : ℝ, 0 ≤ u → ∑' t, q' t * cexp (lam t * u) = 0 := fun u hu => by
    rw [← h0 (W + u) ((le_max_left V 0).trans (by linarith))]
    refine tsum_congr fun t => ?_
    rw [hq'def, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hne' : ∀ t, q' t = 0 → q t = 0 := fun t h =>
    (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
  set S : Set ι := {t | q' t ≠ 0} with hS
  have hsumS : ∀ u : ℝ, 0 ≤ u → ∑' t : S, q' t * cexp (lam t * u) = 0 := fun u hu => by
    rw [tsum_subtype_eq_of_support_subset (s := S)
      (f := fun t => q' t * cexp (lam t * u)) fun t ht h0 =>
        ht (show q' t * cexp (lam t * u) = 0 by rw [h0, zero_mul])]
    exact h0' u hu
  haveI : Countable S := Set.to_countable S
  -- right of the imaginary axis: no top pole
  have hright : ∀ t, 0 < (lam t).re → q' t = 0 := by
    intro t ht
    by_contra hne
    set L := ((hloc (lam t).im).inter_of_left {s | q' s ≠ 0 ∧ (lam s).im = (lam t).im}).toFinset
      with hL
    have htL : t ∈ L := (Set.Finite.mem_toFinset _).mpr ⟨by simp, hne, rfl⟩
    obtain ⟨s₀, hs₀L, hmax⟩ := L.exists_max_image (fun s => (lam s).re) ⟨t, htL⟩
    obtain ⟨-, hs₀, him₀⟩ := (Set.Finite.mem_toFinset _).mp hs₀L
    have hre₀ : (lam t).re ≤ (lam s₀).re := hmax t htL
    obtain ⟨η, hη, hsep⟩ := exists_sep_of_locFinite hloc (lam s₀).im
    have h := eq_zero_of_norm_tsum_exp_le_exp (ι := S) (lam := fun s => lam s)
      (q := fun s => q' s) (hq'.subtype S) (A := A) (fun s => hA s) (σ := 0) ⟨s₀, hs₀⟩
      (by linarith) (fun s hs => hmax s ((Set.Finite.mem_toFinset _).mpr
        ⟨by simp [hs, him₀], s.2, hs.trans him₀⟩))
      (fun s hs => Subtype.ext (hinj hs)) hη (fun s hs => hsep s hs) (K := 0)
      (fun u hu => by rw [hsumS u hu, norm_zero, zero_mul])
    exact hs₀ h
  -- on the imaginary axis: Cesàro means
  by_contra hne
  have hne₁ : q' t₁ ≠ 0 := fun h => hne (hne' t₁ h)
  have hre : (lam t₁).re = 0 := le_antisymm (by
    by_contra h; exact hne₁ (hright t₁ (not_le.mp h))) h₁
  have h := eq_zero_of_tsum_exp_eq_zero_of_re_nonpos (ι := S) (lam := fun s => lam s)
    (q := fun s => q' s) (hq'.subtype S) (fun s => by
      by_contra h; exact s.2 (hright s (not_le.mp h))) ⟨t₁, hne₁⟩ hre
    (fun s hs => Subtype.ext (hinj hs)) hsumS
  exact hne₁ h

/-! ### The lag family determines the configuration -/

/-- The merged coefficient of the unmodulated bump: `D(z) = (m(½ + z) + m(½ + z̄)) h_w(−iz)²`,
with `m = 0` off the carrier. -/
theorem evenCoeff_modScaledBump_zero_eq (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (z : ℂ) :
    evenCoeff Z (modScaledBump w 0) z =
      (Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + z) +
        Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + conj z)) *
        paperFT (scaledBump w) (-(I * z)) ^ 2 := by
  by_cases hz : (1 / 2 + z) ∈ Z.carrier
  · rw [evenCoeff_modScaledBump_zero Z hw hz, Set.indicator_of_mem hz]
  · rw [evenCoeff, lagCoeff, Set.indicator_of_notMem hz, zero_add, Set.indicator_of_notMem hz,
      zero_add]
    by_cases hzc : (1 / 2 + conj z) ∈ Z.carrier
    · rw [lagCoeff_modScaledBump Z hw 0 hzc, Complex.ofReal_zero, sub_zero, map_mul,
        Complex.conj_natCast, map_pow, conj_paperFT_scaledBump, Set.indicator_of_mem hzc]
      congr 2
      rw [← paperFT_scaledBump_neg w]
      congr 1
      simp [map_neg, map_mul]
    · rw [lagCoeff, Set.indicator_of_notMem hzc, Set.indicator_of_notMem hzc, map_zero, zero_mul]

/-- **Reflection of merged coefficients:** `D(−z̄) = conj D(z)`. -/
theorem evenCoeff_neg_conj (Z : ZeroConfig) {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (z : ℂ) : evenCoeff Z b (-conj z) = conj (evenCoeff Z b z) := by
  have h1 := lagCoeff_neg_conj Z hb hbc z
  have h2 := lagCoeff_neg_conj Z hb hbc (conj z)
  rw [Complex.conj_conj] at h2
  rw [evenCoeff, evenCoeff, map_neg, Complex.conj_conj, h1, h2, map_add, Complex.conj_conj]

/-- The odd lag test reads the real part of the lag structure:
`Re W(f_v, f_v) = 2 Re S(0) − 2 Re S(v)` for `f_v = b(· + v/2) − b(· − v/2)`. -/
theorem re_W_lag_eq (Y : ZeroConfig) (hY : TemperedConfig Y) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b)
    {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) (v : ℝ) :
    (Y.W (twoBump b v (-1)) (twoBump b v (-1))).re =
      2 * (lagStructure Y b 0).re - 2 * (lagStructure Y b v).re := by
  rw [re_W_unit_twoBump Y hY hb hbs v (by simp), show lagStructure Y b v +
    conj (lagStructure Y b (-v)) = 2 * lagStructure Y b v by
      rw [conj_lagStructure_neg Y hY hb hbs v]; ring]
  simp only [neg_mul, one_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  ring

/-- **The lag family determines the symmetrized multiplicities.** Let `Z, Z'` be tempered and let
`h_w` vanish at no zero ordinate of `Z` or `Z'`. If the tests `κ_w(t + v/2) − κ_w(t − v/2)` have
the same `Re W` for both configurations at every lag `v ≥ V`, then `m(ρ) + m(ρ̄)` agree at every
`ρ ≠ ½`. -/
theorem symmMult_eq_of_lag_weil_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {V : ℝ}
    (hW : ∀ v : ℝ, V ≤ v → (Z.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re = (Z'.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re)
    {ρ : ℂ} (hρ : ρ ≠ 1 / 2) :
    Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) ρ +
        Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (conj ρ) =
      Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) ρ +
        Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) (conj ρ) := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  have hbc : HasCompactSupport b := hasCompactSupport_of_support_subset_abs hbs
  -- `Re S_Z − Re S_{Z'}` is constant on `[V, ∞)`
  set c := (lagStructure Z b 0).re - (lagStructure Z' b 0).re with hc
  have hRe : ∀ v : ℝ, V ≤ v → (lagStructure Z b v).re - (lagStructure Z' b v).re = c := by
    intro v hv
    have h := hW v hv
    rw [re_W_lag_eq Z hZ hb hbs, re_W_lag_eq Z' hZ' hb hbs] at h
    rw [hc]
    linarith
  -- the difference as an exponential sum with no constant term
  set q : ℂ → ℂ := fun z =>
    evenCoeff Z b z - evenCoeff Z' b z - if z = 0 then 2 * (c : ℂ) else 0
    with hq
  obtain ⟨hs, -⟩ := two_re_lagStructure_eq Z hZ hb hbs 0
  have hDs : ∀ Y : ZeroConfig, TemperedConfig Y → Summable fun z : ℂ => ‖evenCoeff Y b z‖ :=
    fun Y hY => by
      have h0 := (two_re_lagStructure_eq Y hY hb hbs 0).1.norm
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
      exact h0
  have hqs : Summable fun z : ℂ => ‖q z‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
      (((hDs Z hZ).add (hDs Z' hZ')).add
        ((summable_of_ne_finset_zero (s := {0}) (f := fun z : ℂ =>
          if z = 0 then ‖2 * (c : ℂ)‖ else 0) fun z hz => by simp_all)))
    rw [hq]
    refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
    split_ifs <;> simp
  have hzero : ∀ v : ℝ, V ≤ v → ∑' z : ℂ, q z * cexp (z * v) = 0 := by
    intro v hv
    obtain ⟨h1, e1⟩ := two_re_lagStructure_eq Z hZ hb hbs v
    obtain ⟨h2, e2⟩ := two_re_lagStructure_eq Z' hZ' hb hbs v
    have h3 : Summable fun z : ℂ => (if z = 0 then 2 * (c : ℂ) else 0) * cexp (z * v) :=
      summable_of_ne_finset_zero (s := {0}) fun z hz => by simp_all
    have e3 : ∑' z : ℂ, (if z = 0 then 2 * (c : ℂ) else 0) * cexp (z * v) = 2 * c := by
      rw [tsum_eq_single 0 fun z hz => by simp [hz]]
      simp
    have hfun : (fun z : ℂ => q z * cexp (z * v)) = fun z =>
        evenCoeff Z b z * cexp (z * v) - evenCoeff Z' b z * cexp (z * v) -
          (if z = 0 then 2 * (c : ℂ) else 0) * cexp (z * v) := by
      funext z; simp only [hq]; ring
    rw [hfun, (h1.sub h2).tsum_sub h3, h1.tsum_sub h2, ← e1, ← e2, e3]
    have := hRe v hv
    push_cast
    rw [← this]
    push_cast
    ring
  -- locally finite exponents
  set ι : Set ℂ := {z | q z ≠ 0} with hι
  haveI : Countable ι := by
    refine ((countable_evenCoeff_support Z b).union ((countable_evenCoeff_support Z' b).union
      (Set.countable_singleton 0))).mono (fun z hz => ?_) |>.to_subtype
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or, not_not] at h
    exact hz (by rw [hq]; simp [h.1, h.2.1, h.2.2])
  have hband : ∀ γ : ℝ, {t : ι | |(t : ℂ).im - γ| < 1}.Finite := fun γ => by
    have hfin : ∀ Y : ZeroConfig, {z : ℂ | evenCoeff Y b z ≠ 0 ∧ |z.im - γ| < 1}.Finite :=
      fun Y => by
        refine (((Y.finite_window (γ - 1) (γ + 1)).image fun ρ => ρ - 1 / 2).union
          ((Y.finite_window (-γ - 1) (-γ + 1)).image fun ρ => conj (ρ - 1 / 2))).subset
          fun z hz => ?_
        obtain ⟨hz1, hz2⟩ := hz
        obtain ⟨hl, hr⟩ := abs_lt.mp hz2
        rcases mem_of_evenCoeff_ne_zero hz1 with h | h
        · exact Or.inl ⟨1 / 2 + z, ⟨h, by simp; linarith, by simp; linarith⟩, by ring⟩
        · exact Or.inr ⟨1 / 2 + conj z, ⟨h, by simp; linarith, by simp; linarith⟩, by simp⟩
    refine (((hfin Z).union ((hfin Z').union (Set.finite_singleton 0))).preimage
      Subtype.val_injective.injOn).subset fun t ht => ?_
    have ht' : |(t : ℂ).im - γ| < 1 := ht
    by_cases h1 : evenCoeff Z b t = 0
    · by_cases h2 : evenCoeff Z' b t = 0
      · refine Or.inr (Or.inr ?_)
        by_contra h3
        have h3' : (t : ℂ) ≠ 0 := h3
        exact t.2 (by simp only [hq]; simp [h1, h2, h3'])
      · exact Or.inr (Or.inl ⟨h2, ht'⟩)
    · exact Or.inl ⟨h1, ht'⟩
  -- uniqueness: no exponent of `ι` has `Re ≥ 0`
  have hι0 : ∀ v : ℝ, V ≤ v → ∑' t : ι, q t * cexp ((t : ℂ) * v) = 0 := fun v hv => by
    rw [tsum_subtype_eq_of_support_subset (s := ι) (f := fun z => q z * cexp (z * v))
      fun z hz h0 => hz (show q z * cexp (z * v) = 0 by rw [h0, zero_mul])]
    exact hzero v hv
  have hright : ∀ z : ℂ, 0 ≤ z.re → q z = 0 := fun z hz => by
    by_contra hne
    exact hne (eq_zero_of_tsum_cexp_eq_zero (ι := ι) (lam := fun t => (t : ℂ))
      (q := fun t => q t) (hqs.subtype ι) (A := 1 / 2) (fun t => by
        rcases eq_or_ne (t : ℂ) 0 with h | h
        · rw [h]; norm_num
        · by_contra hlt
          push Not at hlt
          have hq0 : q t = evenCoeff Z b t - evenCoeff Z' b t := by rw [hq]; simp [h]
          have : evenCoeff Z b t ≠ 0 ∨ evenCoeff Z' b t ≠ 0 := by
            by_contra hb'
            push Not at hb'
            exact t.2 (by rw [hq0, hb'.1, hb'.2, sub_zero])
          rcases this with h' | h'
          · exact absurd (re_le_of_evenCoeff_ne_zero h') (not_le.mpr hlt)
          · exact absurd (re_le_of_evenCoeff_ne_zero h') (not_le.mpr hlt))
      (fun s t h => Subtype.ext h) hband hι0 (t₁ := ⟨z, hne⟩) hz)
  -- reflection to the left half-plane
  have hD : ∀ z : ℂ, z ≠ 0 → evenCoeff Z b z = evenCoeff Z' b z := by
    intro z hz0
    have hdiff : ∀ y : ℂ, y ≠ 0 → q y = evenCoeff Z b y - evenCoeff Z' b y := fun y hy => by
      rw [hq]; simp [hy]
    rcases le_or_gt 0 z.re with hzr | hzr
    · have := hright z hzr
      rw [hdiff z hz0] at this
      exact sub_eq_zero.mp this
    · have hy0 : -conj z ≠ 0 := by
        intro h; apply hz0
        have := congrArg (fun y => -conj y) h
        simpa using this
      have := hright (-conj z) (by simp; linarith)
      rw [hdiff _ hy0, evenCoeff_neg_conj Z hb.continuous hbc,
        evenCoeff_neg_conj Z' hb.continuous hbc, ← map_sub] at this
      exact sub_eq_zero.mp ((map_eq_zero _).mp this)
  -- read off the symmetrized multiplicities
  have hz0 : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr hρ
  have h := hD _ hz0
  rw [evenCoeff_modScaledBump_zero_eq Z hw, evenCoeff_modScaledBump_zero_eq Z' hw] at h
  have e1 : (1 / 2 + (ρ - 1 / 2) : ℂ) = ρ := by ring
  have e2 : (1 / 2 + conj (ρ - 1 / 2) : ℂ) = conj ρ := by
    rw [map_sub, map_div₀, map_one, map_ofNat]; ring
  have e3 : -(I * (ρ - 1 / 2)) = gammaOf ρ := by
    rw [gammaOf, Complex.div_I]; ring
  rw [e1, e2, e3] at h
  by_cases hseen : paperFT (scaledBump w) (gammaOf ρ) = 0
  · -- neither `ρ` nor `ρ̄` is a zero of `Z` or `Z'`
    have hconjgood : ∀ σ ∈ Z.carrier ∪ Z'.carrier, σ = conj ρ → False := fun σ hσ he => by
      apply hgood σ hσ
      rw [he, RHTower.gammaOf_conj, paperFT_scaledBump_neg, ← conj_paperFT_scaledBump,
        hseen, map_zero]
    have hnot : ∀ σ ∈ Z.carrier ∪ Z'.carrier, σ = ρ → False := fun σ hσ he =>
      hgood σ hσ (by rw [he]; exact hseen)
    have z1 : ρ ∉ Z.carrier := fun h => hnot ρ (Or.inl h) rfl
    have z2 : ρ ∉ Z'.carrier := fun h => hnot ρ (Or.inr h) rfl
    have z3 : conj ρ ∉ Z.carrier := fun h => hconjgood _ (Or.inl h) rfl
    have z4 : conj ρ ∉ Z'.carrier := fun h => hconjgood _ (Or.inr h) rfl
    simp [Set.indicator_of_notMem z1, Set.indicator_of_notMem z2, Set.indicator_of_notMem z3,
      Set.indicator_of_notMem z4]
  · exact mul_right_cancel₀ (pow_ne_zero 2 hseen) h

/-- **Converse.** If `m(ρ) + m(ρ̄)` agree at every `ρ ≠ ½`, the tests
`κ_w(t + v/2) − κ_w(t − v/2)` have the same `Re W` for both configurations at every lag. -/
theorem re_W_lag_eq_of_symmMult_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {w : ℝ} (hw : 0 < w)
    (hsym : ∀ ρ : ℂ, ρ ≠ 1 / 2 → Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) ρ +
        Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (conj ρ) =
      Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) ρ +
        Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) (conj ρ)) (v : ℝ) :
    (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re =
      (Z'.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re := by
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  have hD : ∀ z : ℂ, z ≠ 0 → evenCoeff Z b z = evenCoeff Z' b z := fun z hz => by
    rw [evenCoeff_modScaledBump_zero_eq Z hw, evenCoeff_modScaledBump_zero_eq Z' hw]
    have h := hsym (1 / 2 + z) fun h => hz (by linear_combination h)
    rw [map_add, map_div₀, map_one, map_ofNat] at h
    rw [h]
  have key : ∀ Y : ZeroConfig, TemperedConfig Y →
      (((Y.W (twoBump b v (-1)) (twoBump b v (-1))).re : ℝ) : ℂ) =
        ∑' z : ℂ, evenCoeff Y b z * (1 - cexp (z * v)) := fun Y hY => by
    obtain ⟨h0s, e0⟩ := two_re_lagStructure_eq Y hY hb hbs 0
    obtain ⟨hvs, ev⟩ := two_re_lagStructure_eq Y hY hb hbs v
    rw [re_W_lag_eq Y hY hb hbs, Complex.ofReal_sub, e0, ev, ← h0s.tsum_sub hvs]
    refine tsum_congr fun z => ?_
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  apply Complex.ofReal_injective
  rw [key Z hZ, key Z' hZ']
  refine tsum_congr fun z => ?_
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [hD z hz]

/-- **Exactly what the lag family sees.** For a width at which `h_w` vanishes at no zero
ordinate, the tests `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`, have the same `Re W` for `Z` and
`Z'` if and only if `m(ρ) + m(ρ̄)` agree at every `ρ ≠ ½`. -/
theorem lag_weil_eq_iff_symmMult_eq (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, paperFT (scaledBump w) (gammaOf ρ) ≠ 0) (V : ℝ) :
    (∀ v : ℝ, V ≤ v → (Z.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re = (Z'.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re) ↔
      ∀ ρ : ℂ, ρ ≠ 1 / 2 → Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) ρ +
          Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (conj ρ) =
        Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) ρ +
          Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) (conj ρ) :=
  ⟨fun hW _ hρ => symmMult_eq_of_lag_weil_eq Z Z' hZ hZ' hw hgood hW hρ,
    fun h v _ => re_W_lag_eq_of_symmMult_eq Z Z' hZ hZ' hw h v⟩

/-- **Conjugation-symmetric configurations are determined by the lag family.** If `Z` and `Z'`
are tempered, closed under conjugation with conjugation-invariant multiplicities, have the same
multiplicity at `½`, and `h_w` vanishes at none of their zero ordinates, then equal `Re W` on the
tests `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`, forces `Z = Z'`. -/
theorem eq_of_lag_weil_eq_of_conj (Z Z' : ZeroConfig) (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier ∪ Z'.carrier, paperFT (scaledBump w) (gammaOf ρ) ≠ 0) {V : ℝ}
    (hW : ∀ v : ℝ, V ≤ v → (Z.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re = (Z'.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    (hconj' : ∀ ρ ∈ Z'.carrier, conj ρ ∈ Z'.carrier ∧ Z'.mult (conj ρ) = Z'.mult ρ)
    (hhalf : Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2) =
      Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) (1 / 2)) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  have hsym : ∀ Y : ZeroConfig, (∀ ρ ∈ Y.carrier, conj ρ ∈ Y.carrier ∧ Y.mult (conj ρ) = Y.mult ρ) →
      ∀ ρ : ℂ, Y.carrier.indicator (fun ρ => (Y.mult ρ : ℂ)) (conj ρ) =
        Y.carrier.indicator (fun ρ => (Y.mult ρ : ℂ)) ρ := fun Y hY ρ => by
    by_cases h : ρ ∈ Y.carrier
    · rw [Set.indicator_of_mem (hY ρ h).1, Set.indicator_of_mem h, (hY ρ h).2]
    · have hc : conj ρ ∉ Y.carrier := fun hc => h (by simpa using (hY _ hc).1)
      rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem h]
  refine eq_of_multDiff_eq_zero fun ρ => ?_
  rw [multDiff, sub_eq_zero]
  rcases eq_or_ne ρ (1 / 2) with rfl | hρ
  · exact hhalf
  · have h := symmMult_eq_of_lag_weil_eq Z Z' hZ hZ' hw hgood hW hρ
    rw [hsym Z hconj, hsym Z' hconj'] at h
    have h2 : (2 : ℂ) * Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) ρ =
        2 * Z'.carrier.indicator (fun ρ => (Z'.mult ρ : ℂ)) ρ := by rw [two_mul, two_mul]; exact h
    exact mul_left_cancel₀ two_ne_zero h2

/-- **The lag data of `ζ` determine its zeros.** Let `w > 0` be a width at which `h_w` vanishes
at no zero ordinate of `ζ` or of `Z`. Then a tempered configuration `Z` that is closed under
conjugation with invariant multiplicities, has no zero at `½`, and has the same `Re W` as `ζ` on
every test `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`, is the configuration of the nontrivial zeros
of `ζ`. -/
theorem eq_zetaZeroConfig_of_lag_weil_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {w : ℝ}
    (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier ∪ zetaZeroConfig.carrier, paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    {V : ℝ} (hW : ∀ v : ℝ, V ≤ v → (Z.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re =
        (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1))).re)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    (hhalf : (1 / 2 : ℂ) ∉ Z.carrier) :
    Z.carrier = zetaZeroConfig.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = zetaZeroConfig.mult ρ := by
  have hζhalf : (1 / 2 : ℂ) ∉ zetaZeroConfig.carrier := fun h =>
    zetaZeroConfig_im_ne_zero _ h (by simp)
  exact eq_of_lag_weil_eq_of_conj Z zetaZeroConfig hZ temperedConfig_zetaZeroConfig hw hgood hW
    hconj (fun ρ hρ => ⟨conj_mem_zetaZeroConfig hρ, mult_conj_zetaZeroConfig hρ⟩)
    (by rw [Set.indicator_of_notMem hhalf, Set.indicator_of_notMem hζhalf])

end GaloisForLFunctions.SquareRootThreshold
