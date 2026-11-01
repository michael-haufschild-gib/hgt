import GaloisForLFunctions.TransThresholdPairCorrelation.OddStabilizerLogarithmicTransport
import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowProfile


/-!
# Height-uniform transport for smooth profile stabilizer rows

Compact profile derivatives provide every Fourier moment needed for
logarithmic phase, square-root pair-weight and taper transport. The resulting
row bounds are uniform in the base, aperture and conductor cutoff, while the
signed Poisson comparison retains its primitive spatial correction.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem extended_profile_moment_le {f : ℝ → ℝ} {T B : ℝ}
    (hT : 1 ≤ T) (hB : 0 ≤ B) (hf : Continuous f)
    (hb : ∀ t ∈ Set.Icc (T - 1) (2 * T + 1), |f t| ≤ B) :
    (∫ t in (T - 1)..(2 * T + 1), |f t|) ≤ 3 * T * B := by
  have hab : T - 1 ≤ 2 * T + 1 := by linarith
  calc
    _ ≤ ∫ _t in (T - 1)..(2 * T + 1), B :=
      intervalIntegral.integral_mono_on hab (hf.abs.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) hb
    _ = (T + 2) * B := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith : T + 2 ≤ 3 * T) hB

private theorem weighted_profile_deriv_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {T M : ℝ} (hT : 0 < T)
    (hM : ∀ v, |iteratedDeriv 4 (fun v => v * u (v - 1)^4) v| ≤ M) (t : ℝ) :
    |iteratedDeriv 4 (fun t => t * profileΩ u T t) t| ≤ M / T^3 := by
  let κ : ℝ → ℝ := fun v => v * u (v - 1)^4
  have hk : ContDiff ℝ 4 κ :=
    contDiff_id.mul (((hu.smooth 4).comp (contDiff_id.sub contDiff_const)).pow 4)
  have he : (fun t => t * profileΩ u T t) = fun t => T * κ (T⁻¹ * t) := by
    funext t
    have ha : (t - T) / T = T⁻¹ * t - 1 := by field_simp [hT.ne']
    dsimp [profileΩ, profileU, κ]
    rw [ha]
    field_simp [hT.ne']
  have hscale : ContDiff ℝ 4 (fun v : ℝ => κ (T⁻¹ * v)) :=
    hk.comp (contDiff_const.mul contDiff_id)
  rw [he, iteratedDeriv_const_mul (f := fun v : ℝ => κ (T⁻¹ * v)) T hscale.contDiffAt,
    iteratedDeriv_comp_const_mul hk]
  simp only
  rw [abs_mul, abs_of_pos hT, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hT)]
  calc
    _ ≤ T * ((T⁻¹)^4 * M) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hM _) (by positivity)) hT.le
    _ = _ := by field_simp [hT.ne']

private theorem profile_fourth_moment_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {T M4 : ℝ} (hT1 : 1 ≤ T) (hM4 : 0 ≤ M4)
    (h4 : ∀ v, |iteratedDeriv 4 (fun v => u v^4) v| ≤ M4) :
    (∫ t in (T - 1)..(2 * T + 1), |iteratedDeriv 4 (profileΩ u T) t|) ≤
      3 * M4 / T^3 := by
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have h := extended_profile_moment_le hT1 (div_nonneg hM4 (pow_nonneg hT.le _))
    ((contDiff_profileΩ hu T 4).continuous_iteratedDeriv 4 le_rfl) (B := M4 / T^4) (by
      intro t _
      simpa only [inv_pow, div_eq_mul_inv] using abs_iteratedDeriv_profileΩ_le hu hT 4 h4 t)
  refine h.trans_eq ?_
  field_simp [hT.ne']

private theorem profile_support_interval {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {T : ℝ} (hT : 0 < T) :
    ∀ t ∉ Set.Icc T (2 * T), profileΩ u T t = 0 := by
  intro t ht
  have hz : profileU u T t = 0 := profileU_eq_zero hu hT (by
    intro hh
    have he := mul_nonneg hu.pos.le hT.le
    exact ht ⟨by linarith [hh.1], by linarith [hh.2]⟩)
  norm_num [profileΩ, hz]

private theorem profile_mass_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {T : ℝ} (hT1 : 1 ≤ T) :
    (∫ t in (T - 1)..(2 * T + 1), |profileΩ u T t|) ≤ 3 * T := by
  simpa only [mul_one] using extended_profile_moment_le hT1 (by norm_num : (0 : ℝ) ≤ 1)
    ((contDiff_profileΩ hu T 4).continuous) (by
      intro t _
      change |u ((t - T) / T)^4| ≤ 1
      rw [abs_of_nonneg (pow_nonneg (hu.nonneg _) 4)]
      exact pow_le_one₀ (hu.nonneg _) (hu.le_one _))

private theorem profile_fourier_moments_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) {T M4 k : ℝ} (hT1 : 1 ≤ T) (hM4 : 0 ≤ M4) (hk : 0 ≤ k)
    (h4 : ∀ v, |iteratedDeriv 4 (fun v => u v^4) v| ≤ M4) :
    (∫ t in (T - 1)..(2 * T + 1), |profileΩ u T t|) / T +
      k * T^3 * (∫ t in (T - 1)..(2 * T + 1), |iteratedDeriv 4 (profileΩ u T) t|) ≤
        3 + 3 * k * M4 := by
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have h0 := profile_mass_le hu hT1
  have hd0 := profile_fourth_moment_le hu hT1 hM4 h4
  calc
    _ ≤ (3 * T) / T + k * T^3 * (3 * M4 / T^3) := by gcongr
    _ = _ := by field_simp [hT.ne']

/-- Fixed smooth profiles have a uniform Fourier transport bound at every
height `T≥1`; all derivative constants come from compact profile support. -/
theorem WindowProfile.exists_logarithmicTransportBound_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      logarithmicTransportBound (profileΩ u T) T (2 * T) T ≤ C := by
  obtain ⟨M4, hM4, h4⟩ := hu.exists_iteratedDeriv_pow_four_le 4
  let κ : ℝ → ℝ := fun v => v * u (v - 1)^4
  have hk : ContDiff ℝ 4 κ :=
    contDiff_id.mul (((hu.smooth 4).comp (contDiff_id.sub contDiff_const)).pow 4)
  have hkc : HasCompactSupport κ := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 : ℝ) 2)
      isCompact_Icc ?_
    intro v hv
    by_contra hn
    have hz : u (v - 1) = 0 := hu.zero_of _ (by
      intro h
      exact hn ⟨by linarith [h.1, hu.pos], by linarith [h.2, hu.pos]⟩)
    exact hv (by dsimp [κ]; rw [hz]; ring)
  obtain ⟨Mk, hkbound⟩ := (hk.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hkc.iteratedFDeriv 4)
  have hMk : 0 ≤ Mk := (norm_nonneg _).trans (hkbound 0)
  have hkb (v : ℝ) : |iteratedDeriv 4 κ v| ≤ Mk := by
    rw [← Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm]
    exact hkbound v
  refine ⟨42 + 6 * M4 + 192 * Mk, by positivity, ?_⟩
  intro T hT1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hc := (contDiff_profileΩ hu T 4).continuous
  have hΩ (t : ℝ) : |profileΩ u T t| ≤ 1 := by
    change |u ((t - T) / T)^4| ≤ 1
    rw [abs_of_nonneg (pow_nonneg (hu.nonneg _) 4)]
    exact pow_le_one₀ (hu.nonneg _) (hu.le_one _)
  have h0 := profile_mass_le hu hT1
  have h1 : (∫ t in (T - 1)..(2 * T + 1), |t * profileΩ u T t|) ≤ 9 * T^2 := by
    have h := extended_profile_moment_le (f := fun t : ℝ => t * profileΩ u T t)
      hT1 (by positivity : 0 ≤ 3 * T) (continuous_id.mul hc) (by
        intro t ht
        rw [abs_mul]
        calc
          _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left (hΩ t) (abs_nonneg t)
          _ ≤ 3 * T := by
            rw [mul_one, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]
            linarith [ht.2])
    nlinarith only [h]
  have hd0 := profile_fourth_moment_le hu hT1 hM4 h4
  have hd1 : (∫ t in (T - 1)..(2 * T + 1),
      |iteratedDeriv 4 (fun t => t * profileΩ u T t) t|) ≤ 3 * Mk / T^2 := by
    have h := extended_profile_moment_le hT1 (div_nonneg hMk (pow_nonneg hT.le _))
      ((contDiff_id.mul (contDiff_profileΩ hu T 4)).continuous_iteratedDeriv 4 le_rfl)
      (B := Mk / T^3) (fun t _ => weighted_profile_deriv_le hu hT hkb t)
    refine h.trans_eq ?_
    field_simp [hT.ne']
  unfold logarithmicTransportBound
  calc
    _ ≤ 4 * ((9 * T^2) / T^2 + 16 * T^2 * (3 * Mk / T^2)) +
        2 * ((3 * T) / T + T^3 * (3 * M4 / T^3)) := by
      gcongr
    _ = _ := by field_simp [hT.ne']; ring

/-- For every fixed smooth profile, the literal logarithmic row equals its
primitive spatial correction minus the diagonal, up to a uniform height error
and the cubic relative-aperture error. -/
theorem WindowProfile.exists_stabilizerLogarithmicRow_dual_error_le
    {ε : ℝ} {u : ℝ → ℝ} (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T m : ℝ) (Q R : ℕ),
      1 ≤ T → 0 < m → 1 ≤ R → ((2 * R : ℕ) : ℝ) ≤ m →
      |stabilizerLogarithmicRow Q (profileΩ u T) m R -
        (π * stabilizerSpatialDual Q (profileΩ u T) m -
          cosTransform (profileΩ u T) 0 *
            (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) / m)| ≤
        (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
          C * (1 / T + (m / (T * (R : ℝ)))^3) := by
  obtain ⟨C, hC, hCb⟩ := hu.exists_logarithmicTransportBound_le
  obtain ⟨M4, hM4, h4⟩ := hu.exists_iteratedDeriv_pow_four_le 4
  let K := max C (3 * M4 / 8)
  refine ⟨K, hC.trans (le_max_left _ _), ?_⟩
  intro T m Q R hT1 hm hR hRm
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hRp : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hsupp := profile_support_interval hu hT
  have hd0 := profile_fourth_moment_le hu hT1 hM4 h4
  let O := ∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q
  have hO : 0 ≤ O := sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)
  have h := abs_stabilizerLogarithmicRow_sub_dual_le Q R (by linarith : T ≤ 2 * T)
    hT hm hR hRm (contDiff_profileΩ hu T 4) hsupp
  apply h.trans
  calc
    _ ≤ O * C / T + O * (3 * M4 / T^3) * m^3 / (8 * (R : ℝ)^3) := by
      gcongr
      exact hCb T hT1
    _ = O * (C * (1 / T) + (3 * M4 / 8) * (m / (T * (R : ℝ)))^3) := by ring
    _ ≤ O * (K * (1 / T) + K * (m / (T * (R : ℝ)))^3) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))) hO
    _ = _ := by ring

/-- Every finite logarithmic profile row is bounded by the odd conductor mass,
uniformly in height, base and coalescent aperture. -/
theorem WindowProfile.exists_abs_stabilizerLogarithmicRow_le
    {ε : ℝ} {u : ℝ → ℝ} (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T m : ℝ) (Q R : ℕ),
      1 ≤ T → 0 < m → ((2 * R : ℕ) : ℝ) ≤ m →
      |stabilizerLogarithmicRow Q (profileΩ u T) m R| ≤
        (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) * C := by
  obtain ⟨C, hC, hCb⟩ := hu.exists_logarithmicTransportBound_le
  obtain ⟨M4, hM4, h4⟩ := hu.exists_iteratedDeriv_pow_four_le 4
  refine ⟨4 * (3 + 3 * M4) + C, by positivity, ?_⟩
  intro T m Q R hT1 hm hRm
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hM := profile_fourier_moments_le hu hT1 hM4 (by norm_num : (0 : ℝ) ≤ 1) h4
  simp only [one_mul, mul_one] at hM
  have hphase : logarithmicTransportBound (profileΩ u T) T (2 * T) T / T ≤ C := by
    calc
      _ ≤ C / T := div_le_div_of_nonneg_right (hCb T hT1) hT.le
      _ ≤ C := (div_le_iff₀ hT).mpr (by nlinarith only [hC, hT1])
  have h := abs_stabilizerLogarithmicRow_le Q R (by linarith : T ≤ 2 * T) hT hm hRm
    (contDiff_profileΩ hu T 4) (profile_support_interval hu hT)
  apply h.trans
  apply mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hM (by norm_num)) hphase)
  exact sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q)

/-- Taper variation for a fixed profile costs at most the odd conductor mass
divided by height, with no additional logarithmic factor. -/
theorem WindowProfile.exists_stabilizerLogarithmicMoment_le
    {ε : ℝ} {u : ℝ → ℝ} (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T m : ℝ) (Q R : ℕ),
      1 ≤ T → 0 < m → ((2 * R : ℕ) : ℝ) ≤ m →
      (∑ n ∈ range R, |parityStabilizerWeight Q (2 * (n + 1)) *
        Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m) *
        cosTransform (profileΩ u T) (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
          Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))|) ≤
        (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) * C / T := by
  obtain ⟨M4, hM4, h4⟩ := hu.exists_iteratedDeriv_pow_four_le 4
  refine ⟨4 * (3 + 3 * 16 * M4), by positivity, ?_⟩
  intro T m Q R hT1 hm hRm
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT1
  have hM := profile_fourier_moments_le hu hT1 hM4 (by norm_num : (0 : ℝ) ≤ 16) h4
  have h := sum_abs_stabilizerLogarithmicMoment_le Q R (by linarith : T ≤ 2 * T) hT hm hRm
    (contDiff_profileΩ hu T 4) (profile_support_interval hu hT)
  apply h.trans
  calc
    _ ≤ 4 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        (3 + 3 * 16 * M4) / T := by
      apply div_le_div_of_nonneg_right _ hT.le
      apply mul_le_mul_of_nonneg_left hM
      exact mul_nonneg (by norm_num) (sum_nonneg (fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q))
    _ = _ := by ring

end GaloisForLFunctions.TransThresholdPairCorrelation

