import GaloisForLFunctions.RHTower.FourierPositiveJumpNetwork
import GaloisForLFunctions.RHTower.ThetaQuantileProfileCalculus
import GaloisForLFunctions.RHTower.ThetaCdfActionDyadic
import GaloisForLFunctions.RHTower.ThetaQuotientOppositeFrequencyBlocks

/-!
# The theta quantile action is an electrical potential kernel

The theta quantile profile `h = k(Q)/M = 1/q` (extended by `0` at the endpoints) is a
Fourier-positive jump profile: it is continuous on `[0,1]`, symmetric, positive inside, and its
nonzero cosine coefficients are strictly negative.  The last fact comes from two integrations by
parts against `w(t) = (1 − cos 2πnt)/(2πn)²`, which turn `ĥ(n)` into `∫ h'' w` with
`h'' = H'(Q) q < 0` (strict log-concavity of the theta source); the endpoint terms vanish because
`t² H(Q(t)) ≤ t h(t)`.  Its actions are the CDF actions `Φ_m`.

Consequently the CDF actions are the potential kernel of a reversible jump network with positive
conductances `a_n = −ĥ(n)`: `2Σ a_nΦ_n = 1`, `L_aΦ = −δ₀`, the dipole voltages
`v^(n)_m = Φ_m − Φ_{m−n}` solve `L_a v^(n) = δ_n − δ₀`, decay as `|m| → ∞`, and are exactly the
matrix of the quotient: `⟨e_m, D e_n⟩ = v^(n)_m/(2πn)`.  Each isolated `{n, −n}` block of `D`
squares to `(d² − o²)` times its projection with `d² > o²`, so its eigenvalues are real and nonzero.
-/

namespace RHTower

open MeasureTheory Filter Topology Set HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

noncomputable section

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-! ## The theta network profile -/

/-- The theta network profile `h = k(Q)/M = 1/q` on `(0,1)`, extended by `0`. -/
def thetaNetworkProfile (t : ℝ) : ℝ := if t ∈ Ioo (0 : ℝ) 1 then thetaQuantileProfile t else 0

theorem thetaNetworkProfile_of_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaNetworkProfile t = thetaQuantileProfile t := if_pos ht

theorem thetaQuantileProfile_eq (t : ℝ) :
    thetaQuantileProfile t = thetaCuspFullSource (thetaQuantile t) / thetaSource.mass := by
  rw [thetaQuantileProfile, thetaQuantileSpeed_eq, inv_div]

theorem thetaQuantileProfile_one_sub {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaQuantileProfile (1 - t) = thetaQuantileProfile t := by
  simp only [thetaQuantileProfile, thetaQuantileSpeed]
  rw [quantileSpeed_one_sub ht]

theorem thetaNetworkProfile_one_sub (t : ℝ) : thetaNetworkProfile (1 - t) = thetaNetworkProfile t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) 1
  · have h1 : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [thetaNetworkProfile_of_mem h1, thetaNetworkProfile_of_mem ht, thetaQuantileProfile_one_sub ht]
  · have h1 : 1 - t ∉ Ioo (0 : ℝ) 1 := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [thetaNetworkProfile, ht, h1, if_false]

theorem tendsto_thetaCuspFullSource_atBot_zero : Tendsto thetaCuspFullSource atBot (𝓝 0) :=
  (tendsto_thetaCuspFullSource_atTop_zero.comp tendsto_neg_atBot_atTop).congr fun x => by
    simp [thetaCuspFullSource_neg]

theorem tendsto_thetaQuantileProfile_nhdsGT_zero : Tendsto thetaQuantileProfile (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_thetaCuspFullSource_atBot_zero.comp tendsto_thetaQuantile_nhdsGT_zero).div_const
    thetaSource.mass
  rw [zero_div] at h
  exact h.congr fun t => (thetaQuantileProfile_eq t).symm

theorem continuousOn_thetaNetworkProfile : ContinuousOn thetaNetworkProfile (Icc 0 1) := by
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, ContinuousAt thetaNetworkProfile t := fun t ht =>
    (hasDerivAt_thetaQuantileProfile ht).continuousAt.congr
      (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => (thetaNetworkProfile_of_mem hs).symm)
  have h0 : ContinuousWithinAt thetaNetworkProfile (Icc 0 1) 0 := by
    have hI : ContinuousWithinAt thetaNetworkProfile (Ioi 0) 0 := by
      have hv : thetaNetworkProfile 0 = 0 := if_neg (by simp)
      rw [ContinuousWithinAt, hv]
      refine tendsto_thetaQuantileProfile_nhdsGT_zero.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
      exact (thetaNetworkProfile_of_mem ht).symm
    exact (continuousWithinAt_Ioi_iff_Ici.1 hI).mono Icc_subset_Ici_self
  have h1 : ContinuousWithinAt thetaNetworkProfile (Icc 0 1) 1 := by
    have hcomp : thetaNetworkProfile = thetaNetworkProfile ∘ fun t => 1 - t :=
      funext fun t => (thetaNetworkProfile_one_sub t).symm
    have h0' : ContinuousWithinAt thetaNetworkProfile (Icc 0 1) ((fun t : ℝ => 1 - t) 1) := by
      simpa using h0
    rw [hcomp]
    exact h0'.comp (by fun_prop : Continuous fun t : ℝ => 1 - t).continuousWithinAt
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]; exact h0
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · rw [h']; exact h1
  exact (hint t ⟨h, h'⟩).continuousWithinAt

/-! ## Negative Fourier coefficients -/

/-- The weight `w(t) = (1 − cos 2πnt)/(2πn)²`, with `w'' = cos 2πnt`. -/
def cosineBumpWeight (n : ℕ) (t : ℝ) : ℝ := (1 - Real.cos (2 * Real.pi * n * t)) / (2 * Real.pi * n) ^ 2

/-- `w'(t) = sin(2πnt)/(2πn)`. -/
def cosineBumpWeightDeriv (n : ℕ) (t : ℝ) : ℝ := Real.sin (2 * Real.pi * n * t) / (2 * Real.pi * n)

theorem hasDerivAt_cosineBumpWeight {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (cosineBumpWeight n) (cosineBumpWeightDeriv n t) t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (2 * Real.pi * n : ℝ) ≠ 0 := by positivity
  have h := ((((hasDerivAt_id' t).const_mul (2 * Real.pi * n)).cos).const_sub 1).div_const
    ((2 * Real.pi * n) ^ 2)
  refine h.congr_deriv ?_
  rw [cosineBumpWeightDeriv]
  field_simp

theorem hasDerivAt_cosineBumpWeightDeriv {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (cosineBumpWeightDeriv n) (Real.cos (2 * Real.pi * n * t)) t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (2 * Real.pi * n : ℝ) ≠ 0 := by positivity
  have h := (((hasDerivAt_id' t).const_mul (2 * Real.pi * n)).sin).div_const (2 * Real.pi * n)
  refine h.congr_deriv ?_
  field_simp

theorem continuous_cosineBumpWeight (n : ℕ) : Continuous (cosineBumpWeight n) := by unfold cosineBumpWeight; fun_prop

theorem continuous_cosineBumpWeightDeriv (n : ℕ) : Continuous (cosineBumpWeightDeriv n) := by
  unfold cosineBumpWeightDeriv; fun_prop

theorem cosineBumpWeight_one_sub (n : ℕ) (t : ℝ) : cosineBumpWeight n (1 - t) = cosineBumpWeight n t := by
  simp only [cosineBumpWeight]
  rw [show 2 * Real.pi * n * (1 - t) = ((n : ℤ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * n * t by push_cast; ring,
    Real.cos_int_mul_two_pi_sub]

theorem cosineBumpWeightDeriv_one_sub (n : ℕ) (t : ℝ) : cosineBumpWeightDeriv n (1 - t) = -cosineBumpWeightDeriv n t := by
  simp only [cosineBumpWeightDeriv]
  rw [show 2 * Real.pi * n * (1 - t) = ((n : ℤ) : ℝ) * (2 * Real.pi) - 2 * Real.pi * n * t by push_cast; ring,
    Real.sin_int_mul_two_pi_sub, neg_div]

theorem cosineBumpWeight_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : cosineBumpWeight n t ≤ t ^ 2 / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := abs_one_sub_cos_le_sq (2 * Real.pi * n * t)
  rw [abs_of_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * n * t)])] at h
  rw [cosineBumpWeight, div_le_iff₀ (by positivity)]
  nlinarith

theorem cosineBumpWeight_nonneg (n : ℕ) (t : ℝ) : 0 ≤ cosineBumpWeight n t :=
  div_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * n * t)]) (sq_nonneg _)

/-- The profile curvature `h'' = H'(Q) q`. -/
def thetaProfileCurvature (t : ℝ) : ℝ :=
  thetaCuspLogConcavityNumerator (thetaQuantile t) / thetaCuspFullSource (thetaQuantile t) ^ 2 *
    thetaQuantileSpeed t

theorem hasDerivAt_thetaProfileSlope {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => thetaLogHazard (thetaQuantile s)) (thetaProfileCurvature t) t :=
  (hasDerivAt_thetaLogHazard (thetaQuantile t)).comp t (hasDerivAt_thetaQuantile ht)

theorem thetaProfileCurvature_neg (t : ℝ) : thetaProfileCurvature t < 0 :=
  mul_neg_of_neg_of_pos (thetaLogHazardDeriv_neg _) (thetaQuantileSpeed_pos t)

theorem continuousOn_thetaProfileSlope :
    ContinuousOn (fun s => thetaLogHazard (thetaQuantile s)) (Ioo 0 1) :=
  continuous_thetaLogHazard.comp_continuousOn continuousOn_thetaQuantile

theorem continuousOn_thetaProfileCurvature : ContinuousOn thetaProfileCurvature (Ioo 0 1) :=
  ((continuous_thetaCuspLogConcavityNumerator.comp_continuousOn continuousOn_thetaQuantile).div
    ((continuous_thetaCuspFullSource.comp_continuousOn continuousOn_thetaQuantile).pow 2)
    fun _ _ => (pow_pos (thetaCuspFullSource_pos _) 2).ne').mul continuousOn_thetaQuantileSpeed

theorem continuousOn_thetaQuantileProfile : ContinuousOn thetaQuantileProfile (Ioo 0 1) :=
  fun _ ht => (hasDerivAt_thetaQuantileProfile ht).continuousAt.continuousWithinAt

/-- **Two integrations by parts**: on `[ε, 1−ε]`,
`∫ h cos 2πnt = [h w' − h' w] + ∫ h'' w`. -/
theorem integral_profile_cos_eq {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) (1 / 2)) :
    ∫ t in ε..(1 - ε), thetaQuantileProfile t * Real.cos (2 * Real.pi * n * t) =
      thetaQuantileProfile (1 - ε) * cosineBumpWeightDeriv n (1 - ε) - thetaQuantileProfile ε * cosineBumpWeightDeriv n ε -
        (thetaLogHazard (thetaQuantile (1 - ε)) * cosineBumpWeight n (1 - ε) -
          thetaLogHazard (thetaQuantile ε) * cosineBumpWeight n ε) +
      ∫ t in ε..(1 - ε), thetaProfileCurvature t * cosineBumpWeight n t := by
  have hle : ε ≤ 1 - ε := by linarith [hε.2]
  have hsub : uIcc ε (1 - ε) ⊆ Ioo (0 : ℝ) 1 := by
    rw [uIcc_of_le hle]
    exact fun t ht => ⟨by linarith [hε.1, ht.1], by linarith [hε.1, ht.2]⟩
  have hsubIcc : Icc ε (1 - ε) ⊆ Ioo (0 : ℝ) 1 := by rwa [uIcc_of_le hle] at hsub
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := 1 - ε)
    (u := thetaQuantileProfile) (v := cosineBumpWeightDeriv n)
    (u' := fun s => thetaLogHazard (thetaQuantile s)) (v' := fun s => Real.cos (2 * Real.pi * n * s))
    (fun _ ht => hasDerivAt_thetaQuantileProfile (hsub ht)) (fun t _ => hasDerivAt_cosineBumpWeightDeriv hn t)
    ((continuousOn_thetaProfileSlope.mono hsubIcc).intervalIntegrable_of_Icc hle)
    ((by fun_prop : Continuous fun s : ℝ => Real.cos (2 * Real.pi * n * s)).intervalIntegrable _ _)
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := 1 - ε)
    (u := fun s => thetaLogHazard (thetaQuantile s)) (v := cosineBumpWeight n)
    (u' := thetaProfileCurvature) (v' := cosineBumpWeightDeriv n)
    (fun _ ht => hasDerivAt_thetaProfileSlope (hsub ht)) (fun t _ => hasDerivAt_cosineBumpWeight hn t)
    ((continuousOn_thetaProfileCurvature.mono hsubIcc).intervalIntegrable_of_Icc hle)
    ((continuous_cosineBumpWeightDeriv n).intervalIntegrable _ _)
  rw [h1, h2]
  ring

/-- The boundary terms of the two integrations by parts vanish at the endpoints. -/
theorem tendsto_profile_boundary {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun ε => thetaQuantileProfile (1 - ε) * cosineBumpWeightDeriv n (1 - ε) -
      thetaQuantileProfile ε * cosineBumpWeightDeriv n ε -
        (thetaLogHazard (thetaQuantile (1 - ε)) * cosineBumpWeight n (1 - ε) -
          thetaLogHazard (thetaQuantile ε) * cosineBumpWeight n ε)) (𝓝[>] 0) (𝓝 0) := by
  have hw' : Tendsto (cosineBumpWeightDeriv n) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_cosineBumpWeightDeriv n).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [cosineBumpWeightDeriv] using this
  have hA := tendsto_thetaQuantileProfile_nhdsGT_zero.mul hw'
  rw [zero_mul] at hA
  have hB : Tendsto (fun ε => thetaLogHazard (thetaQuantile ε) * cosineBumpWeight n ε) (𝓝[>] 0) (𝓝 0) := by
    have hup : Tendsto (fun ε : ℝ => ε * thetaQuantileProfile ε / 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)).mul
        tendsto_thetaQuantileProfile_nhdsGT_zero).div_const 2
      simpa using this
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      exact mul_nonneg (thetaLogHazard_thetaQuantile_nonneg ⟨hε.1, by linarith [hε.2]⟩ hε.2.le)
        (cosineBumpWeight_nonneg n ε)
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      have hε1 : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, by linarith [hε.2]⟩
      have hH := thetaLogHazard_thetaQuantile_nonneg hε1 hε.2.le
      have hq := thetaQuantileSpeed_pos ε
      have hb := sq_mul_thetaLogHazard_mul_le hε1
      have hw := cosineBumpWeight_le hn ε
      have hHq : ε ^ 2 * thetaLogHazard (thetaQuantile ε) ≤ ε * thetaQuantileProfile ε := by
        rw [thetaQuantileProfile, ← div_eq_mul_inv, le_div_iff₀ hq]
        linarith
      calc thetaLogHazard (thetaQuantile ε) * cosineBumpWeight n ε ≤ thetaLogHazard (thetaQuantile ε) * (ε ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hw hH
        _ ≤ ε * thetaQuantileProfile ε / 2 := by linarith
  have h := (hA.const_mul (-2)).add (hB.const_mul 2)
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  rw [thetaQuantileProfile_one_sub hε, cosineBumpWeightDeriv_one_sub, cosineBumpWeight_one_sub,
    show thetaQuantile (1 - ε) = -thetaQuantile ε from quantileFun_one_sub hε, thetaLogHazard_neg]
  ring

theorem intervalIntegrable_networkProfile_mul_cos (n : ℤ) :
    IntegrableOn (fun t => thetaNetworkProfile t * Real.cos (2 * Real.pi * n * t)) (Icc 0 1) :=
  (continuousOn_thetaNetworkProfile.mul (by fun_prop : Continuous fun t : ℝ =>
    Real.cos (2 * Real.pi * n * t)).continuousOn).integrableOn_compact isCompact_Icc

/-- **The theta conductances are positive**: `ĥ(n) < 0` for `n ≥ 1`. -/
theorem profileCoeff_thetaNetworkProfile_neg {n : ℕ} (hn : 1 ≤ n) :
    profileCoeff thetaNetworkProfile n < 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set a : ℝ := 1 / (4 * n)
  set b : ℝ := 1 / (2 * n)
  have ha0 : 0 < a := by positivity
  have hab : a < b := by
    simp only [a, b]; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hb2 : b ≤ 1 / 2 := by
    simp only [b]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hbn : b < 1 / n := by
    simp only [b]; rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have habsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set f : ℝ → ℝ := fun t => -(thetaProfileCurvature t * cosineBumpWeight n t)
  have hfc : ContinuousOn f (Ioo 0 1) :=
    (continuousOn_thetaProfileCurvature.mul (continuous_cosineBumpWeight n).continuousOn).neg
  have hc0 : 0 < ∫ t in a..b, f t := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hfc.mono habsub).intervalIntegrable_of_Icc hab.le)
      (fun t ht => ?_) hab
    have hw : 0 < cosineBumpWeight n t := div_pos (one_sub_cos_pos hn ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (by positivity)
    simp only [f]
    nlinarith [thetaProfileCurvature_neg t]
  -- the truncated integrals are bounded by the boundary terms minus `c₀`
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in ε..(1 - ε), thetaNetworkProfile t * Real.cos (2 * Real.pi * ((n : ℤ) : ℝ) * t) ≤
        (thetaQuantileProfile (1 - ε) * cosineBumpWeightDeriv n (1 - ε) - thetaQuantileProfile ε * cosineBumpWeightDeriv n ε -
          (thetaLogHazard (thetaQuantile (1 - ε)) * cosineBumpWeight n (1 - ε) -
            thetaLogHazard (thetaQuantile ε) * cosineBumpWeight n ε)) - ∫ t in a..b, f t := by
    filter_upwards [Ioo_mem_nhdsGT ha0] with ε hε
    have hε2 : ε ∈ Ioo (0 : ℝ) (1 / 2) := ⟨hε.1, by linarith [hε.2, hab, hb2]⟩
    have hle : ε ≤ 1 - ε := by linarith [hε2.2]
    have hsubIcc : Icc ε (1 - ε) ⊆ Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨by linarith [hε.1, ht.1], by linarith [hε.1, ht.2]⟩
    have hcongr : ∫ t in ε..(1 - ε), thetaNetworkProfile t * Real.cos (2 * Real.pi * ((n : ℤ) : ℝ) * t) =
        ∫ t in ε..(1 - ε), thetaQuantileProfile t * Real.cos (2 * Real.pi * n * t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hle] at ht
      simp only [Int.cast_natCast]
      rw [thetaNetworkProfile_of_mem (hsubIcc ht)]
    have hmono : ∫ t in a..b, f t ≤ ∫ t in ε..(1 - ε), f t :=
      intervalIntegral.integral_mono_interval hε.2.le hab.le (by linarith [hε2.2])
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => by
          have hw := cosineBumpWeight_nonneg n t
          simp only [f, Pi.zero_apply]
          nlinarith [thetaProfileCurvature_neg t]))
        ((hfc.mono hsubIcc).intervalIntegrable_of_Icc hle)
    have hneg : ∫ t in ε..(1 - ε), thetaProfileCurvature t * cosineBumpWeight n t = -∫ t in ε..(1 - ε), f t := by
      simp only [f, intervalIntegral.integral_neg, neg_neg]
    rw [hcongr, integral_profile_cos_eq hn hε2, hneg]
    linarith
  have hL : Tendsto (fun ε => ∫ t in ε..(1 - ε), thetaNetworkProfile t * Real.cos (2 * Real.pi * ((n : ℤ) : ℝ) * t))
      (𝓝[>] 0) (𝓝 (profileCoeff thetaNetworkProfile n)) :=
    tendsto_integral_symm_truncation (intervalIntegrable_networkProfile_mul_cos n)
  have hR := (tendsto_profile_boundary hn).sub_const (∫ t in a..b, f t)
  have := le_of_tendsto_of_tendsto hL hR hbound
  linarith

/-! ## The theta jump network -/

theorem intervalIntegrable_thetaAction (m : ℤ) :
    IntervalIntegrable (fun t => (1 - Real.cos (2 * Real.pi * m * t)) / thetaNetworkProfile t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine (integrableOn_thetaQuantileSpeed_mul_one_sub_cos m).congr_fun (fun t ht => ?_) measurableSet_Ioo
  rw [thetaNetworkProfile_of_mem ht, thetaQuantileProfile, div_inv_eq_mul]
  exact mul_comm _ _

/-- **The theta quantile profile is a Fourier-positive jump profile.** -/
theorem isJumpProfile_thetaNetworkProfile : IsJumpProfile thetaNetworkProfile where
  continuousOn := continuousOn_thetaNetworkProfile
  symm := thetaNetworkProfile_one_sub
  pos t ht := by rw [thetaNetworkProfile_of_mem ht]; exact thetaQuantileProfile_pos t
  zero := if_neg (by simp)
  coeff_neg _ hn := profileCoeff_thetaNetworkProfile_neg hn
  action := intervalIntegrable_thetaAction

/-- The network actions are the CDF actions `Φ_m`. -/
theorem profileAction_thetaNetworkProfile (m : ℤ) : profileAction thetaNetworkProfile m = cdfAction m := by
  rw [IsJumpProfile.profileAction_eq, cdfAction_eq_quantileSpeed]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  rw [thetaNetworkProfile_of_mem ht, thetaQuantileProfile, div_inv_eq_mul, mul_comm]

/-- The theta jump conductances `a_n = −ĥ(n)`. -/
abbrev thetaConductance (n : ℕ) : ℝ := jumpConductance thetaNetworkProfile n

theorem thetaConductance_pos {n : ℕ} (hn : 1 ≤ n) : 0 < thetaConductance n :=
  isJumpProfile_thetaNetworkProfile.jumpConductance_pos hn

/-- **(1)** `h(t) = 2Σ_{n ≥ 1} a_n (1 − cos 2πnt)` on `[0,1]`, and `Σ a_n = ĥ(0)/2`. -/
theorem hasSum_thetaNetworkProfile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 2 * thetaConductance (n + 1) *
      (1 - Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℤ) * t))) (thetaNetworkProfile t) :=
  isJumpProfile_thetaNetworkProfile.hasSum_profile ht

/-- **(3) Unit capacity** for theta: `2Σ_{n ≥ 1} a_n Φ_n = 1`. -/
theorem hasSum_theta_unitCapacity :
    HasSum (fun n : ℕ => 2 * thetaConductance (n + 1) * cdfAction ((n + 1 : ℕ) : ℤ)) 1 := by
  have h := isJumpProfile_thetaNetworkProfile.hasSum_unitCapacity
  simp only [profileAction_thetaNetworkProfile] at h
  exact h

/-- **(4) The point-source Green law** for theta: `(L_aΦ)_m = −1_{m=0}`. -/
theorem hasSum_theta_green (m : ℤ) :
    HasSum (fun n : ℕ => thetaConductance (n + 1) *
      (2 * cdfAction m - cdfAction (m - (n + 1 : ℕ)) - cdfAction (m + (n + 1 : ℕ))))
      (-(if m = 0 then 1 else 0)) := by
  have h := isJumpProfile_thetaNetworkProfile.hasSum_green m
  simp only [profileAction_thetaNetworkProfile] at h
  exact h

theorem jumpLaplacian_cdfAction (m : ℤ) :
    jumpLaplacian thetaConductance (fun k => (cdfAction k : ℂ)) m = -(if m = 0 then 1 else 0) := by
  have h := isJumpProfile_thetaNetworkProfile.jumpLaplacian_profileAction m
  simp only [profileAction_thetaNetworkProfile] at h
  exact h

/-- **(5) The theta dipole response**: `L_a v^(n) = δ_n − δ₀` with `v^(n)_m = Φ_m − Φ_{m−n}`. -/
theorem jumpLaplacian_thetaVoltage (n m : ℤ) :
    jumpLaplacian thetaConductance (fun k => ((cdfAction k - cdfAction (k - n) : ℝ) : ℂ)) m =
      (if m = n then 1 else 0) - (if m = 0 then 1 else 0) := by
  have h := isJumpProfile_thetaNetworkProfile.jumpLaplacian_potentialVoltage n m
  simp only [potentialVoltage, profileAction_thetaNetworkProfile] at h
  exact h

theorem thetaVoltage_eq (n m : ℤ) :
    potentialVoltage thetaNetworkProfile n m = cdfAction m - cdfAction (m - n) := by
  simp only [potentialVoltage, profileAction_thetaNetworkProfile]

/-- **The effective resistance** between `0` and `n` is `2Φ_n`. -/
theorem thetaVoltage_drop (n : ℤ) :
    potentialVoltage thetaNetworkProfile n n - potentialVoltage thetaNetworkProfile n 0 = 2 * cdfAction n := by
  rw [potentialVoltage_drop, profileAction_thetaNetworkProfile]

/-- **Grounded positivity** for theta: `Σ c̄_m c_n (Φ_m + Φ_n − Φ_{m−n}) = ∫₀¹ |Σ c_m(1 − e_m)|²/h ≥ 0`. -/
theorem theta_groundedKernel_form (S : Finset ℤ) (c : ℤ → ℂ) :
    ∑ m ∈ S, ∑ n ∈ S, (starRingEnd ℂ) (c m) * c n * ((cdfAction m + cdfAction n - cdfAction (m - n) : ℝ) : ℂ) =
      ((∫ t in (0 : ℝ)..1, ‖∑ m ∈ S, c m * (1 - fourierMode m t)‖ ^ 2 / thetaNetworkProfile t : ℝ) : ℂ) := by
  have h := isJumpProfile_thetaNetworkProfile.sum_groundedKernel_eq S c
  simp only [groundedKernel, profileAction_thetaNetworkProfile] at h
  exact h

/-- **The gauge shift is not in `ℓ²`**: the decaying voltage is the grounded kernel minus the column
constant `Φ_n`, and for `n ≠ 0` that constant sequence is not square summable. -/
theorem not_summable_sq_gauge_shift {n : ℤ} (hn : n ≠ 0) : ¬ Summable fun _ : ℤ => cdfAction n ^ 2 := by
  rw [summable_const_iff]
  have hpos : 0 < cdfAction n := by
    rcases Int.natAbs_eq n with h | h
    · rw [h]; exact cdfAction_pos (by omega)
    · rw [h, cdfAction_neg]; exact cdfAction_pos (by omega)
  positivity

/-! ## The decaying gauge -/

theorem tendsto_cdfAction_add_sub (a : ℤ) :
    Tendsto (fun k : ℕ => cdfAction ((k : ℤ) + a) - cdfAction k) atTop (𝓝 0) := by
  have h := (tendsto_mul_cdfAction_add_sub a).mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [Function.comp_apply]
  field_simp

/-- **The decaying gauge**: `v^(n)_m → 0` as `m → +∞`. -/
theorem tendsto_thetaVoltage_atTop (n : ℤ) :
    Tendsto (fun m : ℕ => potentialVoltage thetaNetworkProfile n m) atTop (𝓝 0) := by
  have h := (tendsto_cdfAction_add_sub (-n)).neg
  rw [neg_zero] at h
  refine h.congr fun m => ?_
  rw [thetaVoltage_eq, ← sub_eq_add_neg]
  ring

/-- **The decaying gauge**: `v^(n)_{−m} → 0` as `m → +∞`. -/
theorem tendsto_thetaVoltage_atBot (n : ℤ) :
    Tendsto (fun m : ℕ => potentialVoltage thetaNetworkProfile n (-(m : ℤ))) atTop (𝓝 0) := by
  have h := (tendsto_cdfAction_add_sub n).neg
  rw [neg_zero] at h
  refine h.congr fun m => ?_
  rw [thetaVoltage_eq, cdfAction_neg, show -(m : ℤ) - n = -((m : ℤ) + n) by ring, cdfAction_neg]
  ring

/-! ## The quotient is the dipole-response operator -/

/-- **(6)** `⟨e_m, D e_n⟩ = v^(n)_m/(2πn)` for `m, n ≠ 0`. -/
theorem inner_unitFourierBasis_thetaQuotientOperator_eq_voltage {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪unitFourierBasis m, thetaQuotientOperator (unitFourierBasis n)⟫_ℂ =
      ((potentialVoltage thetaNetworkProfile n m / (2 * Real.pi * n) : ℝ) : ℂ) := by
  rw [inner_unitFourierBasis_thetaQuotientOperator hm hn, thetaVoltage_eq,
    show n - m = -(m - n) by ring, cdfAction_neg]

/-- **(6) for the full inverse**, including the pinned-mean row `m = 0`. -/
theorem inner_unitFourierBasis_thetaKernelOperator_eq_voltage (m : ℤ) {n : ℤ} (hn : n ≠ 0) :
    ⟪unitFourierBasis m, thetaKernelOperator (unitFourierBasis n)⟫_ℂ =
      ((potentialVoltage thetaNetworkProfile n m / (2 * Real.pi * n) : ℝ) : ℂ) := by
  rw [inner_unitFourierBasis_thetaKernelOperator m hn, thetaVoltage_eq,
    show n - m = -(m - n) by ring, cdfAction_neg]

/-! ## Isolated opposite-frequency blocks -/

theorem blockOff_sq_lt_blockDiag_sq (n : ℕ) : blockOff n ^ 2 < blockDiag n ^ 2 := by
  have h1 := cdfAction_two_mul_lt (n := n + 1) (by omega)
  have ho := blockOff_pos n
  have hlt : blockOff n < blockDiag n := by
    unfold blockOff blockDiag
    have hpi : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
    rw [div_lt_div_iff_of_pos_right hpi]
    push_cast at h1 ⊢
    linarith
  nlinarith

/-- **Each isolated `{n, −n}` block squares to a positive multiple of its projection**:
`X_n² = (d² − o²) Π_n` with `d² > o²`, so its eigenvalues `±√(d² − o²)` are real and nonzero. -/
theorem thetaDiagonalBlock_comp_self (n : ℕ) :
    thetaDiagonalBlock n ∘L thetaDiagonalBlock n = ((blockDiag n ^ 2 - blockOff n ^ 2 : ℝ) : ℂ) • pairProj n := by
  set a := unitFourierBasis (blockPos n)
  set b := unitFourierBasis (blockNeg n)
  have haa : ⟪a, a⟫_ℂ = 1 := by rw [inner_unitFourierBasis, if_pos rfl]
  have hbb : ⟪b, b⟫_ℂ = 1 := by rw [inner_unitFourierBasis, if_pos rfl]
  have hab : ⟪a, b⟫_ℂ = 0 := by rw [inner_unitFourierBasis, if_neg (blockPos_ne_blockNeg n)]
  have hba : ⟪b, a⟫_ℂ = 0 := by rw [inner_unitFourierBasis, if_neg (blockPos_ne_blockNeg n).symm]
  have hX : ∀ y, thetaDiagonalBlock n y =
      ((blockDiag n : ℂ) * ⟪a, y⟫_ℂ + (blockOff n : ℂ) * ⟪b, y⟫_ℂ) • a +
        (-(blockOff n : ℂ) * ⟪a, y⟫_ℂ - (blockDiag n : ℂ) * ⟪b, y⟫_ℂ) • b := by
    intro y
    rw [thetaDiagonalBlock_eq]
    simp only [add_apply, sub_apply, smul_apply,
      rankOneMap_apply]
    module
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, hX (thetaDiagonalBlock n x), hX x, smul_apply,
    pairProj_apply]
  simp only [inner_add_right, inner_smul_right, haa, hbb, hab, hba]
  push_cast
  module

theorem eq_zero_of_thetaDiagonalBlock_eq_zero {n : ℕ} {x : ThetaL2} (hx : pairProj n x = x)
    (h0 : thetaDiagonalBlock n x = 0) : x = 0 := by
  have h := congrArg (fun T : ThetaL2 →L[ℂ] ThetaL2 => T x) (thetaDiagonalBlock_comp_self n)
  simp only [ContinuousLinearMap.comp_apply, h0, map_zero, smul_apply, hx] at h
  have hne : ((blockDiag n ^ 2 - blockOff n ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sub_pos.2 (blockOff_sq_lt_blockDiag_sq n)).ne'
  exact (smul_eq_zero.1 h.symm).resolve_left hne

/-- Every eigenvalue `μ` of an isolated block satisfies `μ² = d² − o² > 0`. -/
theorem sq_eq_of_thetaDiagonalBlock_eigen {n : ℕ} {x : ThetaL2} {μ : ℂ} (hx : pairProj n x = x) (hne : x ≠ 0)
    (h : thetaDiagonalBlock n x = μ • x) : μ ^ 2 = ((blockDiag n ^ 2 - blockOff n ^ 2 : ℝ) : ℂ) := by
  have h2 := congrArg (fun T : ThetaL2 →L[ℂ] ThetaL2 => T x) (thetaDiagonalBlock_comp_self n)
  simp only [ContinuousLinearMap.comp_apply, h, map_smul, smul_apply, hx, smul_smul] at h2
  have := sub_eq_zero.2 h2
  rw [← sub_smul] at this
  have := (smul_eq_zero.1 this).resolve_right hne
  rw [sq]
  exact sub_eq_zero.1 this

end

end RHTower
