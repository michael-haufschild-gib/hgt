import GaloisForLFunctions.RHTower.CausalMobiusThetaPhysicalWavelet
import GaloisForLFunctions.RHTower.EulerDeletionWeightedResidueProjection
import GaloisForLFunctions.RHTower.EulerDeletionLogClockConditionalApproximation
import GaloisForLFunctions.RHTower.EulerDeletionPrimePowerLayerSupport
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!
# History localization of the causal theta coordinate

* **(18)** `Σ_{r≥1} {r/d}/(r(r+1)) = log(d)/d`;
* the base history is the constant vector and the base projection of `C_N` and `P_N` is
  `(Σ_{d≤N} μ(d) log(d)/d) · 1`, with scalar tending to `−1`;
* its pairing with `q_N` is `O(N^{−5/2})`, the high-clock pairing is `O(N^{−1/2})`;
* **(19)** `B(N) = Σ_{l<min(K_N,N), l+1 prime power} ⟨L_l P_N, q_N⟩_H + O(1)`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

namespace DeletionResidueMartingale

/-! ## (18) The residue mean -/

theorem sum_range_succ_eq_sum_Icc_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range N, f (i + 1) = ∑ d ∈ Finset.Icc 1 N, f d := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

theorem natCast_mod_succ_sub_mod (d j : ℕ) (hd : 0 < d) :
    (((j + 1) % d : ℕ) : ℝ) - ((j % d : ℕ) : ℝ) = 1 - if d ∣ j + 1 then (d : ℝ) else 0 := by
  have hdiv := Nat.div_add_mod j d
  have hlt := Nat.mod_lt j hd
  set q := j / d
  set s := j % d
  have hj1 : j + 1 = (s + 1) + d * q := by omega
  by_cases hs : s + 1 < d
  · have hmod : (j + 1) % d = s + 1 := by
      rw [hj1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
    have hndvd : ¬ d ∣ j + 1 := by
      intro h
      have := Nat.mod_eq_zero_of_dvd h
      omega
    rw [hmod, if_neg hndvd]
    push_cast
    ring
  · have hs' : s + 1 = d := by omega
    have hmod : (j + 1) % d = 0 := by rw [hj1, hs', Nat.add_mul_mod_self_left, Nat.mod_self]
    rw [hmod, if_pos (Nat.dvd_of_mod_eq_zero hmod)]
    have : ((s + 1 : ℕ) : ℝ) = d := by rw [hs']
    push_cast at this ⊢
    linarith

/-- Abel summation for the residue mean. -/
theorem sum_residue_mul_cellWeight_abel (d R : ℕ) :
    ∑ j ∈ Finset.range R, residue d j * cellWeight j =
      ∑ j ∈ Finset.range R, ((((j + 1) % d : ℕ) : ℝ) / d - ((j % d : ℕ) : ℝ) / d) / ((j : ℝ) + 1) -
        ((R % d : ℕ) : ℝ) / d / ((R : ℝ) + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, residue, cellWeight]
    have h1 : (R : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (R : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem sum_range_dvd_succ_div (d K : ℕ) (hd : 0 < d) :
    ∑ j ∈ Finset.range (d * K), (if d ∣ j + 1 then (d : ℝ) else 0) / ((j : ℝ) + 1) =
      ∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    rw [Finset.sum_eq_single (d - 1)]
    · rw [if_pos (by rw [show d * K + (d - 1) + 1 = d * (K + 1) by
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring]; exact dvd_mul_right d (K + 1))]
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hcast : ((d * K + (d - 1) : ℕ) : ℝ) + 1 = d * ((K : ℝ) + 1) := by
        rw [show d * K + (d - 1) = d * K + d - 1 by omega]
        rw [Nat.cast_sub (by nlinarith)]
        push_cast; ring
      rw [hcast]
      field_simp
    · intro a ha hne
      rw [if_neg]
      · simp
      · intro hdvd
        have ha' := Finset.mem_range.1 ha
        have h2 : d ∣ a + 1 := by
          have : d ∣ d * K + (a + 1) := by rwa [← add_assoc]
          exact (Nat.dvd_add_right (dvd_mul_right d K)).1 this
        have := Nat.le_of_dvd (by omega) h2
        have h3 : a + 1 = d := by
          obtain ⟨c, hc⟩ := h2
          rcases c with _ | _ | c
          · omega
          · omega
          · nlinarith
        omega
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem natCast_harmonic_eq_sum_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  simp [one_div]

theorem tendsto_harmonic_mul_sub_harmonic {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun K : ℕ => (harmonic (d * K) : ℝ) - harmonic K) atTop (𝓝 (Real.log d)) := by
  have h := Real.tendsto_harmonic_sub_log
  have hdK : Tendsto (fun K : ℕ => d * K) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hd)⟩
  have hlim := ((h.comp hdK).sub h).add_const (Real.log d)
  rw [sub_self, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hKR : (K : ℝ) ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply]
  push_cast
  rw [Real.log_mul hdR hKR]
  ring

/-- **(18)** `Σ_{r≥1} {r/d}/(r(r+1)) = log(d)/d`. -/
theorem hasSum_residue_mul_cellWeight {d : ℕ} (hd : 1 ≤ d) :
    HasSum (fun j => residue d j * cellWeight j) (Real.log d / d) := by
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Summable fun j => residue d j * cellWeight j :=
    hasSum_cellWeight.summable.of_nonneg_of_le
      (fun j => mul_nonneg (residue_bounds d j).1 (cellWeight_pos j).le)
      (fun j => mul_le_of_le_one_left (cellWeight_pos j).le (residue_bounds d j).2)
  set A : ℕ → ℝ := fun R => ∑ j ∈ Finset.range R,
    ((((j + 1) % d : ℕ) : ℝ) / d - ((j % d : ℕ) : ℝ) / d) / ((j : ℝ) + 1) with hA_def
  have hF : Tendsto (fun R : ℕ => ((R % d : ℕ) : ℝ) / d / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℕ => 1 / ((R : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun R => by positivity) (fun R => ?_) hlim
    gcongr
    rw [div_le_one hdR]
    exact_mod_cast (Nat.mod_lt R hd0).le
  have hAlim : Tendsto A atTop (𝓝 (∑' j, residue d j * cellWeight j)) := by
    have := hs.hasSum.tendsto_sum_nat.add hF
    rw [add_zero] at this
    refine this.congr fun R => ?_
    rw [sum_residue_mul_cellWeight_abel]
    ring
  have hdK : Tendsto (fun K : ℕ => d * K) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hd)⟩
  have hAval : ∀ K : ℕ, A (d * K) = ((harmonic (d * K) : ℝ) - harmonic K) / d := by
    intro K
    simp only [A]
    have hterm : ∀ j : ℕ, ((((j + 1) % d : ℕ) : ℝ) / d - ((j % d : ℕ) : ℝ) / d) / ((j : ℝ) + 1) =
        (1 / ((j : ℝ) + 1)) / d - (if d ∣ j + 1 then (d : ℝ) else 0) / ((j : ℝ) + 1) / d := by
      intro j
      rw [← sub_div, natCast_mod_succ_sub_mod d j hd0]
      field_simp
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.sum_div, sum_range_dvd_succ_div d K hd0, natCast_harmonic_eq_sum_range,
      natCast_harmonic_eq_sum_range, sub_div]
  have hlim2 : Tendsto (fun K : ℕ => A (d * K)) atTop (𝓝 (Real.log d / d)) := by
    simp_rw [hAval]
    exact (tendsto_harmonic_mul_sub_harmonic hd).div_const _
  have heq := tendsto_nhds_unique (hAlim.comp hdK) hlim2
  rw [← heq]
  exact hs.hasSum

/-! ## The base history is the constant vector -/

/-- The constant physical vector `1`. -/
def cellUnitVec : Lp ℝ 2 cellMeasure := physVec fun _ => 1

theorem summable_cellUnitVec : Summable fun j : ℕ => ((fun _ : ℕ => (1 : ℝ)) j) ^ 2 * cellWeight j := by
  simpa using hasSum_cellWeight.summable

theorem cellUnitVec_apply (j : ℕ) : cellUnitVec j = 1 := physVec_apply summable_cellUnitVec j

theorem hasSum_inner_cellUnitVec_left (v : Lp ℝ 2 cellMeasure) :
    HasSum (fun j => v j * cellWeight j) (inner ℝ cellUnitVec v) := by
  have h := hasSum_inner cellUnitVec v
  simp only [cellUnitVec_apply, one_mul] at h
  exact h

theorem inner_cellUnitVec_cellUnitVec : inner ℝ cellUnitVec cellUnitVec = 1 := by
  have h := hasSum_inner_cellUnitVec_left cellUnitVec
  simp only [cellUnitVec_apply, one_mul] at h
  exact h.unique hasSum_cellWeight

theorem cellUnitVec_mem_historySpace_zero : cellUnitVec ∈ historySpace 0 := by
  change cellUnitVec ∈ lpMeas ℝ ℝ (residueSigma (clock 0)) 2 cellMeasure
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  refine ⟨fun _ => (1 : ℝ), stronglyMeasurable_const, Eventually.of_forall fun j => ?_⟩
  exact cellUnitVec_apply j

/-- `Π₀ v = ⟨1, v⟩ 1`. -/
theorem starProjection_historySpace_zero (v : Lp ℝ 2 cellMeasure) :
    (historySpace 0).starProjection v = inner ℝ cellUnitVec v • cellUnitVec := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.smul_mem _ _ cellUnitVec_mem_historySpace_zero) fun w hw => ?_
  obtain ⟨h, -, hfac⟩ := historySpace_factors_through_clock 0 w hw
  have hclock : clock 0 = 1 := by simp [clock]
  have hw' : w = h 0 • cellUnitVec := by
    refine Lp.ext_iff.2 ?_
    filter_upwards [Lp.coeFn_smul (h 0) cellUnitVec] with j hj
    rw [hj, Pi.smul_apply, cellUnitVec_apply, hfac j, hclock, Nat.mod_one, smul_eq_mul, mul_one]
  rw [hw', inner_smul_right, inner_sub_left, inner_smul_left, real_inner_comm cellUnitVec v,
    inner_cellUnitVec_cellUnitVec]
  simp

theorem inner_cellUnitVec_residueVec {d : ℕ} (hd : 1 ≤ d) :
    inner ℝ cellUnitVec (residueVec d) = Real.log d / d := by
  have h := hasSum_inner_cellUnitVec_left (residueVec d)
  have hp : ∀ j, residueVec d j = residue d j := fun j => by rw [residueVec_apply_eq_residue]
  simp only [hp] at h
  exact h.unique (hasSum_residue_mul_cellWeight hd)

/-- `⟨1, C_N⟩_H = Σ_{d≤N} μ(d) log(d)/d`. -/
theorem inner_cellUnitVec_sourceVec_moebius (N : ℕ) :
    inner ℝ cellUnitVec (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) =
      ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d := by
  rw [sourceVec, inner_sum]
  simp_rw [inner_smul_right]
  rw [← sum_range_succ_eq_sum_Icc_one N fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_cellUnitVec_residueVec (by omega)]
  push_cast
  ring

theorem inner_cellUnitVec_martingalePart (N : ℕ) : inner ℝ cellUnitVec (martingalePart N) = 0 := by
  rw [martingalePart, inner_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [signedInnovation, inner_smul_right, real_inner_comm]
  have := Submodule.starProjection_inner_eq_zero (K := historySpace i) (residueVec (i + 1)) cellUnitVec
    (historySpace_mono (Nat.zero_le i) cellUnitVec_mem_historySpace_zero)
  rw [innovation, this, mul_zero]

/-- `⟨1, P_N⟩_H = Σ_{d≤N} μ(d) log(d)/d`. -/
theorem inner_cellUnitVec_predictableDrift (N : ℕ) :
    inner ℝ cellUnitVec (predictableDrift N) =
      ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d := by
  have h := source_eq_martingale_add_drift N
  rw [← inner_cellUnitVec_sourceVec_moebius, h, inner_add_right, inner_cellUnitVec_martingalePart, zero_add]

/-- The base projections of `C_N` and of `P_N` are `(Σ_{d≤N} μ(d) log(d)/d) · 1`. -/
theorem starProjection_historySpace_zero_sourceVec_moebius (N : ℕ) :
    (historySpace 0).starProjection (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) =
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) • cellUnitVec := by
  rw [starProjection_historySpace_zero, inner_cellUnitVec_sourceVec_moebius]

theorem starProjection_historySpace_zero_predictableDrift (N : ℕ) :
    (historySpace 0).starProjection (predictableDrift N) =
      (∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) • cellUnitVec := by
  rw [starProjection_historySpace_zero, inner_cellUnitVec_predictableDrift]

end DeletionResidueMartingale

open DeletionResidueMartingale in
/-- The base history scalar tends to `−1`. -/
theorem tendsto_sum_moebius_log_div : Tendsto (fun N : ℕ =>
    ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d) atTop (𝓝 (-1)) := by
  have h := Sieve.tendsto_moebiusLogHarmonicPartial_one.neg
  refine h.congr fun N => ?_
  rw [Sieve.moebiusLogHarmonicPartial, Finset.sum_range_succ', Sieve.moebiusLogHarmonicTerm_zero,
    add_zero, ← sum_range_succ_eq_sum_Icc_one N fun d =>
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Sieve.moebiusLogHarmonicTerm]
  rw [Real.rpow_neg_one]
  push_cast
  ring

open DeletionResidueMartingale

theorem exists_abs_sum_moebius_log_div_le : ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
    |∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d / d| ≤ S := by
  obtain ⟨S, hS⟩ := isBounded_iff_forall_norm_le.1
    (Metric.isBounded_range_of_tendsto _ tendsto_sum_moebius_log_div)
  refine ⟨max S 0, le_max_right _ _, fun N => ?_⟩
  have := hS _ (Set.mem_range_self N)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem inner_cellUnitVec_thetaWaveletVec {N : ℕ} (hN : 1 ≤ N) :
    inner ℝ cellUnitVec (thetaWaveletVec N) = thetaCuspSeed (1 / N) / Real.sqrt N := by
  have h := hasSum_inner_cellUnitVec_left (thetaWaveletVec N)
  simp only [thetaWaveletVec_apply hN] at h
  exact h.unique (hasSum_thetaCellWavelet_mul_cellWeight hN)

/-- The base projection pairs with `q_N` at order `N^{−5/2}`. -/
theorem exists_abs_inner_base_predictableDrift_wavelet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |inner ℝ ((historySpace 0).starProjection (predictableDrift N)) (thetaWaveletVec N)| ≤
      C / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_sum_moebius_log_div_le
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_thetaCuspSeed_le_sq
  refine ⟨S * Cs, by positivity, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [starProjection_historySpace_zero_predictableDrift, inner_smul_left,
    inner_cellUnitVec_thetaWaveletVec hN, conj_trivial, abs_mul, abs_div, abs_of_pos hs]
  calc _ ≤ S * (Cs * (1 / (N : ℝ)) ^ 2 / Real.sqrt N) :=
        mul_le_mul (hS N) (by gcongr; exact hCs _) (by positivity) hS0
    _ = S * Cs / ((N : ℝ) ^ 2 * Real.sqrt N) := by field_simp

/-- The high-clock pairing is `O(N^{−1/2})`. -/
theorem exists_abs_inner_highClock_predictableDrift_wavelet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |inner ℝ (predictableDrift N - (historySpace (min (logarithmicClockThreshold N) N)).starProjection
      (predictableDrift N)) (thetaWaveletVec N)| ≤ C / Real.sqrt N := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  refine ⟨Real.sqrt 110 * B, by positivity, fun N hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  have h := predictableDrift_logClockProjection_error_norm_sq_le N
  have hle : ‖predictableDrift N - (historySpace (min (logarithmicClockThreshold N) N)).starProjection
      (predictableDrift N)‖ ≤ Real.sqrt 110 / Real.sqrt N := by
    rw [← Real.sqrt_div' 110 hNR.le]
    refine Real.le_sqrt_of_sq_le (h.trans ?_)
    gcongr
    linarith
  calc _ ≤ _ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt 110 / Real.sqrt N * B := mul_le_mul hle (hB N hN) (norm_nonneg _) (by positivity)
    _ = Real.sqrt 110 * B / Real.sqrt N := by ring

/-- Telescoping of the nested history projections into layers. -/
theorem starProjection_historySpace_eq_base_add_sum_historyLayer (m : ℕ) (v : Lp ℝ 2 cellMeasure) :
    (historySpace m).starProjection v =
      (historySpace 0).starProjection v + ∑ l ∈ Finset.range m, historyLayer l v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, historyLayer, sub_apply]
    abel

/-- Only prime-power layers carry predictable drift. -/
theorem sum_historyLayer_predictableDrift_eq_primePower (m N : ℕ) :
    ∑ l ∈ Finset.range m, historyLayer l (predictableDrift N) =
      ∑ l ∈ (Finset.range m).filter (fun l => IsPrimePow (l + 1)), historyLayer l (predictableDrift N) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hp : IsPrimePow (l + 1)
  · rw [if_pos hp]
  · rw [if_neg hp, historyLayer_predictableDrift_eq_zero_of_not_isPrimePow l N hp]

/-- **(19)** `B(N) = Σ_{l<min(K_N,N), l+1 prime power} ⟨L_l P_N, q_N⟩_H + O(1)`. -/
theorem exists_abs_causalMobiusThetaTail_sub_primePower_layers_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → |causalMobiusThetaTail N -
      ∑ l ∈ (Finset.range (min (logarithmicClockThreshold N) N)).filter (fun l => IsPrimePow (l + 1)),
        inner ℝ (historyLayer l (predictableDrift N)) (thetaWaveletVec N)| ≤ C := by
  obtain ⟨C17, hC170, hC17⟩ := exists_abs_causalMobiusThetaTail_sub_inner_predictableDrift_le
  obtain ⟨Cb, hCb0, hCb⟩ := exists_abs_inner_base_predictableDrift_wavelet_le
  obtain ⟨Ch, hCh0, hCh⟩ := exists_abs_inner_highClock_predictableDrift_wavelet_le
  refine ⟨C17 + Cb + Ch, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hNR
  have hden : 1 ≤ (N : ℝ) ^ 2 * Real.sqrt N := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hNR) hs1
  set m := min (logarithmicClockThreshold N) N
  set P := predictableDrift N
  set q := thetaWaveletVec N
  have hdecomp : P = (historySpace 0).starProjection P +
      ∑ l ∈ (Finset.range m).filter (fun l => IsPrimePow (l + 1)), historyLayer l P +
      (P - (historySpace m).starProjection P) := by
    rw [← sum_historyLayer_predictableDrift_eq_primePower, ← starProjection_historySpace_eq_base_add_sum_historyLayer]
    abel
  have hinner : inner ℝ P q = inner ℝ ((historySpace 0).starProjection P) q +
      ∑ l ∈ (Finset.range m).filter (fun l => IsPrimePow (l + 1)), inner ℝ (historyLayer l P) q +
      inner ℝ (P - (historySpace m).starProjection P) q := by
    conv_lhs => rw [hdecomp]
    rw [inner_add_left, inner_add_left, sum_inner]
  have h1 := hC17 N hN
  have h2 := (hCb N hN).trans (div_le_self hCb0 hden)
  have h3 := (hCh N hN).trans (div_le_self hCh0 hs1)
  have hkey : causalMobiusThetaTail N - ∑ l ∈ (Finset.range m).filter (fun l => IsPrimePow (l + 1)),
      inner ℝ (historyLayer l P) q = (causalMobiusThetaTail N - inner ℝ P q) +
        inner ℝ ((historySpace 0).starProjection P) q + inner ℝ (P - (historySpace m).starProjection P) q := by
    rw [hinner]; ring
  rw [hkey]
  calc _ ≤ |causalMobiusThetaTail N - inner ℝ P q| + |inner ℝ ((historySpace 0).starProjection P) q| +
        |inner ℝ (P - (historySpace m).starProjection P) q| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C17 + Cb + Ch := add_le_add (add_le_add h1 h2) h3

end

end RHTower
