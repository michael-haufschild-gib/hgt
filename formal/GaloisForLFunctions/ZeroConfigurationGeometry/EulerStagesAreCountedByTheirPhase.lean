import GaloisForLFunctions.ZeroConfigurationGeometry.EulerStagesRepelAboveTheHorizon

/-!
# Euler stages are counted by their phase

The configuration of the finite Euler stage `Λ_X` on the critical line is the preimage of a lattice
under its phase. From a zero `t₀`, the phase law `A_X(½+it) = A_X(½+it₀) exp(i Θ(t))` gives
`Re A_X(½+it) = −b e^{−Im Θ(t)} sin(Re Θ(t))` with `b ≠ 0`.

* **The phase lattice** (`eulerStage_eq_zero_iff_phase`). On the whole line, `t` is a zero of `Λ_X`
  exactly when `Re Θ(t) = ∫_{t₀}^t Re L_X(½+iτ) dτ` lies in `πℤ`.
* **Monotone phase above the horizon** (`stagePhase_re_strictMonoOn`). Above the horizon the phase
  speed is positive, so `Re Θ` is strictly increasing.
* **The exact count** (`ncard_eulerStage_zeros`). Above the horizon the zeros at heights in
  `[t₀, T]` number exactly `⌊Re Θ(T)/π⌋ + 1`: the phase maps them bijectively onto
  `{0, π, …, ⌊Re Θ(T)/π⌋π}`.
* **Riemann–von Mangoldt up to the prime weight** (`ncard_eulerStage_zeros_bounds`). With the
  speed bounds, the count lies between `⌊m(T − t₀)/π⌋ + 1` and `⌊M_T(T − t₀)/π⌋ + 1`, where
  `m = (log(t₀/2π) − 6/t₀ − W)/2` and `M_T = (log((T+1)/2π) + 6/t₀ + W)/2`, `W = W(X, 0)`.

Above its horizon the Euler-stage configuration is therefore completely described: on the line,
simple, and the preimage of `πℤ` under a phase whose speed is the archimedean speed
`½ log(t/2π)` up to the prime weight `W/2`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open _root_.RHTower

/-- **The zeros on the line form a phase lattice.** If `t₀` is a zero of `Λ_X` on the line, then
`t` is a zero iff `Re Θ(t) ∈ πℤ`. -/
theorem eulerStage_eq_zero_iff_phase {X : ℕ} {t₀ : ℝ} (h0 : eulerStage X (linePt t₀) = 0)
    (t : ℝ) : eulerStage X (linePt t) = 0 ↔ ∃ k : ℤ, (stagePhase X t₀ t).re = k * Real.pi := by
  have hre0 := stageLine_re_eq_zero_of_eulerStage h0
  have hb : (stageLine X t₀).im ≠ 0 := fun h => stageLine_ne_zero X t₀ (Complex.ext hre0 h)
  have hE := (Real.exp_pos (-(stagePhase X t₀ t).im)).ne'
  rw [eulerStage_linePt, Complex.ofReal_eq_zero, re_stageLine_of_zero hre0]
  simp only [mul_eq_zero, neg_eq_zero, two_ne_zero, hb, hE, false_or, Real.sin_eq_zero_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

theorem re_stageSpeed_pos {X : ℕ} {t₀ τ : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi))) (hτ : t₀ ≤ τ) :
    0 < (stageSpeed X τ).re := by
  have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith)]; linarith
  have := re_stageSpeed_ge X hτa
  have := horizon_mono ht₀ hτ
  linarith

/-- **The phase is strictly increasing above the horizon.** -/
theorem stagePhase_re_strictMonoOn {X : ℕ} {t₀ : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi))) :
    StrictMonoOn (fun t => (stagePhase X t₀ t).re) (Ici t₀) := by
  intro s hs t _ hst
  have hi := fun a b => (continuous_re_stageSpeed X).intervalIntegrable (μ := volume) a b
  simp only
  rw [re_stagePhase, re_stagePhase,
    ← intervalIntegral.integral_add_adjacent_intervals (hi t₀ s) (hi s t)]
  have := intervalIntegral.intervalIntegral_pos_of_pos_on (hi s t)
    (fun τ hτ => re_stageSpeed_pos ht₀ hhor ((mem_Ici.mp hs).trans hτ.1.le)) hst
  linarith

theorem continuous_stagePhase_re (X : ℕ) (t₀ : ℝ) :
    Continuous fun t => (stagePhase X t₀ t).re :=
  Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun τ =>
    (hasDerivAt_stagePhase X t₀ τ).continuousAt)

/-- **The exact count.** Above the horizon, after a zero `t₀` of `Λ_X` on the line, the zeros at
heights in `[t₀, T]` number exactly `⌊Re Θ(T)/π⌋ + 1`. -/
theorem ncard_eulerStage_zeros {X : ℕ} {t₀ T : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi)))
    (h0 : eulerStage X (linePt t₀) = 0) (hT : t₀ ≤ T) :
    {t ∈ Icc t₀ T | eulerStage X (linePt t) = 0}.ncard =
      ⌊(stagePhase X t₀ T).re / Real.pi⌋₊ + 1 := by
  set Φ : ℝ → ℝ := fun t => (stagePhase X t₀ t).re with hΦdef
  have hmono : StrictMonoOn Φ (Icc t₀ T) :=
    (stagePhase_re_strictMonoOn ht₀ hhor).mono Icc_subset_Ici_self
  have hcont : ContinuousOn Φ (Icc t₀ T) := (continuous_stagePhase_re X t₀).continuousOn
  have hΦ0 : Φ t₀ = 0 := by simp [hΦdef, stagePhase]
  have hT0 : 0 ≤ Φ T := hΦ0 ▸ hmono.monotoneOn ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  set N := ⌊Φ T / Real.pi⌋₊ with hN
  have himage : Φ '' {t ∈ Icc t₀ T | eulerStage X (linePt t) = 0} =
      (fun k : ℕ => (k : ℝ) * Real.pi) '' ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨t, ⟨htI, hz⟩, rfl⟩
      obtain ⟨k, hk⟩ := (eulerStage_eq_zero_iff_phase h0 t).mp hz
      have h1 : 0 ≤ Φ t := hΦ0 ▸ hmono.monotoneOn ⟨le_rfl, hT⟩ htI htI.1
      have h2 : Φ t ≤ Φ T := hmono.monotoneOn htI ⟨hT, le_rfl⟩ htI.2
      have hk' : Φ t = k * Real.pi := hk
      have hk0 : 0 ≤ k := by
        by_contra hneg
        have : (k : ℝ) * Real.pi < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast not_le.mp hneg) Real.pi_pos
        linarith
      have hkcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      refine ⟨k.toNat, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.le_floor ?_))), ?_⟩
      · rw [hkcast, le_div_iff₀ Real.pi_pos]; linarith
      · simp only; rw [hkcast, hk']
    · rintro ⟨k, hk, rfl⟩
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_coe.mp hk))
      have hle : (k : ℝ) * Real.pi ≤ Φ T := by
        have h1 : (k : ℝ) ≤ Φ T / Real.pi :=
          (Nat.cast_le.mpr hkN).trans (Nat.floor_le (div_nonneg hT0 Real.pi_pos.le))
        rwa [le_div_iff₀ Real.pi_pos] at h1
      obtain ⟨t, htI, ht⟩ := intermediate_value_Icc hT hcont
        ⟨by rw [hΦ0]; positivity, hle⟩
      exact ⟨t, ⟨htI, (eulerStage_eq_zero_iff_phase h0 t).mpr ⟨k, by
        have : Φ t = (k : ℝ) * Real.pi := ht
        rw [show (stagePhase X t₀ t).re = Φ t from rfl, this]; push_cast; ring⟩⟩, ht⟩
  have hinj : Function.Injective fun k : ℕ => (k : ℝ) * Real.pi := fun a b h => by
    have := mul_right_cancel₀ Real.pi_ne_zero h
    exact_mod_cast this
  rw [← Set.ncard_image_of_injOn (hmono.injOn.mono fun t ht => ht.1), himage,
    Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]

/-- **Riemann–von Mangoldt up to the prime weight.** Above the horizon, after a zero `t₀`, the
number of zeros of `Λ_X` on the line at heights in `[t₀, T]` lies between `⌊m(T − t₀)/π⌋ + 1` and
`⌊M_T(T − t₀)/π⌋ + 1`, with `m = (log(t₀/2π) − 6/t₀ − W)/2`, `M_T = (log((T+1)/2π) + 6/t₀ + W)/2`
and `W = W(X, 0)`. -/
theorem ncard_eulerStage_zeros_bounds {X : ℕ} {t₀ T : ℝ} (ht₀ : 4 ≤ t₀)
    (hhor : 6 / t₀ + eulerStageWeight X 0 < Real.log (t₀ / (2 * Real.pi)))
    (h0 : eulerStage X (linePt t₀) = 0) (hT : t₀ ≤ T) :
    ⌊(Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - eulerStageWeight X 0) / 2 * (T - t₀) /
        Real.pi⌋₊ + 1 ≤ {t ∈ Icc t₀ T | eulerStage X (linePt t) = 0}.ncard ∧
      {t ∈ Icc t₀ T | eulerStage X (linePt t) = 0}.ncard ≤
        ⌊(Real.log ((T + 1) / (2 * Real.pi)) + 6 / t₀ + eulerStageWeight X 0) / 2 * (T - t₀) /
          Real.pi⌋₊ + 1 := by
  rw [ncard_eulerStage_zeros ht₀ hhor h0 hT, re_stagePhase]
  set m := (Real.log (t₀ / (2 * Real.pi)) - 6 / t₀ - eulerStageWeight X 0) / 2 with hm
  set M := (Real.log ((T + 1) / (2 * Real.pi)) + 6 / t₀ + eulerStageWeight X 0) / 2 with hM
  have hge : ∀ τ ∈ Icc t₀ T, m ≤ (stageSpeed X τ).re := fun τ hτ => by
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.1]
    have := re_stageSpeed_ge X hτa
    have := horizon_mono ht₀ hτ.1
    rw [hm]; linarith
  have hle : ∀ τ ∈ Icc t₀ T, (stageSpeed X τ).re ≤ M := fun τ hτ => by
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hτa : 4 ≤ |τ| := by rw [abs_of_pos hτ0]; linarith [hτ.1]
    have h := re_stageSpeed_le X hτa
    rw [abs_of_pos hτ0] at h
    have h1 : Real.log ((τ + 1) / (2 * Real.pi)) ≤ Real.log ((T + 1) / (2 * Real.pi)) :=
      Real.log_le_log (by positivity)
        (div_le_div_of_nonneg_right (by linarith [hτ.2]) (by positivity))
    have h2 : 6 / τ ≤ 6 / t₀ := div_le_div_of_nonneg_left (by norm_num) (by linarith) hτ.1
    rw [hM]; linarith
  have hi := (continuous_re_stageSpeed X).intervalIntegrable (μ := volume) t₀ T
  have hlow := intervalIntegral.integral_mono_on (μ := volume) hT intervalIntegrable_const hi hge
  have hup := intervalIntegral.integral_mono_on (μ := volume) hT hi intervalIntegrable_const hle
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow hup
  constructor
  · exact Nat.succ_le_succ (Nat.floor_le_floor (div_le_div_of_nonneg_right
      (by rw [mul_comm]; exact hlow) Real.pi_pos.le))
  · exact Nat.succ_le_succ (Nat.floor_le_floor (div_le_div_of_nonneg_right
      (by rw [mul_comm M]; exact hup) Real.pi_pos.le))

end GaloisForLFunctions.ZeroConfigurationGeometry
