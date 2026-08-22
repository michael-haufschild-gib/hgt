/-
# The fidelity recurrence exponent is half the winding exponent

Reading a first return in fidelity rather than in phase squares the radius, so it halves the
logarithmic first-return exponent.  The upper half of the exponent comes from the winding clock: a
first winding return of radius `sqrt δ / (4 π)` is realised at a time whose fidelity deficit is
below `δ`.  The lower half comes from extremality: past the winding threshold every fidelity return
supplies a continuous phase return, and the deficit is bounded away from zero before that
threshold, so no earlier return exists.

Main results:
* `eventually_fidelityReturnTime_le` — **the winding upper bound**.
* `eventually_le_fidelityReturnTime` — **the extremality lower bound**.
* `tendsto_log_sqrt_ratio` — the logarithmic radius of the winding clock is half.
* `tendsto_log_fidelityReturnTime` — **the fidelity recurrence exponent**.
-/
import GaloisForLFunctions.HTGeometry.FidelityReturnTime

open Filter Topology Real
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedVariables false

noncomputable section

variable {e : ℕ}

theorem tendsto_const_mul_sqrt_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => a * Real.sqrt δ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun δ : ℝ => a * Real.sqrt δ) (𝓝 (0 : ℝ)) (𝓝 (a * Real.sqrt 0)) :=
      (continuous_const.mul Real.continuous_sqrt).tendsto 0
    rw [Real.sqrt_zero, mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_pos ha (Real.sqrt_pos.mpr hδ)

/-- **A winding return is available at every small fidelity radius.**  The first fidelity return
after the cutoff happens no later than the clock time of the first winding return of radius
`sqrt δ / (4 π)`. -/
theorem eventually_fidelityReturnTime_le (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) (hg0 : 0 < E 1 - E 0)
    (hnv : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)))
    (t₀ : ℝ) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (fidelityReturnSet E p t₀ δ).Nonempty ∧
        fidelityReturnTime E p t₀ δ
          ≤ 2 * π * ((firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
              (1 / (4 * π) * Real.sqrt δ) : ℕ) : ℝ) / (E 1 - E 0) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hsq := tendsto_const_mul_sqrt_nhdsGT (a := 1 / (4 * π)) (by positivity)
  have hbig : Tendsto (fun δ : ℝ =>
      (firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
        (1 / (4 * π) * Real.sqrt δ) : ℕ)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_firstHit_atTop hnv).comp hsq
  filter_upwards [self_mem_nhdsWithin,
    hbig.eventually_ge_atTop ⌈t₀ * (E 1 - E 0) / (2 * π)⌉₊] with δ hδ hq
  have hδ' : (0 : ℝ) < δ := hδ
  set r : ℝ := 1 / (4 * π) * Real.sqrt δ with hr
  have hrpos : 0 < r := by
    rw [hr]
    exact mul_pos (by positivity) (Real.sqrt_pos.mpr hδ')
  set q : ℕ := firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)) r with hqdef
  have hq1 : 1 ≤ q := one_le_firstHit _ hrpos
  have hmem := (firstHit_mem (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)) hrpos).2
  have hδ8 : 8 * π ^ 2 * r ^ 2 < δ := by
    have hsqrt : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ'.le
    rw [hr, mul_pow, hsqrt]
    have : 8 * π ^ 2 * ((1 / (4 * π)) ^ 2 * δ) = δ / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  have ht₀le : t₀ ≤ 2 * π * (q : ℝ) / (E 1 - E 0) := by
    have hceil : t₀ * (E 1 - E 0) / (2 * π) ≤ (⌈t₀ * (E 1 - E 0) / (2 * π)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hqR : ((⌈t₀ * (E 1 - E 0) / (2 * π)⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [le_div_iff₀ hg0]
    have h1 : t₀ * (E 1 - E 0) / (2 * π) ≤ (q : ℝ) := le_trans hceil hqR
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  exact fidelityReturnTime_le_of_windingReturn E p hp1 hpnn hg0 hrpos hδ8 hq1 hmem ht₀le

/-- **No fidelity return before the winding threshold.**  For a non-approximable projective gap
spectrum the first fidelity return after a positive cutoff is at least a fixed multiple of
`(1/δ)^{β/2}`, where `β` is the continuous winding exponent spoiled by `η`. -/
theorem eventually_le_fidelityReturnTime (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j) {c : ℝ} (hc : 0 < c) (hcp : ∀ j, c ≤ p j)
    (hg0 : 0 < E 1 - E 0)
    (hnv : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      C * (1 / δ) ^ (1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2)
        ≤ fidelityReturnTime E p t₀ δ := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpnn : ∀ j, 0 ≤ p j := fun j => (hppos j).le
  have hg0' : anchoredGapPacket E 0 ≠ 0 := by
    rw [anchoredGapPacket_zero]
    exact hg0.ne'
  have hAnn : (0 : ℝ) ≤ ∑ i, |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hA : ∀ j, |gapRatio (anchoredGapPacket E) j|
      ≤ 1 + ∑ i, |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i| := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [gapRatio_zero (anchoredGapPacket E) hg0', abs_one]
      linarith
    · rw [gapRatio_anchoredGapPacket_succ]
      have hsingle : |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i|
          ≤ ∑ k, |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) k| :=
        Finset.single_le_sum
          (f := fun k => |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) k|)
          (fun k _ => abs_nonneg _) (Finset.mem_univ i)
      linarith
  have hyg : ¬ KleinbockMargulis.VWA
      (fun i : Fin (e + 1) => gapRatio (anchoredGapPacket E) i.succ) := by
    simpa only [gapRatio_anchoredGapPacket_succ] using hnv
  obtain ⟨Q, hQ⟩ := KleinbockMargulis.eventually_continuousReturn_lower_of_not_vwa
    (d := e + 1) (by omega) (anchoredGapPacket E) hg0' hA hyg hη
  set bexp : ℝ := 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) with hbexp
  have hbpos : 0 < bexp := by
    rw [hbexp]
    positivity
  set T : ℝ := 2 * π * ((Q : ℝ) + 1) / (E 1 - E 0) with hT
  obtain ⟨m, hmpos, hmle⟩ := exists_pos_le_spectralReturnDeficit_on_Icc E p hp1 hppos hg0 hnv
    (t₀ := t₀) (T := T) ht₀
  set A : ℝ := 1 + ∑ i, |anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i| with hAdef
  have hApos : 0 < 1 + A := by
    rw [hAdef]
    linarith
  set K : ℝ := (1 + A) / (2 * c) with hK
  have hKpos : 0 < K := by
    rw [hK]
    positivity
  refine ⟨π / (E 1 - E 0) * K ^ (-bexp), by positivity, ?_⟩
  have hXtop : Tendsto (fun δ : ℝ => K ^ (-bexp) * (1 / δ) ^ (bexp / 2))
      (𝓝[>] (0 : ℝ)) atTop := by
    have h1 : Tendsto (fun δ : ℝ => 1 / δ) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [one_div] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    exact Filter.Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop (by positivity)).comp h1)
  have hsmall : Tendsto (fun δ : ℝ => Real.sqrt δ / (2 * c)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ => Real.sqrt δ / (2 * c)) (𝓝 (0 : ℝ))
        (𝓝 (Real.sqrt 0 / (2 * c))) :=
      (Real.continuous_sqrt.div_const _).tendsto 0
    rw [Real.sqrt_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT hmpos,
    eventually_fidelityReturnTime_le E p hp1 hpnn hg0 hnv t₀,
    hXtop.eventually_ge_atTop 2,
    hsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with δ hδm hne hX2 hr1
  obtain ⟨hδ0, hδm⟩ := hδm
  refine le_csInf hne.1 ?_
  intro t ht
  have hr'pos : 0 < Real.sqrt δ / (2 * c) := by positivity
  have hTpos : 0 < T := by
    rw [hT]
    have : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
    positivity
  have htT : T < t := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : t ∈ Set.Icc t₀ T := ⟨ht.1, hcon⟩
    linarith [hmle t hmem, ht.2, hδm]
  have htpos : 0 < t := lt_trans hTpos htT
  have hturnpos : 0 < gapTurn (anchoredGapPacket E) t 0 := by
    rw [gapTurn, anchoredGapPacket_zero]
    positivity
  have hQle : (Q : ℝ) + Real.sqrt δ / (2 * c) ≤ |gapTurn (anchoredGapPacket E) t 0| := by
    rw [abs_of_pos hturnpos, gapTurn, anchoredGapPacket_zero]
    have hTt : 2 * π * ((Q : ℝ) + 1) / (E 1 - E 0) < t := by rw [← hT]; exact htT
    rw [div_lt_iff₀ hg0] at hTt
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [hTt, hr1, hpi]
  have hcont := continuousReturn_of_mem_fidelityReturnSet E p hp1 hpnn hc hcp ht
  have hlow := hQ hQle hcont
  rw [abs_of_pos htpos, anchoredGapPacket_zero, abs_of_pos hg0] at hlow
  have hrA : Real.sqrt δ / (2 * c) * (1 + A) = K * Real.sqrt δ := by
    rw [hK]
    field_simp
  have hsqrtrpow : (Real.sqrt δ) ^ (-bexp) = (1 / δ) ^ (bexp / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ0.le, one_div δ, Real.inv_rpow hδ0.le,
      ← Real.rpow_neg hδ0.le]
    congr 1
    ring
  have hXeq : (Real.sqrt δ / (2 * c) * (1 + A)) ^ (-bexp)
      = K ^ (-bexp) * (1 / δ) ^ (bexp / 2) := by
    rw [hrA, Real.mul_rpow hKpos.le (Real.sqrt_nonneg δ), hsqrtrpow]
  rw [hXeq] at hlow
  have hkey : K ^ (-bexp) * (1 / δ) ^ (bexp / 2) / 2 ≤ t * (E 1 - E 0) / (2 * π) := by
    linarith [hlow, hX2, hr1]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)] at hkey
  rw [mul_assoc, div_mul_eq_mul_div, div_le_iff₀ hg0]
  nlinarith [hkey, hpi]

/-! ## The exponent -/

theorem tendsto_log_one_div_nhdsGT : Tendsto (fun δ : ℝ => Real.log (1 / δ))
    (𝓝[>] (0 : ℝ)) atTop := tendsto_log_one_div

theorem tendsto_const_div_log_one_div (k : ℝ) :
    Tendsto (fun δ : ℝ => k / Real.log (1 / δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_log_one_div_nhdsGT

/-- The logarithmic radius of the winding clock is half the logarithmic fidelity radius. -/
theorem tendsto_log_sqrt_ratio {a : ℝ} (ha : 0 < a) :
    Tendsto (fun δ : ℝ => Real.log (1 / (a * Real.sqrt δ)) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
  have hlim : Tendsto (fun δ : ℝ => (-Real.log a) / Real.log (1 / δ) + 1 / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 2)) := by
    have := (tendsto_const_div_log_one_div (-Real.log a)).add
      (tendsto_const_nhds (x := (1 / 2 : ℝ)) (f := 𝓝[>] (0 : ℝ)))
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ hδ1
  have hδ0 : (0 : ℝ) < δ := hδ
  have hlogpos : 0 < Real.log (1 / δ) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hδ0]
    linarith [hδ1.2]
  have hsq : Real.log (1 / (a * Real.sqrt δ))
      = -Real.log a + 1 / 2 * Real.log (1 / δ) := by
    rw [one_div (a * Real.sqrt δ), Real.log_inv, Real.log_mul ha.ne' (by positivity),
      Real.log_sqrt hδ0.le, one_div δ, Real.log_inv]
    ring
  rw [hsq, add_div]
  congr 1
  rw [mul_div_assoc, div_self hlogpos.ne', mul_one]

/-- **The fidelity recurrence exponent.**  For a weighted spectral packet with strictly positive
weights and a non-approximable projective gap spectrum, the first fidelity return after a positive
cutoff has logarithmic exponent exactly half the winding exponent. -/
theorem tendsto_log_fidelityReturnTime (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j) {c : ℝ} (hc : 0 < c) (hcp : ∀ j, c ≤ p j)
    (hg0 : 0 < E 1 - E 0)
    (hnv : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)))
    {t₀ : ℝ} (ht₀ : 0 < t₀) :
    Tendsto (fun δ : ℝ => Real.log (fidelityReturnTime E p t₀ δ) / Real.log (1 / δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hpnn : ∀ j, 0 ≤ p j := fun j => (hppos j).le
  have hapos : (0 : ℝ) < 1 / (4 * π) := by positivity
  have hΛ : (0 : ℝ) < ((e + 1 : ℕ) : ℝ) := by positivity
  have hupperEv := eventually_fidelityReturnTime_le E p hp1 hpnn hg0 hnv t₀
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower half
    intro b hb
    have hcontη : Tendsto (fun η : ℝ => 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
      have hden : Tendsto (fun η : ℝ => (((e + 1 : ℕ) : ℝ))⁻¹ + η) (𝓝 (0 : ℝ))
          (𝓝 ((((e + 1 : ℕ) : ℝ))⁻¹)) := by
        simpa using (tendsto_const_nhds (x := (((e + 1 : ℕ) : ℝ))⁻¹)
          (f := 𝓝 (0 : ℝ))).add tendsto_id
      have hfull : Tendsto (fun η : ℝ => 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2) (𝓝 (0 : ℝ))
          (𝓝 (1 / ((((e + 1 : ℕ) : ℝ))⁻¹) / 2)) :=
        ((tendsto_const_nhds.div hden (by positivity)).div_const 2)
      rw [one_div, inv_inv] at hfull
      exact hfull.mono_left nhdsWithin_le_nhds
    obtain ⟨η, hηlt, hηpos⟩ :=
      ((hcontη.eventually_const_lt hb).and self_mem_nhdsWithin).exists
    obtain ⟨C, hCpos, hCev⟩ :=
      eventually_le_fidelityReturnTime E p hp1 hppos hc hcp hg0 hnv ht₀ hηpos
    have hlim : Tendsto (fun δ : ℝ => Real.log C / Real.log (1 / δ)
        + 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2) (𝓝[>] (0 : ℝ))
        (𝓝 (1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2)) := by
      have := (tendsto_const_div_log_one_div (Real.log C)).add
        (tendsto_const_nhds (x := 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2) (f := 𝓝[>] (0 : ℝ)))
      simpa using this
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ), hCev, hupperEv,
      hlim.eventually_const_lt hηlt] with δ hδ hδ1 hCδ hne hlt
    have hδ0 : (0 : ℝ) < δ := hδ
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ0]
      linarith [hδ1.2]
    have hpow : (0 : ℝ) < C * (1 / δ) ^ (1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2) := by
      have : (0 : ℝ) < (1 : ℝ) / δ := by positivity
      positivity
    have hlogle : Real.log (C * (1 / δ) ^ (1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2))
        ≤ Real.log (fidelityReturnTime E p t₀ δ) := Real.log_le_log hpow hCδ
    have hlogeq : Real.log (C * (1 / δ) ^ (1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2))
        = Real.log C + 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2 * Real.log (1 / δ) := by
      rw [Real.log_mul hCpos.ne' (by positivity), Real.log_rpow (by positivity)]
    rw [hlogeq] at hlogle
    rw [lt_div_iff₀ hlogpos]
    have hexp : Real.log C + 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2 * Real.log (1 / δ)
        = (Real.log C / Real.log (1 / δ)
            + 1 / ((((e + 1 : ℕ) : ℝ))⁻¹ + η) / 2) * Real.log (1 / δ) := by
      field_simp
    rw [hexp] at hlogle
    nlinarith [hlogle, hlt, hlogpos]
  · -- upper half
    intro b hb
    have hsq := tendsto_const_mul_sqrt_nhdsGT (a := 1 / (4 * π)) hapos
    have hfirst : Tendsto (fun δ : ℝ =>
        Real.log ((firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
            (1 / (4 * π) * Real.sqrt δ) : ℕ) : ℝ)
          / Real.log (1 / (1 / (4 * π) * Real.sqrt δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ))) :=
      (tendsto_log_firstHit_div_log (m := e + 1) (by omega) hnv).comp hsq
    have hratio := tendsto_log_sqrt_ratio hapos
    have hprod : Tendsto (fun δ : ℝ =>
        Real.log (2 * π / (E 1 - E 0)) / Real.log (1 / δ)
          + (Real.log ((firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
              (1 / (4 * π) * Real.sqrt δ) : ℕ) : ℝ)
              / Real.log (1 / (1 / (4 * π) * Real.sqrt δ)))
            * (Real.log (1 / (1 / (4 * π) * Real.sqrt δ)) / Real.log (1 / δ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (((e + 1 : ℕ) : ℝ) / 2)) := by
      have := (tendsto_const_div_log_one_div (Real.log (2 * π / (E 1 - E 0)))).add
        (hfirst.mul hratio)
      have heq : (0 : ℝ) + ((e + 1 : ℕ) : ℝ) * (1 / 2) = ((e + 1 : ℕ) : ℝ) / 2 := by ring
      rw [heq] at this
      exact this
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ), hupperEv,
      hprod.eventually_lt_const hb,
      hsq.eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with δ hδ hδ1 hne hlt hr1
    have hδ0 : (0 : ℝ) < δ := hδ
    have hlogpos : 0 < Real.log (1 / δ) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hδ0]
      linarith [hδ1.2]
    set F : ℕ := firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
      (1 / (4 * π) * Real.sqrt δ) with hF
    have hrpos : 0 < 1 / (4 * π) * Real.sqrt δ := hr1.1
    have hF1 : 1 ≤ F := one_le_firstHit _ hrpos
    have hFpos : (0 : ℝ) < (F : ℝ) := by exact_mod_cast hF1
    have hTpos : 0 < fidelityReturnTime E p t₀ δ :=
      lt_of_lt_of_le ht₀ (le_fidelityReturnTime hne.1)
    have hle : fidelityReturnTime E p t₀ δ ≤ 2 * π / (E 1 - E 0) * (F : ℝ) := by
      have := hne.2
      rw [hF] at this ⊢
      calc fidelityReturnTime E p t₀ δ
          ≤ 2 * π * ((firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
              (1 / (4 * π) * Real.sqrt δ) : ℕ) : ℝ) / (E 1 - E 0) := this
        _ = 2 * π / (E 1 - E 0) * ((firstHit (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ))
              (1 / (4 * π) * Real.sqrt δ) : ℕ) : ℝ) := by ring
    have hlogle : Real.log (fidelityReturnTime E p t₀ δ)
        ≤ Real.log (2 * π / (E 1 - E 0)) + Real.log (F : ℝ) := by
      have hcpos : (0 : ℝ) < 2 * π / (E 1 - E 0) := by positivity
      calc Real.log (fidelityReturnTime E p t₀ δ)
          ≤ Real.log (2 * π / (E 1 - E 0) * (F : ℝ)) := Real.log_le_log hTpos hle
        _ = Real.log (2 * π / (E 1 - E 0)) + Real.log (F : ℝ) :=
            Real.log_mul hcpos.ne' hFpos.ne'
    have hlogrpos : 0 < Real.log (1 / (1 / (4 * π) * Real.sqrt δ)) := by
      refine Real.log_pos ?_
      rw [lt_div_iff₀ hrpos]
      linarith [hr1.2]
    set L1 : ℝ := Real.log (1 / (1 / (4 * π) * Real.sqrt δ)) with hL1
    set L2 : ℝ := Real.log (1 / δ) with hL2
    have hL1ne : L1 ≠ 0 := hlogrpos.ne'
    have hL2ne : L2 ≠ 0 := hlogpos.ne'
    have hsplit : Real.log (F : ℝ) / L1 * (L1 / L2) = Real.log (F : ℝ) / L2 := by
      field_simp
    rw [hsplit] at hlt
    have hsum : (Real.log (2 * π / (E 1 - E 0)) + Real.log (F : ℝ)) / L2 < b := by
      rw [add_div]
      exact hlt
    rw [div_lt_iff₀ hlogpos] at hsum
    rw [div_lt_iff₀ hlogpos]
    linarith [hlogle, hsum]

end

end GaloisForLFunctions.HTGeometry
