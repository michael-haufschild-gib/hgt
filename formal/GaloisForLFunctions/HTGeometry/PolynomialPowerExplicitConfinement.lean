import GaloisForLFunctions.HTGeometry.PolynomialPhaseCluster
import GaloisForLFunctions.HTGeometry.PolynomialPowerDegreeSeparation

open Filter Finset Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

/-- A positive first or second moment produces the explicit `x^(β-2)` gap
needed by the phase-lock remainder estimate. -/
theorem eventually_const_mul_rpow_le_polynomialPowerFiniteDifference_of_pos
    {β : ℝ} (hβ : 2 < β) (d : ℕ →₀ ℝ) (j : ℕ) (hj : j ≤ 2)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : 0 < stretchedMoment d j) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - 2) ≤ polynomialPowerFiniteDifference β d x := by
  have hjcast : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have hjβ : (j : ℝ) < β := hjcast.trans_lt hβ
  have hpochPos : 0 < (descPochhammer ℝ j).eval β :=
    descPochhammer_eval_pos_of_natCast_lt hjβ
  let c₀ := polynomialPowerDifferenceCoefficient β d j
  have hc₀ : 0 < c₀ := by
    dsimp [c₀, polynomialPowerDifferenceCoefficient]
    exact div_pos (mul_pos hmoment hpochPos) (by positivity)
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d j hcancel
    hmoment.ne' hpochPos.ne'
  have hleadPos : ∀ᶠ x : ℝ in atTop, 0 < c₀ * x ^ (β - j) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc₀ (Real.rpow_pos_of_pos hx _)
  have hhalf := eventually_half_le_of_isEquivalent_positive hequiv hleadPos
  refine ⟨c₀ / 2, by positivity, ?_⟩
  filter_upwards [hhalf, eventually_ge_atTop (1 : ℝ)] with x hx hxone
  have hpow : x ^ (β - 2) ≤ x ^ (β - j) := by
    apply Real.rpow_le_rpow_of_exponent_le hxone
    exact sub_le_sub_left hjcast β
  have hmul : (c₀ / 2) * x ^ (β - 2) ≤
      (c₀ / 2) * x ^ (β - j) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hmul.trans (by convert! hx using 1 <;> ring)

/-- Every boundary-shell competitor has an explicit positive-power gap. -/
theorem boundaryOffsetCandidate_eventually_const_mul_rpow_power_gap
    {β : ℝ} (hβ : 2 < β) {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2)
    (u : Fin D → Fin (2 * L + 1)) (hu : boundaryOffsetCandidate δ u) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - 2) ≤
        polynomialPowerFiniteDifference β
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  let d := tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)
  have hm0 : stretchedMoment d 0 = 0 := by
    dsimp [d]
    rw [stretchedMoment_tupleDifference]
    simp
  have hm1nn : 0 ≤ stretchedMoment d 1 := by
    dsimp [d]
    exact boundaryOffsetCandidate_moment_one_nonneg δ u hu
  rcases hm1nn.eq_or_lt with hm1 | hm1
  · have hm2 : 0 < stretchedMoment d 2 := by
      dsimp [d]
      exact boundaryOffsetCandidate_moment_two_pos_of_moment_one_zero
        δ u hu hLsq (by simpa [d] using hm1.symm)
    simpa [d] using
      eventually_const_mul_rpow_le_polynomialPowerFiniteDifference_of_pos
        hβ d 2 (by omega)
          (by
            intro k hk
            interval_cases k
            · exact hm0
            · exact hm1.symm) hm2
  · simpa [d] using
      eventually_const_mul_rpow_le_polynomialPowerFiniteDifference_of_pos
        hβ d 1 (by omega) (by intro k hk; interval_cases k; exact hm0) hm1

/-- The finitely many boundary-shell candidates admit one common gap
coefficient. -/
theorem boundaryOffsetCandidate_eventually_all_const_mul_rpow_power_gap
    {β : ℝ} (hβ : 2 < β) {D L : ℕ} (δ : Fin D → ℕ)
    (hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      ∀ u : Fin D → Fin (2 * L + 1), boundaryOffsetCandidate δ u →
        c * x ^ (β - 2) ≤
          polynomialPowerFiniteDifference β
            (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
  classical
  let T : Finset (Fin D → Fin (2 * L + 1)) :=
    Finset.univ.filter (boundaryOffsetCandidate δ)
  have hgap : ∀ u ∈ T, ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - 2) ≤
        polynomialPowerFiniteDifference β
          (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x := by
    intro u hu
    exact boundaryOffsetCandidate_eventually_const_mul_rpow_power_gap
      hβ δ hLsq u (Finset.mem_filter.mp hu).2
  obtain ⟨c, hc, hall⟩ := exists_uniform_eventually_finset_rpow_gap T (β - 2)
    (fun u x => polynomialPowerFiniteDifference β
      (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L)) x) hgap
  refine ⟨c, hc, hall.mono fun x hx u hu => ?_⟩
  exact hx u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)

/-- A fixed left translation of the balanced parameter retains a uniform
positive multiple of the same real power. -/
theorem exists_eventually_const_mul_natCast_rpow_le_sub_rpow
    {η c : ℝ} (hη : 0 < η) (hc : 0 < c) (L : ℕ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ q : ℕ in atTop,
      c' * (q : ℝ) ^ η ≤ c * ((q : ℝ) - L) ^ η := by
  let c' := c / (2 : ℝ) ^ η
  have hc' : 0 < c' := div_pos hc (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c', hc', ?_⟩
  filter_upwards [eventually_ge_atTop (max (2 * L) 1)] with q hq
  have hqone : 1 ≤ q := (le_max_right _ _).trans hq
  have hqL : 2 * L ≤ q := (le_max_left _ _).trans hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hbase0 : 0 ≤ (q : ℝ) / 2 := by positivity
  have hbase : (q : ℝ) / 2 ≤ (q : ℝ) - L := by
    have hqLreal : (2 : ℝ) * (L : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hqL
    linarith
  have hp := Real.rpow_le_rpow hbase0 hbase hη.le
  have hdiv : ((q : ℝ) / 2) ^ η = (q : ℝ) ^ η / (2 : ℝ) ^ η := by
    rw [Real.div_rpow hq0 (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    c' * (q : ℝ) ^ η = c * ((q : ℝ) ^ η / (2 : ℝ) ^ η) := by
      dsimp [c']
      ring
    _ = c * ((q : ℝ) / 2) ^ η := by rw [hdiv]
    _ ≤ c * ((q : ℝ) - L) ^ η :=
      mul_le_mul_of_nonneg_left hp hc.le

/-- Explicit polynomial confinement: every tuple outside one fixed coordinate
window lies at least `c*q^(β-2)` above a fixed-offset witness. -/
theorem exists_eventually_bounded_powerGap {β : ℝ} (hβ : 2 < β)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (C : ℕ) :
    ∃ (K : ℕ) (c : ℝ), 0 < c ∧ ∀ᶠ q : ℕ in atTop,
      ∀ s : Fin D → ℕ,
        (D * q + (∑ i, δ i) ≤ ∑ i, s i ∧
          (∑ i, s i) ≤ D * q + (∑ i, δ i) + C) →
        ¬ tupleInWindow q K s →
        tuplePowerValuation β (fun i => q + δ i) + c * (q : ℝ) ^ (β - 2) ≤
          tuplePowerValuation β s := by
  classical
  let Aδ := ∑ i, δ i
  let Sδ := ∑ i, (δ i) ^ 2
  let K := C + Aδ + Sδ + 1
  let L := K + 1
  have hCtotK : Aδ + C < K := by dsimp [K]; omega
  have hSltL : Sδ < L := by dsimp [L, K]; omega
  have hLpos : 0 < L := by dsimp [L, K]; omega
  have hLleSq : L ≤ L ^ 2 := by nlinarith
  have hSltLsq : Sδ < L ^ 2 := hSltL.trans_le hLleSq
  have hLsq : (∑ i, (δ i : ℝ) ^ 2) < (L : ℝ) ^ 2 := by
    have hcast : (Sδ : ℝ) < (L : ℝ) ^ 2 := by exact_mod_cast hSltLsq
    simpa [Sδ] using hcast
  obtain ⟨c₀, hc₀, hgapReal⟩ :=
    boundaryOffsetCandidate_eventually_all_const_mul_rpow_power_gap hβ δ hLsq
  have hbaseT : Tendsto (fun q : ℕ => (q : ℝ) - L) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(L : ℝ)) tendsto_natCast_atTop_atTop
  have hgapNat : ∀ᶠ q : ℕ in atTop, ∀ u : Fin D → Fin (2 * L + 1),
      boundaryOffsetCandidate δ u →
        c₀ * ((q : ℝ) - L) ^ (β - 2) ≤
          polynomialPowerFiniteDifference β
            (tupleDifference (fun i => (u i : ℕ)) (fun i => δ i + L))
            ((q : ℝ) - L) := hbaseT.eventually hgapReal
  have heta : 0 < β - 2 := sub_pos.mpr hβ
  obtain ⟨c, hc, hshift⟩ :=
    exists_eventually_const_mul_natCast_rpow_le_sub_rpow heta hc₀ L
  refine ⟨K, c, hc, ?_⟩
  filter_upwards [hgapNat, hshift,
    eventually_ge_atTop (max (2 * L + 4) 2)] with q hgap hshiftq hq
  intro s hsBounds hout
  have hLq : L ≤ q := by omega
  have hsumLower0 : D * q ≤ ∑ i, s i := by
    exact (Nat.le_add_right _ Aδ).trans (by simpa [Aδ] using hsBounds.1)
  have hsumUpper0 : (∑ i, s i) ≤ D * q + (Aδ + C) := by
    simpa [Aδ, Nat.add_assoc] using hsBounds.2
  obtain ⟨t, htsum, htwide, htout, htval⟩ :=
    exists_boundaryShell_of_power_sum_bounds (by linarith : 1 < β) hD hCtotK s
      hsumLower0 hsumUpper0 hout
  have htsumLower : D * q + (∑ i, δ i) ≤ ∑ i, t i := by
    rw [htsum]
    exact hsBounds.1
  have hcand := shellOffset_boundaryCandidate δ t hLq htwide htout htsumLower
  have hgap' := hgap (shellOffset t hLq htwide) hcand
  rw [polynomialPowerFiniteDifference_shellOffset_eq δ t hLq htwide] at hgap'
  have hmain : tuplePowerValuation β (fun i => q + δ i) +
      c * (q : ℝ) ^ (β - 2) ≤ tuplePowerValuation β t := by
    linarith
  exact hmain.trans htval

/-- Positive lower-degree atoms are separated from a degree-`D` balanced
witness by a fixed positive multiple of `q^β`. -/
theorem eventually_lowerDegree_tuplePower_rpow_gap {β : ℝ} (hβ : 1 < β)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (J : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ q : ℕ in atTop,
      ∀ (d : ℕ), 0 < d → d < D → ∀ t : Fin d → ℕ,
        D * q ≤ (∑ i, t i) + J →
        tuplePowerValuation β (fun i => q + δ i) + c * (q : ℝ) ^ β ≤
          tuplePowerValuation β t := by
  by_cases hDone : D = 1
  · refine ⟨1, one_pos, Eventually.of_forall fun q d hd hdD => ?_⟩
    omega
  have hDtwo : 1 < D := by omega
  let den : ℝ := ((D - 1 : ℕ) : ℝ) ^ (β - 1)
  let cLow : ℝ := (D : ℝ) ^ β / den
  let c : ℝ := (cLow - D) / 2
  have hdenpos : 0 < den := by
    dsimp [den]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < D - 1 by omega)) _
  have hcGap : (D : ℝ) < cLow := by
    simpa [cLow, den] using power_degree_gap_constant hβ hDtwo
  have hc : 0 < c := by dsimp [c]; linarith
  have hwitT := tendsto_tuplePowerValuation_div_rpow (β := β) δ
  have hnumT := tendsto_natCast_mul_sub_rpow_div_rpow (β := β) hD J
  have hlowerT : Tendsto (fun q : ℕ =>
      ((((D * q - J : ℕ) : ℝ) ^ β / (q : ℝ) ^ β) / den))
      atTop (𝓝 cLow) := by
    have h := hnumT.div_const den
    simpa [cLow] using h
  have hupperT : Tendsto (fun q : ℕ =>
      tuplePowerValuation β (fun i => q + δ i) / (q : ℝ) ^ β + c)
      atTop (𝓝 ((D : ℝ) + c)) := by
    simpa using hwitT.add_const c
  have hlimitGap : (D : ℝ) + c < cLow := by dsimp [c]; linarith
  have hnormGap := Filter.Tendsto.eventually_lt hupperT hlowerT hlimitGap
  refine ⟨c, hc, ?_⟩
  filter_upwards [hnormGap, eventually_ge_atTop (J + 1)] with q hgap hq
  intro d hd hdD t hsum
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : 0 < (q : ℝ) ^ β := Real.rpow_pos_of_pos hqpos _
  have htargetLow :
      tuplePowerValuation β (fun i => q + δ i) + c * (q : ℝ) ^ β <
        ((D * q - J : ℕ) : ℝ) ^ β / den := by
    have hmul := mul_lt_mul_of_pos_right hgap hqpow
    field_simp [hqpow.ne', hdenpos.ne'] at hmul ⊢
    nlinarith
  have hsub : D * q - J ≤ ∑ i, t i := by omega
  have hsumCast : (((D * q - J : ℕ) : ℝ)) ≤ ∑ i, (t i : ℝ) := by
    exact_mod_cast hsub
  have hpowSum : (((D * q - J : ℕ) : ℝ)) ^ β ≤
      (∑ i, (t i : ℝ)) ^ β :=
    Real.rpow_le_rpow (by positivity) hsumCast (by linarith)
  have hmean := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset (Fin d))) (f := fun i => (t i : ℝ)) hβ.le
    (fun i _ => Nat.cast_nonneg (t i))
  have hmean' : (∑ i, (t i : ℝ)) ^ β ≤
      (d : ℝ) ^ (β - 1) * tuplePowerValuation β t := by
    simpa [tuplePowerValuation] using hmean
  have hdle : d ≤ D - 1 := by omega
  have hdpow : (d : ℝ) ^ (β - 1) ≤ den := by
    dsimp [den]
    apply Real.rpow_le_rpow (by positivity)
    · exact_mod_cast hdle
    · linarith
  have hval0 : 0 ≤ tuplePowerValuation β t := by
    apply Finset.sum_nonneg
    intro i _
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnumLe : (((D * q - J : ℕ) : ℝ)) ^ β ≤
      den * tuplePowerValuation β t := by
    exact hpowSum.trans (hmean'.trans (mul_le_mul_of_nonneg_right hdpow hval0))
  have hdivLe : (((D * q - J : ℕ) : ℝ)) ^ β / den ≤
      tuplePowerValuation β t :=
    (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hnumLe)
  exact htargetLow.le.trans hdivLe

end

end GaloisForLFunctions
