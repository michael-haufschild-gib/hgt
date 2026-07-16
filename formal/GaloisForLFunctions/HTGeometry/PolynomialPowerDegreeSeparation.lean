import GaloisForLFunctions.HTGeometry.PolynomialPowerConvexConfinement
import Mathlib.Analysis.MeanInequalities

open Filter Finset Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

lemma tendsto_natCast_add_div_natCast (c : ℕ) :
    Tendsto (fun q : ℕ => (((q + c : ℕ) : ℝ) / (q : ℝ))) atTop (𝓝 1) := by
  have hzero : Tendsto (fun q : ℕ => (c : ℝ) / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)
  have hone : Tendsto (fun _q : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim : Tendsto (fun q : ℕ => (1 : ℝ) + (c : ℝ) / (q : ℝ))
      atTop (𝓝 1) := by simpa using hone.add hzero
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  push_cast
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  field_simp

lemma tendsto_natCast_mul_sub_div_natCast (D J : ℕ) :
    Tendsto (fun q : ℕ => (((D * q - J : ℕ) : ℝ) / (q : ℝ))) atTop (𝓝 D) := by
  by_cases hD : D = 0
  · subst D
    simp
  have hzero : Tendsto (fun q : ℕ => (J : ℝ) / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (J : ℝ)
  have hlim : Tendsto (fun q : ℕ => (D : ℝ) - (J : ℝ) / (q : ℝ)) atTop (𝓝 D) := by
    simpa using tendsto_const_nhds.sub hzero
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (J + 1)] with q hq
  have hsub : J ≤ D * q := by
    have hDone : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD
    nlinarith
  rw [Nat.cast_sub hsub]
  push_cast
  by_cases hq0 : (q : ℝ) = 0
  · have hq0ne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact False.elim (hq0ne hq0)
  · field_simp

lemma tendsto_natCast_add_rpow_div_rpow {β : ℝ} (c : ℕ) :
    Tendsto (fun q : ℕ => (((q + c : ℕ) : ℝ) ^ β / (q : ℝ) ^ β))
      atTop (𝓝 1) := by
  have hbase := tendsto_natCast_add_div_natCast c
  have hrpow := (Real.continuousAt_rpow_const (1 : ℝ) β (Or.inl one_ne_zero)).tendsto.comp hbase
  have hrpow' : Tendsto ((fun x : ℝ => x ^ β) ∘
      fun q : ℕ => (((q + c : ℕ) : ℝ) / (q : ℝ))) atTop (𝓝 1) := by
    simpa using hrpow
  apply hrpow'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  change (((((q + c : ℕ) : ℝ) / (q : ℝ)) ^ β)) = _
  rw [Real.div_rpow (Nat.cast_nonneg (q + c)) (Nat.cast_nonneg q)]

lemma tendsto_natCast_mul_sub_rpow_div_rpow {β : ℝ} {D : ℕ} (hD : 0 < D) (J : ℕ) :
    Tendsto (fun q : ℕ => (((D * q - J : ℕ) : ℝ) ^ β / (q : ℝ) ^ β))
      atTop (𝓝 ((D : ℝ) ^ β)) := by
  have hbase := tendsto_natCast_mul_sub_div_natCast D J
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hrpow := (Real.continuousAt_rpow_const (D : ℝ) β (Or.inl hD0)).tendsto.comp hbase
  apply hrpow.congr'
  filter_upwards [eventually_ge_atTop (J + 1)] with q hq
  have hsub : J ≤ D * q := by nlinarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hnum0 : (0 : ℝ) ≤ D * q - J := by exact_mod_cast Nat.zero_le (D * q - J)
  change (((((D * q - J : ℕ) : ℝ) / (q : ℝ)) ^ β)) = _
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ (D * q - J : ℕ)) hq0]

lemma tendsto_tuplePowerValuation_div_rpow {β : ℝ} {D : ℕ} (δ : Fin D → ℕ) :
    Tendsto (fun q : ℕ =>
      tuplePowerValuation β (fun i => q + δ i) / (q : ℝ) ^ β)
      atTop (𝓝 D) := by
  have hsum : Tendsto (fun q : ℕ =>
      ∑ i : Fin D, (((q + δ i : ℕ) : ℝ) ^ β / (q : ℝ) ^ β))
      atTop (𝓝 (∑ _i : Fin D, (1 : ℝ))) :=
    tendsto_finsetSum Finset.univ fun i _ => tendsto_natCast_add_rpow_div_rpow (δ i)
  convert hsum using 1
  · funext q
    rw [tuplePowerValuation, Finset.sum_div]
  · simp

lemma tendsto_log_nat_add_two_div_rpow {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun q : ℕ => Real.log ((q : ℝ) + 2) / (q : ℝ) ^ β)
      atTop (𝓝 0) := by
  have hcoreReal := (isLittleO_log_rpow_atTop hβ).tendsto_div_nhds_zero
  have hcoreNat : Tendsto (fun q : ℕ => Real.log (q : ℝ) / (q : ℝ) ^ β)
      atTop (𝓝 0) := hcoreReal.comp tendsto_natCast_atTop_atTop
  have hbound := eventually_log_nat_add_const_le_two_mul_log_nat 0
  apply squeeze_zero'
    (f := fun q : ℕ => Real.log ((q : ℝ) + 2) / (q : ℝ) ^ β)
    (g := fun q : ℕ => 2 * (Real.log (q : ℝ) / (q : ℝ) ^ β))
  · filter_upwards [eventually_ge_atTop 1] with q hq
    exact div_nonneg (Real.log_nonneg (by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.zero_le q
      have : (1 : ℝ) ≤ (q : ℝ) + 2 := by linarith
      exact this)) (Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q) β)
  · filter_upwards [hbound, eventually_ge_atTop 1] with q hqlog hq
    have hden : 0 ≤ (q : ℝ) ^ β := Real.rpow_nonneg (by exact_mod_cast Nat.zero_le q) β
    have := div_le_div_of_nonneg_right hqlog hden
    simpa only [Nat.add_zero, mul_div_assoc] using this
  · simpa using hcoreNat.const_mul 2

lemma power_degree_gap_constant {β : ℝ} (hβ : 1 < β) {D : ℕ} (hD : 1 < D) :
    (D : ℝ) < (D : ℝ) ^ β / ((D - 1 : ℕ) : ℝ) ^ (β - 1) := by
  have hDm1pos : (0 : ℝ) < (D - 1 : ℕ) := by exact_mod_cast (show 0 < D - 1 by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hbase : ((D - 1 : ℕ) : ℝ) < (D : ℝ) := by exact_mod_cast (show D - 1 < D by omega)
  have hexp : 0 < β - 1 := sub_pos.mpr hβ
  have hpow := Real.rpow_lt_rpow hDm1pos.le hbase hexp
  have hdenpos : 0 < ((D - 1 : ℕ) : ℝ) ^ (β - 1) :=
    Real.rpow_pos_of_pos hDm1pos _
  have hratio : 1 < (D : ℝ) ^ (β - 1) / ((D - 1 : ℕ) : ℝ) ^ (β - 1) := by
    rw [lt_div_iff₀ hdenpos]
    simpa using hpow
  have hmul := mul_lt_mul_of_pos_left hratio hDpos
  calc
    (D : ℝ) = (D : ℝ) * 1 := by ring_nf
    _ < (D : ℝ) * ((D : ℝ) ^ (β - 1) /
        ((D - 1 : ℕ) : ℝ) ^ (β - 1)) := hmul
    _ = (D : ℝ) ^ β / ((D - 1 : ℕ) : ℝ) ^ (β - 1) := by
      rw [show β = (β - 1) + 1 by ring_nf, Real.rpow_add hDpos, Real.rpow_one]
      ring_nf

/-- Every positive lower-degree tuple with the source mass of a degree-`D` witness is separated
from that witness by more than any fixed logarithmic allowance. -/
theorem eventually_lowerDegree_tuplePower_gap {β : ℝ} (hβ : 1 < β)
    {D : ℕ} (hD : 0 < D) (δ : Fin D → ℕ) (J A : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ (d : ℕ), 0 < d → d < D → ∀ t : Fin d → ℕ,
      D * q ≤ (∑ i, t i) + J →
      tuplePowerValuation β (fun i => q + δ i) +
          (A : ℝ) * Real.log ((q : ℝ) + 2) <
        tuplePowerValuation β t := by
  by_cases hDone : D = 1
  · filter_upwards [] with q
    intro d hd hdD
    omega
  have hDtwo : 1 < D := by omega
  let den : ℝ := ((D - 1 : ℕ) : ℝ) ^ (β - 1)
  let cLow : ℝ := (D : ℝ) ^ β / den
  have hdenpos : 0 < den := by
    dsimp [den]
    exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < D - 1 by omega)) _
  have hcGap : (D : ℝ) < cLow := by
    simpa [cLow, den] using power_degree_gap_constant hβ hDtwo
  have hwitT := tendsto_tuplePowerValuation_div_rpow (β := β) δ
  have hlogT := (tendsto_log_nat_add_two_div_rpow (β := β) (by linarith)).const_mul (A : ℝ)
  have hupperT : Tendsto (fun q : ℕ =>
      (tuplePowerValuation β (fun i => q + δ i) +
        (A : ℝ) * Real.log ((q : ℝ) + 2)) / (q : ℝ) ^ β)
      atTop (𝓝 D) := by
    have hadd := hwitT.add hlogT
    convert hadd using 1
    · funext q
      ring_nf
    · simp
  have hnumT := tendsto_natCast_mul_sub_rpow_div_rpow (β := β) hD J
  have hlowerT : Tendsto (fun q : ℕ =>
      ((((D * q - J : ℕ) : ℝ) ^ β / (q : ℝ) ^ β) / den))
      atTop (𝓝 cLow) := by
    have h := hnumT.div_const den
    simpa [cLow] using h
  have hnormGap := Filter.Tendsto.eventually_lt hupperT hlowerT hcGap
  filter_upwards [hnormGap, eventually_ge_atTop (J + 1)] with q hgap hq
  intro d hd hdD t hsum
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqpow : 0 < (q : ℝ) ^ β := Real.rpow_pos_of_pos hqpos _
  have htargetLow :
      tuplePowerValuation β (fun i => q + δ i) +
          (A : ℝ) * Real.log ((q : ℝ) + 2) <
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
      tuplePowerValuation β t := (div_le_iff₀ hdenpos).2 (by simpa [mul_comm] using hnumLe)
  exact htargetLow.trans_le hdivLe

end

end GaloisForLFunctions
