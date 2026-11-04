import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeIntermediateDomination

/-!
# Vanishing complete energy between the logarithmic and polynomial cutoffs

The reciprocal-prime coefficient mass absorbs one cutoff logarithm.
Every remaining quadratic correction is multiplied by a subcritical
overlap power or a negative horizon power. The polar near-Gram term
vanishes through the exact harmonic-centering coefficient.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory

/-- No complete physical energy survives in the intermediate cutoff range. -/
theorem tendsto_harmonicPrimeCharge_energy_intermediate {ι : Type*} {l : Filter ι}
    {Q N : ι → ℕ} (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop)
    (hfar : ∀ᶠ i in l, Q i ^ 64 ≤ N i)
    (hlarge : ∀ᶠ i in l, Real.log (N i) ≤ (Q i : ℝ) ^ 32)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun i => completeWeilEnergy φ (2 * K * Real.log (N i) ^ (1 / 8 : ℝ))
      (N i) (harmonicPrimeChargeVector (Q i) (N i) t)) l (𝓝 0) := by
  obtain ⟨A, B, D, hA, hB, hD, hb⟩ := exists_harmonicPrimeCharge_quadratic_error_bound hφ hsupp hM
  let H := 5 + |Real.log (2 * K)|
  let C := 36 * (152 * (∫ v, |φ v|) ^ 2 / (∫ v, φ v ^ 2))
  let c := fun n : ℕ => 2 * K * Real.log n ^ (1 / 8 : ℝ)
  let P := fun i => (|t| + 8 * |t| / primePoleScale (Q i)) / Real.log (N i)
  let V := fun q : ℕ => (t / primePoleScale q) ^ 2 *
    ∑ p ∈ (Icc 1 q).filter Nat.Prime, 1 / (p : ℝ)
  let W := fun q : ℕ => (1 + Real.log q) * V q
  let R := fun n : ℕ =>
    52 * (D + H + 600 * (c n / Real.log n) + 2 * B * (c n ^ 3 / Real.log n)) +
      (3 / 2 : ℝ) * A * H
  let S := fun n : ℕ => 52 * (C * (c n ^ 2 / Real.log n) +
    A * (Real.sqrt (c n ^ 5 / Real.log n) + Real.log n * c n ^ 5 / n +
      c n ^ 3 / (n : ℝ) ^ (1 / 2 : ℝ)) +
    2 * B * Real.sqrt (Real.log n * c n ^ 4 / (n : ℝ) ^ (1 / 2 : ℝ)))
  have hR : Tendsto R atTop (𝓝 (52 * (D + H) + (3 / 2 : ℝ) * A * H)) := by
    have h1 := (tendsto_primeCharge_critical_power_div_log K (by omega : 1 < 8)).const_mul 600
    have h3 := (tendsto_primeCharge_critical_power_div_log K (by omega : 3 < 8)).const_mul (2 * B)
    have h := ((((tendsto_const_nhds (x := D + H)).add h1).add h3).const_mul 52).add_const
      ((3 / 2 : ℝ) * A * H)
    simpa only [R, c, pow_one, mul_zero, add_zero] using h
  have hS : Tendsto S atTop (𝓝 0) := by
    have h2 := (tendsto_primeCharge_critical_power_div_log K (by omega : 2 < 8)).const_mul C
    have h5 := (tendsto_primeCharge_critical_power_div_log K (by omega : 5 < 8)).sqrt
    have h5N := tendsto_receiving_log_mul_critical_power_div_nat_rpow K 1 5
      (by norm_num : (0 : ℝ) < 1)
    have h3N := tendsto_receiving_log_mul_critical_power_div_nat_rpow K 0 3
      (by norm_num : (0 : ℝ) < 1 / 2)
    have h4N := (tendsto_receiving_log_mul_critical_power_div_nat_rpow K 1 4
      (by norm_num : (0 : ℝ) < 1 / 2)).sqrt
    have h := ((h2.add (((h5.add h5N).add h3N).const_mul A)).add
      (h4N.const_mul (2 * B))).const_mul 52
    simpa only [S, c, Real.rpow_one, Real.rpow_zero, one_mul, Real.sqrt_zero,
      zero_add, mul_zero] using h
  have hV := (tendsto_primeCharge_reciprocal_mass t).comp hQ
  have hW := (tendsto_primeCharge_logarithmic_reciprocal_mass t).comp hQ
  have hP := (tendsto_primeCharge_overlap_polar_bound hQ hN K t).pow 2
  have hJ := (primePoleScale_tendsto_atTop.comp hQ).const_div_atTop (2 * t ^ 2)
  have hz := hJ.add (((hR.comp hN).mul hW).add
    (((hS.comp hN).mul hV).add (hP.const_mul A)))
  simp only [zero_pow two_ne_zero, mul_zero, zero_add, add_zero, Function.comp_def] at hz
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hQ.eventually (eventually_ge_atTop 2), hN.eventually (eventually_ge_atTop 1),
    hN.eventually (eventually_primeCharge_uniform_geometry hK), hfar, hlarge]
      with i hQi hNi hgeom hQiN hlargei
  obtain ⟨hL, hc, hw, hrad, hc4, hgeomQ⟩ := hgeom
  obtain ⟨hQ4, hframe, hsize⟩ := hgeomQ (Q i) hQi hQiN
  have hQ8 : Q i ^ 8 ≤ N i :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ Q i) (by omega : 8 ≤ 64)).trans hQiN
  have hL0 : 0 < Real.log (N i) := zero_lt_one.trans_le hL
  have hc0 : 0 ≤ c (N i) := zero_le_one.trans hc
  have hV0 : 0 ≤ V (Q i) := by dsimp only [V]; positivity
  have hq := Real.log_natCast_nonneg (Q i)
  have hlog : 1 + Real.log (c (N i)) ≤ H * (1 + Real.log (Q i)) :=
    primeCharge_intermediate_log_overlap hK hL0 hlargei
  have hscalar : D + Real.log (c (N i)) ≤ (D + H) * (1 + Real.log (Q i)) := by
    have hDq := mul_nonneg hD.le hq
    nlinarith only [hlog, hDq]
  have hlogc : 1 + Real.log (c (N i)) ≤ c (N i) := by
    have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hc)
    linarith only [h]
  have hdown : c (N i) ^ 2 * (1 + Real.log (Q i)) * (1 + Real.log (c (N i))) /
      Real.log (N i) ≤ c (N i) ^ 3 * (1 + Real.log (Q i)) / Real.log (N i) :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogc (by positivity)) hL0.le).trans_eq (by ring)
  have hsqrt := receiving_overlap_sqrt_cost_le hc hL0
  have hquartic := receiving_quartic_boundary_le hNi hQ8 hc0
  have hdownsqrt := receiving_downward_sqrt_cost_le hNi hQ4 hc0 hL0.le
  have hmain :
      D + Real.log (c (N i)) + 600 * c (N i) * (1 + Real.log (Q i)) / Real.log (N i) +
        C * c (N i) ^ 2 / Real.log (N i) +
        A * (c (N i) ^ 2 * Real.sqrt ((1 + Real.log (c (N i))) / Real.log (N i)) +
          c (N i) ^ 5 * Real.log (N i) / N i + c (N i) ^ 3 * (Q i : ℝ) ^ 4 / N i) +
        2 * B * (c (N i) ^ 2 * (1 + Real.log (Q i)) * (1 + Real.log (c (N i))) / Real.log (N i) +
          c (N i) ^ 2 * (Q i : ℝ) * Real.sqrt (Real.log (N i) / N i)) ≤
      (D + H) * (1 + Real.log (Q i)) +
        600 * c (N i) * (1 + Real.log (Q i)) / Real.log (N i) +
        C * c (N i) ^ 2 / Real.log (N i) +
        A * (Real.sqrt (c (N i) ^ 5 / Real.log (N i)) +
          c (N i) ^ 5 * Real.log (N i) / N i + c (N i) ^ 3 / (N i : ℝ) ^ (1 / 2 : ℝ)) +
        2 * B * (c (N i) ^ 3 * (1 + Real.log (Q i)) / Real.log (N i) +
          Real.sqrt (c (N i) ^ 4 * Real.log (N i) / (N i : ℝ) ^ (1 / 2 : ℝ))) := by
    exact add_le_add
      (add_le_add (add_le_add (add_le_add hscalar le_rfl) le_rfl)
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hsqrt le_rfl) hquartic) hA))
      (mul_le_mul_of_nonneg_left (add_le_add hdown hdownsqrt) (by positivity))
  have hmean : (1 + Real.log (c (N i))) * V (Q i) ≤ H * W (Q i) :=
    (mul_le_mul_of_nonneg_right hlog hV0).trans_eq (by dsimp only [W]; ring)
  have hpole := receiving_polar_overlap_cost_le hc (P i)
  have hnear : A * (1 + Real.log (c (N i))) * ((3 / 2 : ℝ) * V (Q i) + c (N i) * P i ^ 2) ≤
      (3 / 2 : ℝ) * A * H * W (Q i) + A * (c (N i) * P i) ^ 2 := by
    calc
      _ = (3 / 2 : ℝ) * A * ((1 + Real.log (c (N i))) * V (Q i)) +
          A * (c (N i) * (1 + Real.log (c (N i))) * P i ^ 2) := by ring
      _ ≤ _ := (add_le_add
        (mul_le_mul_of_nonneg_left hmean (by positivity))
        (mul_le_mul_of_nonneg_left hpole hA)).trans_eq (by ring)
  let J := jumpEnergy (N i)
    (normalizedConductorPacket (Q i) (harmonicPrimeChargeCoefficients (Q i) (N i) t)) /
      Real.log (N i)
  have he := hb hQi hQ4 hframe hc hw hrad hsize t
  have he' : |completeWeilEnergy φ (c (N i)) (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J| ≤
      R (N i) * W (Q i) + S (N i) * V (Q i) + A * (c (N i) * P i) ^ 2 := by
    refine he.trans ((add_le_add
      (mul_le_mul_of_nonneg_left hmain (by positivity)) hnear).trans_eq ?_)
    dsimp only [R, S, W, C]
    rw [mul_comm (Real.log (N i)) (c (N i) ^ 4)]
    ring
  have hj := harmonicPrimeCharge_physical_jump_bounds hQi hL t
  rw [Real.norm_eq_abs]
  calc
    _ = |(completeWeilEnergy φ (c (N i)) (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J) + J| := by
      rw [sub_add_cancel]
    _ ≤ |completeWeilEnergy φ (c (N i)) (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J| + |J| :=
      abs_add_le _ _
    _ ≤ (R (N i) * W (Q i) + S (N i) * V (Q i) + A * (c (N i) * P i) ^ 2) +
        2 * t ^ 2 / primePoleScale (Q i) := by
      rw [abs_of_nonneg hj.1]
      exact add_le_add he' hj.2
    _ = _ := by dsimp only [W, V, P]; ring

#print axioms tendsto_harmonicPrimeCharge_energy_intermediate

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
