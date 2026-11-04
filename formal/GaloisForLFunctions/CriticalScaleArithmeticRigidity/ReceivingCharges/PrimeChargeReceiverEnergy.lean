import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeSignedReceiver
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeWindowEnergy
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormNormCosts

/-!
# Energy of the exact complementary receiver

The terminal conductor projection decays polynomially. Its complete energy
and its mixed contribution therefore vanish even after the logarithmic
receiver normalization. The complementary contrast retains its leading
energy coefficient.
-/

noncomputable section

open Finset Filter Topology MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms ArithmeticEffectivityTheory

/-- The low-conductor part removed from the terminal contrast. -/
def primeChargeTerminalProjection (X : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  (conductorSubspace (X ^ 2) (X ^ 40)).starProjection
    (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))

private theorem projection_power_bound {x L : ℝ} (hx : 0 < x) (hL : 1 ≤ L) (A : ℝ) :
    128 * (x ^ 2) ^ 3 * A ^ 2 / ((x ^ 38 + 1) ^ 2 * L ^ 2) ≤
      128 * A ^ 2 / x ^ 70 := by
  have hA : x ^ 76 ≤ (x ^ 38 + 1) ^ 2 := by
    rw [show x ^ 76 = (x ^ 38) ^ 2 by ring]
    nlinarith only [pow_nonneg hx.le 38]
  have hden : x ^ 76 ≤ (x ^ 38 + 1) ^ 2 * L ^ 2 :=
    hA.trans (le_mul_of_one_le_right (sq_nonneg _) (by nlinarith only [hL]))
  refine (div_le_div_of_nonneg_left (by positivity) (pow_pos hx 76) hden).trans_eq ?_
  field_simp [hx.ne']

private theorem projection_weight_bound {x A y : ℝ} (hx : 0 < x)
    (h : y ^ 2 ≤ 128 * A ^ 2 / x ^ 70) :
    (x * y) ^ 2 ≤ A ^ 2 * (128 / x ^ 68) := by
  rw [mul_pow]
  refine (mul_le_mul_of_nonneg_left h (sq_nonneg x)).trans_eq ?_
  field_simp [hx.ne']

/-- The finite conductor projection has a polynomial bound stronger than mere convergence. -/
theorem primeChargeTerminal_projection_sq_le_power {X : ℕ}
    (hX : 2 ≤ X) (hL : 5 ≤ Real.log (X : ℝ)) :
    ‖primeChargeTerminalProjection X‖ ^ 2 ≤
        128 * (1 + |primeChargeWindowMass (X ^ 39) (X ^ 40) /
          primeChargeWindowMass (X ^ 38) (X ^ 39)|) ^ 2 / (X : ℝ) ^ 70 := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hQ : 2 ≤ X ^ 2 := hX.trans (Nat.le_pow (by omega : 0 < 2))
  have hQN : X ^ 2 * X ^ 2 ≤ X ^ 40 := by
    calc
      _ = X ^ 4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega : 4 ≤ 40)
  have hframe : 18 * (1 + Real.log (X ^ 2 : ℕ)) ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL]
  have hb := primeChargeWindowVector_projection_sq_le
    (A := X ^ 38) (B := X ^ 39) (C := X ^ 40) hQ hQN hframe
    (Nat.pow_lt_pow_right (by omega) (by omega : 38 < 39))
    (Nat.pow_le_pow_right (by omega) (by omega : 39 ≤ 40)) le_rfl
  have hL40 : 1 ≤ Real.log (X ^ 40 : ℕ) := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    linarith only [hL]
  simp only [Nat.cast_pow] at hb hL40
  exact hb.trans (projection_power_bound hXR hL40 _)

/-- Even multiplication by the polynomial base leaves the projection norm vanishing. -/
theorem tendsto_primeChargeTerminal_projection_weighted_norm :
    Tendsto (fun X : ℕ => (X : ℝ) * ‖primeChargeTerminalProjection X‖)
      atTop (𝓝 0) := by
  have hk := tendsto_primeChargeWindowRatio (a := 38) (by omega)
  have hp : Tendsto (fun X : ℕ => (X : ℝ) ^ 68) atTop atTop :=
    (tendsto_pow_atTop (by omega : (68 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add hk.abs).pow 2).mul
    (hp.const_div_atTop 128)
  simp only [mul_zero] at hlim
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun X : ℕ => ((X : ℝ) * ‖primeChargeTerminalProjection X‖) ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 2, hlog.eventually (eventually_ge_atTop 5)] with X hX hL
    have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact projection_weight_bound hXR (primeChargeTerminal_projection_sq_le_power hX hL)
  simpa only [Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)),
    Real.sqrt_zero] using hsq.sqrt

/-- The exact conductor projection changes the logarithmically scaled receiver energy by zero in the limit. -/
theorem tendsto_primeChargeTerminal_projection_energy_error {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun X : ℕ =>
      (completeWeilEnergy φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
          (primeChargeTerminalReceiver X) -
        completeWeilEnergy φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
          (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))) /
            Real.log (X ^ 40 : ℕ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_complete_packet_neutral_norm_cost hφ hφ0 hsupp hM
  have hwp := tendsto_primeChargeTerminal_projection_weighted_norm
  have hp := tendsto_primeChargeTerminal_projection_norm
  have hlim := ((hwp.mul hp).add (hwp.const_mul 2)).const_mul (80 * C)
  simp only [mul_zero, add_zero] at hlim
  have hN : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hzlim : Tendsto (fun X : ℕ =>
      ‖primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖ ^ 2)
      atTop (𝓝 (1 / 20 : ℝ)) := by
    convert tendsto_primeChargeWindowVector_norm_sq (a := 38) (by omega) using 1
    norm_num
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 2,
    hL.eventually (eventually_ge_atTop 1),
    hN.eventually (eventually_primeCharge_criticalOverlap_facts hK),
    (tendsto_primeChargeCriticalOverlap_cube_div_log K (d := 40) (by omega)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hzlim.eventually (ge_mem_nhds (by norm_num : (1 / 20 : ℝ) < 1)),
    eventually_primeChargeTerminalProfile_neutral_unit] with X hX hLX hc hcube hzsq hr
  let L := Real.log (X ^ 40 : ℕ)
  let c := 2 * K * L ^ (1 / 8 : ℝ)
  let z := primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)
  let P := (conductorSubspace (X ^ 2) (X ^ 40)).starProjection z
  let F : ℕ → ℝ := fun n => (Real.sqrt L)⁻¹ *
    primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n
  let G : ℕ → ℝ := fun n => F n - primeChargeTerminalProfile X n
  have hL1 : 1 ≤ L := hLX
  have hL0 : 0 < L := zero_lt_one.trans_le hLX
  have hc0 : 0 < c := zero_lt_one.trans_le hc.1
  have hN1 : 1 ≤ X ^ 40 := Nat.one_le_pow 40 X (by omega)
  have hFpacket : packetVector F (X ^ 40) = z := by
    rw [show F = (fun n => (Real.sqrt L)⁻¹ *
      primeChargeWindowContrast (X ^ 38) (X ^ 39) (X ^ 40) n) from rfl,
      packetVector_const_mul]
    rfl
  have hGpacket : packetVector G (X ^ 40) = P := by
    have he : G = (fun n => F n + (-1 : ℝ) * primeChargeTerminalProfile X n) := by
      funext n
      dsimp only [G]
      ring
    rw [he, packetVector_add, hFpacket, packetVector_const_mul,
      packetVector_primeChargeTerminalProfile, neg_one_smul]
    change z - (z - P) = P
    abel
  have hF : ∑ n ∈ Icc 1 (X ^ 40), F n / (n : ℝ) = 0 := by
    have hneutral := primeChargeWindowContrast_harmonic_neutral
      (A := X ^ 38) (B := X ^ 39) (C := X ^ 40) (N := X ^ 40)
      (Nat.pow_lt_pow_right (by omega) (by omega : 38 < 39))
      (Nat.pow_le_pow_right (by omega) (by omega : 39 ≤ 40)) le_rfl
    simp only [F, mul_div_assoc, ← mul_sum, hneutral, mul_zero]
  have hG : ∑ n ∈ Icc 1 (X ^ 40), G n / (n : ℝ) = 0 := by
    simp only [G, sub_div, sum_sub_distrib, hF, hr.1, sub_self]
  have hz : ‖packetVector F (X ^ 40)‖ ≤ 1 := by
    rw [hFpacket]
    nlinarith only [hzsq, norm_nonneg z]
  have hcost := abs_complete_packet_energy_sub_le_of_neutral_norm_cost φ c (X ^ 40)
    (D := C * c ^ 3 * (L + 1)) (by positivity)
    (hbound (X ^ 40) c hN1 hc.1 hc.2) F G hF hG hz
  have he : (fun n => F n - G n) = primeChargeTerminalProfile X := by
    funext n
    dsimp only [G]
    ring
  rw [he, packetVector_primeChargeTerminalProfile, hFpacket, hGpacket] at hcost
  have hc3 : c ^ 3 ≤ L := (div_le_one hL0).mp hcube
  have hlogX : Real.log (X : ℝ) ≤ (X : ℝ) :=
    (Real.log_le_sub_one_of_pos (by exact_mod_cast (show 0 < X by omega))).trans (by linarith)
  have hlog : L ≤ 40 * (X : ℝ) := by
    dsimp only [L]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_left hlogX (by norm_num)
  have hcostL : C * c ^ 3 * (L + 1) / L ≤ 80 * C * (X : ℝ) := by
    calc
      _ ≤ C * c ^ 3 * (2 * L) / L := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hL1]) (by positivity)) hL0.le
      _ = 2 * C * c ^ 3 := by field_simp [hL0.ne']
      _ ≤ 2 * C * L := mul_le_mul_of_nonneg_left hc3 (by positivity)
      _ ≤ 2 * C * (40 * (X : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL0]
  refine (div_le_div_of_nonneg_right hcost hL0.le).trans ?_
  calc
    _ = (C * c ^ 3 * (L + 1) / L) * (‖P‖ ^ 2 + 2 * ‖P‖) := by ring
    _ ≤ (80 * C * (X : ℝ)) * (‖P‖ ^ 2 + 2 * ‖P‖) :=
      mul_le_mul_of_nonneg_right hcostL (by positivity)
    _ = _ := by dsimp only [P, z, primeChargeTerminalProjection]; ring

/-- The exact complementary receiver has complete energy asymptotic to `log N / 20`. -/
theorem tendsto_primeChargeTerminalReceiver_complete_scaled {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) :
    Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (primeChargeTerminalReceiver X) / Real.log (X ^ 40 : ℕ)) atTop (𝓝 (1 / 20 : ℝ)) := by
  have hz : Tendsto (fun X : ℕ =>
      completeWeilEnergy φ (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)
        (primeChargeWindowVector (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)) /
          Real.log (X ^ 40 : ℕ)) atTop (𝓝 (1 / 20 : ℝ)) := by
    convert tendsto_primeChargeWindowVector_complete_scaled hφ hφ0 hsupp hM hK
      (a := 38) (by omega) using 1
    norm_num
  have h := (tendsto_primeChargeTerminal_projection_energy_error hφ hφ0 hsupp hM hK).add hz
  simp only [sub_div, sub_add_cancel, zero_add] at h
  exact h

#print axioms tendsto_primeChargeTerminal_projection_weighted_norm
#print axioms tendsto_primeChargeTerminalReceiver_complete_scaled

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
