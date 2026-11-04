import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeIntermediateBounds
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformScales

/-!
# Physical charge energy when the cutoff controls the horizon logarithm

If `N ≤ Q⁶⁴`, the critical overlap costs at most a fixed multiple of
`(log Q)^(3/8)`. The exact neutral moment comparison therefore makes the
complete physical energy vanish, without fixing a ratio of logarithms.
-/

noncomputable section

open Finset Filter Topology MeasureTheory

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory CompletedArithmeticForms

/-- A polynomial upper bound for the horizon controls the cubic overlap cost. -/
theorem primeCharge_critical_cube_le_cutoff {Q N : ℕ} {K : ℝ}
    (hK : 0 ≤ K) (hN : 1 ≤ N) (hNQ : N ≤ Q ^ 64) :
    (2 * K * Real.log N ^ (1 / 8 : ℝ)) ^ 3 ≤
      (2 * K) ^ 3 * (64 : ℝ) ^ (3 / 8 : ℝ) * Real.log Q ^ (3 / 8 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log hNR (show (N : ℝ) ≤ (Q : ℝ) ^ 64 by exact_mod_cast hNQ)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hp : (Real.log N ^ (1 / 8 : ℝ)) ^ (3 : ℕ) = Real.log N ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Real.log_natCast_nonneg N)]
    norm_num
  rw [mul_pow, hp]
  calc
    _ ≤ (2 * K) ^ 3 * (64 * Real.log Q) ^ (3 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Real.log_natCast_nonneg N) hlog (by norm_num)) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (Real.log_natCast_nonneg Q), mul_assoc]

/-- Every growing cutoff with `N ≤ Q⁶⁴` has vanishing literal physical energy. -/
theorem tendsto_harmonicPrimeCharge_energy_dense_cutoff {ι : Type*} {l : Filter ι}
    {Q N : ι → ℕ} (hQ : Tendsto Q l atTop) (hN : Tendsto N l atTop)
    (hNQ : ∀ᶠ i in l, N i ≤ Q i ^ 64)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : 0 < K) (t : ℝ) :
    Tendsto (fun i => completeWeilEnergy φ (2 * K * Real.log (N i) ^ (1 / 8 : ℝ))
      (N i) (harmonicPrimeChargeVector (Q i) (N i) t)) l (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := exists_harmonicPrimeCharge_physical_moment_bound hφ hφ0 hsupp hM
  let D := C * (2 * K) ^ 3 * (64 : ℝ) ^ (3 / 8 : ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hj := (primePoleScale_tendsto_atTop.comp hQ).const_div_atTop (2 * t ^ 2)
  have hm := ((tendsto_primeChargeMoment_cost t (by norm_num : (3 / 8 : ℝ) < 1)).comp hQ).const_mul D
  simp only [mul_zero] at hm
  have hz := hj.add hm
  simp only [add_zero, Function.comp_def] at hz
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [hQ.eventually (eventually_ge_atTop 2),
    hN.eventually (eventually_ge_atTop 1),
    hN.eventually ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1),
    hN.eventually (eventually_primeCharge_criticalOverlap_facts hK), hNQ]
      with i hQi hNi hLi hci hNQi
  let c := 2 * K * Real.log (N i) ^ (1 / 8 : ℝ)
  let V := (t / primePoleScale (Q i)) ^ 2 *
    (4 * (∑ p ∈ (Icc 1 (Q i)).filter Nat.Prime, 1 / (p : ℝ)) ^ 2 +
      2 * ∑ p ∈ (Icc 1 (Q i)).filter Nat.Prime, 1 / (p : ℝ))
  let J := jumpEnergy (N i)
    (normalizedConductorPacket (Q i) (harmonicPrimeChargeCoefficients (Q i) (N i) t)) /
      Real.log (N i)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hJ := harmonicPrimeCharge_physical_jump_bounds hQi hLi t
  have he := hb (Q i) (N i) c t hQi hNi hLi hci.1 hci.2
  change |completeWeilEnergy φ c (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J| ≤
    C * c ^ 3 * (t / primePoleScale (Q i)) ^ 2 * _ at he
  have hc3 := primeCharge_critical_cube_le_cutoff hK.le hNi hNQi
  have hmoment : C * c ^ 3 * V ≤
      D * (Real.log (Q i) ^ (3 / 8 : ℝ) * (Real.log (Q i) + 1) * V) := by
    calc
      _ ≤ C * ((2 * K) ^ 3 * (64 : ℝ) ^ (3 / 8 : ℝ) *
          Real.log (Q i) ^ (3 / 8 : ℝ)) * V :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc3 hC) hV
      _ = D * Real.log (Q i) ^ (3 / 8 : ℝ) * V := by dsimp only [D]; ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (show 1 ≤ Real.log (Q i) + 1 by linarith only [Real.log_natCast_nonneg (Q i)])
          (show 0 ≤ D * Real.log (Q i) ^ (3 / 8 : ℝ) * V by positivity)
        simpa only [mul_one] using h.trans_eq (by ring)
  rw [Real.norm_eq_abs]
  calc
    _ = |(completeWeilEnergy φ c (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J) + J| := by
      rw [sub_add_cancel]
    _ ≤ |completeWeilEnergy φ c (N i) (harmonicPrimeChargeVector (Q i) (N i) t) - J| + |J| :=
      abs_add_le _ _
    _ ≤ C * c ^ 3 * V + 2 * t ^ 2 / primePoleScale (Q i) := by
      rw [abs_of_nonneg hJ.1]
      exact add_le_add (he.trans_eq (by dsimp only [V]; ring)) hJ.2
    _ ≤ _ := (add_le_add_right hmoment _).trans_eq (by dsimp only [V]; ring)

#print axioms tendsto_harmonicPrimeCharge_energy_dense_cutoff

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
