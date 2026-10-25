import GaloisForLFunctions.BezoutValuationIncidence.HyperbolaCancellationWithDivisorBoundedCoefficients
import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyFromPrefixCancellation

/-!
Power cancellation in divisor-bounded coefficients survives the damped floor
transform. An explicit split balances the rounding head against the signed
tail and transfers each exponent strictly below the resulting threshold.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A power saving for divisor-square bounded partial sums survives the damped floor transform.
The split at `n^(1/(1+κ))` transfers every gain below `κ(1-ε)/(1+κ)`. -/
theorem exists_uniform_weightCenteredPrefix_dampedSign_power_of_divisor_square
    {ι : Type*} {s : ι → ℕ → ℝ} {ε C B κ γ : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hκ : 0 < κ) (hγ : 0 < γ) (hγκ : γ < κ * (1 - ε) / (1 + κ))
    (hs : ∀ i : ι, ∀ d : ℕ, 1 ≤ d → |s i d| ≤ C * (d.divisors.card : ℝ) ^ 2)
    (hsum : ∀ i, Summable (fun d : ℕ => dampedSignWeight (s i) ε d / d))
    (hS : ∀ᶠ x : ℕ in atTop, ∀ i,
      |∑ d ∈ Icc 1 x, s i d| ≤ B * (x : ℝ) ^ (1 - κ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ i,
      |weightCenteredPrefix (dampedSignWeight (s i) ε)
        (∑' d : ℕ, dampedSignWeight (s i) ε d / d) n| ≤
          K * (n : ℝ) ^ (1 - ε - γ) := by
  let a : ℝ := 1 / (1 + κ)
  let g : ℝ := κ * (1 - ε) / (1 + κ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (div_le_one (by positivity)).mpr (by linarith only [hκ])
  have hgap : 0 < g - γ := sub_pos.mpr hγκ
  have hbalance : a * (1 - ε) = 1 - ε - g := by
    dsimp only [a, g]
    field_simp [(show (1 : ℝ) + κ ≠ 0 by positivity)] <;> ring
  have hbalanceTail : 1 + a * (-(κ + ε)) = a * (1 - ε) := by
    dsimp only [a]
    field_simp [(show (1 : ℝ) + κ ≠ 0 by positivity)] <;> ring
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hS
  let D : ℕ → ℕ := fun n => ⌊(n : ℝ) ^ a⌋₊
  have hDlim : Tendsto D atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogSmall : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) ^ (g - γ) := by
    filter_upwards [eventually_log_pow_le_sqrt_rpow 4 (by positivity : 0 < 2 * (g - γ))]
      with n hn
    simpa only [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n),
      show 2 * (g - γ) * (1 / 2) = g - γ by ring] using hn
  refine ⟨16 * C + 13 / ε * B * (2 : ℝ) ^ (κ + ε), by positivity, ?_⟩
  filter_upwards [hDlim.eventually_ge_atTop (max N₀ 1), hloglim.eventually_ge_atTop 1,
    hlogSmall, eventually_ge_atTop 1] with n hstart hlog hsmall hn i
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD1 : 1 ≤ D n := (le_max_right N₀ 1).trans hstart
  have hD0 : (0 : ℝ) < D n := by exact_mod_cast hD1
  have hDy : (D n : ℝ) ≤ (n : ℝ) ^ a := Nat.floor_le (Real.rpow_nonneg hn0.le _)
  have hDn : D n ≤ n := by
    exact_mod_cast hDy.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 ha1)
  have hyD : (n : ℝ) ^ a / 2 ≤ D n := by
    have hf := Nat.lt_floor_add_one ((n : ℝ) ^ a)
    change (n : ℝ) ^ a < (D n : ℝ) + 1 at hf
    have hD1r : (1 : ℝ) ≤ D n := by exact_mod_cast hD1
    linarith only [hf, hD1r]
  have hlinear (x : ℕ) (hx : D n ≤ x) :
      |∑ d ∈ Icc 1 x, s i d| ≤ B * (D n : ℝ) ^ (-κ) * x := by
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hD1.trans hx
    have hp : (x : ℝ) ^ (-κ) ≤ (D n : ℝ) ^ (-κ) :=
      Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast hx) (neg_nonpos.mpr hκ.le)
    calc
      _ ≤ B * (x : ℝ) ^ (1 - κ) := hN₀ x (((le_max_left N₀ 1).trans hstart).trans hx) i
      _ = B * (x : ℝ) ^ (-κ) * x := by
        rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB) hx0.le
  have hbase := abs_weightCenteredPrefix_dampedSign_le_head_of_linear
    (by positivity : 0 ≤ B * (D n : ℝ) ^ (-κ)) hε hε2 (hsum i) hD1 hDn hlinear
  have hheadPower : (D n : ℝ) ^ (1 - ε) ≤ (n : ℝ) ^ (a * (1 - ε)) := by
    calc
      _ ≤ ((n : ℝ) ^ a) ^ (1 - ε) :=
        Real.rpow_le_rpow hD0.le hDy (by linarith only [hε2])
      _ = _ := (Real.rpow_mul hn0.le _ _).symm
  have hheadLog : (1 + Real.log (D n : ℝ)) ^ 4 ≤ 16 * Real.log (n : ℝ) ^ 4 := by
    have hld : 0 ≤ Real.log (D n : ℝ) := Real.log_nonneg (by exact_mod_cast hD1)
    have hln : Real.log (D n : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hD0 (by exact_mod_cast hDn)
    have h := pow_le_pow_left₀ (by linarith only [hld] : 0 ≤ 1 + Real.log (D n : ℝ))
      (by linarith only [hln, hlog] : 1 + Real.log (D n : ℝ) ≤ 2 * Real.log (n : ℝ)) 4
    simpa only [mul_pow, show (2 : ℝ) ^ 4 = 16 by norm_num] using h
  have hhead : (∑ d ∈ Icc 1 (D n), |s i d| * (d : ℝ) ^ (-ε)) ≤
      16 * C * (n : ℝ) ^ (1 - ε - γ) := by
    calc
      _ ≤ C * (D n : ℝ) ^ (1 - ε) * (1 + Real.log (D n : ℝ)) ^ 4 :=
        sum_abs_mul_rpow_le_divisor_square_head (by linarith only [hε2]) hC (hs i) hD1
      _ ≤ C * (n : ℝ) ^ (a * (1 - ε)) * (16 * (n : ℝ) ^ (g - γ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hheadPower hC)
          (hheadLog.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num)))
          (by positivity) (by positivity)
      _ = 16 * C * ((n : ℝ) ^ (a * (1 - ε)) * (n : ℝ) ^ (g - γ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hn0, hbalance]
        congr 2
        ring
  have hDP : (D n : ℝ) ^ (-(κ + ε)) ≤
      (2 : ℝ) ^ (κ + ε) * (n : ℝ) ^ (a * (-(κ + ε))) := by
    calc
      _ ≤ ((n : ℝ) ^ a / 2) ^ (-(κ + ε)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hyD (by linarith only [hκ, hε])
      _ = (2 : ℝ) ^ (κ + ε) * ((n : ℝ) ^ a) ^ (-(κ + ε)) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv]
        ring
      _ = _ := by rw [← Real.rpow_mul hn0.le]
  have htail : 13 / ε * (B * (D n : ℝ) ^ (-κ)) * n * (D n : ℝ) ^ (-ε) ≤
      (13 / ε * B * (2 : ℝ) ^ (κ + ε)) * (n : ℝ) ^ (1 - ε - γ) := by
    calc
      _ = (13 / ε * B * n) * (D n : ℝ) ^ (-(κ + ε)) := by
        rw [show -(κ + ε) = -κ + -ε by ring, Real.rpow_add hD0]
        ring
      _ ≤ (13 / ε * B * n) * ((2 : ℝ) ^ (κ + ε) * (n : ℝ) ^ (a * (-(κ + ε)))) :=
        mul_le_mul_of_nonneg_left hDP (by positivity)
      _ = (13 / ε * B * (2 : ℝ) ^ (κ + ε)) * (n : ℝ) ^ (a * (1 - ε)) := by
        rw [← hbalanceTail, Real.rpow_add hn0, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hbalance]; linarith only [hgap]))
        (by positivity)
  exact hbase.trans ((add_le_add hhead htail).trans_eq (by ring))

/-- A global prefix power bound controls the pronic norm at the same improved damping. -/
theorem pronicNorm_le_sqrt_rpow_of_prefix_power {f : ℕ → ℝ} {ε γ K : ℝ}
    (hεγ : 0 < ε + γ) (hεγ2 : ε + γ < 1 / 2) (hK : 0 ≤ K)
    (hprefix : ∀ n, 1 ≤ n → |f n| ≤ K * (n : ℝ) ^ (1 - ε - γ))
    {T : ℕ} (hT : 1 ≤ T) :
    pronicNorm f T ≤ K * Real.sqrt (1 + 1 / (1 - 2 * (ε + γ))) *
      Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  have hβ : 0 < 1 - 2 * (ε + γ) := by linarith only [hεγ2]
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hsum : (∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
      K ^ 2 * (1 + 1 / (1 - 2 * (ε + γ))) * (T : ℝ) ^ (1 - 2 * (ε + γ)) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 T, K ^ 2 * (n : ℝ) ^ (-(2 * (ε + γ))) := by
        apply sum_le_sum
        intro n hn
        apply cell_le_of_abs_le_rpow (ε := ε + γ) (mem_Icc.mp hn).1
        simpa only [show 1 - (ε + γ) = 1 - ε - γ by ring] using hprefix n (mem_Icc.mp hn).1
      _ = K ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * (ε + γ))) := (mul_sum _ _ _).symm
      _ ≤ K ^ 2 * (1 + (T : ℝ) ^ (1 - 2 * (ε + γ)) / (1 - 2 * (ε + γ))) :=
        mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_two_mul_le_of_pos hεγ hεγ2 T) (sq_nonneg K)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (add_le_add (Real.one_le_rpow hT1 hβ.le)
            (le_refl ((T : ℝ) ^ (1 - 2 * (ε + γ)) / (1 - 2 * (ε + γ))))) (sq_nonneg K)
        exact h.trans_eq (by ring)
  have h := Real.sqrt_le_sqrt hsum
  change pronicNorm f T ≤ _ at h
  simpa only [Real.sqrt_mul (mul_nonneg (sq_nonneg K) (by positivity)),
    Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK] using h

/-- A common linear bound absorbs the finite head of an eventual prefix power saving. -/
theorem exists_uniform_pronicNorm_power_of_eventually_prefix_power
    {ι : Type*} {f : ι → ℕ → ℝ} {ε γ A B : ℝ}
    (hεγ : 0 < ε + γ) (hεγ2 : ε + γ < 1 / 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hlinear : ∀ i : ι, ∀ n : ℕ, 1 ≤ n → |f i n| ≤ A * n)
    (hprefix : ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * (n : ℝ) ^ (1 - ε - γ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : ι, ∀ T : ℕ, 1 ≤ T →
      pronicNorm (f i) T ≤ K * Real.sqrt ((T : ℝ) ^ (1 - 2 * (ε + γ))) := by
  have hprefix' : ∀ᶠ n : ℕ in atTop, ∀ i,
      |f i n| ≤ B * (n : ℝ) ^ (1 - (ε + γ)) := by
    simpa only [show 1 - (ε + γ) = 1 - ε - γ by ring] using hprefix
  obtain ⟨C, hC, hglobal⟩ := exists_uniform_rpow_bound_of_eventually
    hεγ.le hA hB hlinear hprefix'
  refine ⟨C * Real.sqrt (1 + 1 / (1 - 2 * (ε + γ))), by positivity, fun i T hT => ?_⟩
  apply pronicNorm_le_sqrt_rpow_of_prefix_power hεγ hεγ2 hC
    (fun n hn => ?_) hT
  simpa only [show 1 - (ε + γ) = 1 - ε - γ by ring] using hglobal i n hn

#print axioms exists_uniform_weightCenteredPrefix_dampedSign_power_of_divisor_square
#print axioms pronicNorm_le_sqrt_rpow_of_prefix_power
#print axioms exists_uniform_pronicNorm_power_of_eventually_prefix_power
end GaloisForLFunctions.BezoutValuationIncidence
