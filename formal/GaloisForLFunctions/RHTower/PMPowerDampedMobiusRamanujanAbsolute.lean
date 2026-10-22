import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanVariance

/-!
# Uniform Ramanujan energy budgets in the absolutely convergent range `ε > 1/2`

Using `{x} ≤ x^a` for `x ≥ 0`, `0 ≤ a ≤ 1`, and the cofactor bound `|K_Q(d)| ≤ d^(−ε)`, the
representation `P_Q(N) = −∑_{d≤Q+1} K_{Q+1}(d) {N/d}` of the cumulative Ramanujan prefix gives
`|P_Q(N)| ≤ N^a ∑_d d^(−(ε+a))` uniformly in `Q` whenever `ε + a > 1`. If moreover `a < 1/2`,
the discrete energies `∑_{N≤T} |P_Q(N)|²/(N(N+1))` are bounded by
`(∑_d d^(−(ε+a)))² ∑_N N^(2a−2)` uniformly in `Q` and `T`. For `ε > 1/2` such an `a` exists, so
the truncated prefix energies, the Gram quadratic forms and the Ramanujan variances are all
uniformly bounded.

## Main results

- `pm_fract_le_rpow`: `{x} ≤ x^a` for `x ≥ 0` and `0 ≤ a ≤ 1`.
- `norm_pmPowerDampedRamanujanCumulativePrefix_le_rpow`: for `ε > 0`, `0 ≤ a ≤ 1`, `ε + a > 1`: `|P_Q(N)| ≤ N^a ∑'_d d^(−(ε+a))`.
- `pmPowerDampedRamanujanPrefixEnergy_le_rpow_budget`: for additionally `a < 1/2`, a `Q`, `T`-uniform energy bound.
- `exists_pmPowerDampedRamanujan_budget_of_half_lt`: for `ε > 1/2`, the truncated prefix energies are uniformly bounded.
- `exists_pmPowerDampedRamanujan_gram_budget_of_half_lt`: for `ε > 1/2`, the Gram forms `Γ_Q` are uniformly bounded.
- `exists_pmPowerDampedRamanujan_variance_budget_of_half_lt`: for `ε > 1/2`, the variances `V_Q` are uniformly bounded.

## Hypotheses

All results are unconditional. They require the explicit range conditions: `0 < ε`,
`0 ≤ a ≤ 1` (or `a < 1/2`) and `1 < ε + a`, and for the existence results `1/2 < ε`. Nothing
is claimed for `0 < ε ≤ 1/2`.
-/

open MeasureTheory Set Filter Topology Complex ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace RHTower

/-- For `x ≥ 0` and `0 ≤ a ≤ 1`, the fractional part satisfies `{x} ≤ x^a`. -/
theorem pm_fract_le_rpow {x a : ℝ} (hx : 0 ≤ x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Int.fract x ≤ x^a := by
  by_cases hx1 : x ≤ 1
  · have hf : (0 : ℝ) ≤ (⌊x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.mpr hx
    have hfx : Int.fract x ≤ x := by dsimp only [Int.fract]; linarith
    exact hfx.trans (Real.self_le_rpow_of_le_one hx hx1 ha1)
  · exact (Int.fract_lt_one x).le.trans (Real.one_le_rpow (le_of_not_ge hx1) ha0)

/-- For `ε > 0`, `0 ≤ a ≤ 1`, `d > 0`: `|K_Q(d) {N/d}| ≤ N^a d^(−(ε+a))`. -/
theorem norm_pmPowerDampedRamanujanCofactor_fract_le {ε a : ℝ}
    (hε : 0 < ε) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (Q N : ℕ) {d : ℕ} (hd : 0 < d) :
    ‖pmPowerDampedRamanujanCofactor ε Q d*((Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ)‖ ≤
      (N : ℝ)^a*(d : ℝ)^(-(ε+a)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
  calc
    _ ≤ (d : ℝ)^(-ε)*((N : ℝ)/(d : ℝ))^a :=
      mul_le_mul (norm_pmPowerDampedRamanujanCofactor_le hε Q hd)
        (pm_fract_le_rpow (by positivity) ha0 ha1) (Int.fract_nonneg _)
        (Real.rpow_nonneg hdR.le _)
    _ = (N : ℝ)^a*((d : ℝ)^(-ε)*(d : ℝ)^(-a)) := by
      rw [Real.div_rpow (Nat.cast_nonneg N) hdR.le, Real.rpow_neg hdR.le a]
      ring
    _ = _ := by
      rw [← Real.rpow_add hdR]
      congr 2
      ring

/-- For `ε > 0`, `0 ≤ a ≤ 1` and `ε + a > 1`, the cumulative prefix obeys
`|P_Q(N)| ≤ N^a ∑'_d d^(−(ε+a))` uniformly in `Q`. -/
theorem norm_pmPowerDampedRamanujanCumulativePrefix_le_rpow {ε a : ℝ}
    (hε : 0 < ε) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hεa : 1 < ε+a) (Q N : ℕ) :
    ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖ ≤
      (N : ℝ)^a*(∑' d : ℕ, (d : ℝ)^(-(ε+a))) := by
  have hs : Summable (fun d : ℕ => (d : ℝ)^(-(ε+a))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  rw [pmPowerDampedRamanujanCumulativePrefix_eq_cofactor_fract hε, norm_neg]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (Q+1),
        ‖pmPowerDampedRamanujanCofactor ε (Q+1) d*
          ((Int.fract ((N : ℝ)/(d : ℝ)) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (Q+1), (N : ℝ)^a*(d : ℝ)^(-(ε+a)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact norm_pmPowerDampedRamanujanCofactor_fract_le hε ha0 ha1 (Q+1) N
        (by have := (Finset.mem_Icc.mp hd).1; omega)
    _ = (N : ℝ)^a*(∑ d ∈ Finset.Icc 1 (Q+1), (d : ℝ)^(-(ε+a))) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.Icc 1 (Q+1)) (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _))
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- For `ε > 0`, `0 ≤ a < 1/2` and `ε + a > 1`, every truncated prefix energy is at most
`(∑'_d d^(−(ε+a)))² ∑'_N N^(2a−2)`. -/
theorem pmPowerDampedRamanujanPrefixEnergy_le_rpow_budget {ε a : ℝ}
    (hε : 0 < ε) (ha0 : 0 ≤ a) (ha1 : a < 1/2) (hεa : 1 < ε+a) (Q T : ℕ) :
    pmPowerDampedRamanujanPrefixEnergy ε Q T ≤
      (∑' d : ℕ, (d : ℝ)^(-(ε+a)))^2*(∑' N : ℕ, (N : ℝ)^(a*2-2)) := by
  let C : ℝ := ∑' d : ℕ, (d : ℝ)^(-(ε+a))
  have hs : Summable (fun N : ℕ => (N : ℝ)^(a*2-2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hterm (N : ℕ) (hN : 0 < N) :
      ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2/((N : ℝ)*((N : ℝ)+1)) ≤
        C^2*(N : ℝ)^(a*2-2) := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hb := norm_pmPowerDampedRamanujanCumulativePrefix_le_rpow hε ha0
      (by linarith : a ≤ 1) hεa Q N
    have hsq : ‖pmPowerDampedRamanujanCumulativePrefix ε Q N‖^2 ≤ ((N : ℝ)^a*C)^2 := by
      simpa only [pow_two, C] using mul_self_le_mul_self (norm_nonneg _) hb
    calc
      _ ≤ ((N : ℝ)^a*C)^2/((N : ℝ)*((N : ℝ)+1)) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ ((N : ℝ)^a*C)^2/((N : ℝ)*(N : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ = _ := by
        rw [Real.rpow_sub hNR, Real.rpow_mul hNR.le]
        simp only [Real.rpow_two]
        ring
  calc
    _ ≤ ∑ N ∈ Finset.Icc 1 T, C^2*(N : ℝ)^(a*2-2) := by
      apply Finset.sum_le_sum
      intro N hN
      exact hterm N (by have := (Finset.mem_Icc.mp hN).1; omega)
    _ = C^2*(∑ N ∈ Finset.Icc 1 T, (N : ℝ)^(a*2-2)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Finset.Icc 1 T) (fun N _ => Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (sq_nonneg C)

/-- For `ε > 1/2`, one constant bounds all truncated prefix energies over `Q` and `T`. -/
theorem exists_pmPowerDampedRamanujan_budget_of_half_lt {ε : ℝ} (hε : 1/2 < ε) :
    ∃ B : ℝ, ∀ Q T : ℕ, pmPowerDampedRamanujanPrefixEnergy ε Q T ≤ B := by
  have hgap : max 0 (1-ε) < (1/2 : ℝ) := by
    rw [max_lt_iff]
    constructor <;> linarith
  obtain ⟨a, ha0, ha1⟩ := exists_between hgap
  have ha : 0 ≤ a := (le_max_left 0 (1-ε)).trans ha0.le
  have hεa : 1 < ε+a := by have := (le_max_right 0 (1-ε)).trans_lt ha0; linarith
  exact ⟨_, fun Q T => pmPowerDampedRamanujanPrefixEnergy_le_rpow_budget
    (by linarith) ha ha1 hεa Q T⟩

/-- For `ε > 1/2`, the Gram quadratic forms `Γ_Q` are bounded uniformly in `Q`. -/
theorem exists_pmPowerDampedRamanujan_gram_budget_of_half_lt {ε : ℝ} (hε : 1/2 < ε) :
    ∃ B : ℝ, ∀ Q : ℕ, pmPowerDampedRamanujanGramQuadratic ε Q ≤ B := by
  obtain ⟨B, hB⟩ := exists_pmPowerDampedRamanujan_budget_of_half_lt hε
  exact ⟨B, (pmPowerDampedRamanujan_budget_iff_gram (by linarith)).mp hB⟩

/-- For `ε > 1/2`, the Ramanujan variances `V_Q` are bounded uniformly in `Q`. -/
theorem exists_pmPowerDampedRamanujan_variance_budget_of_half_lt {ε : ℝ} (hε : 1/2 < ε) :
    ∃ B : ℝ, ∀ Q : ℕ, pmPowerDampedRamanujanEnergyVariance ε Q ≤ B := by
  exact (pmPowerDampedRamanujan_gram_budget_iff_variance (by linarith)).mp
    (exists_pmPowerDampedRamanujan_gram_budget_of_half_lt hε)

end RHTower
