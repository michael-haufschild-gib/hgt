import GaloisForLFunctions.RHTower.HighBlockSubBlock
import GaloisForLFunctions.RHTower.HighBlockDirectVariation
import GaloisForLFunctions.RHTower.HighBlockDualVariation
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovWeight

/-!
# High-block law: parameters, the gate mollifier, and the single arithmetic input

* Mollifier: `b_n = μ(n) log(N/n)/log N` (`n ≤ N`), the Barban–Vehov weight normalised to `b_1 = 1`,
  `‖b_n‖ ≤ 1`, real, and `Σ ‖b_n‖ n⁴ ≤ N⁵`.
* Parameters on a block `[a, v] ⊆ [a, 2a]` inside `[20, U]`: `x = √(a/2π)`, head length
  `L = ⌈a^{51/100}⌉`, mollifier length `N = ⌊U^{1/20}⌋`, `J = ⌈a^{3/10} U^{1/20}⌉` sub-blocks.
* `SharpEnergyInput C`: the sharp-cutoff critical energy against the displaced gate mollifier is at
  most `C` for every head length `u < L`, every displacement `0 < d ≤ ¼`, every `1 ≤ a ≤ U`, for
  all large `U`. This is the only arithmetic input of the high-block law.
-/

open Complex Finset Set Filter Topology

namespace RHTower

noncomputable section

/-- Gate mollifier coefficients `μ(n) log(N/n)/log N`. -/
def hbCoeff (N : ℕ) (n : ℕ) : ℂ := ((Sieve.barbanVehovWeight N n / Real.log N : ℝ) : ℂ)

theorem hbCoeff_one {N : ℕ} (hN : 2 ≤ N) : hbCoeff N 1 = 1 := by
  unfold hbCoeff Sieve.barbanVehovWeight
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [if_pos (by omega), ArithmeticFunction.moebius_apply_one]
  have hreal : (((1 : ℤ) : ℝ) * Real.log ((N : ℝ) / ((1 : ℕ) : ℝ)) / Real.log N) = 1 := by
    rw [Nat.cast_one, div_one, Int.cast_one, one_mul, div_self hlog.ne']
  rw [hreal]
  simp

theorem norm_hbCoeff_le {N n : ℕ} (hN : 2 ≤ N) (hn : n ∈ Finset.Icc 1 N) :
    ‖hbCoeff N n‖ ≤ 1 := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  unfold hbCoeff Sieve.barbanVehovWeight
  rw [if_pos hnN, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul]
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [abs_of_pos hlog, div_le_one hlog]
  have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hq : 1 ≤ (N : ℝ) / n := by
    rw [le_div_iff₀ hn0, one_mul]
    exact hnN'
  have hq2 : (N : ℝ) / n ≤ N := by
    rw [div_le_iff₀ hn0]
    nlinarith
  have hlogq : 0 ≤ Real.log ((N : ℝ) / n) := Real.log_nonneg hq
  rw [abs_of_nonneg hlogq]
  calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)| * Real.log ((N : ℝ) / n)
      ≤ 1 * Real.log N :=
        mul_le_mul hμ (Real.log_le_log (by positivity) hq2) hlogq zero_le_one
    _ = Real.log N := one_mul _

theorem conj_hbCoeff (N n : ℕ) : (starRingEnd ℂ) (hbCoeff N n) = hbCoeff N n :=
  Complex.conj_ofReal _

theorem sum_norm_hbCoeff_mul_rpow_le {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ‖hbCoeff N n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ (N : ℝ) ^ (5 : ℕ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖hbCoeff N n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ (N : ℝ) ^ (4 : ℕ) := by
    intro n hn
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖hbCoeff N n‖ * ((n : ℝ) ^ (4 : ℝ)) ≤ 1 * ((N : ℝ) ^ (4 : ℝ)) :=
          mul_le_mul (norm_hbCoeff_le hN hn) (Real.rpow_le_rpow hn0 hnN (by norm_num))
            (by positivity) zero_le_one
      _ = (N : ℝ) ^ (4 : ℕ) := by rw [one_mul, Real.rpow_ofNat]
  calc (∑ n ∈ Finset.Icc 1 N, ‖hbCoeff N n‖ * ((n : ℝ) ^ (4 : ℝ)))
      ≤ ∑ _n ∈ Finset.Icc 1 N, (N : ℝ) ^ (4 : ℕ) := Finset.sum_le_sum hterm
    _ = (N : ℝ) * (N : ℝ) ^ (4 : ℕ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ = (N : ℝ) ^ (5 : ℕ) := by ring

/-! ### Block parameters -/

/-- The AFE scale `x = √(a/2π)`. -/
def hbX (a : ℝ) : ℝ := Real.sqrt (a / (2 * Real.pi))

/-- The head length `L = ⌈a^{51/100}⌉`. -/
def hbL (a : ℝ) : ℕ := ⌈a ^ ((51 : ℝ) / 100)⌉₊

/-- The mollifier length `N = ⌊U^{1/20}⌋`. -/
def hbN (U : ℝ) : ℕ := ⌊U ^ ((1 : ℝ) / 20)⌋₊

/-- The number of sub-blocks `J = ⌈a^{3/10} U^{1/20}⌉`. -/
def hbJ (a U : ℝ) : ℕ := ⌈a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20)⌉₊

theorem hbX_pos {a : ℝ} (ha : 0 < a) : 0 < hbX a := by
  unfold hbX
  positivity

theorem hbX_le_sqrt {a : ℝ} (ha : 0 ≤ a) : hbX a ≤ Real.sqrt a := by
  unfold hbX
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

theorem hbX_le {a : ℝ} (ha : 1 ≤ a) : hbX a ≤ a := by
  refine (hbX_le_sqrt (by linarith)).trans ?_
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

theorem hbL_ge {a : ℝ} : a ^ ((51 : ℝ) / 100) ≤ (hbL a : ℝ) := Nat.le_ceil _

theorem hbL_le {a : ℝ} (ha : 0 ≤ a) : (hbL a : ℝ) ≤ a ^ ((51 : ℝ) / 100) + 1 := by
  unfold hbL
  exact (Nat.ceil_lt_add_one (by positivity)).le

theorem hbL_pos {a : ℝ} (ha : 1 ≤ a) : 1 ≤ hbL a := by
  unfold hbL
  have : (0 : ℝ) < a ^ ((51 : ℝ) / 100) := by positivity
  exact Nat.ceil_pos.mpr this

theorem one_le_hbL_real {a : ℝ} (ha : 1 ≤ a) : (1 : ℝ) ≤ (hbL a : ℝ) := by
  exact_mod_cast hbL_pos ha

theorem hbN_le {U : ℝ} (hU : 0 ≤ U) : (hbN U : ℝ) ≤ U ^ ((1 : ℝ) / 20) := Nat.floor_le (by positivity)

theorem hbN_gt {U : ℝ} : U ^ ((1 : ℝ) / 20) - 1 < (hbN U : ℝ) := by
  unfold hbN
  linarith [Nat.lt_floor_add_one (U ^ ((1 : ℝ) / 20))]

theorem hbJ_ge {a U : ℝ} : a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) ≤ (hbJ a U : ℝ) := Nat.le_ceil _

theorem hbJ_le {a U : ℝ} (ha : 0 ≤ a) (hU : 0 ≤ U) :
    (hbJ a U : ℝ) ≤ a ^ ((3 : ℝ) / 10) * U ^ ((1 : ℝ) / 20) + 1 := by
  unfold hbJ
  exact (Nat.ceil_lt_add_one (by positivity)).le

/-! ### The single arithmetic input -/

/-- **The sharp-energy input.** For all large `U`, every displacement `0 < d ≤ ¼`, every block base
`1 ≤ a ≤ U` and every head length `u < L(a)`, the critical sharp-cutoff energy of the head of
length `u+1` against the displaced gate mollifier is at most `C`. -/
def SharpEnergyInput (C : ℝ) : Prop :=
  ∀ᶠ U in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 / 4 → ∀ a : ℝ, 1 ≤ a → a ≤ U →
    ∀ u ∈ Finset.range (hbL a),
      ∑ r : Fin (hbL a * hbN U),
        ‖Sieve.dirConv (hbL a) (hbN U) (sharpHead criticalHeadCoeff (hbL a) u)
          (fun m => highBlockMollifierCoeffNat d (hbCoeff (hbN U)) m) r‖ ^ 2 ≤ C

end

end RHTower
