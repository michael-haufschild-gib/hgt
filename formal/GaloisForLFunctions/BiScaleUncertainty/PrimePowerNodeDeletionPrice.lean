import GaloisForLFunctions.BiScaleUncertainty.PrimePowerZeroPoleNodeCriticality
import GaloisForLFunctions.RHTower.MarkovOriginBoundaryAbsorptionAndTrapezoidalPBAP

/-!
# The price of a node: deleting `m` from the prime-power blind cone costs exactly `Λ(m)/√m`

Write `A(c)` for the pole and archimedean energy of a nonnegative combination `c` of Weil tests
(`nodeArchEnergy`), `W(c)` for its full Weil functional with the von Mangoldt weights
(`weilEnergy`), `L_n(c)` for its node values and `‖c‖² = massOf c` for its mass. The identity
`A(c) = W(c) + Σ_n Λ(n) L_n(c)` is the explicit formula read on the prime side.

**The deletion law.** Let `m` be a prime power and let `c` be blind at every prime power except `m`.
* (`nodeArchEnergy_eq_weilEnergy_add_of_blindOn_deleted`) `A(c) = W(c) + Λ(m) L_m(c)`: every other
  node is either blind or carries `Λ = 0`.
* (`abs_nodeVector_le_massOf_div_sqrt`, the tower Fejér bound) `|L_m(c)| ≤ ‖c‖²/√m`. The powers
  `m^k`, `k ≥ 2`, are prime powers, hence blind; so the phase `r log m mod 2π` of the spectral density
  has exactly one free Fourier coefficient, and positivity of the phase measure
  `(∫G + 2a cos z) dz/2π` caps it at half the mass. Without the tower the cap would be `2‖c‖²/√m`.
* (`abs_nodeArchEnergy_sub_weilEnergy_le`) Hence `|A(c) − W(c)| ≤ (Λ(m)/√m) ‖c‖²`, and
  (`isLeast_deletionDeviations`, `isGreatest_deletionDeviations`) both ends are attained, by the
  narrow pair tests `h(u) ± h(u − log m)`: the exact range of `(A − W)/‖·‖²` on the cone is
  `[−Λ(m)/√m, Λ(m)/√m]`.

So the price of a node is its prime atom read through its own tower: `log 2 / 2` for `log 4`,
`log 3/√3` for `log 3`, and `0` for `log 6` and every integer that is not a prime power
(`nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers`: on the prime-power blind cone `A = W`
whatever the composite nodes do).

**Criterion** (`riemannHypothesis_iff_forall_zeroPoleBlindSymbolSlackOn_deleted`). RH holds iff,
for every prime power `m`, deleting `m` from the prime-power node set costs at most `Λ(m)/√m` of
zero-pole symbol slack. One direction is `W ≥ 0` plus the deletion law; for the other, the prices
of the nodes `4^k` are `log 2/2^k → 0`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- The prime powers. -/
abbrev primePowerNodes : Set ℕ := {n | IsPrimePow n}

/-- The full Weil functional of a combination, with the von Mangoldt weights and pole weight one. -/
def weilEnergy (c : WeilTestFn →₀ ℝ) : ℝ :=
  c.sum fun f t =>
    t * (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest f.1 f.1)).re

/-- The explicit formula on the prime side: `A(c) = W(c) + Σ_n Λ(n) L_n(c)`. -/
theorem nodeArchEnergy_eq_weilEnergy_add (c : WeilTestFn →₀ ℝ) :
    nodeArchEnergy c = weilEnergy c +
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (nodeVector c) := by
  rw [weilEnergy, sum_re_weilFullFunctional, nodeArchEnergy_eq, nodeVector_eq]
  ring

/-- **Composite nodes are free.** On the prime-power blind cone `A = W`. -/
theorem nodeArchEnergy_eq_weilEnergy_of_blindOn_primePowers {c : WeilTestFn →₀ ℝ}
    (hb : BlindOn primePowerNodes c) : nodeArchEnergy c = weilEnergy c := by
  rw [nodeArchEnergy_eq_weilEnergy_add, linearCombination_apply, Finsupp.sum,
    Finset.sum_eq_zero fun j _ => ?_, add_zero]
  by_cases hj : IsPrimePow (j : ℕ)
  · rw [hb j hj, zero_smul]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hj, smul_zero]

/-- **The deletion identity.** On the cone blind at every prime power except `m`,
`A(c) = W(c) + Λ(m) L_m(c)`. -/
theorem nodeArchEnergy_eq_weilEnergy_add_of_blindOn_deleted {c : WeilTestFn →₀ ℝ} {m : ℕ}
    (hm : 2 ≤ m) (hb : BlindOn (primePowerNodes \ {m}) c) :
    nodeArchEnergy c = weilEnergy c + ArithmeticFunction.vonMangoldt m * nodeVector c ⟨m, hm⟩ := by
  rw [nodeArchEnergy_eq_weilEnergy_add, linearCombination_apply,
    Finsupp.sum_eq_single (⟨m, hm⟩ : LogIndex) (fun j _ hj => ?_) (fun _ => zero_smul _ _),
    smul_eq_mul, mul_comm]
  by_cases hp : IsPrimePow (j : ℕ)
  · rw [hb j ⟨hp, fun h => hj (Subtype.ext h)⟩, zero_smul]
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, smul_zero]

/-- **The tower Fejér bound.** A nonnegative combination blind at every `m^k`, `k ≥ 2`, has
`|L_m(c)| ≤ ‖c‖²/√m`: one free Fourier coefficient of the phase measure is at most half the mass. -/
theorem abs_nodeVector_le_massOf_div_sqrt {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ}
    (hm : 2 ≤ m)
    (hb : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0) :
    |nodeVector c ⟨m, hm⟩| ≤ massOf c / Real.sqrt m := by
  have hcos : ∀ n : ℕ, 1 ≤ n → n ≠ 1 →
      ∫ r, combinationSpectralDensity c r * Real.cos (r * ((n : ℝ) * Real.log m)) = 0 := by
    intro n hn hn1
    rw [integral_combinationSpectralDensity_mul_cos_pow c hm hn, hb _ ⟨n, by omega, rfl⟩,
      mul_zero]
  have h1 := two_mul_abs_cos_moment_le_of_cos_blind_off (continuous_combinationSpectralDensity c)
    (combinationSpectralDensity_nonneg hc) (integrable_combinationSpectralDensity c) le_rfl hcos
  have e : (fun r => combinationSpectralDensity c r * Real.cos (r * (((1 : ℕ) : ℝ) * Real.log m))) =
      fun r => combinationSpectralDensity c r * Real.cos (r * Real.log m) := by
    funext r; rw [Nat.cast_one, one_mul]
  rw [e, integral_combinationSpectralDensity_mul_cos_log c hm,
    integral_combinationSpectralDensity] at h1
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hs] at h1
  rw [le_div_iff₀ hs]
  nlinarith [Real.pi_pos]

/-- The powers `m^k`, `k ≥ 2`, of a prime power are prime powers different from `m`. -/
theorem pow_mem_primePowerNodes_diff {m : ℕ} (hm : IsPrimePow m) {k : ℕ} (hk : 2 ≤ k) :
    m ^ k ∈ primePowerNodes \ {m} := by
  refine ⟨hm.pow (by omega), fun h => ?_⟩
  have h2 := hm.two_le
  have h1 : m ^ 2 ≤ m ^ k := Nat.pow_le_pow_right (by omega) hk
  rw [Set.mem_singleton_iff] at h
  nlinarith

/-- **The deletion law.** On the cone blind at every prime power except `m`,
`|A(c) − W(c)| ≤ (Λ(m)/√m) ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m : ℕ}
    (hm : IsPrimePow m) (hb : BlindOn (primePowerNodes \ {m}) c) :
    |nodeArchEnergy c - weilEnergy c| ≤
      ArithmeticFunction.vonMangoldt m / Real.sqrt m * massOf c := by
  rw [nodeArchEnergy_eq_weilEnergy_add_of_blindOn_deleted hm.two_le hb, add_sub_cancel_left,
    abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, div_mul_eq_mul_div, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left (abs_nodeVector_le_massOf_div_sqrt hc hm.two_le ?_)
    ArithmeticFunction.vonMangoldt_nonneg
  rintro j ⟨k, hk, hj⟩
  exact hb j (hj ▸ pow_mem_primePowerNodes_diff hm hk)

/-! ### Sharpness: the narrow pair tests -/

/-- The mass of a narrow pair test with `σ² = 1` is `2 ∫ h²`. -/
theorem massOf_single_pairTestFn {m : ℕ} (hm : 2 ≤ m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    massOf (Finsupp.single (pairTestFn m σ) 1) = 2 * ∫ t, (narrowBump m t) ^ 2 := by
  have hlog2 : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl2 := Real.log_pos one_lt_two
  have hsmall : 1 / (2 * ((m : ℝ) + 1)) < Real.log 2 := by
    refine lt_of_le_of_lt ?_ WeilExcess.seventeen_div_twentyfive_lt_log_two
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hk : EF.weilTest (pairTest m σ) (pairTest m σ) 0 = (((1 + σ ^ 2) * ∫ t, (narrowBump m t) ^ 2 : ℝ) : ℂ) := by
    rw [weilTest_pairTest, zero_add, zero_sub,
      weilTest_narrowBumpC_eq_zero m (Y := Real.log m) (by rw [abs_of_pos (by linarith)]; linarith),
      weilTest_narrowBumpC_eq_zero m (Y := -Real.log m)
        (by rw [abs_neg, abs_of_pos (by linarith)]; linarith), weilTest_narrowBumpC_zero]
    push_cast; ring
  have hmass : ∫ u, ‖pairTest m σ u‖ ^ 2 = (1 + σ ^ 2) * ∫ t, (narrowBump m t) ^ 2 := by
    have := RHTower.weilTest_zero_eq_integral_norm_sq (pairTest m σ)
    rw [hk] at this
    exact_mod_cast this.symm
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  change ∫ u, ‖pairTest m σ u‖ ^ 2 = _
  rw [hmass, hσ]; ring

/-- The narrow pair test is blind off `m` and has `L_m = σ ‖·‖²/√m`. -/
theorem nodeVector_single_pairTestFn {m : ℕ} (hm : 2 ≤ m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    nodeVector (Finsupp.single (pairTestFn m σ) 1) ⟨m, hm⟩ =
      σ * massOf (Finsupp.single (pairTestFn m σ) 1) / Real.sqrt m := by
  rw [nodeVector_single_test, logVector_pairTestFn ⟨m, hm⟩, Finsupp.single_eq_same,
    massOf_single_pairTestFn hm hσ]
  ring

theorem blindOn_single_pairTestFn {m : ℕ} (hm : 2 ≤ m) (σ : ℝ) (𝒩 : Set ℕ) (h𝒩 : m ∉ 𝒩) :
    BlindOn 𝒩 (Finsupp.single (pairTestFn m σ) 1) := fun j hj => by
  rw [nodeVector_single_test, logVector_pairTestFn ⟨m, hm⟩, Finsupp.single_apply,
    if_neg fun h => h𝒩 (by rw [← h] at hj; exact hj)]

/-- The normalized deviations `(A − W)/‖·‖²` on the cone blind at every prime power except `m`. -/
def deletionDeviations (m : ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ {m}) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem deviation_single_pairTestFn {m : ℕ} (hm : 2 ≤ m) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    σ * (ArithmeticFunction.vonMangoldt m / Real.sqrt m) ∈ deletionDeviations m := by
  classical
  have hpos : 0 < massOf (Finsupp.single (pairTestFn m σ) 1) := by
    rw [massOf_single_pairTestFn hm hσ]; linarith [integral_narrowBump_sq_pos m]
  refine ⟨_, fun f => ?_, blindOn_single_pairTestFn hm σ _ (by simp), hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [nodeArchEnergy_eq_weilEnergy_add_of_blindOn_deleted hm
      (blindOn_single_pairTestFn hm σ _ (by simp)), add_sub_cancel_left,
      nodeVector_single_pairTestFn hm hσ]
    field_simp

/-- **The price of deleting `m` is attained from below:** the least normalized deviation is
`−Λ(m)/√m`. -/
theorem isLeast_deletionDeviations {m : ℕ} (hm : IsPrimePow m) :
    IsLeast (deletionDeviations m) (-(ArithmeticFunction.vonMangoldt m / Real.sqrt m)) := by
  refine ⟨by simpa using deviation_single_pairTestFn hm.two_le (σ := -1) (by norm_num), ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le hc hm hb
  rw [le_div_iff₀ hpos]
  linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]

/-- The greatest normalized deviation is `Λ(m)/√m`. -/
theorem isGreatest_deletionDeviations {m : ℕ} (hm : IsPrimePow m) :
    IsGreatest (deletionDeviations m) (ArithmeticFunction.vonMangoldt m / Real.sqrt m) := by
  refine ⟨by simpa using deviation_single_pairTestFn hm.two_le (σ := 1) (by norm_num), ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le hc hm hb
  rw [div_le_iff₀ hpos]
  linarith [le_abs_self (nodeArchEnergy c - weilEnergy c)]

/-- `log 4` costs `log 2 / 2`. -/
theorem isLeast_deletionDeviations_four :
    IsLeast (deletionDeviations 4) (-(Real.log 2 / 2)) := by
  have h := isLeast_deletionDeviations (m := 4) (by decide)
  have hΛ : (ArithmeticFunction.vonMangoldt 4 : ℝ) = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hs : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [hΛ, hs] at h

/-! ### The criterion -/

/-- **RH is the bound on all deletion prices.** RH holds iff for every prime power `m`, the zero-pole
symbol slack on the prime powers other than `m` is at most `Λ(m)/√m`. -/
theorem riemannHypothesis_iff_forall_zeroPoleBlindSymbolSlackOn_deleted :
    RiemannHypothesis ↔ ∀ m : ℕ, IsPrimePow m →
      ZeroPoleBlindSymbolSlackOn (primePowerNodes \ {m})
        (ArithmeticFunction.vonMangoldt m / Real.sqrt m) := by
  constructor
  · intro hRH m hm c hc hb _
    have hW : 0 ≤ weilEnergy c :=
      sum_nonneg_of_weilPositiveFull (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc
    have h := abs_nodeArchEnergy_sub_weilEnergy_le hc hm hb
    linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]
  · intro h
    refine riemannHypothesis_iff_zeroPoleBlindPositiveOn_primePowers.mpr fun c hc hb hp => ?_
    -- the nodes `4^k = 2^(2k)` cost `log 2 / 2^k`
    have hk : ∀ k : ℕ, 0 ≤ nodeArchEnergy c + Real.log 2 * massOf c * (1 / 2) ^ (k + 1) := by
      intro k
      have hm : IsPrimePow (2 ^ (2 * (k + 1))) := Nat.prime_two.isPrimePow.pow (by omega)
      have h1 := h _ hm c hc (fun j hj => hb j hj.1) hp
      have hΛ : (ArithmeticFunction.vonMangoldt (2 ^ (2 * (k + 1))) : ℝ) = Real.log 2 := by
        rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num
      have hs : Real.sqrt ((2 ^ (2 * (k + 1)) : ℕ) : ℝ) = 2 ^ (k + 1) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show 2 * (k + 1) = (k + 1) * 2 by ring, pow_mul,
          Real.sqrt_sq (by positivity)]
      rw [hΛ, hs] at h1
      have e : Real.log 2 / 2 ^ (k + 1) * massOf c =
          Real.log 2 * massOf c * (1 / 2) ^ (k + 1) := by
        rw [one_div_pow]; field_simp
      linarith
    have hlim : Tendsto (fun k : ℕ => nodeArchEnergy c + Real.log 2 * massOf c * (1 / 2) ^ (k + 1))
        atTop (𝓝 (nodeArchEnergy c)) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)).const_mul (Real.log 2 * massOf c)
      simpa using tendsto_const_nhds.add this
    exact ge_of_tendsto' hlim hk

end

end GaloisForLFunctions.BiScaleUncertainty
