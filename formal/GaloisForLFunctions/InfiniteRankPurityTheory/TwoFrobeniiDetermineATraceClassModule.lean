import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansReadTheModesOfASummableTower
import GaloisForLFunctions.HTGeometry.WeldClassTable

/-!
# Two Frobenii determine a trace-class module

A **Frobenius module over `ℤ`** is a family of modes `ρ_i ∈ ℂ` with weights `c_i`; the Frobenius at
`n` acts on the mode `ρ_i` by `n^{ρ_i}`, and its trace is `t(n) = Σ_i c_i n^{ρ_i}`. The weight of a
mode is `Re ρ_i`. The module is of trace class when `Σ ‖c_i‖ < ∞`; its rank is arbitrary.

**Theorem** (`re_le_of_frobTrace_bound`, `frobTrace_bound_iff`). Let the modes be distinct, the
weights summable, and let the set of weights have no infinite ascending chain. Then
`‖t(n)‖ ≤ C n^s` for all large `n` exactly when every visible mode has weight `≤ s`: the weight
filtration of the module is its filtration by the growth of the traces. In particular a trace that
vanishes at all large integers has all weights `c_i` zero (`eq_zero_of_frobTrace_eventually_zero`).
Only the integers `2^a 3^b` are used.

**Proof.** Take the largest weight `σ` that carries a nonzero `c_i`, and suppose `s < σ`. Dividing the
trace at `2^a 3^b` by `(2^a 3^b)^σ` leaves a tower in two parameters whose modes `2^{ρ_i − σ}`,
`3^{ρ_i − σ}` lie in the closed unit disc and whose level sums tend to zero in `a`. A Cesàro mean in
`a` isolates the modes with `2^{ρ_i} = 2^{ρ_{i₀}}`, a second one in `b` those with also
`3^{ρ_i} = 3^{ρ_{i₀}}`. Since `log 2 / log 3` is irrational the two conditions force `ρ_i = ρ_{i₀}`, so
the mean is `c_{i₀}`, and it is zero.

The Frobenius at one prime sees a mode only modulo `2πi / log p`; two primes separate all modes.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*}

/-- The trace of the Frobenius at `x` on the module with modes `ρ` and weights `b`:
`t(x) = Σ_i b_i x^{ρ_i}`. -/
noncomputable def frobTrace (b ρ : ι → ℂ) (x : ℝ) : ℂ := ∑' i, b i * (x : ℂ) ^ ρ i

/-- The weights `Re ρ_i` have no infinite ascending chain: every nonempty set of weights has a
greatest element. -/
def WeightsWellFounded (ρ : ι → ℂ) : Prop :=
  ∀ S : Set ℝ, S ⊆ Set.range (fun i => (ρ i).re) → S.Nonempty → ∃ σ ∈ S, ∀ τ ∈ S, τ ≤ σ

/-! ### Powers of `2` and `3` -/

theorem norm_two_cpow (s : ℂ) : ‖(2 : ℂ) ^ s‖ = (2 : ℝ) ^ s.re := by
  simpa using Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 2) s

theorem norm_three_cpow (s : ℂ) : ‖(3 : ℂ) ^ s‖ = (3 : ℝ) ^ s.re := by
  simpa using Complex.norm_natCast_cpow_of_pos (by norm_num : 0 < 3) s

/-- `(p^a)^ρ = (p^ρ)^a` for a natural base. -/
theorem natCast_pow_cpow (p a : ℕ) (ρ : ℂ) : ((p ^ a : ℕ) : ℂ) ^ ρ = ((p : ℂ) ^ ρ) ^ a := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- **The Frobenii at `2` and `3` separate the modes.** -/
theorem cpow_two_three_injective {s t : ℂ} (h2 : (2 : ℂ) ^ s = (2 : ℂ) ^ t)
    (h3 : (3 : ℂ) ^ s = (3 : ℂ) ^ t) : s = t := by
  have l2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have e2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]
    norm_num
  have e3 : Complex.log (3 : ℂ) = (Real.log 3 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]
    norm_num
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num), e2,
    Complex.exp_eq_exp_iff_exists_int] at h2
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num), e3,
    Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨k, hk⟩ := h2
  obtain ⟨l, hl⟩ := h3
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hrel : (k : ℂ) * (Real.log 3 : ℂ) = (l : ℂ) * (Real.log 2 : ℂ) := by
    apply mul_right_cancel₀ hpi
    linear_combination -(Real.log 3 : ℂ) * hk + (Real.log 2 : ℂ) * hl
  have hreal : (k : ℝ) * Real.log ((3 : ℕ) : ℝ) + ((-l : ℤ) : ℝ) * Real.log ((2 : ℕ) : ℝ) = 0 := by
    have h := congrArg Complex.re hrel
    simp only [Complex.mul_re, Complex.intCast_re, Complex.ofReal_re, Complex.intCast_im,
      Complex.ofReal_im, mul_zero, sub_zero] at h
    push_cast
    linarith
  obtain ⟨hk0, -⟩ := GaloisForLFunctions.RHTower.two_prime_log_indep Nat.prime_three
    Nat.prime_two (by norm_num) k (-l) hreal
  rw [hk0] at hk
  have hne : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast l2.ne'
  apply mul_left_cancel₀ hne
  simpa using hk

/-! ### The trace at the integers `2^a 3^b` -/

/-- `t(2^a 3^b) = Σ_i c_i (2^{ρ_i})^a (3^{ρ_i})^b`. -/
theorem frobTrace_two_pow_mul_three_pow (c ρ : ι → ℂ) (a b : ℕ) :
    frobTrace c ρ ((2 ^ a * 3 ^ b : ℕ) : ℝ) =
      ∑' i, c i * ((2 : ℂ) ^ ρ i) ^ a * ((3 : ℂ) ^ ρ i) ^ b := by
  rw [frobTrace]
  refine tsum_congr fun i => ?_
  rw [Complex.ofReal_natCast, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, natCast_pow_cpow,
    natCast_pow_cpow]
  norm_num
  ring

/-- **The growth of the trace bounds the weights.** Distinct modes, summable weights, weights
without an infinite ascending chain: if `‖t(n)‖ ≤ C n^s` at all large integers, every visible mode
has weight `≤ s`. Only the integers `2^a 3^b` are used. -/
theorem re_le_of_frobTrace_bound {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) {s C : ℝ} {n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) :
    ∀ i, c i ≠ 0 → (ρ i).re ≤ s := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₁, hi₁c, hi₁s⟩ := hcon
  -- the top visible weight
  set S : Set ℝ := {σ | ∃ i, (ρ i).re = σ ∧ c i ≠ 0} with hS
  have hSsub : S ⊆ Set.range (fun i => (ρ i).re) := by
    rintro σ ⟨i, hi, -⟩
    exact ⟨i, hi⟩
  have hSne : S.Nonempty := ⟨(ρ i₁).re, i₁, rfl, hi₁c⟩
  obtain ⟨σ, ⟨i₀, hi₀σ, hi₀c⟩, hmax⟩ := hwf S hSsub hSne
  have hsσ : s < σ := lt_of_lt_of_le hi₁s (hmax _ ⟨i₁, rfl, hi₁c⟩)
  have habove : ∀ i, σ < (ρ i).re → c i = 0 := by
    intro i hlt
    by_contra hne
    have := hmax (ρ i).re ⟨i, rfl, hne⟩
    linarith
  -- the normalized modes
  have hr2 : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
  have hr3 : (0 : ℝ) < (3 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
  set r2 : ℂ := (((2 : ℝ) ^ σ : ℝ) : ℂ) with hr2def
  set r3 : ℂ := (((3 : ℝ) ^ σ : ℝ) : ℂ) with hr3def
  have hr2C : r2 ≠ 0 := by rw [hr2def]; exact_mod_cast hr2.ne'
  have hr3C : r3 ≠ 0 := by rw [hr3def]; exact_mod_cast hr3.ne'
  have hr2n : ‖r2‖ = (2 : ℝ) ^ σ := by
    rw [hr2def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
  have hr3n : ‖r3‖ = (3 : ℝ) ^ σ := by
    rw [hr3def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr3]
  set U : ι → ℂ := fun i => if (ρ i).re ≤ σ then (2 : ℂ) ^ ρ i / r2 else 1 with hU
  set V : ι → ℂ := fun i => if (ρ i).re ≤ σ then (3 : ℂ) ^ ρ i / r3 else 1 with hV
  have hU1 : ∀ i, ‖U i‖ ≤ 1 := by
    intro i
    rw [hU]
    simp only
    split_ifs with h
    · rw [norm_div, norm_two_cpow, hr2n, div_le_one hr2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    · simp
  have hV1 : ∀ i, ‖V i‖ ≤ 1 := by
    intro i
    rw [hV]
    simp only
    split_ifs with h
    · rw [norm_div, norm_three_cpow, hr3n, div_le_one hr3]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h
    · simp
  have hUi₀ : U i₀ = (2 : ℂ) ^ ρ i₀ / r2 := by
    rw [hU]
    simp only
    rw [if_pos hi₀σ.le]
  have hVi₀ : V i₀ = (3 : ℂ) ^ ρ i₀ / r3 := by
    rw [hV]
    simp only
    rw [if_pos hi₀σ.le]
  have hUn : ‖U i₀‖ = 1 := by
    rw [hUi₀, norm_div, norm_two_cpow, hr2n, hi₀σ, div_self hr2.ne']
  have hVn : ‖V i₀‖ = 1 := by
    rw [hVi₀, norm_div, norm_three_cpow, hr3n, hi₀σ, div_self hr3.ne']
  -- the trace at `2^a 3^b`, normalized
  have hW : ∀ a b : ℕ, frobTrace c ρ ((2 ^ a * 3 ^ b : ℕ) : ℝ) =
      r2 ^ a * r3 ^ b * ∑' i, c i * V i ^ b * U i ^ a := by
    intro a b
    rw [frobTrace_two_pow_mul_three_pow, ← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [hU, hV]
    simp only
    by_cases h : (ρ i).re ≤ σ
    · rw [if_pos h, if_pos h, div_pow, div_pow]
      field_simp
    · rw [habove i (lt_of_not_ge h)]
      simp
  -- for fixed `b` the normalized trace tends to zero in `a`
  have hsmall : ∀ b : ℕ,
      Tendsto (fun a : ℕ => ∑' i, c i * V i ^ b * U i ^ a) atTop (𝓝 0) := by
    intro b
    set κ : ℝ := (2 : ℝ) ^ (s - σ) with hκ
    have hκ0 : 0 ≤ κ := (Real.rpow_pos_of_pos (by norm_num) _).le
    have hκ1 : κ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    set K : ℝ := |C| * (3 : ℝ) ^ ((s - σ) * b) with hK
    have hgeom : Tendsto (fun a : ℕ => K * κ ^ a) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).const_mul K
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgeom
      (Eventually.of_forall fun a => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop n₀] with a ha
    have hn : n₀ ≤ 2 ^ a * 3 ^ b := by
      calc n₀ ≤ a := ha
        _ ≤ 2 ^ a := Nat.lt_two_pow_self.le
        _ = 2 ^ a * 1 := (mul_one _).symm
        _ ≤ 2 ^ a * 3 ^ b := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by norm_num))
    have h := h0 _ hn
    rw [hW a b, norm_mul, norm_mul, norm_pow, norm_pow, hr2n, hr3n] at h
    -- exponents as real powers
    have e2 : ((2 : ℝ) ^ σ) ^ a = (2 : ℝ) ^ (σ * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have e3 : ((3 : ℝ) ^ σ) ^ b = (3 : ℝ) ^ (σ * b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have en : (((2 ^ a * 3 ^ b : ℕ) : ℝ)) ^ s = (2 : ℝ) ^ (a * s) * (3 : ℝ) ^ (b * s) := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
    have eκ : κ ^ a = (2 : ℝ) ^ ((s - σ) * a) := by
      rw [hκ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [e2, e3, en] at h
    have hfac : (0 : ℝ) < (2 : ℝ) ^ (σ * a) * (3 : ℝ) ^ (σ * b) := by positivity
    refine le_of_mul_le_mul_left ?_ hfac
    have hsplit : (2 : ℝ) ^ (σ * a) * (3 : ℝ) ^ (σ * b) * (K * κ ^ a) =
        |C| * ((2 : ℝ) ^ (a * s) * (3 : ℝ) ^ (b * s)) := by
      rw [hK, eκ]
      have h2 : (2 : ℝ) ^ (σ * a) * (2 : ℝ) ^ ((s - σ) * a) = (2 : ℝ) ^ (a * s) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      have h3 : (3 : ℝ) ^ (σ * b) * (3 : ℝ) ^ ((s - σ) * b) = (3 : ℝ) ^ (b * s) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
      rw [← h2, ← h3]
      ring
    rw [hsplit]
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  -- a Cesàro mean in `a` isolates the modes with `2^{ρ_i} = 2^{ρ_{i₀}}`
  have hM : ∀ b : ℕ, (∑' i, if U i = U i₀ then c i * V i ^ b else 0) = 0 := by
    intro b
    have hs : Summable fun i => ‖c i * V i ^ b‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_towerTerm_le hV1 b) hc
    have h0' : Tendsto (towerSum (fun i => c i * V i ^ b) U) atTop (𝓝 0) := hsmall b
    exact merged_eq_zero_of_tendsto_zero hs hU1 h0' hUn
  -- a Cesàro mean in `b` isolates those with also `3^{ρ_i} = 3^{ρ_{i₀}}`
  have hs2 : Summable fun i => ‖(if U i = U i₀ then c i else 0 : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hc
    split_ifs <;> simp
  have h0'' : Tendsto (towerSum (fun i => if U i = U i₀ then c i else 0) V) atTop (𝓝 0) := by
    have hfun : towerSum (fun i => if U i = U i₀ then c i else 0) V = fun _ => 0 := by
      funext b
      have hcongr : (∑' i, (if U i = U i₀ then c i else 0) * V i ^ b) =
          ∑' i, if U i = U i₀ then c i * V i ^ b else 0 := by
        refine tsum_congr fun i => ?_
        split_ifs <;> simp
      rw [towerSum, hcongr, hM b]
    rw [hfun]
    exact tendsto_const_nhds
  have hfinal := merged_eq_zero_of_tendsto_zero hs2 hV1 h0'' hVn
  -- only `i₀` survives
  have hsingle : (∑' i, if V i = V i₀ then (if U i = U i₀ then c i else 0) else 0) = c i₀ := by
    have hterm : ∀ i, (if V i = V i₀ then (if U i = U i₀ then c i else 0) else 0) =
        if i = i₀ then c i else 0 := by
      intro i
      by_cases hi : i = i₀
      · rw [hi]
        simp
      · rw [if_neg hi]
        by_cases hci : c i = 0
        · rw [hci]
          split_ifs <;> rfl
        · have hle : (ρ i).re ≤ σ := not_lt.mp fun h => hci (habove i h)
          have hnot : ¬ (U i = U i₀ ∧ V i = V i₀) := by
            rintro ⟨hu, hv⟩
            rw [hUi₀, hU] at hu
            rw [hVi₀, hV] at hv
            simp only [if_pos hle] at hu hv
            have h2 : (2 : ℂ) ^ ρ i = (2 : ℂ) ^ ρ i₀ := by
              field_simp at hu
              exact hu
            have h3 : (3 : ℂ) ^ ρ i = (3 : ℂ) ^ ρ i₀ := by
              field_simp at hv
              exact hv
            exact hi (hρ (cpow_two_three_injective h2 h3))
          by_cases hv : V i = V i₀
          · have hu : U i ≠ U i₀ := fun hu => hnot ⟨hu, hv⟩
            rw [if_pos hv, if_neg hu]
          · rw [if_neg hv]
    rw [tsum_congr hterm, tsum_ite_eq]
  rw [hsingle] at hfinal
  exact hi₀c hfinal

/-- **Two Frobenii determine a trace-class module.** Distinct modes, summable weights, weights
without an infinite ascending chain: if the trace vanishes at all large integers, every weight
vanishes. -/
theorem eq_zero_of_frobTrace_eventually_zero {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) {n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → frobTrace c ρ n = 0) : ∀ i, c i = 0 := by
  intro i
  by_contra hne
  have h := re_le_of_frobTrace_bound hc hρ hwf (s := (ρ i).re - 1) (C := 0) (n₀ := n₀)
    (fun n hn => by rw [h0 n hn]; simp) i hne
  linarith

/-- **The weight filtration is the growth filtration.** For distinct modes, summable weights and
weights without an infinite ascending chain: the trace is `O(n^s)` at the integers exactly when
every visible mode has weight `≤ s`. -/
theorem frobTrace_bound_iff {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hρ : Function.Injective ρ) (hwf : WeightsWellFounded ρ) (s : ℝ) :
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) ↔
      ∀ i, c i ≠ 0 → (ρ i).re ≤ s := by
  constructor
  · rintro ⟨C, n₀, h⟩
    exact re_le_of_frobTrace_bound hc hρ hwf h
  · intro hle
    refine ⟨∑' i, ‖c i‖, 1, fun n hn => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [frobTrace, ← tsum_mul_right]
    refine tsum_of_norm_bounded (hc.mul_right _).hasSum fun i => ?_
    by_cases hci : c i = 0
    · simp [hci]
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (hle i hci)) (norm_nonneg _)

end GaloisForLFunctions.InfiniteRankPurityTheory
