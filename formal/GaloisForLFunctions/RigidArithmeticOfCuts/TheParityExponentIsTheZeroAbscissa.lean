import GaloisForLFunctions.RigidArithmeticOfCuts.AParityBoundConfinesTheZeros
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheOneFifthRateUnderTheRiemannHypothesis
import GaloisForLFunctions.ArithmeticProduction.TypeIInformationIsParityBlind
import GaloisForLFunctions.RHTower.NymanBeurlingCriterion

/-!
# The parity exponent is the zero abscissa

The parity ledger of a stencil is its Type I correlation with `λ`:

`P_c(x) = Σ_k c(k) λ(k) L(⌊x/k⌋) = Σ_{n ≤ x} λ(n) h(n)`, with `h = 1 ∗ c` the increment
(`parityLedger_eq_sum_liouville_mul_increment`).

So a parity input is a bound for this correlation, and the question is what source can give one. The two ends are now both exact.

* **At log powers there is a source.** Vinogradov–Korobov gives `P_c(x) ≪_c x/log^k x` for every `k`, unconditionally
  (`exists_abs_parityLedger_le_log`).
* **At a power saving the source is the conclusion.** For `½ ≤ Θ < 1`, `L(x) ≪ x^a` for every `a > Θ` iff `ζ` has no zero with
  `Re s > Θ` (`zeroFree_iff_liouville_power`). In particular RH is the square-root law for `L`
  (`riemannHypothesis_iff_liouville_power`). For a general stencil a zero-free strip gives the bound with the same exponent
  (`exists_parityLedger_power_of_zeroFree`), and conversely a bound confines zeros to zeros of the twist `D_{cλ}`.

Hence no independent parity source at any power saving can exist: any such source would be a zero-free strip, up to the zeros a
twist absorbs.
-/

open Finset Filter Topology
open ArithmeticFunction (moebius)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

theorem mertensR_eq_mertensM (n : ℕ) : mertensR n = _root_.RHTower.Sieve.mertensM n := by
  rw [mertensR, _root_.RHTower.Sieve.mertensM]
  refine sum_subset (fun j hj => ?_) fun j hj hj' => ?_
  · have := (mem_Ioc.mp hj).2
    exact mem_range.mpr (by omega)
  · have h0 : j = 0 := by
      by_contra h0
      have := mem_range.mp hj
      exact hj' (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, by omega⟩)
    simp [h0]

/-- The parity ledger is the Type I correlation of `λ` with the increment of the stencil. -/
theorem parityLedger_eq_sum_liouville_mul_increment {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (x : ℕ) :
    parityLedger c x =
      ∑ n ∈ Icc 1 x, (ArithmeticFunction.liouville n : ℝ) * (increment c n : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (sum_Icc_liouville_mul_increment hc0 x)
  simp only [Int.cast_sum, Int.cast_mul] at h
  rw [h, parityLedger]
  refine sum_congr rfl fun k _ => ?_
  rw [liouvilleR_eq]

private lemma summable_rpow {a : ℝ} (ha : 1 / 2 < a) : Summable fun d : ℕ => (d : ℝ) ^ (-(2 * a)) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- **A power law for `M` is a power law for `L`, with the same exponent.** -/
theorem abs_liouvilleR_le_of_power {C a : ℝ} (hC : 0 ≤ C) (ha : 1 / 2 < a)
    (hM : ∀ y : ℕ, 1 ≤ y → |mertensR y| ≤ C * (y : ℝ) ^ a) (x : ℕ) :
    |liouvilleR x| ≤ C * (∑' d : ℕ, (d : ℝ) ^ (-(2 * a))) * (x : ℝ) ^ a := by
  have ha0 : 0 < a := by linarith
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  rw [liouvilleR_eq_squareMertens, squareMertens]
  have hterm : ∀ d ∈ Ioc 0 (Nat.sqrt x), |mertensR (x / (d * d))| ≤
      C * (x : ℝ) ^ a * (d : ℝ) ^ (-(2 * a)) := by
    intro d hd
    obtain ⟨hd0, hdx⟩ := mem_Ioc.mp hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hsq : d * d ≤ x := Nat.le_sqrt.mp hdx
    have hy : 1 ≤ x / (d * d) := (Nat.one_le_div_iff (Nat.mul_pos hd0 hd0)).mpr hsq
    have hdiv : ((x / (d * d) : ℕ) : ℝ) ≤ (x : ℝ) / ((d : ℝ) * d) := by
      have := Nat.cast_div_le (α := ℝ) (m := x) (n := d * d)
      push_cast at this
      exact this
    have hpow : ((x / (d * d) : ℕ) : ℝ) ^ a ≤ ((x : ℝ) / ((d : ℝ) * d)) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hdiv ha0.le
    have hsplit : ((x : ℝ) / ((d : ℝ) * d)) ^ a = (x : ℝ) ^ a * (d : ℝ) ^ (-(2 * a)) := by
      rw [Real.div_rpow hx0 (by positivity), div_eq_mul_inv, ← sq, ← Real.rpow_natCast (d : ℝ) 2,
        ← Real.rpow_mul hdR.le, ← Real.rpow_neg hdR.le]
      norm_num
    calc |mertensR (x / (d * d))| ≤ C * ((x / (d * d) : ℕ) : ℝ) ^ a := hM _ hy
      _ ≤ C * ((x : ℝ) ^ a * (d : ℝ) ^ (-(2 * a))) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by ring
  have hsum : ∑ d ∈ Ioc 0 (Nat.sqrt x), (d : ℝ) ^ (-(2 * a)) ≤ ∑' d : ℕ, (d : ℝ) ^ (-(2 * a)) :=
    (summable_rpow ha).sum_le_tsum _ fun d _ => by positivity
  calc _ ≤ ∑ d ∈ Ioc 0 (Nat.sqrt x), |mertensR (x / (d * d))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Ioc 0 (Nat.sqrt x), C * (x : ℝ) ^ a * (d : ℝ) ^ (-(2 * a)) := sum_le_sum hterm
    _ = C * (x : ℝ) ^ a * ∑ d ∈ Ioc 0 (Nat.sqrt x), (d : ℝ) ^ (-(2 * a)) := by rw [mul_sum]
    _ ≤ C * (x : ℝ) ^ a * ∑' d : ℕ, (d : ℝ) ^ (-(2 * a)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A zero-free strip gives a power law for `L`, for every exponent above the strip. -/
theorem exists_liouville_power_of_zeroFree {Θ a : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (ha : Θ < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, |liouvilleR x| ≤ C * (x : ℝ) ^ a := by
  have hσ0 : 0 < 1 - a := by linarith
  obtain ⟨C, hC, hM⟩ := exists_mertens_power_of_zeroFree hΘ hΘ1 hzf hσ0 (by linarith)
  have hval : (1 : ℝ) - (1 - a) = a := by ring
  rw [hval] at hM
  have ha2 : 1 / 2 < a := by linarith
  refine ⟨C * ∑' d : ℕ, (d : ℝ) ^ (-(2 * a)), mul_nonneg hC (tsum_nonneg fun d => by positivity), ?_⟩
  exact abs_liouvilleR_le_of_power hC ha2 fun y hy => by
    rw [mertensR_eq_mertensM]
    exact hM y hy

/-- **The parity exponent is the zero abscissa.** For `½ ≤ Θ < 1`, `ζ` has no zero with `Re s > Θ` iff `L(x) ≪ x^a` for every
`a > Θ`. -/
theorem zeroFree_iff_liouville_power {Θ : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1) :
    (∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) ↔
      ∀ a : ℝ, Θ < a → a < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x → |liouvilleR x| ≤ C * (x : ℝ) ^ a := by
  constructor
  · intro hzf a ha ha1
    obtain ⟨C, hC, h⟩ := exists_liouville_power_of_zeroFree hΘ hΘ1 hzf ha ha1
    exact ⟨C, hC, fun x _ => h x⟩
  · intro h s hs
    by_cases hs1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hs1
    · push Not at hs1
      obtain ⟨C, hC, hL⟩ := h ((Θ + s.re) / 2) (by linarith) (by linarith)
      refine riemannZeta_ne_zero_of_liouville_bound hC hL (fun h1 => ?_) (by linarith) (by linarith)
      rw [h1] at hs1
      simp at hs1

/-- **RH is the square-root law for `L`.** -/
theorem riemannHypothesis_iff_liouville_power :
    RiemannHypothesis ↔ ∀ a : ℝ, 1 / 2 < a → a < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 1 ≤ x → |liouvilleR x| ≤ C * (x : ℝ) ^ a := by
  rw [← zeroFree_iff_liouville_power le_rfl (by norm_num)]
  constructor
  · intro hRH s hs hz
    have hne : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      have him : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      rw [him] at hs
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h1 : s ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hz)
    have := hRH s hz hne h1
    linarith
  · intro h
    by_contra hRH
    obtain ⟨ρ, hzero, hρ, -⟩ := _root_.RHTower.exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    exact h ρ hρ hzero

/-- **A zero-free strip bounds every parity ledger, at the exponent of the strip.** -/
theorem exists_parityLedger_power_of_zeroFree {Θ a : ℝ} (hΘ : 1 / 2 ≤ Θ) (hΘ1 : Θ < 1)
    (hzf : ∀ s : ℂ, Θ < s.re → riemannZeta s ≠ 0) (ha : Θ < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℕ →₀ ℤ, c 0 = 0 → ∀ x : ℕ,
      |parityLedger c x| ≤ C * (∑ k ∈ c.support, |(c k : ℝ)| * (k : ℝ) ^ (-a)) * (x : ℝ) ^ a := by
  obtain ⟨C, hC, hL⟩ := exists_liouville_power_of_zeroFree hΘ hΘ1 hzf ha ha1
  have ha0 : 0 < a := by linarith
  refine ⟨C, hC, fun c hc0 x => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  rw [parityLedger, mul_assoc, sum_mul, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
    subst h
    exact Finsupp.mem_support_iff.mp hk hc0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hlam : |(ArithmeticFunction.liouville k : ℝ)| = 1 := by
    rw [ArithmeticFunction.liouville_apply hk0.ne']
    push_cast
    simp
  have hdiv : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / k := Nat.cast_div_le
  have hpow : ((x / k : ℕ) : ℝ) ^ a ≤ (x : ℝ) ^ a * (k : ℝ) ^ (-a) := by
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hdiv ha0.le
    rwa [Real.div_rpow hx0 hkR.le, div_eq_mul_inv, ← Real.rpow_neg hkR.le] at h1
  rw [abs_mul, abs_mul, hlam, one_mul]
  have h2 : |liouvilleR (x / k)| ≤ C * ((x : ℝ) ^ a * (k : ℝ) ^ (-a)) :=
    (hL _).trans (mul_le_mul_of_nonneg_left hpow hC)
  calc |(c k : ℝ)| * |liouvilleR (x / k)|
      ≤ |(c k : ℝ)| * (C * ((x : ℝ) ^ a * (k : ℝ) ^ (-a))) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by ring

theorem liouvilleR_eq_liouvilleCount (N : ℕ) :
    liouvilleR N = ArithmeticProduction.liouvilleCount N := by
  rw [liouvilleR, ArithmeticProduction.liouvilleCount]
  have hset : Ioc 0 N = Icc 1 N := by
    ext j
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hset]
  refine sum_congr rfl fun j _ => ?_
  simp [ArithmeticProduction.lam, _root_.RHTower.liouvilleR]

/-- **The unconditional parity source.** Every parity ledger is `≪ x/log^k x`, for every `k`, from Vinogradov–Korobov. -/
theorem exists_abs_parityLedger_le_log {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (e : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℕ in atTop, |parityLedger c x| ≤ K * x / Real.log x ^ e := by
  obtain ⟨K₀, hK₀, hL⟩ := ArithmeticProduction.exists_abs_liouvilleCount_le e
  refine ⟨K₀ * 2 ^ e * ∑ k ∈ c.support, |(c k : ℝ)| / k, by positivity, ?_⟩
  have hev : ∀ᶠ x : ℕ in atTop, ∀ k ∈ c.support, |liouvilleR (x / k)| ≤
      K₀ * 2 ^ e * ((x : ℝ) / k) / Real.log x ^ e := by
    refine (Filter.eventually_all_finset _).mpr fun k hk => ?_
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h
      exact Finsupp.mem_support_iff.mp hk hc0
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have htend : Tendsto (fun x : ℕ => x / k) atTop atTop := Nat.tendsto_div_const_atTop hk0.ne'
    filter_upwards [htend.eventually hL, eventually_ge_atTop (4 * k * k), eventually_ge_atTop 3] with
      x hx hxk hx3
    have hxR : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    -- `⌊x/k⌋ ≥ √x`, so its logarithm is at least `½ log x`.
    have h2 : 2 * k ≤ x / k := by
      rw [Nat.le_div_iff_mul_le hk0]
      nlinarith
    have hsq : x ≤ (x / k) ^ 2 := by
      have h1 : x < k * (x / k + 1) := Nat.lt_mul_div_succ x hk0
      nlinarith
    have hq1 : 1 < x / k := by omega
    have hqR : (1 : ℝ) < ((x / k : ℕ) : ℝ) := by exact_mod_cast hq1
    have hlogq : Real.log x / 2 ≤ Real.log ((x / k : ℕ) : ℝ) := by
      have h3 : Real.log x ≤ Real.log (((x / k : ℕ) : ℝ) ^ 2) :=
        Real.log_le_log hxR (by exact_mod_cast hsq)
      rw [Real.log_pow] at h3
      push_cast at h3
      linarith
    have hpow : (Real.log x / 2) ^ e ≤ Real.log ((x / k : ℕ) : ℝ) ^ e :=
      pow_le_pow_left₀ (by positivity) hlogq e
    have hpos : 0 < (Real.log x / 2) ^ e := by positivity
    have hdiv : ((x / k : ℕ) : ℝ) ≤ (x : ℝ) / k := Nat.cast_div_le
    rw [liouvilleR_eq_liouvilleCount]
    calc _ ≤ K₀ * ((x / k : ℕ) : ℝ) / Real.log ((x / k : ℕ) : ℝ) ^ e := hx
      _ ≤ K₀ * ((x : ℝ) / k) / (Real.log x / 2) ^ e :=
          div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hdiv hK₀) hpos hpow
      _ = _ := by
          rw [div_pow]
          field_simp
  filter_upwards [hev, eventually_ge_atTop 3] with x hx hx3
  have hxR : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  rw [parityLedger]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ c.support, |(c k : ℝ) * ((ArithmeticFunction.liouville k : ℝ) * liouvilleR (x / k))| ≤
      (|(c k : ℝ)| / k) * (K₀ * 2 ^ e * x / Real.log x ^ e) := by
    intro k hk
    have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by
      subst h
      exact Finsupp.mem_support_iff.mp hk hc0
    have hlam : |(ArithmeticFunction.liouville k : ℝ)| = 1 := by
      rw [ArithmeticFunction.liouville_apply hk0.ne']
      push_cast
      simp
    rw [abs_mul, abs_mul, hlam, one_mul]
    calc |(c k : ℝ)| * |liouvilleR (x / k)|
        ≤ |(c k : ℝ)| * (K₀ * 2 ^ e * ((x : ℝ) / k) / Real.log x ^ e) :=
          mul_le_mul_of_nonneg_left (hx k hk) (abs_nonneg _)
      _ = _ := by ring
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← sum_mul]
  ring

end GaloisForLFunctions.RigidArithmeticOfCuts
