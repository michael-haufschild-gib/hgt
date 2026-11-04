import GaloisForLFunctions.ArithmeticGaugeTheory.ThePoleDoesNotDecideTheHalfPowerLaw
import GaloisForLFunctions.RHTower.DirichletUniformAbel
import GaloisForLFunctions.RHTower.DirichletPolyBoundedAbel
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanKernelMass

/-!
# The flip points break the Möbius half-power law

The half-power law at a gauge point is `θ_μ(x) ≤ 1/2` for the Möbius source; at `x = 0` it is RH.
The flip points `x_θ` of `ThePoleDoesNotDecideTheHalfPowerLaw` carry the pole of the trivial point,
and their Möbius exponent is exactly `max(θ, Θ)` (`gaugeExponent_moebius_flipPoint`), unconditionally.
So for `θ > 1/2` they violate the half-power law while sharing the pole of `0`: no property of the
pole implies the Möbius half-power law (`moebius_halfPowerLaw_not_decided_by_pole`).

**The lower bound `θ_μ(x_θ) ≥ θ`** (`not_gaugePowerBound_moebius_flipPoint`). Write `f = μχ` for
the twisted Möbius function and `b = f * 1`. Then `b` is multiplicative with `b(p^k) = 1 − χ(p)`,
i.e. `2` on the flip primes and `0` elsewhere, so `b ≥ 0` and `Σ b(n) n^{−σ}` converges exactly for
`σ > θ` (Euler-product bound, `flipDivisorSeries_summable`) and diverges at `θ`
(`exists_sum_flipPrimes_rpow_gt`). A power bound `O(N^a)`, `a < θ`, on the Möbius sums makes the
conditionally convergent series `D(s) = Σ f(n) n^{−s}` holomorphic on `Re s > a`. On `Re s > 1`,
`ζ D = Σ b(n) n^{−s}`; the identity theorem on a connected open set around the segment `(θ, 1)`,
avoiding the pole of `ζ`, extends this to real `σ ∈ (θ, 1)`. As `σ ↓ θ` the left side stays bounded and
the right side does not.

**The upper bound** comes from the sparse invariance of the exponent: `x_θ` and `0` agree off a
prime set with `Σ p^{−σ}` bounded for every `σ > θ`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### The flip twist is real and multiplicative -/

/-- The flip point is real: `χ(n) = ±1`. -/
theorem twist_flipPoint_eq_ofReal_re (θ : ℝ) (n : ℕ) :
    twist (flipPoint θ) n = ((twist (flipPoint θ) n).re : ℂ) := by
  refine Nat.recOnMul ?_ ?_ (fun p hp => ?_) (fun a b ha hb => ?_) n
  · rw [twist_at_zero]; simp
  · simp
  · by_cases h : p ∈ flipPrimes θ
    · rw [twist_flipPoint_of_mem hp h]; simp
    · rw [twist_flipPoint_of_notMem hp h]; simp
  · rcases eq_or_ne a 0 with rfl | ha0
    · rw [zero_mul, twist_at_zero]; simp
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [mul_zero, twist_at_zero]; simp
    rw [twist_mul _ ha0 hb0, ha, hb, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The flip twist as a multiplicative arithmetic function. -/
def flipTwist (θ : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else twist (flipPoint θ) n, by simp⟩

theorem flipTwist_apply {θ : ℝ} {n : ℕ} (hn : n ≠ 0) : flipTwist θ n = twist (flipPoint θ) n := by
  simp [flipTwist, hn]

theorem isMultiplicative_flipTwist (θ : ℝ) : (flipTwist θ).IsMultiplicative := by
  refine ⟨by simp [flipTwist], fun {m n} _ => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [flipTwist]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [flipTwist]
  rw [flipTwist_apply (mul_ne_zero hm hn), flipTwist_apply hm, flipTwist_apply hn,
    twist_mul _ hm hn]

/-- The twisted Möbius function `f = μχ`. -/
def flipMoebius (θ : ℝ) : ArithmeticFunction ℂ :=
  (↑(ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ).pmul (flipTwist θ)

/-- `b = f * 1`. -/
def flipDivisorSum (θ : ℝ) : ArithmeticFunction ℂ :=
  flipMoebius θ * ↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ)

theorem flipMoebius_eq (θ : ℝ) (n : ℕ) : flipMoebius θ n = moebiusSource n * twist (flipPoint θ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [flipMoebius, moebiusSource]
  simp [flipMoebius, ArithmeticFunction.pmul_apply, flipTwist_apply hn, moebiusSource]

theorem norm_flipMoebius_le (θ : ℝ) (n : ℕ) : ‖flipMoebius θ n‖ ≤ 1 := by
  rw [flipMoebius_eq, norm_mul, norm_twist, mul_one]
  exact norm_moebiusSource_le n

theorem isMultiplicative_flipDivisorSum (θ : ℝ) : (flipDivisorSum θ).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_moebius.intCast.pmul (isMultiplicative_flipTwist θ)).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast

/-- `b(p^k) = 1 − χ(p)` for `k ≥ 1`. -/
theorem flipDivisorSum_prime_pow {θ : ℝ} {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    flipDivisorSum θ (p ^ k) = 1 - twist (flipPoint θ) p := by
  have hvan : ∀ i : ℕ, flipMoebius θ (p ^ (i + 2)) = 0 := fun i => by
    simp [flipMoebius, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega : i + 2 ≠ 0)]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [flipDivisorSum, ArithmeticFunction.coe_mul_zeta_apply, Nat.divisors_prime_pow hp, sum_map,
    sum_range_succ', sum_range_succ']
  simp only [Function.Embedding.coeFn_mk, zero_add, pow_one, pow_zero]
  rw [sum_eq_zero fun i _ => by rw [show i + 1 + 1 = i + 2 by ring]; exact hvan i, zero_add,
    flipMoebius_eq, flipMoebius_eq,
    show moebiusSource p = -1 by simp [moebiusSource, ArithmeticFunction.moebius_apply_prime hp]]
  simp [moebiusSource]
  ring

/-- `1 − χ(p)` is `2` on the flip primes and `0` elsewhere. -/
theorem one_sub_twist_flipPoint {θ : ℝ} {p : ℕ} (hp : p.Prime) :
    1 - twist (flipPoint θ) p = ((if p ∈ flipPrimes θ then 2 else 0 : ℝ) : ℂ) := by
  by_cases h : p ∈ flipPrimes θ
  · rw [twist_flipPoint_of_mem hp h, if_pos h]; norm_num
  · rw [twist_flipPoint_of_notMem hp h, if_neg h]; simp

/-- **`b` is real and nonnegative.** -/
theorem flipDivisorSum_eq_ofReal (θ : ℝ) (n : ℕ) :
    flipDivisorSum θ n = ((flipDivisorSum θ n).re : ℂ) ∧ 0 ≤ (flipDivisorSum θ n).re := by
  have key : ∃ r : ℝ, 0 ≤ r ∧ flipDivisorSum θ n = r := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact ⟨0, le_rfl, by simp⟩
    rw [(isMultiplicative_flipDivisorSum θ).multiplicative_factorization hn, Finsupp.prod]
    refine Finset.prod_induction _ (fun z => ∃ r : ℝ, 0 ≤ r ∧ z = r)
      (fun z w ⟨r, hr, hz⟩ ⟨t, ht, hw⟩ => ⟨r * t, mul_nonneg hr ht, by rw [hz, hw]; push_cast; rfl⟩)
      ⟨1, zero_le_one, by simp⟩ fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    rw [flipDivisorSum_prime_pow hpp (Finsupp.mem_support_iff.mp hp), one_sub_twist_flipPoint hpp]
    exact ⟨_, by split_ifs <;> norm_num, rfl⟩
  obtain ⟨r, hr, he⟩ := key
  rw [he, Complex.ofReal_re]
  exact ⟨rfl, hr⟩

/-! ### The flip primes: sparse above `θ`, divergent at `θ` -/

theorem eq_of_mem_flipBlock {θ : ℝ} {j k p : ℕ} (hj : p ∈ flipBlock θ j) (hk : p ∈ flipBlock θ k) :
    j = k := by
  obtain ⟨-, hj1, hj2⟩ := mem_flipBlock hj
  obtain ⟨-, hk1, hk2⟩ := mem_flipBlock hk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
    rw [pow_succ] at this
    omega
  · have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
    rw [pow_succ] at this
    omega

/-- **Sparse above `θ`**: every finite set of flip primes has `Σ p^{−σ} ≤ (1 − 4^{θ−σ})^{−1}`. -/
theorem sum_rpow_le_of_subset_flipPrimes {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : θ < σ) (F : Finset ℕ)
    (hF : (↑F : Set ℕ) ⊆ flipPrimes θ) :
    ∑ p ∈ F, (p : ℝ) ^ (-σ) ≤ (1 - (4 : ℝ) ^ (θ - σ))⁻¹ := by
  classical
  set r : ℝ := (4 : ℝ) ^ (θ - σ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℕ := F.sup id + 1
  have hsub : F ⊆ (range K).biUnion (flipBlock θ) := by
    intro p hp
    obtain ⟨k, hk⟩ := hF hp
    have hpK : p ≤ F.sup id := le_sup (f := id) hp
    have hkp : k < p := (Nat.lt_pow_self (by norm_num : 1 < 4)).trans (mem_flipBlock hk).2.1
    exact mem_biUnion.mpr ⟨k, mem_range.mpr (by omega), hk⟩
  have hdisj : (↑(range K) : Set ℕ).PairwiseDisjoint (flipBlock θ) := by
    intro j _ k _ hjk
    exact Finset.disjoint_left.mpr fun p hpj hpk => hjk (eq_of_mem_flipBlock hpj hpk)
  have hblock : ∀ k, ∑ p ∈ flipBlock θ k, (p : ℝ) ^ (-σ) ≤ r ^ k := by
    intro k
    have hterm : ∀ p ∈ flipBlock θ k, (p : ℝ) ^ (-σ) ≤ ((4 : ℝ) ^ (-σ)) ^ k := by
      intro p hp
      have hlt : ((4 ^ k : ℕ) : ℝ) ≤ p := by exact_mod_cast (mem_flipBlock hp).2.1.le
      rw [Real.rpow_pow_comm (by norm_num)]
      push_cast at hlt
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hlt (by linarith)
    calc ∑ p ∈ flipBlock θ k, (p : ℝ) ^ (-σ) ≤ ∑ _p ∈ flipBlock θ k, ((4 : ℝ) ^ (-σ)) ^ k :=
          sum_le_sum hterm
      _ = (flipBlock θ k).card * ((4 : ℝ) ^ (-σ)) ^ k := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((4 : ℝ) ^ θ) ^ k * ((4 : ℝ) ^ (-σ)) ^ k := by
          gcongr
          rw [card_flipBlock]
          exact (Nat.cast_le.mpr (min_le_left _ _)).trans (flipSize_le k)
      _ = r ^ k := by rw [← mul_pow, ← Real.rpow_add (by norm_num), sub_eq_add_neg]
  have hgeom : ∑ k ∈ range K, r ^ k ≤ (1 - r)⁻¹ := by
    rw [geom_sum_eq hr1.ne, div_le_iff_of_neg (by linarith : r - 1 < 0)]
    have hm : (1 - r)⁻¹ * (r - 1) = -1 := by
      rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ (by linarith)]
    rw [hm]
    linarith [pow_nonneg hr0 K]
  calc ∑ p ∈ F, (p : ℝ) ^ (-σ) ≤ ∑ p ∈ (range K).biUnion (flipBlock θ), (p : ℝ) ^ (-σ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => Real.rpow_nonneg (Nat.cast_nonneg p) _
    _ = ∑ k ∈ range K, ∑ p ∈ flipBlock θ k, (p : ℝ) ^ (-σ) := sum_biUnion hdisj
    _ ≤ ∑ k ∈ range K, r ^ k := sum_le_sum fun k _ => hblock k
    _ ≤ (1 - r)⁻¹ := hgeom

/-- **Divergent at `θ`**: finite sets of flip primes have unbounded `Σ p^{−θ}`. -/
theorem exists_sum_flipPrimes_rpow_gt {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (M : ℝ) :
    ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ flipPrimes θ ∧ M < ∑ p ∈ F, (p : ℝ) ^ (-θ) := by
  have hgrow : Tendsto (fun k : ℕ => (4 : ℝ) ^ (θ * k)) atTop atTop := by
    have := tendsto_pow_atTop_atTop_of_one_lt (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 4) hθ)
    refine this.congr fun k => ?_
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    ((eventually_card_flipBlock hθ1).and (hgrow.eventually_ge_atTop 2))
  set c : ℝ := (2 : ℝ) ^ (-θ) / 2
  have hc : 0 < c := by positivity
  -- Each full block contributes at least `c`.
  have hblock : ∀ k, K₀ ≤ k → c ≤ ∑ p ∈ flipBlock θ k, (p : ℝ) ^ (-θ) := by
    intro k hk
    obtain ⟨hcard, h2⟩ := hK₀ k hk
    have hterm : ∀ p ∈ flipBlock θ k, (2 * (4 : ℝ) ^ k) ^ (-θ) ≤ (p : ℝ) ^ (-θ) := by
      intro p hp
      have hle : (p : ℝ) ≤ 2 * (4 : ℝ) ^ k := by exact_mod_cast (mem_flipBlock hp).2.2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (mem_flipBlock hp).1.pos
      exact Real.rpow_le_rpow_of_nonpos hp0 hle (by linarith)
    have hfl : (4 : ℝ) ^ (θ * k) - 1 < (flipSize θ k : ℝ) := by
      have := Nat.lt_floor_add_one ((4 : ℝ) ^ (θ * k)); rw [flipSize]; linarith
    have hsplit : (2 * (4 : ℝ) ^ k) ^ (-θ) = (2 : ℝ) ^ (-θ) / (4 : ℝ) ^ (θ * k) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv,
        show ((k : ℝ) * -θ) = -(θ * k) by ring, Real.rpow_neg (by norm_num)]
    have hpos4 : 0 < (4 : ℝ) ^ (θ * k) := by positivity
    calc c ≤ (flipSize θ k : ℝ) * ((2 : ℝ) ^ (-θ) / (4 : ℝ) ^ (θ * k)) := by
          rw [mul_div_assoc', le_div_iff₀ hpos4]
          simp only [c]
          have h2θ : 0 < (2 : ℝ) ^ (-θ) := by positivity
          nlinarith
      _ = ∑ _p ∈ flipBlock θ k, (2 * (4 : ℝ) ^ k) ^ (-θ) := by
          rw [sum_const, nsmul_eq_mul, hcard, hsplit]
      _ ≤ _ := sum_le_sum hterm
  obtain ⟨m, hm⟩ := exists_nat_gt (M / c)
  refine ⟨(Ico K₀ (K₀ + m)).biUnion (flipBlock θ), ?_, ?_⟩
  · intro p hp
    obtain ⟨k, -, hk⟩ := mem_biUnion.mp hp
    exact ⟨k, hk⟩
  · have hdisj : (↑(Ico K₀ (K₀ + m)) : Set ℕ).PairwiseDisjoint (flipBlock θ) := by
      intro j _ k _ hjk
      exact Finset.disjoint_left.mpr fun p hpj hpk => hjk (eq_of_mem_flipBlock hpj hpk)
    rw [sum_biUnion hdisj]
    calc M < m * c := by rwa [div_lt_iff₀ hc] at hm
      _ = ∑ _k ∈ Ico K₀ (K₀ + m), c := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]; congr 2; omega
      _ ≤ _ := sum_le_sum fun k hk => hblock k (mem_Ico.mp hk).1

/-! ### The Euler product of `b` -/

/-- The real summands `b(n) n^{−σ}`, a multiplicative function. -/
def flipDivisorTerm (θ σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (flipDivisorSum θ n).re * (n : ℝ) ^ (-σ), by simp⟩

theorem flipDivisorTerm_nonneg (θ σ : ℝ) (n : ℕ) : 0 ≤ flipDivisorTerm θ σ n :=
  mul_nonneg (flipDivisorSum_eq_ofReal θ n).2 (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem isMultiplicative_flipDivisorTerm (θ σ : ℝ) : (flipDivisorTerm θ σ).IsMultiplicative := by
  have hb := isMultiplicative_flipDivisorSum θ
  refine ⟨by simp [flipDivisorTerm, hb.map_one], fun {m n} hmn => ?_⟩
  simp only [flipDivisorTerm, ZeroHom.coe_mk]
  have hre : (flipDivisorSum θ (m * n)).re = (flipDivisorSum θ m).re * (flipDivisorSum θ n).re := by
    rw [hb.map_mul_of_coprime hmn, (flipDivisorSum_eq_ofReal θ m).1, (flipDivisorSum_eq_ofReal θ n).1,
      ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  rw [hre, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

/-- **The local factor**: `Σ_k b(p^k) p^{−kσ} = 1 + c_p r/(1 − r)`, `r = p^{−σ}`, `c_p = 1 − χ(p)`. -/
theorem flipDivisorTerm_prime_pow {θ σ : ℝ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    flipDivisorTerm θ σ (p ^ k) =
      if k = 0 then 1 else (if p ∈ flipPrimes θ then 2 else 0) * ((p : ℝ) ^ (-σ)) ^ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [flipDivisorTerm, (isMultiplicative_flipDivisorSum θ).map_one]
  rw [if_neg hk]
  simp only [flipDivisorTerm, ZeroHom.coe_mk]
  rw [flipDivisorSum_prime_pow hp hk, one_sub_twist_flipPoint hp, Complex.ofReal_re, Nat.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm (k : ℝ),
    Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]

/-- **`Σ b(n) n^{−σ}` converges for `σ > θ`.** -/
theorem flipDivisorSeries_summable {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : θ < σ) :
    Summable (fun n => flipDivisorTerm θ σ n) := by
  classical
  have hσ0 : 0 < σ := lt_of_le_of_lt hθ hσ
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set K : ℝ := 2 / (1 - (2 : ℝ) ^ (-σ))
  have hK : 0 ≤ K := div_nonneg (by norm_num) (by linarith)
  -- `r_p = p^{−σ} ≤ 2^{−σ} < 1`.
  have hr : ∀ {p : ℕ}, p.Prime → 0 ≤ (p : ℝ) ^ (-σ) ∧ (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
    intro p hp
    exact ⟨Real.rpow_nonneg (Nat.cast_nonneg p) _, Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast hp.two_le) (by linarith)⟩
  set bnd : ℕ → ℝ := fun n => if n ∈ flipPrimes θ then K * (n : ℝ) ^ (-σ) else 0
  refine RHTower.pm_summable_of_multiplicative_local_bound _ (isMultiplicative_flipDivisorTerm θ σ)
    (flipDivisorTerm_nonneg θ σ) (fun {p} hp => ?_) bnd (fun n => ?_) ?_ (fun {p} hp => ?_)
  · -- Local summability: dominated by a geometric series.
    obtain ⟨hr0, hr1⟩ := hr hp
    refine Summable.of_nonneg_of_le (fun k => flipDivisorTerm_nonneg θ σ _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 (hr1.trans_lt h2)).mul_left 3)
    rw [flipDivisorTerm_prime_pow hp]
    split_ifs with hk <;> [rw [hk, pow_zero]; skip] <;> [norm_num; skip]
    have := pow_nonneg hr0 k
    split_ifs <;> nlinarith
  · simp only [bnd]; split_ifs <;> [exact mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg n) _);
      exact le_rfl]
  · -- Sparse above `θ`.
    refine summable_of_sum_le (c := K * (1 - (4 : ℝ) ^ (θ - σ))⁻¹)
      (fun n => by simp only [bnd]; split_ifs <;> [exact mul_nonneg hK
        (Real.rpow_nonneg (Nat.cast_nonneg n) _); exact le_rfl]) fun F => ?_
    calc ∑ n ∈ F, bnd n = ∑ n ∈ F.filter (· ∈ flipPrimes θ), K * (n : ℝ) ^ (-σ) := by
          rw [sum_filter]
      _ = K * ∑ n ∈ F.filter (· ∈ flipPrimes θ), (n : ℝ) ^ (-σ) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_rpow_le_of_subset_flipPrimes hθ hσ _
          fun n hn => (mem_filter.mp hn).2) hK
  · -- `1 + c r/(1 − r) ≤ exp(c r/(1 − r)) ≤ exp(bnd p)`.
    obtain ⟨hr0, hr1⟩ := hr hp
    set r := (p : ℝ) ^ (-σ)
    have hr1' : r < 1 := hr1.trans_lt h2
    set c : ℝ := if p ∈ flipPrimes θ then 2 else 0
    have hsum : HasSum (fun k => flipDivisorTerm θ σ (p ^ k)) (1 + c * (r / (1 - r))) := by
      have hgeo : HasSum (fun k : ℕ => c * r ^ (k + 1)) (c * (r / (1 - r))) := by
        have := (hasSum_geometric_of_lt_one hr0 hr1').mul_left (c * r)
        convert this using 1
        · funext k; ring
        · field_simp
      have := hgeo.zero_add (f := fun k => flipDivisorTerm θ σ (p ^ k))
      refine (hasSum_nat_add_iff' 1).mp ?_
      simp only [range_one, sum_singleton]
      rw [flipDivisorTerm_prime_pow hp, if_pos rfl]
      convert hgeo using 1
      · funext k; rw [flipDivisorTerm_prime_pow hp, if_neg (by omega)]
      · ring
    rw [hsum.tsum_eq]
    refine (Real.add_one_le_exp _).trans' (le_of_eq (by ring)) |>.trans (Real.exp_le_exp.mpr ?_)
    simp only [bnd, c]
    split_ifs with hS
    · have h1r : 0 < 1 - r := by linarith
      have h12 : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - r := by linarith
      rw [show (2 : ℝ) * (r / (1 - r)) = r * (2 / (1 - r)) by ring, mul_comm K]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by norm_num) (by linarith) h12) hr0
    · simp

/-- The coefficient series of `b` as an `LSeries` at real `σ`. -/
theorem term_flipDivisorSum (θ σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => flipDivisorSum θ n) (σ : ℂ) n = (flipDivisorTerm θ σ n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def, flipDivisorTerm]
  rw [LSeries.term_def, if_neg hn, (flipDivisorSum_eq_ofReal θ n).1]
  simp only [flipDivisorTerm, ZeroHom.coe_mk]
  rw [Real.rpow_neg (Nat.cast_nonneg n), ← div_eq_mul_inv, Complex.ofReal_div,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

theorem LSeriesSummable_flipDivisorSum {θ σ : ℝ} (hθ : 0 ≤ θ) (hσ : θ < σ) :
    LSeriesSummable (fun n => flipDivisorSum θ n) (σ : ℂ) := by
  have h := (flipDivisorSeries_summable hθ hσ).map (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
    Complex.ofRealCLM.continuous
  refine h.congr fun n => ?_
  simp [term_flipDivisorSum]

theorem abscissaOfAbsConv_flipDivisorSum_le {θ : ℝ} (hθ : 0 ≤ θ) :
    LSeries.abscissaOfAbsConv (fun n => flipDivisorSum θ n) ≤ θ :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun _ hy =>
    LSeriesSummable_flipDivisorSum hθ hy

/-! ### The lower bound -/

/-- **Below `θ` the Möbius sums of `x_θ` admit no power bound.** -/
theorem not_gaugePowerBound_moebius_flipPoint {θ a : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (ha : a < θ) :
    ¬ GaugePowerBound moebiusSource (flipPoint θ) a := by
  rintro ⟨C, hC, hb⟩
  set a' := max a 0
  have ha' : a' < θ := max_lt ha hθ
  set c : ℝ := (a' + θ) / 2
  have hc : a' < c := by simp only [c]; linarith
  have hcθ : c < θ := by simp only [c]; linarith
  set g : ℕ → ℂ := fun n => flipMoebius θ (n + 1)
  -- The partial sums of `g` are the Möbius gauge sums.
  have hg : ∀ N : ℕ, ‖∑ n ∈ range N, g n‖ ≤ C * ((N : ℝ) + 1) ^ a' := by
    intro N
    have he : ∑ n ∈ range N, g n = ∑ n ∈ range (N + 1), moebiusSource n * twist (flipPoint θ) n := by
      rw [sum_range_succ']
      simp only [g, ← flipMoebius_eq]
      simp [flipMoebius]
    rw [he]
    exact (hb N).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [N.cast_nonneg (α := ℝ)]) (le_max_left _ _)) hC)
  -- `D(s) = Σ f(n) n^{−s}` converges at `c` and is holomorphic on `Re s > c`.
  obtain ⟨L, hL⟩ := RHTower.tendsto_dirichlet_partialSum_of_poly_bounded hC (le_max_right a 0) hg
    (s := (c : ℂ)) (by simpa using hc)
  set D := GaloisForLFunctions.RHTower.dirichletSum g
  have hDd : DifferentiableOn ℂ D {s : ℂ | c < s.re} := by
    have := GaloisForLFunctions.RHTower.differentiableOn_dirichletSum (a := g) (s₀ := (c : ℂ))
      ⟨L, hL⟩
    simpa using this
  -- On `Re s > 1`, `D` is the absolutely convergent `LSeries` of `f`.
  have hfabs : LSeries.abscissaOfAbsConv (fun n => flipMoebius θ n) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_flipMoebius_le θ n⟩
  have hzabs : LSeries.abscissaOfAbsConv
      (fun n => (↑(ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => by
      simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply]; split_ifs <;> simp⟩
  have hDL : ∀ s : ℂ, 1 < s.re → D s = LSeries (fun n => flipMoebius θ n) s := by
    intro s hs
    have hsum : LSeriesSummable (fun n => flipMoebius θ n) s :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (lt_of_le_of_lt hfabs (by exact_mod_cast hs))
    have hconv : Tendsto (fun N => GaloisForLFunctions.RHTower.dirichletPartialSum g N s) atTop
        (𝓝 (LSeries (fun n => flipMoebius θ n) s)) := by
      have h1 := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
      refine h1.congr fun N => ?_
      simp only [Function.comp_apply, GaloisForLFunctions.RHTower.dirichletPartialSum, g]
      rw [sum_range_succ']
      simp only [LSeries.term_def, Nat.succ_ne_zero, if_false, CharP.cast_eq_zero, if_true, add_zero]
      refine sum_congr rfl fun n _ => ?_
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      push_cast
      ring_nf
    have hDconv : GaloisForLFunctions.RHTower.DirichletConvergesAt g s :=
      ⟨_, hconv⟩
    exact tendsto_nhds_unique (GaloisForLFunctions.RHTower.tendsto_dirichletSum hDconv) hconv
  -- `ζ D = Σ b(n) n^{−s}` on `Re s > 1`.
  have hmul : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * D s = LSeries (fun n => flipDivisorSum θ n) s := by
    intro s hs
    have hs' : (1 : EReal) < s.re := by exact_mod_cast hs
    rw [hDL s hs, flipDivisorSum, ArithmeticFunction.LSeries_mul (lt_of_le_of_lt hfabs hs')
      (lt_of_le_of_lt hzabs hs'), mul_comm]
    congr 1
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    congr 1
    funext n
    simp [ArithmeticFunction.natCoe_apply]
  -- The identity theorem on a connected open set around `(θ, 1)` avoiding `s = 1`.
  set A : Set ℂ := {s | θ < s.re ∧ s.re < 1}
  set B : Set ℂ := {s | θ < s.re ∧ 0 < s.im}
  set E : Set ℂ := {s | 1 < s.re}
  set U := (A ∪ B) ∪ E
  have hAo : IsOpen A := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hBo : IsOpen B := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hEo : IsOpen E := isOpen_lt continuous_const Complex.continuous_re
  have hUo : IsOpen U := (hAo.union hBo).union hEo
  have hconvA : Convex ℝ A := (convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt 1)
  have hconvB : Convex ℝ B := (convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt 0)
  have hconvE : Convex ℝ E := convex_halfSpace_re_gt 1
  have hUc : IsPreconnected U := by
    refine IsPreconnected.union ((2 : ℂ) + Complex.I) (Or.inr ?_) ?_
      (IsPreconnected.union (((θ + 1) / 2 : ℝ) + Complex.I) ?_ ?_ hconvA.isPreconnected
        hconvB.isPreconnected) hconvE.isPreconnected
    · exact ⟨by simp; linarith, by simp⟩
    · simp [E]
    · simp only [A, Set.mem_setOf_eq]; simp; constructor <;> linarith
    · simp only [B, Set.mem_setOf_eq]; simp; linarith
  have hUre : ∀ s ∈ U, θ < s.re ∧ s ≠ 1 := by
    rintro s ((⟨h1, h2⟩ | ⟨h1, h2⟩) | h1)
    · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
    · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
    · exact ⟨by simp only [E, Set.mem_setOf_eq] at h1; linarith,
        fun h => by simp only [E, Set.mem_setOf_eq] at h1; rw [h] at h1; simp at h1⟩
  have hF₁ : AnalyticOnNhd ℂ (fun s => riemannZeta s * D s) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    obtain ⟨hθs, hs1⟩ := hUre s hs
    exact ((differentiableAt_riemannZeta hs1).mul
      ((hDd s (show c < s.re by linarith)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (show c < s.re by linarith)))).differentiableWithinAt
  have hF₂ : AnalyticOnNhd ℂ (LSeries (fun n => flipDivisorSum θ n)) U := fun s hs =>
    LSeries_analyticOnNhd _ s (lt_of_le_of_lt (abscissaOfAbsConv_flipDivisorSum_le hθ.le)
      (by exact_mod_cast (hUre s hs).1))
  have h2U : (2 : ℂ) ∈ U := Or.inr (by simp [E]; norm_num)
  have heq : Set.EqOn (fun s => riemannZeta s * D s) (LSeries (fun n => flipDivisorSum θ n)) U :=
    hF₁.eqOn_of_preconnected_of_eventuallyEq hF₂ hUc h2U
      (Filter.eventually_of_mem (hEo.mem_nhds (by simp [E]; norm_num)) fun s hs => hmul s hs)
  -- Contradiction as `σ ↓ θ`.
  have hcont : ContinuousAt (fun σ : ℝ => riemannZeta σ * D σ) θ := by
    have hθ1' : (θ : ℂ) ≠ 1 := by exact_mod_cast hθ1.ne
    have h := ((differentiableAt_riemannZeta hθ1').mul
      ((hDd θ (by simpa using hcθ)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by simpa using hcθ)))).continuousAt
    exact h.comp Complex.continuous_ofReal.continuousAt
  set M := ‖riemannZeta θ * D θ‖ + 1
  obtain ⟨F, hFS, hFM⟩ := exists_sum_flipPrimes_rpow_gt hθ hθ1 M
  have hev1 : ∀ᶠ σ : ℝ in 𝓝 θ, ‖riemannZeta σ * D σ‖ < M := by
    have := (continuous_norm.continuousAt.comp hcont).eventually
      (gt_mem_nhds (show ‖riemannZeta θ * D θ‖ < M by simp [M]))
    exact this
  have hev2 : ∀ᶠ σ : ℝ in 𝓝 θ, M < ∑ p ∈ F, (p : ℝ) ^ (-σ) := by
    have hc2 : ContinuousAt (fun σ : ℝ => ∑ p ∈ F, (p : ℝ) ^ (-σ)) θ := by
      refine continuousAt_finset_sum F fun p hp => ?_
      have hp0 : (p : ℝ) ≠ 0 := by
        obtain ⟨k, hk⟩ := hFS hp; exact_mod_cast (mem_flipBlock hk).1.ne_zero
      exact (Real.continuousAt_const_rpow hp0).comp continuous_neg.continuousAt
    exact hc2.eventually (lt_mem_nhds hFM)
  obtain ⟨σ, ⟨h1, h2⟩, hσθ, hσ1⟩ := ((hev1.and hev2).filter_mono nhdsWithin_le_nhds |>.and
    (Ioo_mem_nhdsGT_of_mem ⟨le_rfl, hθ1⟩)).exists (f := 𝓝[>] θ)
  have hσU : (σ : ℂ) ∈ U := Or.inl (Or.inl ⟨by simpa using hσθ, by simpa using hσ1⟩)
  have hval := heq hσU
  simp only at hval
  -- The `LSeries` at `σ` is the real tsum of the nonnegative terms.
  have hσθ' : θ < σ := hσθ
  have hLS : LSeries (fun n => flipDivisorSum θ n) σ = ((∑' n, flipDivisorTerm θ σ n : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_flipDivisorSum θ σ n
  have hge : ∑ p ∈ F, (p : ℝ) ^ (-σ) ≤ ∑' n, flipDivisorTerm θ σ n := by
    calc ∑ p ∈ F, (p : ℝ) ^ (-σ) ≤ ∑ p ∈ F, flipDivisorTerm θ σ p := sum_le_sum fun p hp => by
          obtain ⟨k, hk⟩ := hFS hp
          have hpp := (mem_flipBlock hk).1
          have := flipDivisorTerm_prime_pow (θ := θ) (σ := σ) hpp 1
          rw [pow_one, if_neg one_ne_zero, if_pos ⟨k, hk⟩, pow_one] at this
          rw [this]
          linarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) p) (-σ)]
      _ ≤ _ := sum_le_tsum F (fun n _ => flipDivisorTerm_nonneg θ σ n)
          (flipDivisorSeries_summable hθ.le hσθ')
  rw [hval, hLS, Complex.norm_real, Real.norm_of_nonneg
    (tsum_nonneg fun n => flipDivisorTerm_nonneg θ σ n)] at h1
  linarith

/-! ### The exponent -/

/-- **The Möbius exponent of a flip point is `max(θ, Θ)`.** -/
theorem gaugeExponent_moebius_flipPoint {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    gaugeExponent moebiusSource (flipPoint θ) = max θ RHTower.zetaZeroAbscissa := by
  have hsparse : ∀ σ, θ < σ → ∃ B : ℝ, ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ flipPrimes θ →
      ∑ p ∈ F, (p : ℝ) ^ (-σ) ≤ B := fun σ hσ =>
    ⟨_, fun F hF => sum_rpow_le_of_subset_flipPrimes hθ.le hσ F hF⟩
  have hagree : ∀ q, q.Prime → q ∉ flipPrimes θ → twist (flipPoint θ) q = twist 0 q :=
    fun q hq h => by rw [twist_flipPoint_of_notMem hq h, twist_zero]
  have hup := gaugeExponent_moebius_le_of_agree_off_sparse hθ.le hsparse hagree
  have hdown := gaugeExponent_moebius_le_of_agree_off_sparse hθ.le hsparse
    (fun q hq h => (hagree q hq h).symm)
  rw [gaugeExponent_moebius_trivial] at hup hdown
  -- `θ ≤ θ_μ(x_θ)`.
  have hlow : θ ≤ gaugeExponent moebiusSource (flipPoint θ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, ha1, ha2⟩ := exists_between hlt
    exact not_gaugePowerBound_moebius_flipPoint hθ hθ1 ha2
      (gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le ha1)
  refine le_antisymm hup (max_le hlow ?_)
  rcases le_or_gt RHTower.zetaZeroAbscissa θ with h | h
  · exact h.trans hlow
  · exact (le_max_iff.mp hdown).resolve_left (not_le.mpr h)

/-- **Every value in `[Θ, 1)` is a Möbius exponent of a point carrying the pole of `0`.** -/
theorem gaugeExponent_moebius_flipPoint_of_le {θ : ℝ} (hΘ : RHTower.zetaZeroAbscissa ≤ θ)
    (hθ1 : θ < 1) : gaugeExponent moebiusSource (flipPoint θ) = θ := by
  have hθ : 0 < θ := lt_of_lt_of_le RHTower.zetaZeroAbscissa_pos hΘ
  rw [gaugeExponent_moebius_flipPoint hθ hθ1, max_eq_left hΘ]

/-- For `θ > 1/2` the flip point violates the Möbius half-power law. -/
theorem not_gaugeHalfPowerLaw_moebius_flipPoint {θ : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ < 1) :
    ¬ GaugeHalfPowerLaw moebiusSource (flipPoint θ) := by
  rw [← gaugeExponent_le_half_iff norm_moebiusSource_le, gaugeExponent_moebius_flipPoint
    (by linarith) hθ1]
  intro h
  linarith [le_max_left θ RHTower.zetaZeroAbscissa]

/-! ### The answer -/

/-- **No property of the pole implies the Möbius half-power law.** For `1/2 < b < 1`, if `P` holds at
every point carrying the pole of `0` up to `(N+1)^b`, then `P` does not imply the half-power law:
the flip point `x_θ`, `θ = (1/2 + b)/2`, carries the pole and has Möbius exponent `≥ θ > 1/2`. -/
theorem moebius_halfPowerLaw_not_decided_by_pole {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1)
    (P : GaugeTorus → Prop) (hP : ∀ y, SharesPoleUpTo y b → P y) :
    ¬ ∀ y, P y → GaugeHalfPowerLaw moebiusSource y := by
  intro h
  set θ := (1 / 2 + b) / 2
  have hθ : 1 / 2 < θ := by simp only [θ]; linarith
  have hθb : θ < b := by simp only [θ]; linarith
  exact not_gaugeHalfPowerLaw_moebius_flipPoint hθ (hθb.trans hb1)
    (h _ (hP _ (sharesPoleUpTo_flipPoint (by linarith) hθb)))

end GaloisForLFunctions.ArithmeticGaugeTheory
