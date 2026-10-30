import GaloisForLFunctions.ArithmeticResonanceTheory.PrimesObeyNoAffineRecurrence

/-!
# Integrality forbids super-conformal distortion

Along a cycle family `u^n v` of a dynamical system the exponentiated lengths `p n = e^{S(u^n v)}`
grow like `C a^n` with `a = e^{S(u)}`. Write the ratio as `p (n + 1) = a · p n · e^{δ n}`, or the
size as `p n = C a^n e^{ε n}`. The **conformal threshold** is distortion of size `a^{−n}`.

* **Super-conformal ratios** (`eventually_succ_eq_mul_of_ratio`): if `|δ n| ≤ K ρ^n` with `a ρ < 1`,
  the integers `p (n + 1) − a · p n = a · p n · (e^{δ n} − 1) = O((aρ)^n)` tend to `0`, so
  `p (n + 1) = a · p n` eventually. With `a ≥ 2` the members are then composite
  (`not_eventually_prime_of_ratio`).
* **Conformal expansions** (`not_eventually_prime_of_conformal_expansion`): if `a^n ε n → A` for
  some real `A` (including `A = 0`, the super-conformal case), the integers `p (n + 1) − a · p n`
  converge to `C (A − aA)`, hence are eventually constant, and the primes would obey an affine
  recurrence, which `not_eventually_affine_recurrence` excludes.

This is margin from integrality: Beurling systems, whose lengths are not logarithms of integers,
are untouched.
-/

open Filter Topology

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- A convergent sequence of integers is eventually constant. -/
theorem exists_eventually_eq_of_tendsto_int {z : ℕ → ℤ} {L : ℝ}
    (h : Tendsto (fun n => (z n : ℝ)) atTop (𝓝 L)) : ∃ c : ℤ, ∀ᶠ n in atTop, z n = c := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (1 / 2) (by norm_num)
  refine ⟨z N, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have h1 := hN n hn
  have h2 := hN N le_rfl
  rw [Real.dist_eq] at h1 h2
  have h3 : |((z n - z N : ℤ) : ℝ)| < 1 := by
    push_cast
    calc |(z n : ℝ) - z N| = |((z n : ℝ) - L) - ((z N : ℝ) - L)| := by ring_nf
      _ ≤ |(z n : ℝ) - L| + |(z N : ℝ) - L| := abs_sub _ _
      _ < 1 := by linarith
  have h4 : |z n - z N| < 1 := by exact_mod_cast h3
  have := Int.abs_lt_one_iff.mp h4
  omega

/-- A prime that is `a` times a prime, `a ≥ 2`, does not exist. -/
theorem not_prime_mul_of_prime {a q : ℕ} (ha : 2 ≤ a) (hq : q.Prime) : ¬ (a * q).Prime := by
  rw [Nat.prime_mul_iff]
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · exact hq.one_lt.ne' h
  · omega

/-- **Super-conformal ratios force exact multiplicativity.** If integers satisfy
`p (n + 1) = a · p n · e^{δ n}` with `|δ n| ≤ K ρ^n` and `a ρ < 1`, then `p (n + 1) = a · p n`
for all large `n`. -/
theorem eventually_succ_eq_mul_of_ratio {p : ℕ → ℕ} {a : ℕ} (ha : 1 ≤ a) {δ : ℕ → ℝ} {K ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (haρ : a * ρ < 1) (hδ : ∀ n, |δ n| ≤ K * ρ ^ n)
    (hp : ∀ n, (p (n + 1) : ℝ) = a * p n * Real.exp (δ n)) :
    ∀ᶠ n in atTop, p (n + 1) = a * p n := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hρ1 : ρ < 1 := lt_of_le_of_lt (le_mul_of_one_le_left hρ0 ha1) haρ
  have hK : 0 ≤ K := by simpa using (abs_nonneg _).trans (hδ 0)
  -- size: `p n ≤ B a^n` with `B = p 0 · e^{K/(1−ρ)}`
  set B : ℝ := p 0 * Real.exp (K / (1 - ρ)) with hB
  have hsize : ∀ n, (p n : ℝ) ≤ B * (a : ℝ) ^ n := by
    have hexact : ∀ n, (p n : ℝ) = p 0 * (a : ℝ) ^ n *
        Real.exp (∑ i ∈ Finset.range n, δ i) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hp n, ih, Finset.sum_range_succ, Real.exp_add, pow_succ]; ring
    intro n
    have hsum : ∑ i ∈ Finset.range n, δ i ≤ K / (1 - ρ) := by
      calc ∑ i ∈ Finset.range n, δ i ≤ ∑ i ∈ Finset.range n, K * ρ ^ i :=
            Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hδ i)
        _ = K * ∑ i ∈ Finset.range n, ρ ^ i := by rw [Finset.mul_sum]
        _ ≤ K * (1 - ρ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ hK
            exact (Summable.sum_le_tsum _ (fun i _ => pow_nonneg hρ0 i)
              (summable_geometric_of_lt_one hρ0 hρ1)).trans
              (tsum_geometric_of_lt_one hρ0 hρ1).le
        _ = K / (1 - ρ) := by rw [div_eq_mul_inv]
    rw [hexact n, hB]
    have hp0 : (0 : ℝ) ≤ p 0 := Nat.cast_nonneg _
    have hpow : (0 : ℝ) ≤ (a : ℝ) ^ n := by positivity
    calc (p 0 : ℝ) * (a : ℝ) ^ n * Real.exp (∑ i ∈ Finset.range n, δ i)
        ≤ (p 0 : ℝ) * (a : ℝ) ^ n * Real.exp (K / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (mul_nonneg hp0 hpow)
      _ = p 0 * Real.exp (K / (1 - ρ)) * (a : ℝ) ^ n := by ring
  -- the integer defects `p (n + 1) − a · p n` tend to `0`
  set m : ℕ → ℤ := fun n => (p (n + 1) : ℤ) - a * p n with hm
  have hsmall : ∀ᶠ n in atTop, K * ρ ^ n ≤ 1 := by
    have ht : Tendsto (fun n : ℕ => K * ρ ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul K
    exact ht.eventually (ge_mem_nhds one_pos)
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hlim : Tendsto (fun n => (m n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun n : ℕ => 2 * a * B * K * ((a : ℝ) * ρ) ^ n)
      atTop (𝓝 0))
    · filter_upwards [hsmall] with n hn
      have hδ1 : |δ n| ≤ 1 := (hδ n).trans hn
      have hval : (m n : ℝ) = a * p n * (Real.exp (δ n) - 1) := by
        simp only [hm]; push_cast; rw [hp n]; ring
      rw [Real.norm_eq_abs, hval, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a),
        abs_of_nonneg (Nat.cast_nonneg (p n))]
      have he := Real.abs_exp_sub_one_le hδ1
      have hpn := hsize n
      calc (a : ℝ) * p n * |Real.exp (δ n) - 1| ≤ a * (B * (a : ℝ) ^ n) * (2 * (K * ρ ^ n)) := by
            gcongr
            exact he.trans (by linarith [hδ n])
        _ = 2 * a * B * K * ((a : ℝ) * ρ) ^ n := by rw [mul_pow]; ring
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) haρ).const_mul
        (2 * a * B * K)
  have hlt := (hlim.norm).eventually (gt_mem_nhds (show ‖(0 : ℝ)‖ < 1 by simp))
  filter_upwards [hlt] with n hn
  have h1 : |m n| < 1 := by
    have : |(m n : ℝ)| < 1 := by simpa [Real.norm_eq_abs] using hn
    exact_mod_cast this
  have h0 := Int.abs_lt_one_iff.mp h1
  simp only [hm] at h0
  omega

/-- **No super-conformal prime family.** Under the hypotheses of
`eventually_succ_eq_mul_of_ratio` with `a ≥ 2`, the integers `p n` are not eventually prime. -/
theorem not_eventually_prime_of_ratio {p : ℕ → ℕ} {a : ℕ} (ha : 2 ≤ a) {δ : ℕ → ℝ} {K ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (haρ : a * ρ < 1) (hδ : ∀ n, |δ n| ≤ K * ρ ^ n)
    (hp : ∀ n, (p (n + 1) : ℝ) = a * p n * Real.exp (δ n)) :
    ¬ ∀ᶠ n in atTop, (p n).Prime := by
  intro hprime
  have hmul := eventually_succ_eq_mul_of_ratio (by omega) hρ0 haρ hδ hp
  obtain ⟨n, hn1, hn2, hn3⟩ :=
    (hprime.and ((tendsto_add_atTop_nat 1).eventually hprime |>.and hmul)).exists
  rw [hn3] at hn2
  exact not_prime_mul_of_prime ha hn1 hn2

/-- **The conformal threshold.** Integers `p n = C a^n e^{ε n}` with `a ≥ 2`, `C > 0` and
`a^n ε n → A` (any real `A`) are not eventually prime: the defects `p (n + 1) − a · p n` converge,
hence stabilize, and primes obey no eventual affine recurrence. -/
theorem not_eventually_prime_of_conformal_expansion {p : ℕ → ℕ} {a : ℕ} (ha : 2 ≤ a) {C A : ℝ}
    (hC : 0 < C) {ε : ℕ → ℝ} (hε : Tendsto (fun n => (a : ℝ) ^ n * ε n) atTop (𝓝 A))
    (hp : ∀ n, (p n : ℝ) = C * (a : ℝ) ^ n * Real.exp (ε n)) :
    ¬ ∀ᶠ n in atTop, (p n).Prime := by
  intro hprime
  have ha1 : (1 : ℝ) < a := by exact_mod_cast ha
  have hpowtop : Tendsto (fun n : ℕ => (a : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ha1
  -- `ε n → 0`
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    have h := hε.mul (tendsto_inv_atTop_zero.comp hpowtop)
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    have : (a : ℝ) ^ n ≠ 0 := by positivity
    simp only [Function.comp]; field_simp
  -- the second-order remainder `R n = e^{ε n} − 1 − ε n` is negligible against `a^{−n}`
  set R : ℕ → ℝ := fun n => Real.exp (ε n) - 1 - ε n with hR
  have hRlim : Tendsto (fun n => (a : ℝ) ^ n * R n) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n => |(a : ℝ) ^ n * ε n| * |ε n|) atTop (𝓝 0) := by
      simpa using hε.abs.mul hε0.abs
    refine squeeze_zero_norm' ?_ hprod
    filter_upwards [hε0.eventually (Metric.closedBall_mem_nhds 0 one_pos)] with n hn
    have hn1 : |ε n| ≤ 1 := by simpa [Real.dist_eq] using hn
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a : ℝ) ^ n)]
    have h2 := Real.abs_exp_sub_one_sub_id_le hn1
    calc (a : ℝ) ^ n * |R n| ≤ (a : ℝ) ^ n * ε n ^ 2 := by gcongr
      _ = (a : ℝ) ^ n * |ε n| * |ε n| := by rw [mul_assoc, ← sq, sq_abs]
  -- the defects converge
  set m : ℕ → ℤ := fun n => (p (n + 1) : ℤ) - a * p n with hm
  have hmlim : Tendsto (fun n => (m n : ℝ)) atTop
      (𝓝 (C * (A - a * A + 0 - a * 0))) := by
    have hshift := hε.comp (tendsto_add_atTop_nat 1)
    have hRshift := hRlim.comp (tendsto_add_atTop_nat 1)
    refine ((((hshift.sub (hε.const_mul (a : ℝ))).add hRshift).sub
      (hRlim.const_mul (a : ℝ))).const_mul C).congr fun n => ?_
    simp only [Function.comp, hm, hR]
    push_cast
    rw [hp (n + 1), hp n, pow_succ]
    ring
  obtain ⟨c, hc⟩ := exists_eventually_eq_of_tendsto_int hmlim
  -- the members grow, so the recurrence is eventually increasing
  have hptop : Tendsto (fun n => (p n : ℝ)) atTop atTop := by
    have hlow : ∀ᶠ n in atTop, C * Real.exp (-1) * (a : ℝ) ^ n ≤ p n := by
      filter_upwards [hε0.eventually (Metric.closedBall_mem_nhds 0 one_pos)] with n hn
      have hn1 : -1 ≤ ε n := by
        have : |ε n| ≤ 1 := by simpa [Real.dist_eq] using hn
        linarith [neg_abs_le (ε n)]
      rw [hp n]
      have := Real.exp_le_exp.mpr hn1
      have hpos : 0 ≤ C * (a : ℝ) ^ n := by positivity
      nlinarith
    exact tendsto_atTop_mono' atTop hlow
      (Tendsto.const_mul_atTop (by positivity) hpowtop)
  have hbig : ∀ᶠ n in atTop, (|c| : ℝ) < p n := hptop.eventually_gt_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hprime.and hc).and hbig)
  refine not_eventually_affine_recurrence (p := p) (a := a) (by omega) c (N := N)
    (fun n hn => (hN n hn).1.1) (fun n hn => ?_) (fun n hn => ?_)
  · have hcn := (hN n hn).1.2
    have hb : (|c| : ℝ) < p n := (hN n hn).2
    have hb' : |c| < (p n : ℤ) := by exact_mod_cast hb
    have hrec : (p (n + 1) : ℤ) = a * p n + c := by rw [← hcn]; simp [hm]
    have ha2 : (2 : ℤ) ≤ a := by exact_mod_cast ha
    have : (p n : ℤ) < p (n + 1) := by
      rw [hrec]; nlinarith [neg_abs_le c, Int.natCast_nonneg (p n)]
    exact_mod_cast this
  · have hcn := (hN n hn).1.2
    rw [← hcn]; simp [hm]

end GaloisForLFunctions.ArithmeticResonanceTheory
