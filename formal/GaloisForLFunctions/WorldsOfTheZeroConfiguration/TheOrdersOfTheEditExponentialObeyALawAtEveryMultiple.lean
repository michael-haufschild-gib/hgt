import GaloisForLFunctions.WorldsOfTheZeroConfiguration.AnOddZeroOfTheEditExponentialCostsHalfItsRealPart

/-!
# The orders of the edit exponential obey a law at every multiple

For an edit `e` of the rational primes write `E(s) = Σ_p e(p) p^{−s}`.  To order `k` the Euler
product is

  `ζ_B(s) = ζ(s) · e^{E(s)} · Π_{j=2}^{k} e^{E(js)/j} · e^{Q_{k+1}(s)}`,

where `Q_{k+1}(s) = Σ_p e(p) r_{k+1}(p^{−s})`, `r_{k+1}(z) = −log(1 − z) − Σ_{i ≤ k} z^i/i`, is
holomorphic on `Re s > θ/(k+1)` if the edit is summable at `θ` (`differentiableOn_editRemOf`).
With `N = k!` this reads `((s − 1)ζ_B)^N = (u e^{E} e^{Q_{k+1}})^N Π_{j=2}^{k} (e^{E(js)})^{N/j}`.

**The order law** (`factorial_dvd_sum_order_of_count`).  Let the edit have count `A x + O(x^β)`,
and let `F` continue `e^{E}` to `Re s > c₀`.  At every `s₁` with
`Re s₁ > max(β, c₀, θ/(k+1))` the orders `n(z) = ord_z F` satisfy

  `k! ∣ Σ_{j=2}^{k} (k!/j) · n(j s₁)`,   i.e. `Σ_{j=2}^{k} n(j s₁)/j ∈ ℤ`.

Proof: compare orders at `s₁` of both sides of the identity above.

**Prime multiples** (`prime_dvd_order_of_count`).  A zero `ρ` of `F` with
`Re ρ > p · max(β, c₀, θ/(p+1))`, `p` prime, has order divisible by `p`: modulo `p` only the term
`j = p` survives, with the unit `(p − 1)!`.

**Isolated multiples** (`dvd_order_of_count_of_ne_zero`).  If `F(jρ/k) ≠ 0` for `2 ≤ j < k`, then
`k ∣ ord_ρ F` for `Re ρ > k · max(β, c₀, θ/(k+1))`.

The case `k = 2` is `even_order_of_count`.
-/

open Complex Filter Topology Finset
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw

open PrimeEdits TwoSidedEdits

/-! ## The remainder of order `k` -/

/-- `r_{k+1}(z) = −log(1 − z) − Σ_{i=1}^{k} z^i/i`. -/
def logRemOf (k : ℕ) (z : ℂ) : ℂ := -Complex.log (1 - z) - ∑ i ∈ Icc 1 k, z ^ i / i

theorem norm_logRemOf_le (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logRemOf k z‖ ≤ ‖z‖ ^ (k + 1) * (1 - ‖z‖)⁻¹ / (k + 1) := by
  have hmem : 1 + -z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one (by rwa [norm_neg])
  have hlog : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) := by
    rw [sub_eq_add_neg]
    exact Complex.log_inv _ (Complex.slitPlane_arg_ne_pi hmem)
  have hrange : range (k + 1) = insert 0 (Icc 1 k) := by
    ext j; simp only [mem_range, mem_insert, mem_Icc]; omega
  have hT : Complex.logTaylor (k + 1) (-z) = -∑ i ∈ Icc 1 k, z ^ i / i := by
    simp only [Complex.logTaylor]
    rw [hrange, sum_insert (by simp), ← sum_neg_distrib]
    simp only [Nat.cast_zero, div_zero, zero_add]
    refine sum_congr rfl fun i _ => ?_
    rw [neg_pow z, ← mul_assoc, ← pow_add, show i + 1 + i = 2 * i + 1 by ring,
      (odd_two_mul_add_one i).neg_one_pow]
    ring
  have h := Complex.norm_log_one_sub_inv_add_logTaylor_neg_le k hz
  rwa [hlog, hT, ← sub_eq_add_neg] at h

/-- `r_{k+1}(z) = r_2(z) − Σ_{i=2}^{k} z^i/i` for `k ≥ 1`. -/
theorem logRemOf_eq {k : ℕ} (hk : 1 ≤ k) (z : ℂ) :
    logRemOf k z = logRem z - ∑ i ∈ Icc 2 k, z ^ i / i := by
  have hI : Icc 1 k = insert 1 (Icc 2 k) := by
    ext j; simp only [mem_Icc, mem_insert]; omega
  rw [logRemOf, logRem, hI, sum_insert (by simp)]
  simp only [pow_one, Nat.cast_one, div_one]
  ring

/-- The remainder of order `k`: `Q_{k+1}(s) = Σ_p e(p) r_{k+1}(p^{−s})`. -/
def editRemOf (k : ℕ) (e : ℕ → ℤ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (e p : ℂ) * logRemOf k (((p : ℕ) : ℂ) ^ (-s))

/-- The remainder of order `k ≥ 1` of an edit that is summable at `θ > 0` is holomorphic on
`Re s > θ/(k+1)`. -/
theorem differentiableOn_editRemOf {k : ℕ} (hk : 1 ≤ k) {e : ℕ → ℤ} {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun n : ℕ => |(e n : ℝ)| * (n : ℝ) ^ (-θ)) :
    DifferentiableOn ℂ (editRemOf k e) {s : ℂ | θ / (k + 1) < s.re} := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hθk : 0 < θ / (k + 1) := div_pos hθ hk1
  have hUo : IsOpen {s : ℂ | θ / (k + 1) < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hq : (2 : ℝ) ^ (-(θ / (k + 1))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmaj : Summable fun p : Nat.Primes =>
      |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) * ((1 - (2 : ℝ) ^ (-(θ / (k + 1))))⁻¹ / (k + 1)) :=
    (hS.subtype _).mul_right _
  refine differentiableOn_tsum_of_summable_norm hmaj (fun p => ?_) hUo (fun p w hw => ?_)
  · intro w hw
    have hw' : θ / (k + 1) < w.re := hw
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hlt : ‖((p : ℕ) : ℂ) ^ (-(w + 0))‖ < 1 := by
      rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; linarith)
    have h := differentiableAt_logRem_cpow (n := (p : ℕ)) p.2.pos (c := 0) (s := w) hlt
    simp only [add_zero] at h
    have hpow : DifferentiableAt ℂ (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-s)) w :=
      differentiableAt_id.neg.const_cpow (Or.inl hp0)
    have hsum : DifferentiableAt ℂ
        (fun s : ℂ => ∑ i ∈ Icc 2 k, (((p : ℕ) : ℂ) ^ (-s)) ^ i / (i : ℂ)) w :=
      DifferentiableAt.fun_sum fun i _ => (hpow.pow i).div_const _
    have hd : DifferentiableAt ℂ
        (fun s : ℂ => (e p : ℂ) * logRemOf k (((p : ℕ) : ℂ) ^ (-s))) w := by
      simp only [logRemOf_eq hk]
      exact (h.sub hsum).const_mul _
    exact hd.differentiableWithinAt
  · have hw' : θ / (k + 1) < w.re := hw
    have hz : ‖((p : ℕ) : ℂ) ^ (-w)‖ = ((p : ℕ) : ℝ) ^ (-w.re) :=
      norm_natCast_cpow_neg (p : ℕ) p.2.pos w
    have hzq : ‖((p : ℕ) : ℂ) ^ (-w)‖ ≤ (2 : ℝ) ^ (-(θ / (k + 1))) := by
      rw [hz]; exact rpow_neg_le_two p.2.two_le hθk.le hw'.le
    -- `|z|^{k+1} ≤ p^{−θ}` for `Re w ≥ θ/(k+1)`
    have hzk : ‖((p : ℕ) : ℂ) ^ (-w)‖ ^ (k + 1) ≤ ((p : ℕ) : ℝ) ^ (-θ) := by
      rw [hz]
      calc (((p : ℕ) : ℝ) ^ (-w.re)) ^ (k + 1)
          ≤ (((p : ℕ) : ℝ) ^ (-(θ / (k + 1)))) ^ (k + 1) :=
            pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
              (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_le) (by linarith)) _
        _ = ((p : ℕ) : ℝ) ^ (-θ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
            congr 1
            push_cast
            field_simp
    have h := norm_logRemOf_le k (hzq.trans_lt hq)
    have h1 : 0 < 1 - ‖((p : ℕ) : ℂ) ^ (-w)‖ := by linarith
    have h2 : (1 - ‖((p : ℕ) : ℂ) ^ (-w)‖)⁻¹ ≤ (1 - (2 : ℝ) ^ (-(θ / (k + 1))))⁻¹ :=
      inv_anti₀ (by linarith) (by linarith)
    have h5 := mul_le_mul hzk h2 (inv_nonneg.mpr h1.le)
      (Real.rpow_nonneg (Nat.cast_nonneg ((p : ℕ))) (-θ))
    have h6 : ‖logRemOf k (((p : ℕ) : ℂ) ^ (-w))‖ ≤
        ((p : ℕ) : ℝ) ^ (-θ) * (1 - (2 : ℝ) ^ (-(θ / (k + 1))))⁻¹ / (k + 1) :=
      h.trans (div_le_div_of_nonneg_right h5 hk1.le)
    rw [norm_mul, Complex.norm_intCast]
    calc |(e p : ℝ)| * ‖logRemOf k (((p : ℕ) : ℂ) ^ (-w))‖
        ≤ |(e p : ℝ)| * (((p : ℕ) : ℝ) ^ (-θ) * (1 - (2 : ℝ) ^ (-(θ / (k + 1))))⁻¹ / (k + 1)) :=
          mul_le_mul_of_nonneg_left h6 (abs_nonneg _)
      _ = |(e p : ℝ)| * ((p : ℕ) : ℝ) ^ (-θ) *
          ((1 - (2 : ℝ) ^ (-(θ / (k + 1))))⁻¹ / (k + 1)) := by ring

/-- **The Euler product to order `k`.**  On `Re s > 1` the prime-power remainder is
`Σ_{j=2}^{k} E(js)/j + Q_{k+1}(s)`. -/
theorem editRem_eq_sum_add {e : ℕ → ℤ} (he : IsEdit e) {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hs : 1 < s.re) :
    editRem e s = ∑ j ∈ Icc 2 k, LSeries (fun n => (e n : ℂ)) (j * s) / j + editRemOf k e s := by
  have hjre : ∀ j ∈ Icc 2 k, 1 < ((j : ℂ) * s).re := fun j hj => by
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
    have hre : ((j : ℂ) * s).re = j * s.re := by simp
    have := mul_le_mul_of_nonneg_right hj2 (by linarith : (0 : ℝ) ≤ s.re)
    rw [hre]; linarith
  -- the series `Σ_p e(p) p^{−js}/j = E(js)/j`
  have hEj : ∀ j ∈ Icc 2 k, HasSum (fun p : Nat.Primes =>
      (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-((j : ℂ) * s)) / j)
      (LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s) / j) := fun j hj => by
    have hprime : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-((j : ℂ) * s).re) :=
      (Real.summable_nat_rpow.mpr (show -((j : ℂ) * s).re < -1 by linarith [hjre j hj])).subtype _
    have hsum : Summable fun p : Nat.Primes => (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-((j : ℂ) * s)) :=
      Summable.of_norm_bounded hprime fun p => by
        rw [norm_mul, norm_natCast_cpow_neg _ p.2.pos]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (he.norm_le_one p)
    have hL : ∑' p : Nat.Primes, (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-((j : ℂ) * s)) =
        LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s) :=
      tsum_primes_eq_LSeries (fun n => (e n : ℂ)) (fun n hn => by simp [he.prime n hn]) _
    rw [← hL]
    exact hsum.hasSum.div_const _
  have hB : Summable fun p : Nat.Primes => (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded (summable_editMaj (a := 1) (by norm_num)) fun p =>
      norm_edit_mul_logRem_le he p (by norm_num) hs.le
  have hterm : ∀ p : Nat.Primes, (e p : ℂ) * logRemOf k (((p : ℕ) : ℂ) ^ (-s)) =
      (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s)) -
        ∑ j ∈ Icc 2 k, (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-((j : ℂ) * s)) / j := fun p => by
    rw [logRemOf_eq hk, mul_sub, mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [← Complex.cpow_nat_mul, show (j : ℂ) * -s = -((j : ℂ) * s) by ring]
    ring
  have hQ : editRemOf k e s =
      editRem e s - ∑ j ∈ Icc 2 k, LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s) / j := by
    refine HasSum.tsum_eq ?_
    have h := hB.hasSum.sub (hasSum_sum hEj)
    rw [show (fun p : Nat.Primes => (e p : ℂ) * logRemOf k (((p : ℕ) : ℂ) ^ (-s))) = _ from
      funext hterm]
    exact h
  rw [hQ]
  ring

/-! ## Orders -/

/-- The vanishing order of a finite product is the sum of the vanishing orders. -/
theorem analyticOrderAt_prod_eq_sum {ι : Type*} (t : Finset ι) (g : ι → ℂ → ℂ) {w : ℂ}
    (hg : ∀ i ∈ t, AnalyticAt ℂ (g i) w) :
    analyticOrderAt (∏ i ∈ t, g i) w = ∑ i ∈ t, analyticOrderAt (g i) w := by
  classical
  induction t using Finset.induction with
  | empty =>
      simp only [prod_empty, sum_empty]
      exact analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Pi.one_apply]; exact one_ne_zero))
  | insert a t ha ih =>
      rw [prod_insert ha, sum_insert ha,
        analyticOrderAt_mul (hg a (mem_insert_self a t))
          (Finset.analyticAt_prod t (fun i hi => hg i (mem_insert_of_mem hi))),
        ih (fun i hi => hg i (mem_insert_of_mem hi))]

/-- The order of `s ↦ F(j s)` at `s₁` is the order of `F` at `j s₁`. -/
theorem analyticOrderAt_comp_mul {F : ℂ → ℂ} {j : ℂ} (hj : j ≠ 0) (s₁ : ℂ) :
    analyticOrderAt (fun s => F (j * s)) s₁ = analyticOrderAt F (j * s₁) := by
  have hg : AnalyticAt ℂ (fun s : ℂ => j * s) s₁ := analyticAt_const.mul analyticAt_id
  have hd : deriv (fun s : ℂ => j * s) s₁ = j := by
    simp
  exact analyticOrderAt_comp_of_deriv_ne_zero (f := F) hg (by rw [hd]; exact hj)

/-! ## The order law -/

/-- The exponential identity behind the law: with `j ∣ N` for every `j`,
`exp(a + Σ_j b_j/j + q)^N = exp(a)^N exp(q)^N Π_j exp(b_j)^{N/j}`. -/
theorem exp_pow_eq_prod {N : ℕ} {t : Finset ℕ} (ht : ∀ j ∈ t, j ≠ 0 ∧ j ∣ N) (a q : ℂ)
    (b : ℕ → ℂ) :
    cexp (a + (∑ j ∈ t, b j / j + q)) ^ N =
      cexp a ^ N * cexp q ^ N * ∏ j ∈ t, cexp (b j) ^ (N / j) := by
  simp only [← Complex.exp_nat_mul, ← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  rw [mul_add, mul_add, mul_sum]
  have hterm : ∀ j ∈ t, (N : ℂ) * (b j / j) = ((N / j : ℕ) : ℂ) * b j := fun j hj => by
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (ht j hj).1
    rw [Nat.cast_div (ht j hj).2 hj0]
    ring
  rw [sum_congr rfl hterm]
  ring

/-- **The order law at multiple `k`.**  Let an edit be summable at `θ`, have count
`A x + O(x^β)`, and let `F` continue the edit exponential to `Re s > c₀`.  At a point `s₁` right
of `β`, `c₀` and `θ/(k+1)`, the orders `n(j)` of `F` at `j s₁` satisfy
`k! ∣ Σ_{j=2}^{k} (k!/j) n(j)`. -/
theorem factorial_dvd_sum_order_of_count {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun n : ℕ => |(e n : ℝ)| * (n : ℝ) ^ (-θ)) {A C β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {c₀ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun n => (e n : ℂ)) s))
    (k : ℕ) {s₁ : ℂ} (h1 : β < s₁.re) (h2 : c₀ < s₁.re) (h3 : θ / (k + 1) < s₁.re)
    {n : ℕ → ℕ} (hn : ∀ j ∈ Icc 2 k, analyticOrderAt F (j * s₁) = n j) :
    k.factorial ∣ ∑ j ∈ Icc 2 k, k.factorial / j * n j := by
  rcases Nat.lt_or_ge k 1 with hk | hk
  · rw [Finset.Icc_eq_empty (by omega), sum_empty]
    exact dvd_zero _
  set N := k.factorial with hNdef
  obtain ⟨G, hG, hGeq⟩ := exists_continuation_of_count (hasIntegerNorms_editSystem e)
    (isDiscrete_editSystem e) hβ hβ1 hN
  have hQ := differentiableOn_editRemOf hk hθ hS
  -- the half-plane of the identity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max β (max c₀ (θ / (k + 1))) := ⟨_, rfl⟩
  have hcβ : β ≤ c := by rw [hc]; exact le_max_left _ _
  have hc₀ : c₀ ≤ c := by rw [hc]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hcθ : θ / (k + 1) ≤ c := by rw [hc]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hcs : c < s₁.re := by rw [hc]; exact max_lt h1 (max_lt h2 h3)
  have hc0 : 0 < c := lt_of_lt_of_le (div_pos hθ (by positivity)) hcθ
  have hUo : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hs₁ : s₁ ∈ {s : ℂ | c < s.re} := hcs
  have hjre : ∀ j ∈ Icc 2 k, ∀ s : ℂ, c < s.re → c₀ < ((j : ℂ) * s).re := fun j hj s hs => by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_trans (by norm_num) (mem_Icc.mp hj).1)
    have hre : ((j : ℂ) * s).re = j * s.re := by simp
    have := mul_le_mul_of_nonneg_right hj1 (hc0.trans hs).le
    rw [hre]; linarith
  have hGc : DifferentiableOn ℂ G {s : ℂ | c < s.re} :=
    hG.mono fun s (hs : c < s.re) => show β < s.re from lt_of_le_of_lt hcβ hs
  have hFc : DifferentiableOn ℂ F {s : ℂ | c < s.re} :=
    hF.mono fun s (hs : c < s.re) => show c₀ < s.re from lt_of_le_of_lt hc₀ hs
  have hQc : DifferentiableOn ℂ (editRemOf k e) {s : ℂ | c < s.re} :=
    hQ.mono fun s (hs : c < s.re) => show θ / (k + 1) < s.re from lt_of_le_of_lt hcθ hs
  have hFj : ∀ j ∈ Icc 2 k, DifferentiableOn ℂ (fun s : ℂ => F ((j : ℂ) * s))
      {s : ℂ | c < s.re} := fun j hj =>
    hF.comp (differentiable_id.const_mul (j : ℂ)).differentiableOn fun s hs => hjre j hj s hs
  set P : ℂ → ℂ := fun s => zetaResidueUnit s * F s * Complex.exp (editRemOf k e s) with hPdef
  have hP : DifferentiableOn ℂ P {s : ℂ | c < s.re} :=
    (differentiable_zetaResidueUnit.differentiableOn.mul hFc).mul hQc.cexp
  set R : ℂ → ℂ := fun s => P s ^ N * ∏ j ∈ Icc 2 k, F ((j : ℂ) * s) ^ (N / j) with hRdef
  have hR : DifferentiableOn ℂ R {s : ℂ | c < s.re} :=
    (hP.pow N).mul (DifferentiableOn.fun_finsetProd
      (f := fun (j : ℕ) (s : ℂ) => F ((j : ℂ) * s) ^ (N / j)) fun j hj => (hFj j hj).pow _)
  -- the identity on `Re s > 1`
  have hdiv : ∀ j ∈ Icc 2 k, j ≠ 0 ∧ j ∣ N := fun j hj =>
    ⟨by have := (mem_Icc.mp hj).1; omega,
      Nat.dvd_factorial (by have := (mem_Icc.mp hj).1; omega) (mem_Icc.mp hj).2⟩
  have hagree : ∀ s : ℂ, 1 < s.re → G s ^ N = R s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hFjs : ∀ j ∈ Icc 2 k, F ((j : ℂ) * s) =
        Complex.exp (LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s)) := fun j hj => by
      refine hFeq _ ?_
      have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast (mem_Icc.mp hj).1
      have hre : ((j : ℂ) * s).re = j * s.re := by simp
      have := mul_le_mul_of_nonneg_right hj2 (by linarith : (0 : ℝ) ≤ s.re)
      rw [hre]; linarith
    have hprod : ∏ j ∈ Icc 2 k, F ((j : ℂ) * s) ^ (N / j) =
        ∏ j ∈ Icc 2 k, Complex.exp (LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s)) ^ (N / j) :=
      prod_congr rfl fun j hj => by rw [hFjs j hj]
    have hexp := exp_pow_eq_prod hdiv (LSeries (fun n => (e n : ℂ)) s) (editRemOf k e s)
      (fun j => LSeries (fun n => (e n : ℂ)) ((j : ℂ) * s))
    simp only [hRdef, hPdef]
    rw [hGeq s hs, editSystem_zetaSeriesC he hs, editRem_eq_sum_add he hk hs,
      zetaResidueUnit_of_ne hs1, hFeq s hs, hprod]
    -- `s − 1` as an atom, so that `ring` distributes the power over the product
    generalize s - 1 = t
    linear_combination (t * riemannZeta s) ^ N * hexp
  have hon := eqOn_halfPlane (c := c) (F₁ := fun s => G s ^ N) (F₂ := R) (hGc.pow N) hR hagree
  -- orders at `s₁`
  have hGan : AnalyticAt ℂ G s₁ := hGc.analyticAt (hUo.mem_nhds hs₁)
  have hPan : AnalyticAt ℂ P s₁ := hP.analyticAt (hUo.mem_nhds hs₁)
  have hFjan : ∀ j ∈ Icc 2 k, AnalyticAt ℂ (fun s : ℂ => F ((j : ℂ) * s)) s₁ := fun j hj =>
    (hFj j hj).analyticAt (hUo.mem_nhds hs₁)
  have hPpow : AnalyticAt ℂ (P ^ N) s₁ := hPan.pow N
  have hFjpow : ∀ j ∈ Icc 2 k,
      AnalyticAt ℂ ((fun s : ℂ => F ((j : ℂ) * s)) ^ (N / j)) s₁ := fun j hj =>
    (hFjan j hj).pow _
  have hordL : analyticOrderAt (G ^ N) s₁ = N • analyticOrderAt G s₁ := analyticOrderAt_pow hGan N
  have hordR : analyticOrderAt R s₁ =
      N • analyticOrderAt P s₁ + ∑ j ∈ Icc 2 k, (N / j) • (n j : ℕ∞) := by
    have hRfun : R = P ^ N * ∏ j ∈ Icc 2 k, (fun s : ℂ => F ((j : ℂ) * s)) ^ (N / j) := by
      funext s
      simp only [hRdef, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
    rw [hRfun, analyticOrderAt_mul hPpow (Finset.analyticAt_prod _ hFjpow),
      analyticOrderAt_pow hPan, analyticOrderAt_prod_eq_sum _ _ hFjpow]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [analyticOrderAt_pow (hFjan j hj),
      analyticOrderAt_comp_mul (by exact_mod_cast (hdiv j hj).1) s₁, hn j hj]
  have hev : (G ^ N) =ᶠ[𝓝 s₁] R :=
    eventuallyEq_of_mem (hUo.mem_nhds hs₁) fun s hs => by
      show G s ^ N = R s
      exact hon hs
  have hord : N • analyticOrderAt G s₁ =
      N • analyticOrderAt P s₁ + ∑ j ∈ Icc 2 k, (N / j) • (n j : ℕ∞) :=
    hordL.symm.trans ((analyticOrderAt_congr hev).trans hordR)
  -- the order of `G` is finite: `G(2) ≠ 0` on the connected half-plane `Re s > β`
  have hUβ : IsOpen {s : ℂ | β < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have hG2 : G 2 ≠ 0 := by
    rw [hGeq 2 (by rw [h2re]; norm_num), editSystem_zetaSeriesC he (by rw [h2re]; norm_num)]
    exact mul_ne_zero (by norm_num) (mul_ne_zero
      (riemannZeta_ne_zero_of_one_lt_re (by rw [h2re]; norm_num)) (Complex.exp_ne_zero _))
  have hGfin : analyticOrderAt G s₁ ≠ ⊤ :=
    (hG.analyticOnNhd hUβ).analyticOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt β).isPreconnected (show β < (2 : ℂ).re by rw [h2re]; linarith)
      (show β < s₁.re from h1)
      (by rw [analyticOrderAt_eq_zero.mpr (Or.inr hG2)]; simp)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hGfin
  have hN0 : N ≠ 0 := Nat.factorial_ne_zero k
  have hcast : ∀ x y : ℕ, x • (y : ℕ∞) = ((x * y : ℕ) : ℕ∞) := fun x y => by
    rw [nsmul_eq_mul, Nat.cast_mul]
  have hPfin : analyticOrderAt P s₁ ≠ ⊤ := by
    intro htop
    have htopN : N • (⊤ : ℕ∞) = ⊤ := by
      rw [nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hN0)]
    rw [← ha, htop, htopN, top_add, hcast] at hord
    exact ENat.coe_ne_top _ hord
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hPfin
  rw [← ha, ← hb] at hord
  simp only [hcast] at hord
  rw [← Nat.cast_sum, ← Nat.cast_add] at hord
  have hnat : N * a = N * b + ∑ j ∈ Icc 2 k, N / j * n j := by exact_mod_cast hord
  exact (Nat.dvd_add_right (dvd_mul_right N b)).mp (hnat ▸ dvd_mul_right N a)

/-! ## Consequences -/

/-- The order of the continuation `F` of the edit exponential is finite at every point of its
half-plane: `F(2) = e^{E(2)} ≠ 0`. -/
theorem analyticOrderAt_ne_top_of_continuation {e : ℕ → ℤ} {c₀ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun n => (e n : ℂ)) s))
    {z : ℂ} (hz : c₀ < z.re) : analyticOrderAt F z ≠ ⊤ := by
  have hU : IsOpen {s : ℂ | c₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  set w : ℂ := ((max c₀ 1 + 1 : ℝ) : ℂ) with hw
  have hwre : w.re = max c₀ 1 + 1 := by rw [hw, Complex.ofReal_re]
  have hw0 : F w ≠ 0 := by
    rw [hFeq w (by rw [hwre]; linarith [le_max_right c₀ 1])]
    exact Complex.exp_ne_zero _
  exact (hF.analyticOnNhd hU).analyticOrderAt_ne_top_of_isPreconnected
    (convex_halfSpace_re_gt c₀).isPreconnected
    (show c₀ < w.re by rw [hwre]; linarith [le_max_left c₀ 1]) hz
    (by rw [analyticOrderAt_eq_zero.mpr (Or.inr hw0)]; simp)

/-- **Zeros beyond `p` times the count exponent have order divisible by `p`.**  Let an edit be
summable at `θ`, have count `A x + O(x^β)`, and let `F` continue the edit exponential to
`Re s > c₀`.  A zero `ρ` of `F` of order `m` with `Re ρ > p max(β, c₀, θ/(p+1))`, `p` prime, has
`p ∣ m`. -/
theorem prime_dvd_order_of_count {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun n : ℕ => |(e n : ℝ)| * (n : ℝ) ^ (-θ)) {A C β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {c₀ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun n => (e n : ℂ)) s))
    {p : ℕ} (hp : p.Prime) {ρ : ℂ} {m : ℕ} (hm : analyticOrderAt F ρ = m)
    (h1 : p * β < ρ.re) (h2 : p * c₀ < ρ.re) (h3 : p * (θ / (p + 1)) < ρ.re) : p ∣ m := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set s₁ : ℂ := ρ / p with hs₁
  have hre : s₁.re = ρ.re / p := by rw [hs₁]; simp
  have hs₁β : β < s₁.re := by rw [hre, lt_div_iff₀ hp0]; linarith
  have hs₁c : c₀ < s₁.re := by rw [hre, lt_div_iff₀ hp0]; linarith
  have hs₁θ : θ / (p + 1) < s₁.re := by rw [hre, lt_div_iff₀ hp0]; linarith
  have hs₁0 : 0 < s₁.re := lt_of_le_of_lt (div_pos hθ (by positivity)).le hs₁θ
  -- the orders at the multiples `j s₁`
  set n : ℕ → ℕ := fun j => (analyticOrderAt F ((j : ℂ) * s₁)).toNat with hndef
  have hn : ∀ j ∈ Icc 2 p, analyticOrderAt F (j * s₁) = n j := fun j hj => by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_trans (by norm_num) (mem_Icc.mp hj).1)
    have hjre : c₀ < ((j : ℂ) * s₁).re := by
      have hre' : ((j : ℂ) * s₁).re = j * s₁.re := by simp
      have := mul_le_mul_of_nonneg_right hj1 hs₁0.le
      rw [hre']; linarith
    exact (ENat.coe_toNat (analyticOrderAt_ne_top_of_continuation hF hFeq hjre)).symm
  have hnp : n p = m := by
    have : (p : ℂ) * s₁ = ρ := by rw [hs₁]; field_simp
    simp only [hndef, this, hm, ENat.toNat_coe]
  have hlaw := factorial_dvd_sum_order_of_count he hθ hS hβ hβ1 hN hF hFeq p hs₁β hs₁c hs₁θ hn
  -- modulo `p` only the term `j = p` survives
  have hfp : p.factorial / p = (p - 1).factorial := by
    rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.mul_div_cancel_left _ hp.pos]
  have hI : Icc 2 p = insert p (Ico 2 p) := by
    have := hp.two_le
    ext j; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  have hsplit : ∑ j ∈ Icc 2 p, p.factorial / j * n j =
      (p - 1).factorial * m + ∑ j ∈ Ico 2 p, p.factorial / j * n j := by
    rw [hI, sum_insert (by simp), hnp, hfp]
  have hlow : p ∣ ∑ j ∈ Ico 2 p, p.factorial / j * n j := by
    refine dvd_sum fun j hj => dvd_mul_of_dvd_left ?_ _
    obtain ⟨hj2, hjp⟩ := mem_Ico.mp hj
    have hjd : j ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    rw [← Nat.mul_factorial_pred hp.ne_zero, Nat.mul_div_assoc _ hjd]
    exact dvd_mul_right _ _
  have htop : p ∣ (p - 1).factorial * m := by
    rw [hsplit] at hlaw
    exact (Nat.dvd_add_left hlow).mp ((Nat.dvd_factorial hp.pos le_rfl).trans hlaw)
  rcases (Nat.Prime.dvd_mul hp).mp htop with h | h
  · have h2 := hp.two_le
    exact absurd ((Nat.Prime.dvd_factorial hp).mp h) (by omega)
  · exact h

/-- **Isolated multiples.**  If `F` has no zero at `jρ/k` for `2 ≤ j < k`, a zero `ρ` with
`Re ρ > k max(β, c₀, θ/(k+1))` has order divisible by `k`. -/
theorem dvd_order_of_count_of_ne_zero {e : ℕ → ℤ} (he : IsEdit e) {θ : ℝ} (hθ : 0 < θ)
    (hS : Summable fun n : ℕ => |(e n : ℝ)| * (n : ℝ) ^ (-θ)) {A C β : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β)
    {c₀ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re})
    (hFeq : ∀ s : ℂ, 1 < s.re → F s = Complex.exp (LSeries (fun n => (e n : ℂ)) s))
    {k : ℕ} (hk : 2 ≤ k) {ρ : ℂ} {m : ℕ} (hm : analyticOrderAt F ρ = m)
    (hiso : ∀ j ∈ Ico 2 k, F (j * (ρ / k)) ≠ 0)
    (h1 : k * β < ρ.re) (h2 : k * c₀ < ρ.re) (h3 : k * (θ / (k + 1)) < ρ.re) : k ∣ m := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  set s₁ : ℂ := ρ / k with hs₁
  have hre : s₁.re = ρ.re / k := by rw [hs₁]; simp
  have hs₁β : β < s₁.re := by rw [hre, lt_div_iff₀ hk0]; linarith
  have hs₁c : c₀ < s₁.re := by rw [hre, lt_div_iff₀ hk0]; linarith
  have hs₁θ : θ / (k + 1) < s₁.re := by rw [hre, lt_div_iff₀ hk0]; linarith
  have hs₁0 : 0 < s₁.re := lt_of_le_of_lt (div_pos hθ (by positivity)).le hs₁θ
  set n : ℕ → ℕ := fun j => (analyticOrderAt F ((j : ℂ) * s₁)).toNat with hndef
  have hn : ∀ j ∈ Icc 2 k, analyticOrderAt F (j * s₁) = n j := fun j hj => by
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_trans (by norm_num) (mem_Icc.mp hj).1)
    have hjre : c₀ < ((j : ℂ) * s₁).re := by
      have hre' : ((j : ℂ) * s₁).re = j * s₁.re := by simp
      have := mul_le_mul_of_nonneg_right hj1 hs₁0.le
      rw [hre']; linarith
    exact (ENat.coe_toNat (analyticOrderAt_ne_top_of_continuation hF hFeq hjre)).symm
  have hnk : n k = m := by
    have : (k : ℂ) * s₁ = ρ := by rw [hs₁]; field_simp
    simp only [hndef, this, hm, ENat.toNat_coe]
  have hn0 : ∀ j ∈ Ico 2 k, n j = 0 := fun j hj => by
    simp only [hndef]
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (hiso j hj))]
    rfl
  have hlaw := factorial_dvd_sum_order_of_count he hθ hS hβ hβ1 hN hF hFeq k hs₁β hs₁c hs₁θ hn
  have hfk : k.factorial / k = (k - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : k ≠ 0), Nat.mul_div_cancel_left _ (by omega)]
  have hI : Icc 2 k = insert k (Ico 2 k) := by
    ext j; simp only [mem_Icc, mem_insert, mem_Ico]; omega
  have hsum : ∑ j ∈ Icc 2 k, k.factorial / j * n j = (k - 1).factorial * m := by
    rw [hI, sum_insert (by simp), hnk, hfk,
      sum_eq_zero fun j hj => by rw [hn0 j hj, mul_zero], add_zero]
  rw [hsum, ← Nat.mul_factorial_pred (by omega : k ≠ 0), mul_comm k] at hlaw
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos _) hlaw

/-! ## Multiple twins -/

/-- The target `M · (−2 Re k^{ρ−1})` of an `M`-fold zero pair has Dirichlet series
`−M (ζ(s + 1 − ρ) + ζ(s + 1 − ρ̄))`. -/
theorem lseriesHasSum_mul_target {ρ s : ℂ} (hs : ρ.re < s.re) (M : ℕ) :
    LSeriesHasSum (fun k : ℕ => (((M : ℝ) * target ρ k : ℝ) : ℂ)) s
      ((M : ℂ) * -(riemannZeta (s - (ρ - 1)) + riemannZeta (s - ((starRingEnd ℂ) ρ - 1)))) := by
  have h := (lseriesHasSum_target hs).mul_left (M : ℂ)
  have hfun : LSeries.term (fun k : ℕ => (((M : ℝ) * target ρ k : ℝ) : ℂ)) s =
      fun n => (M : ℂ) * LSeries.term (fun k : ℕ => (target ρ k : ℂ)) s n := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      push_cast
      ring
  show HasSum (LSeries.term _ s) _
  rw [hfun]
  exact h

/-- **An `M`-fold twin pays `Re ρ/p` in the count for every prime `p ∤ M`.**  For a non-real
`ρ` with `1/2 < Re ρ` and `Re ρ (1 − 1/p) < 13/30`, every count exponent `β` of the greedy edit
of the target `M · (−2 Re k^{ρ−1})` has `β ≥ Re ρ/p`.  Its exponential is
`C ((s − ρ)(s − ρ̄))^M e^{K}` on a half-plane containing `ρ/p`, with a zero of order `M` at `ρ`. -/
theorem re_div_le_of_count_multiple_edit {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (him : ρ.im ≠ 0) {M : ℕ}
    {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (hρp : ρ.re * (1 - 1 / p) < 13 / 30) {A C β : ℝ}
    (hβ : 0 ≤ β)
    (hN : ∀ x : ℝ, 1 ≤ x → |((editSystem (gedit fun k => (M : ℝ) * target ρ k)).countBall x : ℝ) -
      A * x| ≤ C * x ^ β) :
    ρ.re / p ≤ β := by
  by_contra hlt
  have hβρ : β < ρ.re / p := not_le.mp hlt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hρ0 : 0 < ρ.re := by linarith
  have hinv : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hρ1 : ρ.re < 13 / 15 := by nlinarith
  have hρp' : ρ.re - 13 / 30 < ρ.re / p := by
    have : ρ.re / p = ρ.re * (1 / p) := by ring
    rw [this]; nlinarith
  have hρdiv : ρ.re / p < ρ.re := div_lt_self hρ0 (by linarith)
  -- a half-plane `Re s > c₀` with `Re ρ − 13/30 < c₀ < Re ρ/p`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (ρ.re - 13 / 30 + ρ.re / p) / 2 := ⟨_, rfl⟩
  have hc₀1 : ρ.re - 13 / 30 < c₀ := by rw [hc₀]; linarith
  have hc₀2 : c₀ < ρ.re / p := by rw [hc₀]; linarith
  have hc₀0 : 0 < c₀ := by linarith
  -- the discrepancy of the greedy edit is `O(n^{c₀})`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (17 / 30 + (c₀ + (1 - ρ.re))) / 2 := ⟨_, rfl⟩
  have hα0 : 17 / 30 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have hαc : α - (1 - ρ.re) ≤ c₀ := by rw [hα]; linarith
  obtain ⟨X, -, hwin⟩ := RHTower.exists_theta_window_lower_seventeenThirtieths hα0 hα1
  set m : ℕ → ℝ := fun k => (M : ℝ) * target ρ k with hmdef
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hm : ∀ k : ℕ, 1 ≤ k → |m k| ≤ 2 * M * (k : ℝ) ^ (-(1 - ρ.re)) := fun k hk => by
    have h := abs_target_le ρ hk
    rw [show ρ.re - 1 = -(1 - ρ.re) by ring] at h
    simp only [hmdef, abs_mul, abs_of_nonneg hM0]
    nlinarith
  obtain ⟨K₀, hK₀, hdisc⟩ := exists_abs_gdisc_le_rpow_of_abs_le (m := m) (A := 2 * M)
    (η := 1 - ρ.re) (c := c₀) (by positivity) (by linarith) (by linarith) hm hα1 hc₀0 hαc hwin
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable (fun k => (m k : ℂ)) s := by
    intro s hs
    refine LSeriesSummable_of_le_const_mul_rpow (x := 1 - (1 - ρ.re)) (by linarith)
      ⟨2 * M, fun n hn => ?_⟩
    show ‖((m n : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, show 1 - (1 - ρ.re) - 1 = -(1 - ρ.re) by ring]
    exact hm n (Nat.one_le_iff_ne_zero.mpr hn)
  have hm0 : m 0 = 0 := by simp only [hmdef, target_zero (by linarith), mul_zero]
  set ρc : ℂ := (starRingEnd ℂ) ρ with hρc
  have hL : ∀ s : ℂ, 1 < s.re →
      ((s - ρ) * (s - ρc)) ^ M ≠ 0 ∧
        DifferentiableAt ℂ (fun z : ℂ => ((z - ρ) * (z - ρc)) ^ M) s ∧
        logDeriv (fun z : ℂ => ((z - ρ) * (z - ρc)) ^ M) s =
          -LSeries (fun k => (m k : ℂ)) s -
            (M : ℂ) * (zetaRegular (s - (ρ - 1)) + zetaRegular (s - (ρc - 1))) := by
    intro s hs
    obtain ⟨hne, hd, hld⟩ := logDeriv_pair_eq (ρ := ρ) (s := s) (by linarith) hs
    have hLm := (lseriesHasSum_mul_target (ρ := ρ) (s := s) (by linarith) M).LSeries_eq
    have hLt := (lseriesHasSum_target (ρ := ρ) (s := s) (by linarith)).LSeries_eq
    refine ⟨pow_ne_zero M hne, hd.pow M, ?_⟩
    rw [logDeriv_fun_pow hd M, hld, hLt]
    simp only [hmdef]
    rw [hLm]
    ring
  obtain ⟨C₁, K, hC₁, hK, hfac⟩ := exists_exp_geditSeries_eq (m := m) hm0 hK₀ hc₀0
    (by linarith) hdisc hsumm (L := fun s => ((s - ρ) * (s - ρc)) ^ M)
    (Φ₀ := fun s => (M : ℂ) * (zetaRegular (s - (ρ - 1)) + zetaRegular (s - (ρc - 1))))
    ((differentiable_const _).mul
      ((differentiable_zetaRegular.comp (differentiable_id.sub_const _)).add
        (differentiable_zetaRegular.comp (differentiable_id.sub_const _)))).differentiableOn hL
  -- the continuation of the edit exponential and its zero of order `M` at `ρ`
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ,
      F = fun s => C₁ * ((s - ρ) * (s - ρc)) ^ M * Complex.exp (K s) := ⟨_, rfl⟩
  have hU₀ : IsOpen {s : ℂ | c₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ F {s : ℂ | c₀ < s.re} := by
    rw [hFdef]
    exact ((differentiableOn_const C₁).mul (((differentiableOn_id.sub_const ρ).mul
      (differentiableOn_id.sub_const _)).pow M)).mul hK.cexp
  have hFeq : ∀ s : ℂ, 1 < s.re →
      F s = Complex.exp (LSeries (fun k => (gedit m k : ℂ)) s) := fun s hs => by
    rw [hFdef]
    exact (hfac s hs).symm
  have hρmem : ρ ∈ {s : ℂ | c₀ < s.re} := show c₀ < ρ.re by linarith
  have hfan : AnalyticAt ℂ (fun s : ℂ => C₁ * (s - ρc) ^ M * Complex.exp (K s)) ρ := by
    have hd : DifferentiableOn ℂ (fun s : ℂ => C₁ * (s - ρc) ^ M * Complex.exp (K s))
        {s : ℂ | c₀ < s.re} :=
      ((differentiableOn_const C₁).mul ((differentiableOn_id.sub_const _).pow M)).mul hK.cexp
    exact hd.analyticAt (hU₀.mem_nhds hρmem)
  have hne : ρ - ρc ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    rw [Complex.sub_im, hρc, Complex.conj_im, Complex.zero_im] at h'
    exact him (by linarith)
  have hord : analyticOrderAt F ρ = (M : ℕ∞) := by
    refine (hF.analyticAt (hU₀.mem_nhds hρmem)).analyticOrderAt_eq_natCast.mpr
      ⟨_, hfan, mul_ne_zero (mul_ne_zero hC₁ (pow_ne_zero M hne)) (Complex.exp_ne_zero _),
        Filter.Eventually.of_forall fun s => ?_⟩
    rw [hFdef]
    show C₁ * ((s - ρ) * (s - ρc)) ^ M * Complex.exp (K s) =
      (s - ρ) ^ M • (C₁ * (s - ρc) ^ M * Complex.exp (K s))
    rw [smul_eq_mul, mul_pow]
    ring
  -- the edit is summable at `θ = Re ρ (1 + 1/(2p))`, and `θ/(p+1) < Re ρ/p`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = ρ.re * (1 + 1 / (2 * p)) := ⟨_, rfl⟩
  have hθρ : ρ.re < θ := by
    rw [hθ]
    have : 0 < 1 / (2 * (p : ℝ)) := by positivity
    nlinarith
  have hS : Summable fun k : ℕ => |(gedit m k : ℝ)| * (k : ℝ) ^ (-θ) :=
    summable_abs_gedit_rpow (m := m) hρ0.le (K := M * (2 / ρ.re)) (by positivity)
      (fun n _ => by
        have h := sum_abs_target_le hρ0 (by linarith) n
        calc ∑ k ∈ Finset.Ioc 0 n, |m k| = M * ∑ k ∈ Finset.Ioc 0 n, |target ρ k| := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [hmdef, abs_mul, abs_of_nonneg hM0]
          _ ≤ M * (2 / ρ.re * (n : ℝ) ^ ρ.re) := mul_le_mul_of_nonneg_left h hM0
          _ = M * (2 / ρ.re) * (n : ℝ) ^ ρ.re := by ring) hθρ
  have hpθ : (p : ℝ) * (θ / (p + 1)) < ρ.re := by
    have hpθ' : (p : ℝ) * θ = ρ.re * p + ρ.re / 2 := by
      rw [hθ]; field_simp; ring
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hdvd := prime_dvd_order_of_count (isEdit_gedit m) (θ := θ) (by linarith) hS hβ
    (by linarith) hN hF hFeq hp hord
    (by have := (lt_div_iff₀ hp0).mp hβρ; linarith)
    (by have := (lt_div_iff₀ hp0).mp hc₀2; linarith) hpθ
  exact hpM hdvd

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.BalanceLaw
