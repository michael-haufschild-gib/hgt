import GaloisForLFunctions.RHTower.WeilConeSoundararajanSplit

/-!
# Large values of `log|F_lam|` on the Weil cone

Let `lam` be full-cone Weil-positive with `|lam(n)| ≤ κ log n` and summable rest weight
`A_c = Σ_{n ∉ {p, p²}} |lam(n)|/(√n log n)`.  Fix `σ = ½ + 1/log T`.  For a level `V`, take the
polynomial length `L = log T/(εV)` and split the primes at `z = e^{L/ℓ}`, `ℓ = log log T`.  By the
split Soundararajan inequality (`re_producerLogZeta_le_split`), `log|F(σ+it)| ≥ V` forces one of

* `|S₁(t)| ≥ (1 − 4ε)V`  (primes `≤ z`),
* `|S₂(t)| ≥ εV/2`  (primes in `(z, e^L)`),
* `|S_{p²}(2t)| ≥ εV/2`  (prime squares),

once `V ≥ (A_c + M₂ + 2)/ε` (`le_norm_split_of_le`).  Each event is controlled by the high-moment
bound for prime polynomials in the form `T·(e²/δ)·e^{−k}` (`measureReal_large_primePoly_le_exp`),
with `k` limited by the length condition `8N^k(1 + k log N) ≤ T`.
-/

open Complex Set Filter MeasureTheory

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz WeilConeMoments

/-! ### Moments in exponential form -/

/-- **High moments as an exponential tail.**  If `e^δ k W ≤ q V²` for a variance bound `W` and
`q > 0`, then `|{τ ∈ (T₁, T₂] : |E_a(½ − d + iτ)| ≥ V}| ≤ (e²/δ)(T₂ − T₁)(q/e)^k`. -/
theorem measureReal_large_primePoly_le_pow {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) (d : ℝ) (k : ℕ)
    {T₁ T₂ V W δ q : ℝ} (hT : T₁ ≤ T₂) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hq : 0 < q)
    (hW : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤ W)
    (hkW : Real.exp δ * k * W ≤ q * V ^ 2)
    (hN : 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ T₂ - T₁) :
    (volume.restrict (Ioc T₁ T₂)).real
        {τ | V ≤ ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ)‖} ≤
      Real.exp 2 / δ * (T₂ - T₁) * (q / Real.exp 1) ^ k := by
  have hT0 : 0 ≤ T₂ - T₁ := by linarith
  have he1 := Real.exp_pos 1
  have he2 : 1 ≤ Real.exp 2 / δ := by
    rw [le_div_iff₀ hδ]
    have : δ ≤ Real.exp 2 := hδ1.trans (by
      have := Real.add_one_le_exp 2; linarith)
    linarith
  have htot : (volume.restrict (Ioc T₁ T₂)).real
      {τ | V ≤ ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ)‖} ≤ T₂ - T₁ := by
    refine (measureReal_mono (subset_univ _) (by simp [Real.volume_Ioc])).trans (le_of_eq ?_)
    rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc,
      ENNReal.toReal_ofReal hT0]
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [pow_zero, mul_one]
    calc _ ≤ T₂ - T₁ := htot
      _ ≤ Real.exp 2 / δ * (T₂ - T₁) := le_mul_of_one_le_left hT0 he2
  have hk1 : 1 ≤ k := hkpos
  have h := measureReal_large_primePoly_le ha haN d hk1 hT hV hN
  set W₀ : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) with hW₀
  have hW₀0 : 0 ≤ W₀ := Finset.sum_nonneg fun n _ => by positivity
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hbase : k * W₀ / (Real.exp 1 * V ^ 2) ≤ q / Real.exp 1 * Real.exp (-δ) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : k * W₀ ≤ k * W := mul_le_mul_of_nonneg_left hW (by linarith)
    have h3 : q / Real.exp 1 * Real.exp (-δ) * (Real.exp 1 * V ^ 2) = q * V ^ 2 * Real.exp (-δ) := by
      field_simp
    rw [h3]
    have h4 : k * W ≤ q * V ^ 2 * Real.exp (-δ) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]; linarith
    linarith
  have hbase0 : 0 ≤ k * W₀ / (Real.exp 1 * V ^ 2) := by positivity
  have hpow : (k * W₀ / (Real.exp 1 * V ^ 2)) ^ k ≤ (q / Real.exp 1 * Real.exp (-δ)) ^ k :=
    pow_le_pow_left₀ hbase0 hbase k
  rw [mul_pow, ← Real.exp_nat_mul] at hpow
  have hsqrt : Real.sqrt k * Real.exp (k * -δ) ≤ 1 / δ := by
    have h1 : Real.sqrt k ≤ k := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h2 : δ * k ≤ Real.exp (δ * k) := by
      have := Real.add_one_le_exp (δ * k); linarith
    have h3 : Real.exp (k * -δ) = 1 / Real.exp (δ * k) := by
      rw [show (k : ℝ) * -δ = -(δ * k) by ring, Real.exp_neg, one_div]
    rw [h3, mul_one_div, div_le_div_iff₀ (Real.exp_pos _) hδ]
    nlinarith [Real.exp_pos (δ * k)]
  have hqe : 0 ≤ (q / Real.exp 1) ^ k := by positivity
  calc _ ≤ 2 * Real.exp 1 * Real.sqrt k * (T₂ - T₁) * (k * W₀ / (Real.exp 1 * V ^ 2)) ^ k := h
    _ ≤ 2 * Real.exp 1 * Real.sqrt k * (T₂ - T₁) * ((q / Real.exp 1) ^ k * Real.exp (k * -δ)) := by
        gcongr
    _ = 2 * Real.exp 1 * (T₂ - T₁) * (Real.sqrt k * Real.exp (k * -δ)) * (q / Real.exp 1) ^ k := by
        ring
    _ ≤ 2 * Real.exp 1 * (T₂ - T₁) * (1 / δ) * (q / Real.exp 1) ^ k := by gcongr
    _ ≤ Real.exp 2 / δ * (T₂ - T₁) * (q / Real.exp 1) ^ k := by
        have h2e : 2 * Real.exp 1 ≤ Real.exp 2 := by
          have h := Real.add_one_le_exp 1
          have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        have : 2 * Real.exp 1 * (T₂ - T₁) * (1 / δ) = 2 * Real.exp 1 / δ * (T₂ - T₁) := by ring
        rw [this]
        gcongr

/-- The case `q = 1`: an `e^{−k}` tail. -/
theorem measureReal_large_primePoly_le_exp {a : ArithmeticFunction ℂ} {N : ℕ}
    (ha : ∀ k, a k ≠ 0 → k.Prime) (haN : ∀ k, a k ≠ 0 → k ≤ N) (d : ℝ) (k : ℕ)
    {T₁ T₂ V W δ : ℝ} (hT : T₁ ≤ T₂) (hV : 0 < V) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hW : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤ W)
    (hkW : Real.exp δ * k * W ≤ V ^ 2)
    (hN : 8 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log (N ^ k : ℕ)) ≤ T₂ - T₁) :
    (volume.restrict (Ioc T₁ T₂)).real
        {τ | V ≤ ‖edPoly (⇑a) (Finset.Icc 1 N) (displacedLinePt d τ)‖} ≤
      Real.exp 2 / δ * (T₂ - T₁) * Real.exp (-k) := by
  have h := measureReal_large_primePoly_le_pow ha haN d k hT hV hδ hδ1 one_pos hW
    (by linarith) hN
  rwa [one_div, inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg, show -((k : ℝ) * 1) = -k by ring]
    at h

/-! ### Splitting the primes at `z` -/

theorem primeCoeff_zero (lam : ℕ → ℝ) (L : ℝ) : primeCoeff lam L 0 = 0 := by
  rw [primeCoeff_apply, if_neg (fun h => Nat.not_prime_zero h.1)]

/-- Prime coefficients up to `z`. -/
def primeCoeffLE (lam : ℕ → ℝ) (L : ℝ) (z : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ z then primeCoeff lam L n else 0, by simp⟩

/-- Prime coefficients above `z`. -/
def primeCoeffGT (lam : ℕ → ℝ) (L : ℝ) (z : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ z then 0 else primeCoeff lam L n, by simp⟩

theorem primeCoeffLE_apply (lam : ℕ → ℝ) (L : ℝ) (z n : ℕ) :
    primeCoeffLE lam L z n = if n ≤ z then primeCoeff lam L n else 0 := rfl

theorem primeCoeffGT_apply (lam : ℕ → ℝ) (L : ℝ) (z n : ℕ) :
    primeCoeffGT lam L z n = if n ≤ z then 0 else primeCoeff lam L n := rfl

theorem edPoly_primeCoeff_split (lam : ℕ → ℝ) (L : ℝ) (z : ℕ) (S : Finset ℕ) (w : ℂ) :
    edPoly (⇑(primeCoeff lam L)) S w =
      edPoly (⇑(primeCoeffLE lam L z)) S w + edPoly (⇑(primeCoeffGT lam L z)) S w := by
  unfold edPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primeCoeffLE_apply, primeCoeffGT_apply]
  split_ifs <;> ring

theorem primeCoeffLE_supp {lam : ℕ → ℝ} {L : ℝ} {z k : ℕ} (h : primeCoeffLE lam L z k ≠ 0) :
    k.Prime ∧ k ≤ z ∧ k ≤ polyLength L := by
  rw [primeCoeffLE_apply] at h
  split_ifs at h with hk
  · exact ⟨primeCoeff_prime h, hk, primeCoeff_le h⟩
  · exact absurd rfl h

theorem primeCoeffGT_supp {lam : ℕ → ℝ} {L : ℝ} {z k : ℕ} (h : primeCoeffGT lam L z k ≠ 0) :
    k.Prime ∧ z < k ∧ k ≤ polyLength L := by
  rw [primeCoeffGT_apply] at h
  split_ifs at h with hk
  · exact absurd rfl h
  · exact ⟨primeCoeff_prime h, by omega, primeCoeff_le h⟩

/-! ### Coefficient bounds -/

theorem norm_primeCoeff_le {lam : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ‖primeCoeff lam L n‖ ≤ κ := by
  rw [primeCoeff_apply]
  split_ifs with h
  · have hn2 := h.1.two_le
    have hl : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (le_max_right (L - Real.log n) 0),
      abs_of_pos (mul_pos hL hl), div_le_iff₀ (mul_pos hL hl)]
    have hmax : max (L - Real.log n) 0 ≤ L := max_le (by linarith) hL.le
    calc |lam n| * max (L - Real.log n) 0 ≤ κ * Real.log n * L :=
          mul_le_mul (hlam n hn2) hmax (le_max_right _ _) (by positivity)
      _ = κ * (L * Real.log n) := by ring
  · rw [norm_zero]; exact hκ

theorem norm_sqCoeff_le {lam : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {L : ℝ} (hL : 0 < L) (n : ℕ) :
    ‖sqCoeff lam L n‖ ≤ κ := by
  rw [sqCoeff_apply]
  split_ifs with h
  · have hn2 := h.1.two_le
    have hq2 : 2 ≤ n ^ 2 := le_trans hn2 (Nat.le_self_pow (by norm_num) n)
    have hl : 0 < Real.log (n ^ 2 : ℕ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n ^ 2))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (le_max_right (L - Real.log (n ^ 2 : ℕ)) 0),
      abs_of_pos (mul_pos hL hl), div_le_iff₀ (mul_pos hL hl)]
    have hmax : max (L - Real.log (n ^ 2 : ℕ)) 0 ≤ L := max_le (by linarith) hL.le
    calc |lam (n ^ 2)| * max (L - Real.log (n ^ 2 : ℕ)) 0 ≤ κ * Real.log (n ^ 2 : ℕ) * L :=
          mul_le_mul (hlam (n ^ 2) hq2) hmax (le_max_right _ _) (by positivity)
      _ = κ * (L * Real.log (n ^ 2 : ℕ)) := by ring
  · rw [norm_zero]; exact hκ

theorem primeCoeffLE_norm_le {lam : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {L : ℝ} (hL : 0 < L) (z n : ℕ) :
    ‖primeCoeffLE lam L z n‖ ≤ κ := by
  rw [primeCoeffLE_apply]; split_ifs
  · exact norm_primeCoeff_le hκ hlam hL n
  · rw [norm_zero]; exact hκ

theorem primeCoeffGT_norm_le {lam : ℕ → ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {L : ℝ} (hL : 0 < L) (z n : ℕ) :
    ‖primeCoeffGT lam L z n‖ ≤ κ := by
  rw [primeCoeffGT_apply]; split_ifs
  · rw [norm_zero]; exact hκ
  · exact norm_primeCoeff_le hκ hlam hL n

/-! ### Variance bounds -/

theorem rpow_le_inv_of_le {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he : e ≤ -1) :
    (n : ℝ) ^ e ≤ 1 / n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ e ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 he
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]

theorem rpow_le_inv_sq_of_le {n : ℕ} (hn : 1 ≤ n) {e : ℝ} (he : e ≤ -2) :
    (n : ℝ) ^ e ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ e ≤ (n : ℝ) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 he
    _ = ((n : ℝ) ^ 2)⁻¹ := by
        rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]

/-- A variance sum restricted to the support of the coefficients. -/
theorem sum_norm_sq_le_of_supp {a : ℕ → ℂ} {κ : ℝ} {P : ℕ → Prop} [DecidablePred P]
    (hsupp : ∀ n, a n ≠ 0 → P n) (hnorm : ∀ n, ‖a n‖ ≤ κ) {e : ℝ} (he : e ≤ -1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ e ≤
      κ ^ 2 * ∑ n ∈ (Finset.Icc 1 N).filter P, 1 / (n : ℝ) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) P]
  have hnot : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ P n), ‖a n‖ ^ 2 * (n : ℝ) ^ e = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [Finset.mem_filter] at hn
    have : a n = 0 := by by_contra h; exact hn.2 (hsupp n h)
    rw [this, norm_zero]; ring
  rw [hnot, add_zero, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  have h1 := rpow_le_inv_of_le hn.1.1 he
  have h2 : ‖a n‖ ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
  exact mul_le_mul h2 h1 (by positivity) (by positivity)

theorem sum_filter_prime_le_mertensS (N z : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Prime ∧ n ≤ z), 1 / (n : ℝ) ≤ Sieve.mertensS z := by
  unfold Sieve.mertensS
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
  rw [Finset.mem_filter] at hn
  rw [Nat.primesLE, Nat.mem_primesBelow]
  exact ⟨by omega, hn.2.1⟩

theorem sum_filter_prime_gt_le_mertensS {N z : ℕ} (hzN : z ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => n.Prime ∧ z < n), 1 / (n : ℝ) ≤
      Sieve.mertensS N - Sieve.mertensS z := by
  unfold Sieve.mertensS
  have hsub : Nat.primesLE z ⊆ Nat.primesLE N := fun p hp => by
    rw [Nat.primesLE, Nat.mem_primesBelow] at hp ⊢; exact ⟨by omega, hp.2⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => by positivity)
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  rw [Finset.mem_sdiff, Nat.primesLE, Nat.mem_primesBelow, Nat.primesLE, Nat.mem_primesBelow]
  exact ⟨⟨by omega, hn.2.1⟩, fun h => by omega⟩

theorem sum_norm_sq_le_two {a : ℕ → ℂ} {κ : ℝ} (hnorm : ∀ n, ‖a n‖ ≤ κ) {e : ℝ} (he : e ≤ -2)
    (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ e ≤ 2 * κ ^ 2 := by
  have h1 : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (n : ℝ) ^ e ≤
      ∑ n ∈ Finset.Icc 1 N, κ ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2)
      (rpow_le_inv_sq_of_le hn.1 he) (by positivity) (by positivity)
  have h2 : ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) ^ 2)⁻¹ ≤ 2 := by
    have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
    have e : Finset.Ioo 0 (N + 1) = Finset.Icc 1 N := by
      ext n; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    rw [e] at h
    simpa using h
  rw [← Finset.mul_sum] at h1
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  nlinarith


/-! ### The large-value event splits -/

/-- **The event split.**  At `σ = ½ + 1/log T`, with `L = log T/(εV)`, `εV ≥ 1`, `L ≥ 2`,
`T ≤ |t| ≤ 2T`, `log T ≥ log 2 + 6` and `A_c + M₂ + 2 ≤ εV`: if `log|F(σ+it)| ≥ V`, then
`|S₁(t)| ≥ (1−4ε)V` or `|S₂(t)| ≥ εV/2` or `|S_{p²}(2t)| ≥ εV/2`. -/
theorem le_norm_split_of_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {T ε V t : ℝ} (z : ℕ) (hT4 : 4 ≤ T)
    (hlogT : Real.log 2 + 6 ≤ Real.log T) (hε : 0 < ε) (hεV : 1 ≤ ε * V)
    (hL2 : 2 ≤ Real.log T / (ε * V)) (ht1 : T ≤ |t|) (ht2 : |t| ≤ 2 * T)
    (hV0 : (∑' n, restWeight lam n) + ((∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) + 2) ≤ ε * V)
    (hlevel : V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re) :
    (1 - 4 * ε) * V ≤ ‖edPoly (⇑(primeCoeffLE lam (Real.log T / (ε * V)) z))
        (Finset.Icc 1 (polyLength (Real.log T / (ε * V))))
        (displacedLinePt (1 / 2 - (1 / 2 + 1 / (Real.log T / (ε * V)))) t)‖ ∨
      ε * V / 2 ≤ ‖edPoly (⇑(primeCoeffGT lam (Real.log T / (ε * V)) z))
        (Finset.Icc 1 (polyLength (Real.log T / (ε * V))))
        (displacedLinePt (1 / 2 - (1 / 2 + 1 / (Real.log T / (ε * V)))) t)‖ ∨
      ε * V / 2 ≤ ‖edPoly (⇑(sqCoeff lam (Real.log T / (ε * V))))
        (Finset.Icc 1 (polyLength (Real.log T / (ε * V))))
        (displacedLinePt (1 / 2 - 2 * (1 / 2 + 1 / (Real.log T / (ε * V)))) (2 * t))‖ := by
  set L : ℝ := Real.log T / (ε * V) with hLdef
  have hlogTpos : 0 < Real.log T := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hV : 0 < V := by
    by_contra h; push Not at h; nlinarith
  have hεVpos : 0 < ε * V := by linarith
  have hLpos : 0 < L := by linarith
  have hLle : L ≤ Real.log T := by
    rw [hLdef, div_le_iff₀ hεVpos]; nlinarith
  have hσ : 1 / 2 < 1 / 2 + 1 / Real.log T := by
    have : 0 < 1 / Real.log T := by positivity
    linarith
  have hσL : 1 / 2 + 1 / Real.log T ≤ 1 / 2 + 1 / L := by
    have : 1 / Real.log T ≤ 1 / L := one_div_le_one_div_of_le hLpos hLle
    linarith
  have ht4 : 4 ≤ |t| := hT4.trans ht1
  have hexp : Real.exp L ≤ |t| := by
    have hT0 : 0 < T := by linarith
    calc Real.exp L ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr hLle
      _ = T := Real.exp_log hT0
      _ ≤ |t| := ht1
  have hmain := re_producerLogZeta_le_split hW hA hσ hσL hL2 ht4 hexp
  rw [edPoly_primeCoeff_split lam L z] at hmain
  set S₁ := edPoly (⇑(primeCoeffLE lam L z)) (Finset.Icc 1 (polyLength L))
    (displacedLinePt (1 / 2 - (1 / 2 + 1 / L)) t)
  set S₂ := edPoly (⇑(primeCoeffGT lam L z)) (Finset.Icc 1 (polyLength L))
    (displacedLinePt (1 / 2 - (1 / 2 + 1 / L)) t)
  set S₃ := edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 (polyLength L))
    (displacedLinePt (1 / 2 - 2 * (1 / 2 + 1 / L)) (2 * t))
  -- the archimedean term
  have harch : (Real.log |t| + 6) / L ≤ 2 * ε * V := by
    have hT0 : 0 < T := by linarith
    have hlt : Real.log |t| ≤ Real.log 2 + Real.log T := by
      rw [← Real.log_mul (by norm_num) hT0.ne']
      exact Real.log_le_log (by linarith) ht2
    rw [div_le_iff₀ hLpos, hLdef]
    have e : 2 * ε * V * (Real.log T / (ε * V)) = 2 * Real.log T := by field_simp
    rw [e]; linarith
  have hre : (S₁ + S₂).re + S₃.re ≤ ‖S₁‖ + ‖S₂‖ + ‖S₃‖ := by
    have h1 := Complex.re_le_norm (S₁ + S₂)
    have h2 := norm_add_le S₁ S₂
    have h3 := Complex.re_le_norm S₃
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have : V ≤ ‖S₁‖ + ‖S₂‖ + ‖S₃‖ + 2 * ε * V + ε * V := by linarith
  nlinarith


/-! ### Measure of a level set -/

theorem edPoly_Icc_eq_of_supp {a : ℕ → ℂ} {M N : ℕ} (hMN : M ≤ N)
    (hsupp : ∀ n, a n ≠ 0 → n ≤ M) (w : ℂ) :
    edPoly a (Finset.Icc 1 N) w = edPoly a (Finset.Icc 1 M) w := by
  unfold edPoly
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hMN) fun n hn hnM => ?_
  rw [Finset.mem_Icc] at hn hnM
  have : a n = 0 := by
    by_contra h; exact hnM ⟨hn.1, hsupp n h⟩
  rw [this, zero_mul]

theorem measureReal_restrict_Ioc_le_volume (T₁ T₂ : ℝ) (A : Set ℝ) :
    (volume.restrict (Ioc T₁ T₂)) A ≠ ⊤ := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono inter_subset_right)

/-- Doubling the variable halves the measure. -/
theorem measureReal_restrict_two_mul {T : ℝ} (g : ℝ → ℂ) (c : ℝ) :
    (volume.restrict (Ioc T (2 * T))).real {t | c ≤ ‖g (2 * t)‖} =
      (1 / 2) * (volume.restrict (Ioc (2 * T) (4 * T))).real {τ | c ≤ ‖g τ‖} := by
  rw [Measure.real, Measure.real, Measure.restrict_apply' measurableSet_Ioc,
    Measure.restrict_apply' measurableSet_Ioc]
  have hset : {t : ℝ | c ≤ ‖g (2 * t)‖} ∩ Ioc T (2 * T) =
      (fun t : ℝ => 2 * t) ⁻¹' ({τ | c ≤ ‖g τ‖} ∩ Ioc (2 * T) (4 * T)) := by
    ext t
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ioc, mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  rw [hset, Real.volume_preimage_mul_left (by norm_num), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  norm_num

/-- **The level-set bound.**  Under the hypotheses of `le_norm_split_of_le`, and for any
`k₁, k₂, k₃` satisfying the variance and length conditions, the measure of
`{t ∈ (T, 2T] : log|F(σ+it)| ≥ V}` is at most `(e²/δ) T (e^{−k₁} + e^{−k₂} + e^{−k₃})`. -/
theorem measureReal_level_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {T ε V δ : ℝ} (z k₁ k₂ k₃ : ℕ)
    (hT4 : 4 ≤ T) (hlogT : Real.log 2 + 6 ≤ Real.log T) (hε : 0 < ε) (hε4 : ε < 1 / 4)
    (hεV : 1 ≤ ε * V) (hL2 : 2 ≤ Real.log T / (ε * V))
    (hV0 : (∑' n, restWeight lam n) + ((∑' n : ℕ, |lam n| / (n : ℝ) ^ (2 : ℝ)) + 2) ≤ ε * V)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {q : ℝ} (hq : 0 < q) (hz : z ≤ polyLength (Real.log T / (ε * V)))
    (hk₁ : Real.exp δ * k₁ * (κ ^ 2 * Sieve.mertensS z) ≤ ((1 - 4 * ε) * V) ^ 2)
    (hN₁ : 8 * ((z ^ k₁ : ℕ) : ℝ) * (1 + Real.log (z ^ k₁ : ℕ)) ≤ T)
    (hk₂ : Real.exp δ * k₂ * (κ ^ 2 * (Sieve.mertensS (polyLength (Real.log T / (ε * V))) -
      Sieve.mertensS z)) ≤ q * (ε * V / 2) ^ 2)
    (hN₂ : 8 * ((polyLength (Real.log T / (ε * V)) ^ k₂ : ℕ) : ℝ) *
      (1 + Real.log (polyLength (Real.log T / (ε * V)) ^ k₂ : ℕ)) ≤ T)
    (hk₃ : Real.exp δ * k₃ * (2 * κ ^ 2) ≤ q * (ε * V / 2) ^ 2)
    (hN₃ : 8 * ((polyLength (Real.log T / (ε * V)) ^ k₃ : ℕ) : ℝ) *
      (1 + Real.log (polyLength (Real.log T / (ε * V)) ^ k₃ : ℕ)) ≤ 2 * T) :
    (volume.restrict (Ioc T (2 * T))).real
        {t | V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ≤
      Real.exp 2 / δ * T * (Real.exp (-k₁) + (q / Real.exp 1) ^ k₂ + (q / Real.exp 1) ^ k₃) := by
  set L : ℝ := Real.log T / (ε * V) with hLdef
  set N : ℕ := polyLength L with hNdef
  have hT0 : 0 < T := by linarith
  have hV : 0 < V := by
    by_contra h; push Not at h; nlinarith
  have hεVpos : 0 < ε * V := by linarith
  have hLpos : 0 < L := by linarith
  set d : ℝ := 1 / 2 - (1 / 2 + 1 / L) with hd
  have hd1 : 2 * d - 1 ≤ -1 := by
    have : 0 < 1 / L := by positivity
    rw [hd]; linarith
  set d' : ℝ := 1 / 2 - 2 * (1 / 2 + 1 / L) with hd'
  have hd2 : 2 * d' - 1 ≤ -2 := by
    have : 0 < 1 / L := by positivity
    rw [hd']; linarith
  set E₁ : Set ℝ := {t | (1 - 4 * ε) * V ≤
    ‖edPoly (⇑(primeCoeffLE lam L z)) (Finset.Icc 1 N) (displacedLinePt d t)‖}
  set E₂ : Set ℝ := {t | ε * V / 2 ≤
    ‖edPoly (⇑(primeCoeffGT lam L z)) (Finset.Icc 1 N) (displacedLinePt d t)‖}
  set E₃ : Set ℝ := {t | ε * V / 2 ≤
    ‖edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 N) (displacedLinePt d' (2 * t))‖}
  set μ := volume.restrict (Ioc T (2 * T))
  -- the inclusion
  have hsub : {t | V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ∩ Ioc T (2 * T) ⊆
      E₁ ∪ E₂ ∪ E₃ := by
    intro t ⟨ht, htI⟩
    have hta : |t| = t := abs_of_pos (by linarith [htI.1])
    have h := le_norm_split_of_le hW hA z hT4 hlogT hε hεV hL2 (by rw [hta]; exact htI.1.le)
      (by rw [hta]; exact htI.2) hV0 ht
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hfin : ∀ A, μ A ≠ ⊤ := fun A => measureReal_restrict_Ioc_le_volume _ _ A
  have hstep : μ.real {t | V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ≤
      μ.real E₁ + μ.real E₂ + μ.real E₃ := by
    have heq : μ.real {t | V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} =
        μ.real ({t | V ≤ (producerLogZeta hW (1 / 2 + 1 / Real.log T) t).re} ∩ Ioc T (2 * T)) := by
      rw [Measure.real, Measure.real, Measure.restrict_apply' measurableSet_Ioc,
        Measure.restrict_apply' measurableSet_Ioc, inter_assoc, inter_self]
    rw [heq]
    refine (measureReal_mono hsub (hfin _)).trans ?_
    refine (measureReal_union_le _ _).trans ?_
    have := measureReal_union_le (μ := μ) E₁ E₂
    linarith
  -- the first event
  have hm₁ : μ.real E₁ ≤ Real.exp 2 / δ * T * Real.exp (-k₁) := by
    have hsupp : ∀ n, primeCoeffLE lam L z n ≠ 0 → n ≤ z := fun n h => (primeCoeffLE_supp h).2.1
    have hE : E₁ = {t | (1 - 4 * ε) * V ≤
        ‖edPoly (⇑(primeCoeffLE lam L z)) (Finset.Icc 1 z) (displacedLinePt d t)‖} := by
      ext t; simp only [E₁, mem_setOf_eq, edPoly_Icc_eq_of_supp hz hsupp]
    rw [hE]
    have hvar : ∑ n ∈ Finset.Icc 1 z, ‖primeCoeffLE lam L z n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤
        κ ^ 2 * Sieve.mertensS z := by
      refine (sum_norm_sq_le_of_supp (P := fun n => n.Prime ∧ n ≤ z)
        (fun n h => ⟨(primeCoeffLE_supp h).1, (primeCoeffLE_supp h).2.1⟩)
        (primeCoeffLE_norm_le hκ hlam hLpos z) hd1 z).trans ?_
      exact mul_le_mul_of_nonneg_left (sum_filter_prime_le_mertensS z z) (sq_nonneg κ)
    have h := measureReal_large_primePoly_le_exp (a := primeCoeffLE lam L z) (N := z)
      (fun n h => (primeCoeffLE_supp h).1) hsupp d k₁ (T₁ := T) (T₂ := 2 * T) (by linarith)
      (by nlinarith) hδ hδ1 hvar hk₁ (by linarith)
    calc _ ≤ Real.exp 2 / δ * (2 * T - T) * Real.exp (-k₁) := h
      _ = Real.exp 2 / δ * T * Real.exp (-k₁) := by ring
  -- the second event
  have hm₂ : μ.real E₂ ≤ Real.exp 2 / δ * T * (q / Real.exp 1) ^ k₂ := by
    have hvar : ∑ n ∈ Finset.Icc 1 N, ‖primeCoeffGT lam L z n‖ ^ 2 * (n : ℝ) ^ (2 * d - 1) ≤
        κ ^ 2 * (Sieve.mertensS N - Sieve.mertensS z) := by
      refine (sum_norm_sq_le_of_supp (P := fun n => n.Prime ∧ z < n)
        (fun n h => ⟨(primeCoeffGT_supp h).1, (primeCoeffGT_supp h).2.1⟩)
        (primeCoeffGT_norm_le hκ hlam hLpos z) hd1 N).trans ?_
      exact mul_le_mul_of_nonneg_left (sum_filter_prime_gt_le_mertensS hz) (sq_nonneg κ)
    have h := measureReal_large_primePoly_le_pow (a := primeCoeffGT lam L z) (N := N)
      (fun n h => (primeCoeffGT_supp h).1) (fun n h => (primeCoeffGT_supp h).2.2) d k₂
      (T₁ := T) (T₂ := 2 * T) (by linarith) (by positivity) hδ hδ1 hq hvar hk₂ (by linarith)
    calc _ ≤ Real.exp 2 / δ * (2 * T - T) * (q / Real.exp 1) ^ k₂ := h
      _ = Real.exp 2 / δ * T * (q / Real.exp 1) ^ k₂ := by ring
  -- the third event
  have hm₃ : μ.real E₃ ≤ Real.exp 2 / δ * T * (q / Real.exp 1) ^ k₃ := by
    have hvar : ∑ n ∈ Finset.Icc 1 N, ‖sqCoeff lam L n‖ ^ 2 * (n : ℝ) ^ (2 * d' - 1) ≤
        2 * κ ^ 2 := sum_norm_sq_le_two (norm_sqCoeff_le hκ hlam hLpos) hd2 N
    have h := measureReal_large_primePoly_le_pow (a := sqCoeff lam L) (N := N)
      (fun n h => sqCoeff_prime h) (fun n h => sqCoeff_le h) d' k₃
      (T₁ := 2 * T) (T₂ := 4 * T) (by linarith) (by positivity) hδ hδ1 hq hvar hk₃ (by linarith)
    have h2 := measureReal_restrict_two_mul (T := T)
      (fun τ => edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 N) (displacedLinePt d' τ)) (ε * V / 2)
    show μ.real E₃ ≤ _
    rw [show μ.real E₃ = (volume.restrict (Ioc T (2 * T))).real {t | ε * V / 2 ≤
      ‖edPoly (⇑(sqCoeff lam L)) (Finset.Icc 1 N) (displacedLinePt d' (2 * t))‖} from rfl, h2]
    calc 1 / 2 * _ ≤ 1 / 2 * (Real.exp 2 / δ * (4 * T - 2 * T) * (q / Real.exp 1) ^ k₃) := by
          gcongr
      _ = Real.exp 2 / δ * T * (q / Real.exp 1) ^ k₃ := by ring
  calc _ ≤ μ.real E₁ + μ.real E₂ + μ.real E₃ := hstep
    _ ≤ _ := by
        have := add_le_add (add_le_add hm₁ hm₂) hm₃
        linarith

end RHTower.WeilSpectral
