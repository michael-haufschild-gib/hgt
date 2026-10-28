import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# The rough harmonic measure has thin shells

The harmonic measure `1/K` on the `Q`-rough numbers of `[1, X]` (every prime factor `≥ Q`) has total
mass `F_Q(X) ≍ log X/log Q`, and its multiplicative shells of ratio `p` carry `O(1)`:

* **Levels** (`sum_roughInterval_eq_levels`): for a prime `p`, the `p`-rough numbers of `[1, X]` are
  `⊔_j p^j · {(p+1)-rough numbers of [1, X/p^j]}`.
* **Mass** (`mertensPrimeProduct_mul_log_le_roughHarmonic`): `F_{p+1}(X) ≥ log(X + 1) Π_{q ≤ p}(1 − 1/q)`,
  by the levels (`F_q ≤ F_{q+1}/(1 − 1/q)`) and the harmonic sum.
* **Thin shells** (`exists_roughHarmonic_shell_le`): `Σ_{Y < K ≤ X} 1/K ≤ C` over `(p+1)`-rough `K` whenever
  `X ≤ p(Y + 1)`; Selberg's sieve with level `min(p, x^{1/4})` on dyadic blocks `(x, 2x]`.
* **The shell rate** (`exists_shellTau_le`): `τ(p, X) = Σ_{j ≥ 1} p^{−j}(F_0 − F_j)/F_0`, with
  `F_j = F_{p+1}(X/p^j)`, satisfies `τ(p, X) ≤ C log p/(p log X)` and `τ ≤ 1 − 1/(1 + 2C) < 1`.

`τ(p, X)` is the fraction of harmonic mass that the `p`-levels lose to the horizon; it is the only
dependence between prime coordinates of the harmonic measure on `[1, X]`.
-/

noncomputable section

open Finset Filter

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-! ### 1. Rough intervals -/

/-- The `Q`-rough numbers of `[1, X]`: every prime factor is at least `Q`. -/
def roughInterval (Q X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter fun K => ∀ q ∈ K.primeFactors, Q ≤ q

/-- The harmonic mass `F_Q(X) = Σ_{K ∈ R(Q, X)} 1/K`. -/
def roughHarmonic (Q X : ℕ) : ℝ := ∑ K ∈ roughInterval Q X, (1 : ℝ) / K

theorem mem_roughInterval {Q X K : ℕ} :
    K ∈ roughInterval Q X ↔ 1 ≤ K ∧ K ≤ X ∧ ∀ q, q.Prime → q ∣ K → Q ≤ q := by
  simp only [roughInterval, mem_filter, mem_Icc, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun q hq hd => h3 q ⟨hq, hd, by omega⟩⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun q ⟨hq, hd, _⟩ => h3 q hq hd⟩

theorem one_mem_roughInterval (Q : ℕ) {X : ℕ} (hX : 1 ≤ X) : 1 ∈ roughInterval Q X :=
  mem_roughInterval.mpr ⟨le_rfl, hX, fun q hq h => absurd (Nat.le_of_dvd one_pos h) (by
    have := hq.two_le; omega)⟩

theorem roughInterval_mono {Q X X' : ℕ} (h : X ≤ X') : roughInterval Q X ⊆ roughInterval Q X' :=
  fun K hK => by
    obtain ⟨h1, h2, h3⟩ := mem_roughInterval.mp hK
    exact mem_roughInterval.mpr ⟨h1, h2.trans h, h3⟩

theorem roughInterval_zero (X : ℕ) : roughInterval 0 X = Icc 1 X := by
  ext K
  rw [mem_roughInterval, mem_Icc]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ _ _ => Nat.zero_le _⟩⟩

theorem roughInterval_succ_of_not_prime {Q : ℕ} (hQ : ¬ Q.Prime) (X : ℕ) :
    roughInterval (Q + 1) X = roughInterval Q X := by
  ext K
  simp only [mem_roughInterval]
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun q hq hd => (h3 q hq hd).trans' (by omega)⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun q hq hd => ?_⟩⟩
  have := h3 q hq hd
  rcases this.lt_or_eq with h | h
  · omega
  · exact absurd (h ▸ hq) hQ

theorem not_dvd_of_mem_roughInterval_succ {p Y K : ℕ} (hK : K ∈ roughInterval (p + 1) Y)
    (hp : p.Prime) : ¬ p ∣ K := fun h => by
  have := (mem_roughInterval.mp hK).2.2 p hp h
  omega

/-- A rough number above `1` exceeds `Q − 1`. -/
theorem lt_of_mem_roughInterval {Q X K : ℕ} (hK : K ∈ roughInterval Q X) (h1 : 2 ≤ K) :
    Q ≤ K := by
  obtain ⟨-, -, h3⟩ := mem_roughInterval.mp hK
  obtain ⟨q, hq, hqK⟩ := Nat.exists_prime_and_dvd (show K ≠ 1 by omega)
  exact (h3 q hq hqK).trans (Nat.le_of_dvd (by omega) hqK)

theorem roughHarmonic_nonneg (Q X : ℕ) : 0 ≤ roughHarmonic Q X :=
  sum_nonneg fun _ _ => by positivity

theorem roughHarmonic_mono {Q X X' : ℕ} (h : X ≤ X') : roughHarmonic Q X ≤ roughHarmonic Q X' :=
  sum_le_sum_of_subset_of_nonneg (roughInterval_mono h) fun _ _ _ => by positivity

theorem one_le_roughHarmonic (Q : ℕ) {X : ℕ} (hX : 1 ≤ X) : 1 ≤ roughHarmonic Q X := by
  have h := single_le_sum (f := fun K : ℕ => (1 : ℝ) / K) (fun _ _ => by positivity)
    (one_mem_roughInterval Q hX)
  unfold roughHarmonic
  calc (1 : ℝ) = (1 : ℝ) / ((1 : ℕ) : ℝ) := by norm_num
    _ ≤ _ := h

theorem roughHarmonic_le_one_add_log (Q X : ℕ) : roughHarmonic Q X ≤ 1 + Real.log X := by
  have hsub : roughInterval Q X ⊆ Icc 1 X := fun K hK =>
    mem_Icc.mpr ⟨(mem_roughInterval.mp hK).1, (mem_roughInterval.mp hK).2.1⟩
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  calc roughHarmonic Q X ≤ ∑ K ∈ Icc 1 X, (1 : ℝ) / K :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 1 + Real.log X := by simpa [one_div] using h

/-- `F_Q(X) − F_Q(Y)` is the mass of the shell `(Y, X]`. -/
theorem roughHarmonic_sub_eq {Q Y X : ℕ} (h : Y ≤ X) :
    roughHarmonic Q X - roughHarmonic Q Y =
      ∑ K ∈ (roughInterval Q X).filter (fun K => Y < K), (1 : ℝ) / K := by
  have hY : roughInterval Q Y = (roughInterval Q X).filter (fun K => K ≤ Y) := by
    ext K
    simp only [mem_filter, mem_roughInterval]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2.trans h, h3⟩, h2⟩
    · rintro ⟨⟨h1, -, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
  rw [roughHarmonic, roughHarmonic, hY, ← sum_filter_add_sum_filter_not (roughInterval Q X)
    (fun K => K ≤ Y)]
  simp only [not_le]
  ring

/-! ### 2. The level decomposition -/

/-- **Levels.** For a prime `p`, `R(p, X) = ⊔_j p^j · R(p + 1, ⌊X/p^j⌋)`. -/
theorem sum_roughInterval_eq_levels {p : ℕ} (hp : p.Prime) (X : ℕ) (φ : ℕ → ℝ) :
    ∑ n ∈ roughInterval p X, φ n =
      ∑ j ∈ range (X + 1), ∑ K ∈ roughInterval (p + 1) (X / p ^ j), φ (p ^ j * K) := by
  rw [sum_sigma']
  symm
  refine sum_nbij' (fun x => p ^ x.1 * x.2)
    (fun n => ⟨n.factorization p, n / p ^ n.factorization p⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨j, K⟩ h
    rw [mem_sigma, mem_range] at h
    obtain ⟨hK1, hKX, hKq⟩ := mem_roughInterval.mp h.2
    refine mem_roughInterval.mpr ⟨?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega))
    · have := (Nat.le_div_iff_mul_le (pow_pos hp.pos j)).mp hKX
      linarith [mul_comm K (p ^ j)]
    · intro q hq hqd
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h' | h'
      · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h')).symm
      · have := hKq q hq h'
        omega
  · intro n hn
    obtain ⟨hn1, hnX, hnq⟩ := mem_roughInterval.mp hn
    rw [mem_sigma, mem_range]
    refine ⟨?_, mem_roughInterval.mpr ⟨?_, ?_, ?_⟩⟩
    · have h1 : p ^ n.factorization p ≤ n := Nat.ordProj_le p (by omega)
      have h2 : n.factorization p < p ^ n.factorization p := Nat.lt_pow_self hp.one_lt
      show n.factorization p < X + 1
      omega
    · exact Nat.ordCompl_pos p (by omega)
    · rw [Nat.le_div_iff_mul_le (pow_pos hp.pos _), mul_comm, Nat.ordProj_mul_ordCompl_eq_self]
      exact hnX
    · intro q hq hqd
      have hpq := hnq q hq (hqd.trans (Nat.ordCompl_dvd n p))
      have hne : q ≠ p := fun h => Nat.not_dvd_ordCompl hp (by omega) (h ▸ hqd)
      omega
  · rintro ⟨j, K⟩ h
    rw [mem_sigma, mem_range] at h
    dsimp only at h
    have hpK := not_dvd_of_mem_roughInterval_succ h.2 hp
    have hK0 : K ≠ 0 := by have := (mem_roughInterval.mp h.2).1; omega
    have hfac : (p ^ j * K).factorization p = j := by
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hK0, Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpK,
        add_zero]
    dsimp only
    rw [hfac, Nat.mul_div_cancel_left K (pow_pos hp.pos j)]
  · intro n _
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  · intro _ _
    rfl

/-- `F_p(X) = Σ_j p^{−j} F_{p+1}(⌊X/p^j⌋)`. -/
theorem roughHarmonic_eq_levels {p : ℕ} (hp : p.Prime) (X : ℕ) :
    roughHarmonic p X =
      ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * roughHarmonic (p + 1) (X / p ^ j) := by
  rw [roughHarmonic, sum_roughInterval_eq_levels hp]
  refine sum_congr rfl fun j _ => ?_
  rw [roughHarmonic, mul_sum]
  refine sum_congr rfl fun K _ => ?_
  push_cast
  rw [one_div_pow, one_div_mul_one_div]

/-- **Buchstab's inequality**: `(1 − 1/p) F_p(X) ≤ F_{p+1}(X)`. -/
theorem one_sub_inv_mul_roughHarmonic_le {p : ℕ} (hp : p.Prime) (X : ℕ) :
    (1 - (p : ℝ)⁻¹) * roughHarmonic p X ≤ roughHarmonic (p + 1) X := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hc : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by rw [← one_div]; linarith
  have hgeom : ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j ≤ 1 / (1 - 1 / p) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := X + 1) hr0 hr1
    rwa [← range_eq_Ico, pow_zero] at this
  rw [roughHarmonic_eq_levels hp]
  calc (1 - (p : ℝ)⁻¹) * ∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j * roughHarmonic (p + 1) (X / p ^ j)
      ≤ (1 - (p : ℝ)⁻¹) * ((∑ j ∈ range (X + 1), (1 / (p : ℝ)) ^ j) * roughHarmonic (p + 1) X) := by
        rw [sum_mul]
        exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (roughHarmonic_mono (Nat.div_le_self _ _)) (pow_nonneg hr0 _)) hc
    _ ≤ (1 - (p : ℝ)⁻¹) * (1 / (1 - 1 / p) * roughHarmonic (p + 1) X) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hgeom (roughHarmonic_nonneg _ _)) hc
    _ = roughHarmonic (p + 1) X := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-! ### 3. The total mass -/

theorem mertensPrimeProduct_pos (n : ℕ) : 0 < RHTower.mertensPrimeProduct n := by
  refine prod_pos fun m _ => ?_
  split_ifs with hm
  · have : (1 : ℝ) < m := by exact_mod_cast hm.one_lt
    have : (m : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  · exact one_pos

/-- `Π_{q ≤ n}(1 − 1/q) · F_0(X) ≤ F_{n+1}(X)`. -/
theorem mertensPrimeProduct_mul_le_roughHarmonic (n X : ℕ) :
    RHTower.mertensPrimeProduct n * roughHarmonic 0 X ≤ roughHarmonic (n + 1) X := by
  induction n with
  | zero =>
    have hM : RHTower.mertensPrimeProduct 0 = 1 := by
      simp [RHTower.mertensPrimeProduct, Nat.not_prime_zero]
    rw [hM, one_mul, roughHarmonic, roughHarmonic, roughInterval_succ_of_not_prime Nat.not_prime_zero]
  | succ n ih =>
    have hM : RHTower.mertensPrimeProduct (n + 1) = RHTower.mertensPrimeProduct n *
        (if (n + 1).Prime then 1 - (((n + 1 : ℕ) : ℝ))⁻¹ else 1) := by
      rw [RHTower.mertensPrimeProduct, RHTower.mertensPrimeProduct, prod_Icc_succ_top (by omega)]
    by_cases hp : (n + 1).Prime
    · rw [hM, if_pos hp]
      have hb := one_sub_inv_mul_roughHarmonic_le hp X
      have hf : (0 : ℝ) ≤ 1 - (((n + 1 : ℕ) : ℝ))⁻¹ := by
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        have := inv_le_one_of_one_le₀ this
        linarith
      calc RHTower.mertensPrimeProduct n * (1 - (((n + 1 : ℕ) : ℝ))⁻¹) * roughHarmonic 0 X
          = (1 - (((n + 1 : ℕ) : ℝ))⁻¹) * (RHTower.mertensPrimeProduct n * roughHarmonic 0 X) := by
            ring
        _ ≤ (1 - (((n + 1 : ℕ) : ℝ))⁻¹) * roughHarmonic (n + 1) X :=
            mul_le_mul_of_nonneg_left ih hf
        _ ≤ roughHarmonic (n + 1 + 1) X := hb
    · rw [hM, if_neg hp, mul_one]
      unfold roughHarmonic at ih ⊢
      rw [roughInterval_succ_of_not_prime hp]
      exact ih

/-- **The rough mass**: `F_{n+1}(X) ≥ log(X + 1) · Π_{q ≤ n}(1 − 1/q)`. -/
theorem mertensPrimeProduct_mul_log_le_roughHarmonic (n X : ℕ) :
    Real.log (X + 1) * RHTower.mertensPrimeProduct n ≤ roughHarmonic (n + 1) X := by
  have h0 : Real.log (X + 1) ≤ roughHarmonic 0 X := by
    have h := log_add_one_le_harmonic X
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    rw [roughHarmonic, roughInterval_zero]
    simpa [one_div] using h
  calc Real.log (X + 1) * RHTower.mertensPrimeProduct n
      ≤ roughHarmonic 0 X * RHTower.mertensPrimeProduct n :=
        mul_le_mul_of_nonneg_right h0 (mertensPrimeProduct_pos n).le
    _ ≤ roughHarmonic (n + 1) X := by
        rw [mul_comm]; exact mertensPrimeProduct_mul_le_roughHarmonic n X

/-- Mertens' product is `≍ 1/log`: `Π_{q ≤ n}(1 − 1/q) log n ≥ c > 0` for `n ≥ 2`. -/
theorem exists_mertensPrimeProduct_mul_log_ge :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c ≤ RHTower.mertensPrimeProduct n * Real.log n := by
  have hlim := RHTower.tendsto_mertensPrimeProduct_mul_log
  set e := Real.exp (-Real.eulerMascheroniConstant)
  have he : 0 < e := Real.exp_pos _
  have hev : ∀ᶠ N : ℕ in atTop, e / 2 < RHTower.mertensPrimeProduct N * Real.log N :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hev
  have hS : (Icc 2 (max N₁ 2)).Nonempty := ⟨2, mem_Icc.mpr ⟨le_rfl, le_max_right _ _⟩⟩
  set m := (Icc 2 (max N₁ 2)).inf' hS (fun n => RHTower.mertensPrimeProduct n * Real.log n)
  have hm : 0 < m := (lt_inf'_iff hS).mpr fun n hn => mul_pos (mertensPrimeProduct_pos n)
    (Real.log_pos (by exact_mod_cast (show 1 < n by have := (mem_Icc.mp hn).1; omega)))
  refine ⟨min (e / 2) m, lt_min (by linarith) hm, fun n hn => ?_⟩
  by_cases h : n ≤ max N₁ 2
  · exact (min_le_right _ _).trans (inf'_le _ (mem_Icc.mpr ⟨hn, h⟩))
  · exact (min_le_left _ _).trans (hN₁ n (by omega)).le

/-! ### 4. Thin shells -/

/-- **One dyadic block** (Selberg's sieve): for `1 < z ≤ p`, the `(p+1)`-rough numbers of `(x, 2x]`
carry mass at most `2/log z + 5z(1 + log z)³/x`. -/
theorem sum_roughInterval_block_le {p : ℕ} (hp : p.Prime) (X x : ℕ) (hx : 0 < x) {z : ℝ}
    (hz : 1 < z) (hzp : z ≤ p) :
    ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => x < K ∧ K ≤ 2 * x), (1 : ℝ) / K ≤
      2 / Real.log z + 5 * z * (1 + Real.log z) ^ 3 / x := by
  classical
  set T := (roughInterval (p + 1) X).filter (fun K => x < K ∧ K ≤ 2 * x)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have h1 : ∑ K ∈ T, (1 : ℝ) / K ≤ T.card * (1 / (x : ℝ)) := by
    rw [← nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ fun K hK => ?_
    have hxK : (x : ℝ) < K := by exact_mod_cast (mem_filter.mp hK).2.1
    exact one_div_le_one_div_of_le hx0 hxK.le
  have hceil : ⌈(x : ℝ)⌉₊ = x := Nat.ceil_natCast x
  have hfloor : ⌊(x : ℝ) + x⌋₊ = 2 * x := by
    rw [show (x : ℝ) + x = ((2 * x : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hsub : T ⊆ (Icc ⌈(x : ℝ)⌉₊ ⌊(x : ℝ) + x⌋₊).filter
      (fun d => ∀ q : ℕ, q.Prime → (q : ℝ) ≤ z → ¬ q ∣ d) := by
    intro K hK
    obtain ⟨hKR, hxK, hK2⟩ := mem_filter.mp hK
    refine mem_filter.mpr ⟨by rw [hceil, hfloor]; exact mem_Icc.mpr ⟨hxK.le, hK2⟩, ?_⟩
    intro q hq hqz hqK
    have := (mem_roughInterval.mp hKR).2.2 q hq hqK
    have : ((p + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast this
    push_cast at this
    linarith
  have hcard : (T.card : ℝ) ≤ 2 * x / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
    have e1 := BrunTitchmarsh.siftedSum_eq_card (x : ℝ) (x : ℝ) z hz.le
    have e2 := BrunTitchmarsh.siftedSum_le (x : ℝ) (x : ℝ) z hx0 hx0 hz
    calc (T.card : ℝ) ≤ (((Icc ⌈(x : ℝ)⌉₊ ⌊(x : ℝ) + x⌋₊).filter
          (fun d => ∀ q : ℕ, q.Prime → (q : ℝ) ≤ z → ¬ q ∣ d)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ = _ := by rw [e1]
      _ ≤ _ := e2
  calc ∑ K ∈ T, (1 : ℝ) / K ≤ T.card * (1 / (x : ℝ)) := h1
    _ ≤ (2 * x / Real.log z + 5 * z * (1 + Real.log z) ^ 3) * (1 / (x : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 / Real.log z + 5 * z * (1 + Real.log z) ^ 3 / x := by field_simp

/-- `(1 + log x)³ ≤ 343 √x` for `x ≥ 1`. -/
theorem one_add_log_pow_three_le {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 3 ≤ 343 * x ^ (1 / 2 : ℝ) := by
  have hlog := Real.log_le_rpow_div (x := x) (ε := 1 / 6) (by linarith) (by norm_num)
  have h1 : 1 ≤ x ^ (1 / 6 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have h2 : 1 + Real.log x ≤ 7 * x ^ (1 / 6 : ℝ) := by
    have : x ^ (1 / 6 : ℝ) / (1 / 6) = 6 * x ^ (1 / 6 : ℝ) := by ring
    linarith
  have h0 : 0 ≤ 1 + Real.log x := by have := Real.log_nonneg hx; linarith
  calc (1 + Real.log x) ^ 3 ≤ (7 * x ^ (1 / 6 : ℝ)) ^ 3 := pow_le_pow_left₀ h0 h2 3
    _ = 343 * x ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 6 : ℝ)) 3, ← Real.rpow_mul (by linarith)]
        norm_num

/-- The sieve remainder at level `z ≤ x^{1/4}`: `5z(1 + log z)³/x ≤ 1715 x^{−1/4}`. -/
theorem sieve_error_le {x z : ℝ} (hx : 1 ≤ x) (hz : 1 ≤ z) (hzx : z ≤ x ^ (1 / 4 : ℝ)) :
    5 * z * (1 + Real.log z) ^ 3 / x ≤ 1715 * x ^ (-(1 / 4) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hqx : x ^ (1 / 4 : ℝ) ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hlogz : Real.log z ≤ Real.log x := Real.log_le_log (by linarith) (hzx.trans hqx)
  have hz0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hc : (1 + Real.log z) ^ 3 ≤ 343 * x ^ (1 / 2 : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) 3).trans (one_add_log_pow_three_le hx)
  have hmain : 5 * z * (1 + Real.log z) ^ 3 ≤ 5 * x ^ (1 / 4 : ℝ) * (343 * x ^ (1 / 2 : ℝ)) := by
    have : 0 ≤ (1 + Real.log z) ^ 3 := by positivity
    calc 5 * z * (1 + Real.log z) ^ 3 ≤ 5 * x ^ (1 / 4 : ℝ) * (1 + Real.log z) ^ 3 := by
          gcongr
      _ ≤ 5 * x ^ (1 / 4 : ℝ) * (343 * x ^ (1 / 2 : ℝ)) := by gcongr
  rw [div_le_iff₀ hx0]
  calc 5 * z * (1 + Real.log z) ^ 3 ≤ 5 * x ^ (1 / 4 : ℝ) * (343 * x ^ (1 / 2 : ℝ)) := hmain
    _ = 1715 * x ^ ((1 / 4 : ℝ) + 1 / 2) := by rw [Real.rpow_add hx0]; ring
    _ = 1715 * x ^ (-(1 / 4) : ℝ) * x := by
        rw [mul_assoc, ← Real.rpow_add_one hx0.ne']
        norm_num

/-- Dyadic decomposition of `(a, 2^I a]`. -/
theorem sum_filter_dyadic (S : Finset ℕ) (f : ℕ → ℝ) (a I : ℕ) :
    ∑ K ∈ S.filter (fun K => a < K ∧ K ≤ 2 ^ I * a), f K =
      ∑ i ∈ range I, ∑ K ∈ S.filter (fun K => 2 ^ i * a < K ∧ K ≤ 2 * (2 ^ i * a)), f K := by
  induction I with
  | zero =>
    rw [sum_range_zero, pow_zero, one_mul]
    exact sum_eq_zero fun K hK => absurd (mem_filter.mp hK).2 (by omega)
  | succ I ih =>
    rw [Finset.sum_range_succ, ← ih, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun K _ => ?_
    have h2 : 2 ^ (I + 1) * a = 2 * (2 ^ I * a) := by ring
    have h3 : a ≤ 2 ^ I * a := Nat.le_mul_of_pos_left a (by positivity)
    rw [h2]
    set b := 2 ^ I * a
    by_cases c1 : a < K ∧ K ≤ b
    · rw [if_pos c1, if_pos (by omega), if_neg (by omega), add_zero]
    · by_cases c2 : b < K ∧ K ≤ 2 * b
      · rw [if_neg c1, if_pos c2, if_pos (by omega), zero_add]
      · rw [if_neg c1, if_neg c2, if_neg (by omega), add_zero]

/-- **Thin shells.** There is `C` such that for every prime `p` and `1 ≤ Y`, `X ≤ p(Y + 1)`, the
`(p+1)`-rough numbers of `(Y, X]` carry harmonic mass at most `C`. -/
theorem exists_roughHarmonic_shell_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ Y X : ℕ, 1 ≤ Y →
    X ≤ p * (Y + 1) →
      ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => Y < K), (1 : ℝ) / K ≤ C := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 4) : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨24 / Real.log 2 + 1715 * (1 / (1 - r)), ?_, fun p hp Y X hY hX => ?_⟩
  · have h1r : 0 < 1 - r := by linarith
    exact add_nonneg (div_nonneg (by norm_num) hlog2.le)
      (mul_nonneg (by norm_num) (div_nonneg zero_le_one h1r.le))
  have hp2 := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  set a := max Y p
  have ha1 : p ≤ a := le_max_right _ _
  have haY : Y ≤ a := le_max_left _ _
  set I := Nat.log 2 p + 2
  -- the shell lies in `(a, 2^I a]`
  have hsub : (roughInterval (p + 1) X).filter (fun K => Y < K) ⊆
      (roughInterval (p + 1) X).filter (fun K => a < K ∧ K ≤ 2 ^ I * a) := by
    intro K hK
    obtain ⟨hKR, hYK⟩ := mem_filter.mp hK
    have hKp : p + 1 ≤ K := lt_of_mem_roughInterval hKR (by omega)
    have hKX := (mem_roughInterval.mp hKR).2.1
    have hpow : p < 2 ^ (Nat.log 2 p + 1) := Nat.lt_pow_succ_log_self (by norm_num) p
    have hI : 2 ^ I = 2 * 2 ^ (Nat.log 2 p + 1) := by rw [pow_succ]; ring
    have hXa : X ≤ 2 ^ I * a := by
      have h1 : p * (Y + 1) ≤ p * (2 * a) := Nat.mul_le_mul_left p (by omega)
      have h2 : p * (2 * a) ≤ 2 ^ (Nat.log 2 p + 1) * (2 * a) := Nat.mul_le_mul_right _ hpow.le
      rw [hI]
      calc X ≤ p * (Y + 1) := hX
        _ ≤ 2 ^ (Nat.log 2 p + 1) * (2 * a) := h1.trans h2
        _ = 2 * 2 ^ (Nat.log 2 p + 1) * a := by ring
    exact mem_filter.mpr ⟨hKR, by omega, hKX.trans hXa⟩
  have hblock : ∀ i ∈ range I, ∑ K ∈ (roughInterval (p + 1) X).filter
      (fun K => 2 ^ i * a < K ∧ K ≤ 2 * (2 ^ i * a)), (1 : ℝ) / K ≤
        8 / Real.log p + 1715 * r ^ i := by
    intro i _
    set x := 2 ^ i * a
    have hxa : a ≤ x := Nat.le_mul_of_pos_left a (by positivity)
    have hxp : (p : ℝ) ≤ x := by exact_mod_cast ha1.trans hxa
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx2 : (2 : ℝ) ^ (i + 1) ≤ x := by
      have : 2 ^ (i + 1) ≤ x := by
        rw [pow_succ]; exact Nat.mul_le_mul_left _ (by omega)
      exact_mod_cast this
    set z : ℝ := min (p : ℝ) ((x : ℝ) ^ (1 / 4 : ℝ))
    have hz1 : (p : ℝ) ^ (1 / 4 : ℝ) ≤ z := le_min
      (by simpa using Real.rpow_le_rpow_of_exponent_le hp1.le (show (1 / 4 : ℝ) ≤ 1 by norm_num))
      (Real.rpow_le_rpow (by positivity) hxp (by norm_num))
    have hpz : 1 < (p : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow hp1 (by norm_num)
    have hz : 1 < z := hpz.trans_le hz1
    have hlz : (1 / 4) * Real.log p ≤ Real.log z := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) hz1
    have hmain : 2 / Real.log z ≤ 8 / Real.log p := by
      have hlp : 0 < Real.log p := Real.log_pos hp1
      calc 2 / Real.log z ≤ 2 / ((1 / 4) * Real.log p) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) hlz
        _ = 8 / Real.log p := by field_simp; ring
    have herr : 5 * z * (1 + Real.log z) ^ 3 / x ≤ 1715 * r ^ i := by
      refine (sieve_error_le hx1 hz.le (min_le_right _ _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc (x : ℝ) ^ (-(1 / 4) : ℝ) ≤ ((2 : ℝ) ^ (i + 1)) ^ (-(1 / 4) : ℝ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hx2 (by norm_num)
        _ = r ^ (i + 1) := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num), mul_comm]
        _ ≤ r ^ i := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ i)
    have hx0 : 0 < x := by positivity
    calc _ ≤ 2 / Real.log z + 5 * z * (1 + Real.log z) ^ 3 / x :=
          sum_roughInterval_block_le hp X x hx0 hz (min_le_left _ _)
      _ ≤ 8 / Real.log p + 1715 * r ^ i := add_le_add hmain herr
  have hgeom : ∑ i ∈ range I, r ^ i ≤ 1 / (1 - r) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := I) hr0 hr1
    rwa [← range_eq_Ico, pow_zero] at this
  have hIlog : (I : ℝ) * (8 / Real.log p) ≤ 24 / Real.log 2 := by
    have hn : (Nat.log 2 p : ℝ) ≤ Real.log p / Real.log 2 := by
      have := Real.natLog_le_logb p 2
      rwa [Real.logb] at this
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have : (I : ℝ) = Nat.log 2 p + 2 := by simp [I]
    rw [this]
    calc ((Nat.log 2 p : ℝ) + 2) * (8 / Real.log p)
        ≤ (Real.log p / Real.log 2 + 2) * (8 / Real.log p) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 8 / Real.log 2 + 16 / Real.log p := by field_simp; ring
      _ ≤ 8 / Real.log 2 + 16 / Real.log 2 := by
          gcongr
      _ = 24 / Real.log 2 := by ring
  calc ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => Y < K), (1 : ℝ) / K
      ≤ ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => a < K ∧ K ≤ 2 ^ I * a), (1 : ℝ) / K :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ i ∈ range I, ∑ K ∈ (roughInterval (p + 1) X).filter
          (fun K => 2 ^ i * a < K ∧ K ≤ 2 * (2 ^ i * a)), (1 : ℝ) / K := sum_filter_dyadic _ _ a I
    _ ≤ ∑ i ∈ range I, (8 / Real.log p + 1715 * r ^ i) := sum_le_sum hblock
    _ = (I : ℝ) * (8 / Real.log p) + 1715 * ∑ i ∈ range I, r ^ i := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ 24 / Real.log 2 + 1715 * (1 / (1 - r)) := by gcongr

/-! ### 5. The shell rate -/

/-- The **shell rate** `τ(p, X) = Σ_{j ≥ 0, p^j ≤ X} p^{−j}(F_0 − F_j)/F_0`, `F_j = F_{p+1}(⌊X/p^j⌋)`. -/
def shellTau (p X : ℕ) : ℝ :=
  ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (1 / (p : ℝ)) ^ j *
    ((roughHarmonic (p + 1) X - roughHarmonic (p + 1) (X / p ^ j)) / roughHarmonic (p + 1) X)

theorem shellTau_nonneg (p X : ℕ) : 0 ≤ shellTau p X :=
  sum_nonneg fun j _ => mul_nonneg (by positivity) (div_nonneg
    (sub_nonneg.mpr (roughHarmonic_mono (Nat.div_le_self _ _))) (roughHarmonic_nonneg _ _))

/-- Telescoping the shells: `F_0 − F_j ≤ j C` while `p^j ≤ X`. -/
theorem roughHarmonic_sub_level_le {C : ℝ}
    (hC : ∀ p : ℕ, p.Prime → ∀ Y X : ℕ, 1 ≤ Y → X ≤ p * (Y + 1) →
      ∑ K ∈ (roughInterval (p + 1) X).filter (fun K => Y < K), (1 : ℝ) / K ≤ C)
    {p : ℕ} (hp : p.Prime) {X j : ℕ} (hj : p ^ j ≤ X) :
    roughHarmonic (p + 1) X - roughHarmonic (p + 1) (X / p ^ j) ≤ j * C := by
  have htel := sum_range_sub' (fun i => roughHarmonic (p + 1) (X / p ^ i)) j
  simp only [pow_zero, Nat.div_one] at htel
  rw [← htel]
  have hterm : ∀ i ∈ range j, roughHarmonic (p + 1) (X / p ^ i) -
      roughHarmonic (p + 1) (X / p ^ (i + 1)) ≤ C := by
    intro i hi
    have hi' : i + 1 ≤ j := mem_range.mp hi
    have hdiv : X / p ^ (i + 1) = X / p ^ i / p := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hY : 1 ≤ X / p ^ (i + 1) :=
      (Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr
        (by rw [one_mul]; exact (Nat.pow_le_pow_right hp.pos hi').trans hj)
    have hle : X / p ^ (i + 1) ≤ X / p ^ i := by rw [hdiv]; exact Nat.div_le_self _ _
    have hXY : X / p ^ i ≤ p * (X / p ^ (i + 1) + 1) := by
      rw [hdiv]
      have h1 := Nat.div_add_mod (X / p ^ i) p
      have h2 := Nat.mod_lt (X / p ^ i) hp.pos
      nlinarith
    rw [roughHarmonic_sub_eq hle]
    exact hC p hp _ _ hY hXY
  calc ∑ i ∈ range j, (roughHarmonic (p + 1) (X / p ^ i) - roughHarmonic (p + 1) (X / p ^ (i + 1)))
      ≤ ∑ _i ∈ range j, C := sum_le_sum hterm
    _ = j * C := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **The shell rate is `O(log p/(p log X))` and uniformly below one.** -/
theorem exists_shellTau_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ p X : ℕ, p.Prime → p ≤ X →
    shellTau p X ≤ C * (Real.log p / (p * Real.log X)) ∧ shellTau p X ≤ 1 - 1 / (1 + 2 * C) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_roughHarmonic_shell_le
  obtain ⟨cM, hcM, hM⟩ := exists_mertensPrimeProduct_mul_log_ge
  set C := max 1 (4 * Cs / cM)
  refine ⟨C, le_max_left _ _, fun p X hp hpX => ?_⟩
  have hp2 := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hlp : 0 < Real.log p := Real.log_pos hp1
  set F0 := roughHarmonic (p + 1) X
  have hF1 : 1 ≤ F0 := one_le_roughHarmonic _ (by omega)
  have hF0 : 0 < F0 := by linarith
  -- `F_0 ≥ c_M log X/log p`
  have hFlow : cM * Real.log X / Real.log p ≤ F0 := by
    have h1 := mertensPrimeProduct_mul_log_le_roughHarmonic p X
    have h2 := hM p hp2
    have hlog : Real.log X ≤ Real.log (X + 1) := Real.log_le_log (by linarith) (by linarith)
    have hMp := mertensPrimeProduct_pos p
    rw [div_le_iff₀ hlp]
    calc cM * Real.log X ≤ RHTower.mertensPrimeProduct p * Real.log p * Real.log X :=
          mul_le_mul_of_nonneg_right h2 hlX.le
      _ = Real.log X * RHTower.mertensPrimeProduct p * Real.log p := by ring
      _ ≤ Real.log (X + 1) * RHTower.mertensPrimeProduct p * Real.log p := by gcongr
      _ ≤ F0 * Real.log p := mul_le_mul_of_nonneg_right h1 hlp.le
  -- termwise: `p^{−j}(F_0 − F_j)/F_0 ≤ (C_s/F_0) j p^{−j}`
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hterm : ∀ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (1 / (p : ℝ)) ^ j *
      ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0) ≤ Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := by
    intro j hj
    have h := roughHarmonic_sub_level_le hCs hp (mem_filter.mp hj).2
    have hpj : (0 : ℝ) ≤ (1 / (p : ℝ)) ^ j := pow_nonneg hr0 _
    calc (1 / (p : ℝ)) ^ j * ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0)
        ≤ (1 / (p : ℝ)) ^ j * (j * Cs / F0) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hF0.le) hpj
      _ = Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := by ring
  have hsumj : ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (j : ℝ) * (1 / (p : ℝ)) ^ j ≤
      (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 := by
    have hhs := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / (p : ℝ)))
      (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    exact sum_le_hasSum _ (fun i _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0 _)) hhs
  have hgeo : (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 ≤ 4 / p := by
    have hp0 : (0 : ℝ) < p := by linarith
    have e : (1 / (p : ℝ)) / (1 - 1 / p) ^ 2 = p / ((p : ℝ) - 1) ^ 2 := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [e, div_le_div_iff₀ (by nlinarith) hp0]
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    nlinarith
  have hτ1 : shellTau p X ≤ Cs / F0 * (4 / p) := by
    calc shellTau p X ≤ ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          Cs / F0 * (j * (1 / (p : ℝ)) ^ j) := sum_le_sum hterm
      _ = Cs / F0 * ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (j : ℝ) * (1 / (p : ℝ)) ^ j := by rw [mul_sum]
      _ ≤ Cs / F0 * (4 / p) :=
          mul_le_mul_of_nonneg_left (hsumj.trans hgeo) (div_nonneg hCs0 hF0.le)
  have hτ2 : shellTau p X ≤ C * (Real.log p / (p * Real.log X)) := by
    have hinv : 1 / F0 ≤ Real.log p / (cM * Real.log X) := by
      rw [div_le_div_iff₀ hF0 (by positivity), one_mul]
      rw [div_le_iff₀ hlp] at hFlow
      linarith
    have hCge : 4 * Cs / cM ≤ C := le_max_right _ _
    calc shellTau p X ≤ Cs / F0 * (4 / p) := hτ1
      _ = 4 * Cs * (1 / F0) / p := by ring
      _ ≤ 4 * Cs * (Real.log p / (cM * Real.log X)) / p := by gcongr
      _ = 4 * Cs / cM * (Real.log p / (p * Real.log X)) := by field_simp
      _ ≤ C * (Real.log p / (p * Real.log X)) := by gcongr
  refine ⟨hτ2, ?_⟩
  -- the uniform bound: `τ ≤ 1 − 1/F_0` and either `log X ≥ 2C` or `F_0 ≤ 1 + 2C`
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hτ3 : shellTau p X ≤ 1 - 1 / F0 := by
    have hterm' : ∀ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X), (1 / (p : ℝ)) ^ j *
        ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0) ≤
          (1 - 1 / F0) * (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [F0]
      rw [if_neg hj0.ne']
      have hlev : 1 ≤ roughHarmonic (p + 1) (X / p ^ j) :=
        one_le_roughHarmonic _ ((Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr
          (by rw [one_mul]; exact (mem_filter.mp hj).2))
      have : (F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0 ≤ 1 - 1 / F0 := by
        rw [sub_div, div_self hF0.ne']
        exact sub_le_sub_left (div_le_div_of_nonneg_right hlev hF0.le) 1
      calc (1 / (p : ℝ)) ^ j * ((F0 - roughHarmonic (p + 1) (X / p ^ j)) / F0)
          ≤ (1 / (p : ℝ)) ^ j * (1 - 1 / F0) := mul_le_mul_of_nonneg_left this (pow_nonneg hr0 _)
        _ = (1 - 1 / F0) * (1 / (p : ℝ)) ^ j := by ring
    have hgeom : ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
        (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) ≤ 1 := by
      calc ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
            (if j = 0 then 0 else (1 / (p : ℝ)) ^ j)
          ≤ ∑ j ∈ range (X + 1), (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => by
              split_ifs <;> positivity
        _ = (1 / (p : ℝ)) * ∑ j ∈ range X, (1 / (p : ℝ)) ^ j := by
            rw [Finset.sum_range_succ', if_pos rfl, add_zero, mul_sum]
            exact sum_congr rfl fun j _ => by rw [if_neg (Nat.succ_ne_zero j), pow_succ]; ring
        _ ≤ (1 / (p : ℝ)) * (1 / (1 - 1 / p)) := by
            refine mul_le_mul_of_nonneg_left ?_ hr0
            have := geom_sum_Ico_le_of_lt_one (m := 0) (n := X) hr0 hr1
            rwa [← range_eq_Ico, pow_zero] at this
        _ ≤ 1 := by
            have hp0 : (0 : ℝ) < p := by linarith
            have hq : (0 : ℝ) < 1 - 1 / p := by linarith
            rw [mul_one_div, div_le_one hq]
            have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
            rw [div_le_iff₀ hp0]
            have : 1 / (p : ℝ) * p = 1 := by field_simp
            nlinarith
    have hnn : 0 ≤ 1 - 1 / F0 := by
      have : 1 / F0 ≤ 1 := by rw [div_le_one hF0]; exact hF1
      linarith
    calc shellTau p X ≤ ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (1 - 1 / F0) * (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := sum_le_sum hterm'
      _ = (1 - 1 / F0) * ∑ j ∈ (range (X + 1)).filter (fun j => p ^ j ≤ X),
          (if j = 0 then 0 else (1 / (p : ℝ)) ^ j) := by rw [mul_sum]
      _ ≤ (1 - 1 / F0) * 1 := mul_le_mul_of_nonneg_left hgeom hnn
      _ = 1 - 1 / F0 := mul_one _
  have h12 : 1 / (1 + 2 * C) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  by_cases hbig : 2 * C ≤ Real.log X
  · -- `τ ≤ C log p/(p log X) ≤ C/log X ≤ 1/2`
    have hlpp : Real.log p / p ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have : C * (Real.log p / (p * Real.log X)) ≤ 1 / 2 := by
      have e : C * (Real.log p / (p * Real.log X)) = C * (Real.log p / p) / Real.log X := by
        field_simp
      rw [e, div_le_iff₀ hlX]
      nlinarith
    linarith
  · -- `F_0 ≤ 1 + log X < 1 + 2C`
    replace hbig := not_le.mp hbig
    have hFle : F0 ≤ 1 + 2 * C := (roughHarmonic_le_one_add_log _ _).trans (by linarith)
    have : 1 / (1 + 2 * C) ≤ 1 / F0 := one_div_le_one_div_of_le hF0 hFle
    linarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
