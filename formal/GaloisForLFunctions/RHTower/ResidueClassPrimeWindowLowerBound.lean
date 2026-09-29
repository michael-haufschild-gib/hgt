import GaloisForLFunctions.RHTower.ResidueClassPrimeSumSharpUpper
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Primes in a residue class with a prescribed logarithmic phase

Fix `ρ > 1` and a residue class `a mod q` with `a` coprime to `q`. The primes `p ≡ a` whose phase
`{log p / log ρ}` lies in `[¼, ¾]` carry a positive proportion of the logarithmic mass:

```text
Σ_{p < Y, p ≡ a, {log p/log ρ} ∈ [¼,¾]} p^{−σ} ≥ c · log(1/(σ−1)) − C     (1 < σ ≤ 2, Y ≥ Y₀(σ)).
```

Proof.
* On each block `[ρ^{k+1/4}, ρ^{k+3/4})`, the prime number theorem in progressions (`WeakPNT_AP`)
  gives class Chebyshev mass `≫ ρ^k`.
* Dividing by `log n · n^σ ≤ (k+1) log ρ · ρ^{(k+1)σ}` gives `≫ q^k/(k+1)` with `q = ρ^{−(σ−1)}`.
* Summing over the blocks gives `≫ −log(1 − q) ≥ log(1/(σ−1)) − |log log ρ|`.
* Composite prime powers contribute at most `Σ_{m ≥ 2} 1/(m(m−1)) = 1` in total.
-/

noncomputable section

open ArithmeticFunction Filter

namespace RHTower.ResidueClassPrimes

/-- `Σ_{m ∈ [2, M)} 1/(m(m−1)) ≤ 1`. -/
theorem sum_Ico_inv_mul_pred_le_one (M : ℕ) :
    ∑ m ∈ Finset.Ico 2 M, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 := by
  have key : ∀ M : ℕ, 2 ≤ M →
      ∑ m ∈ Finset.Ico 2 M, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - 1 / ((M : ℝ) - 1) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have h1 : (1 : ℝ) < n := by exact_mod_cast hn
      have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
      have h3 : (n : ℝ) ≠ 0 := by linarith
      have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
      rw [e]
      field_simp
      ring
  rcases Nat.lt_or_ge M 2 with hM | hM
  · rw [Finset.Ico_eq_empty (by omega)]; simp
  · rw [key M hM]
    have : (0 : ℝ) ≤ 1 / ((M : ℝ) - 1) := by
      have : (2 : ℝ) ≤ M := by exact_mod_cast hM
      exact div_nonneg zero_le_one (by linarith)
    linarith

/-- Composite prime powers carry total weight at most `1`. -/
theorem sum_compositePrimePow_le_one (Y : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    ∑ n ∈ (Finset.range Y).filter (fun n => IsPrimePow n ∧ ¬ n.Prime),
      vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) ≤ 1 := by
  classical
  set S := (Finset.range Y).filter (fun n => IsPrimePow n ∧ ¬ n.Prime) with hS
  set P := Finset.Ico 2 Y ×ˢ Finset.Ico 2 Y with hP
  have hsub : S ⊆ P.image (fun mj : ℕ × ℕ => mj.1 ^ mj.2) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnY, hpp, hnp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := hpp
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; simp at hnp; exact hnp hp'
    have hp2 : 2 ≤ p := hp'.two_le
    have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have hkk : k < p ^ k := Nat.lt_pow_self (by omega)
    refine Finset.mem_image.mpr ⟨(p, k), ?_, rfl⟩
    rw [hP, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico]
    exact ⟨⟨hp2, by omega⟩, ⟨hk2, by omega⟩⟩
  have hf0 : ∀ n : ℕ, 0 ≤ vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) := fun n =>
    mul_nonneg (vonMangoldt_div_log_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc ∑ n ∈ S, vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ P.image (fun mj : ℕ × ℕ => mj.1 ^ mj.2),
          vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hf0 n
    _ ≤ ∑ mj ∈ P, vonMangoldt (mj.1 ^ mj.2) / Real.log (mj.1 ^ mj.2 : ℕ) *
          ((mj.1 ^ mj.2 : ℕ) : ℝ) ^ (-σ) :=
        Finset.sum_image_le_of_nonneg fun n _ => hf0 n
    _ ≤ ∑ mj ∈ P, ((1 : ℝ) / mj.1) ^ mj.2 := by
        refine Finset.sum_le_sum fun mj hmj => ?_
        rw [hP, Finset.mem_product, Finset.mem_Ico, Finset.mem_Ico] at hmj
        have hm1 : (1 : ℝ) ≤ mj.1 := by exact_mod_cast (by omega : 1 ≤ mj.1)
        have hpow1 : (1 : ℝ) ≤ ((mj.1 ^ mj.2 : ℕ) : ℝ) := by
          push_cast; exact one_le_pow₀ hm1
        calc vonMangoldt (mj.1 ^ mj.2) / Real.log (mj.1 ^ mj.2 : ℕ) *
              ((mj.1 ^ mj.2 : ℕ) : ℝ) ^ (-σ)
            ≤ 1 * ((mj.1 ^ mj.2 : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
              mul_le_mul (vonMangoldt_div_log_le_one _)
                (Real.rpow_le_rpow_of_exponent_le hpow1 (by linarith))
                (Real.rpow_nonneg (by positivity) _) zero_le_one
          _ = ((1 : ℝ) / mj.1) ^ mj.2 := by
              rw [one_mul, Real.rpow_neg_one]; push_cast; rw [one_div, inv_pow]
    _ = ∑ m ∈ Finset.Ico 2 Y, ∑ j ∈ Finset.Ico 2 Y, ((1 : ℝ) / m) ^ j := by
        rw [hP, Finset.sum_product]
    _ ≤ ∑ m ∈ Finset.Ico 2 Y, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_Ico] at hm
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
        have hx0 : (0 : ℝ) ≤ 1 / m := by positivity
        have hx1 : (1 : ℝ) / m < 1 := by rw [div_lt_one (by linarith)]; linarith
        refine (geom_sum_Ico_le_of_lt_one hx0 hx1).trans (le_of_eq ?_)
        field_simp
    _ ≤ 1 := sum_Ico_inv_mul_pred_le_one Y

/-- The class Chebyshev function `ψ(N; q, a) = Σ_{n < N, n ≡ a} Λ(n)`. -/
def classPsi (q a : ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (if n % q = a then vonMangoldt n else 0)

/-- Two-sided bounds from the prime number theorem in progressions. -/
theorem exists_classPsi_bounds {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q)
    {η : ℝ} (hη : 0 < η) : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (1 / (q.totient : ℝ) - η) * N ≤ classPsi q a N ∧
        classPsi q a N ≤ (1 / (q.totient : ℝ) + η) * N := by
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (WeakPNT_AP hq ha haq) η hη
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hd := hN₀ N (le_of_max_le_left hN)
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq, abs_lt] at hd
  obtain ⟨h1, h2⟩ := hd
  have hc : cumsum (fun n => if n % q = a then vonMangoldt n else 0) N = classPsi q a N := rfl
  rw [hc] at h1 h2
  constructor
  · have : 1 / (q.totient : ℝ) - η < classPsi q a N / N := by linarith
    rw [lt_div_iff₀ hNpos] at this; linarith
  · have : classPsi q a N / N < 1 / (q.totient : ℝ) + η := by linarith
    rw [div_lt_iff₀ hNpos] at this; linarith

theorem classPsi_sub (q a : ℕ) {A B : ℕ} (hAB : A ≤ B) :
    classPsi q a B - classPsi q a A =
      ∑ n ∈ Finset.Ico A B, (if n % q = a then vonMangoldt n else 0) := by
  rw [classPsi, classPsi, Finset.sum_Ico_eq_sub _ hAB]

/-- Left end `⌈ρ^{k+1/4}⌉` of the `k`-th block. -/
def blockLo (ρ : ℝ) (k : ℕ) : ℕ := ⌈ρ ^ ((k : ℝ) + 1 / 4)⌉₊

/-- Right end `⌊ρ^{k+3/4}⌋` of the `k`-th block. -/
def blockHi (ρ : ℝ) (k : ℕ) : ℕ := ⌊ρ ^ ((k : ℝ) + 3 / 4)⌋₊

/-- **Block lower bound.** For large `k` the class Chebyshev mass of the `k`-th block is
`≥ c₀ ρ^k`. -/
theorem exists_block_lower {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q) {ρ : ℝ}
    (hρ : 1 < ρ) : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      2 ≤ blockLo ρ k ∧ blockLo ρ k ≤ blockHi ρ k ∧
      c₀ * ρ ^ k ≤ ∑ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
        (if n % q = a then vonMangoldt n else 0) := by
  have htot : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 1 / (q.totient : ℝ) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ρ ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ρ ^ ((3 : ℝ) / 4) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy]; exact Real.one_le_rpow hρ.le (by norm_num)
  have hyz : y < z := by rw [hy, hz]; exact Real.rpow_lt_rpow_of_exponent_lt hρ (by norm_num)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = d * ((z - y) / (2 * (z + y))) := ⟨_, rfl⟩
  have hzy : 0 < (z - y) / (2 * (z + y)) := div_pos (by linarith) (by linarith)
  have hzy1 : (z - y) / (2 * (z + y)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hη0 : 0 < η := by rw [hη]; exact mul_pos hd0 hzy
  have hdη : 0 ≤ d - η := by
    have : η ≤ d / 2 := by rw [hη]; nlinarith
    linarith
  obtain ⟨N₀, hN₀⟩ := exists_classPsi_bounds hq ha haq hη0
  -- `(d − η) z − (d + η) y = d (z − y)/2`
  have hzy0 : z + y ≠ 0 := by linarith
  have hηzy : η * (z + y) = d * (z - y) / 2 := by
    rw [hη]; field_simp
  have hkey : (d - η) * z - (d + η) * y = d * (z - y) / 2 := by
    linear_combination (-1 : ℝ) * hηzy
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = d * (z - y) / 4 := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by rw [hc₀]; have := mul_pos hd0 (sub_pos.mpr hyz); linarith
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, max (max (N₀ : ℝ) 2) (max (8 / (z - y)) (4 / (z - y))) ≤ ρ ^ k₀ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hρ).eventually_ge_atTop _).exists
  refine ⟨c₀, hc₀pos, k₀, fun k hk => ?_⟩
  have hbig := hk₀.trans (pow_le_pow_right₀ hρ.le hk)
  set R := ρ ^ k with hR
  have hN : (N₀ : ℝ) ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hbig)
  have h2 : (2 : ℝ) ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hbig)
  have h8 : 8 / (z - y) ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hbig)
  have h8' : 8 ≤ R * (z - y) := by rw [div_le_iff₀ (by linarith)] at h8; linarith
  have hlo : ρ ^ ((k : ℝ) + 1 / 4) = R * y := by
    rw [hR, hy, Real.rpow_add hρ0, Real.rpow_natCast]
  have hhi : ρ ^ ((k : ℝ) + 3 / 4) = R * z := by
    rw [hR, hz, Real.rpow_add hρ0, Real.rpow_natCast]
  have hRy : R ≤ R * y := le_mul_of_one_le_right (by linarith) hy1
  have hA_ge : R * y ≤ (blockLo ρ k : ℝ) := hlo ▸ Nat.le_ceil _
  have hA_le : (blockLo ρ k : ℝ) < R * y + 1 := hlo ▸ Nat.ceil_lt_add_one (by positivity)
  have hB_ge : R * z - 1 < (blockHi ρ k : ℝ) := hhi ▸ Nat.sub_one_lt_floor _
  have hRzy : R * z - R * y = R * (z - y) := by ring
  have hAB : (blockLo ρ k : ℝ) ≤ blockHi ρ k := by linarith
  have hAB' : blockLo ρ k ≤ blockHi ρ k := by exact_mod_cast hAB
  have hA2 : 2 ≤ blockLo ρ k := by
    have : (2 : ℝ) ≤ blockLo ρ k := by linarith
    exact_mod_cast this
  refine ⟨hA2, hAB', ?_⟩
  rw [← classPsi_sub q a hAB']
  have hAN : N₀ ≤ blockLo ρ k := by
    have : (N₀ : ℝ) ≤ blockLo ρ k := by linarith
    exact_mod_cast this
  have hupA := (hN₀ _ hAN).2
  have hloB := (hN₀ _ (hAN.trans hAB')).1
  rw [← hd] at hupA hloB
  have e1 : (d - η) * (R * z - 1) ≤ (d - η) * (blockHi ρ k : ℝ) :=
    mul_le_mul_of_nonneg_left hB_ge.le hdη
  have e2 : (d + η) * (blockLo ρ k : ℝ) ≤ (d + η) * (R * y + 1) :=
    mul_le_mul_of_nonneg_left hA_le.le (by linarith)
  have e3 : (d - η) * (R * z - 1) - (d + η) * (R * y + 1) = R * (d * (z - y) / 2) - 2 * d := by
    rw [← hkey]; ring
  have e4 : R * (d * (z - y) / 2) - 2 * d ≥ c₀ * R := by
    rw [hc₀]
    have : d * 8 ≤ d * (R * (z - y)) := mul_le_mul_of_nonneg_left h8' hd0.le
    nlinarith
  linarith

/-- Block ends in terms of powers of `ρ`. -/
theorem blockLo_ge (ρ : ℝ) (k : ℕ) : ρ ^ ((k : ℝ) + 1 / 4) ≤ (blockLo ρ k : ℝ) := Nat.le_ceil _

theorem blockHi_le {ρ : ℝ} (hρ : 1 < ρ) (k : ℕ) : (blockHi ρ k : ℝ) ≤ ρ ^ ((k : ℝ) + 3 / 4) :=
  Nat.floor_le (Real.rpow_nonneg (by linarith) _)

/-- Blocks are disjoint and increasing: `blockHi k ≤ blockLo j` for `k < j`. -/
theorem blockHi_le_blockLo {ρ : ℝ} (hρ : 1 < ρ) {k j : ℕ} (hkj : k < j) :
    blockHi ρ k ≤ blockLo ρ j := by
  have h1 := blockHi_le hρ k
  have h2 := blockLo_ge ρ j
  have h3 : ρ ^ ((k : ℝ) + 3 / 4) ≤ ρ ^ ((j : ℝ) + 1 / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le hρ.le
    have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
    linarith
  exact_mod_cast h1.trans (h3.trans h2)

theorem blockHi_mono {ρ : ℝ} (hρ : 1 < ρ) {k j : ℕ} (hkj : k ≤ j) : blockHi ρ k ≤ blockHi ρ j := by
  apply Nat.floor_le_floor
  apply Real.rpow_le_rpow_of_exponent_le hρ.le
  have : (k : ℝ) ≤ j := by exact_mod_cast hkj
  linarith

/-- Points of the `k`-th block have phase in `[¼, ¾]`. -/
theorem fract_mem_of_mem_block {ρ : ℝ} (hρ : 1 < ρ) {k n : ℕ}
    (hn : n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k)) :
    1 / 4 ≤ Int.fract (Real.log n / Real.log ρ) ∧ Int.fract (Real.log n / Real.log ρ) ≤ 3 / 4 := by
  rw [Finset.mem_Ico] at hn
  have hρ0 : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlo : ρ ^ ((k : ℝ) + 1 / 4) ≤ (n : ℝ) :=
    (blockLo_ge ρ k).trans (by exact_mod_cast hn.1)
  have hhi : (n : ℝ) ≤ ρ ^ ((k : ℝ) + 3 / 4) :=
    (by exact_mod_cast hn.2.le : (n : ℝ) ≤ blockHi ρ k).trans (blockHi_le hρ k)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.rpow_pos_of_pos hρ0 _) hlo
  have h1 : ((k : ℝ) + 1 / 4) * Real.log ρ ≤ Real.log n := by
    rw [← Real.log_rpow hρ0]; exact Real.log_le_log (Real.rpow_pos_of_pos hρ0 _) hlo
  have h2 : Real.log n ≤ ((k : ℝ) + 3 / 4) * Real.log ρ := by
    rw [← Real.log_rpow hρ0]; exact Real.log_le_log hnpos hhi
  have h1' : (k : ℝ) + 1 / 4 ≤ Real.log n / Real.log ρ := by rw [le_div_iff₀ hlogρ]; exact h1
  have h2' : Real.log n / Real.log ρ ≤ (k : ℝ) + 3 / 4 := by rw [div_le_iff₀ hlogρ]; exact h2
  have hfl : ⌊Real.log n / Real.log ρ⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [Int.fract, hfl]
  push_cast
  constructor <;> linarith

/-- **Weighted block bound.** -/
theorem block_weighted_lower {q a : ℕ} {ρ : ℝ} (hρ : 1 < ρ) {c₀ : ℝ} (hc₀ : 0 < c₀) {k : ℕ}
    (hA2 : 2 ≤ blockLo ρ k)
    (hmass : c₀ * ρ ^ k ≤ ∑ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
      (if n % q = a then vonMangoldt n else 0))
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    c₀ * ρ ^ (-(2 : ℝ)) / Real.log ρ * (ρ ^ (-(σ - 1))) ^ k / ((k : ℝ) + 1) ≤
      ∑ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
        (if n % q = a then vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) else 0) := by
  have hρ0 : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  set T : ℝ := ρ ^ ((k : ℝ) + 1) with hT
  have hTpos : 0 < T := Real.rpow_pos_of_pos hρ0 _
  set W : ℝ := 1 / (((k : ℝ) + 1) * Real.log ρ * T ^ σ) with hW
  have hWpos : 0 < W := by rw [hW]; positivity
  have hterm : ∀ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
      W * (if n % q = a then vonMangoldt n else 0) ≤
        (if n % q = a then vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) else 0) := by
    intro n hn
    split_ifs
    · have hn' := Finset.mem_Ico.mp hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hA2.trans hn'.1
      have hnT : (n : ℝ) ≤ T := by
        have := (by exact_mod_cast hn'.2.le : (n : ℝ) ≤ blockHi ρ k).trans (blockHi_le hρ k)
        exact this.trans (Real.rpow_le_rpow_of_exponent_le hρ.le (by linarith))
      have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
      have hlognT : Real.log n ≤ ((k : ℝ) + 1) * Real.log ρ := by
        rw [← Real.log_rpow hρ0]; exact Real.log_le_log (by linarith) hnT
      have hpow : T ^ (-σ) ≤ (n : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hnT (by linarith)
      have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
      rw [hW]
      have e : 1 / (((k : ℝ) + 1) * Real.log ρ * T ^ σ) * vonMangoldt n =
          vonMangoldt n / (((k : ℝ) + 1) * Real.log ρ) * T ^ (-σ) := by
        rw [Real.rpow_neg hTpos.le]; field_simp
      rw [e]
      apply mul_le_mul _ hpow (Real.rpow_nonneg hTpos.le _) (div_nonneg hΛ hlogn.le)
      exact div_le_div_of_nonneg_left hΛ hlogn hlognT
    · simp
  calc c₀ * ρ ^ (-(2 : ℝ)) / Real.log ρ * (ρ ^ (-(σ - 1))) ^ k / ((k : ℝ) + 1)
      ≤ W * (c₀ * ρ ^ k) := by
        have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hL : c₀ * ρ ^ (-(2 : ℝ)) / Real.log ρ * (ρ ^ (-(σ - 1))) ^ k / ((k : ℝ) + 1) =
            c₀ / (((k : ℝ) + 1) * Real.log ρ) * (ρ ^ (-(2 : ℝ)) * ρ ^ (-(σ - 1) * k)) := by
          rw [← Real.rpow_natCast (ρ ^ (-(σ - 1))) k, ← Real.rpow_mul hρ0.le]
          field_simp
        have hR' : W * (c₀ * ρ ^ k) = c₀ / (((k : ℝ) + 1) * Real.log ρ) *
            (ρ ^ (k : ℝ) / ρ ^ (((k : ℝ) + 1) * σ)) := by
          rw [hW, hT, ← Real.rpow_mul hρ0.le, ← Real.rpow_natCast ρ k]
          field_simp
        rw [hL, hR']
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_add hρ0, ← Real.rpow_sub hρ0]
        apply Real.rpow_le_rpow_of_exponent_le hρ.le
        nlinarith
    _ ≤ W * ∑ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
          (if n % q = a then vonMangoldt n else 0) := mul_le_mul_of_nonneg_left hmass hWpos.le
    _ = ∑ n ∈ Finset.Ico (blockLo ρ k) (blockHi ρ k),
          W * (if n % q = a then vonMangoldt n else 0) := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum hterm


/-- **Window prime-sum lower bound.** Primes `p ≡ a (mod q)` with `{log p / log ρ} ∈ [¼, ¾]`
satisfy `Σ p^{−σ} ≥ c log(1/(σ−1)) − C` once all primes below a threshold `Y₀(σ)` are included. -/
theorem exists_window_prime_sum_lower {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q) (haq : a < q)
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      c * Real.log (1 / (σ - 1)) - C ≤
        ∑ p ∈ (Finset.range Y).filter (fun p => p.Prime ∧ p % q = a ∧
          1 / 4 ≤ Int.fract (Real.log p / Real.log ρ) ∧
            Int.fract (Real.log p / Real.log ρ) ≤ 3 / 4), (p : ℝ) ^ (-σ) := by
  classical
  obtain ⟨c₀, hc₀, k₀, hk₀⟩ := exists_block_lower hq ha haq hρ
  have hρ0 : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = c₀ * ρ ^ (-(2 : ℝ)) / Real.log ρ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; have := Real.rpow_pos_of_pos hρ0 (-(2 : ℝ)); positivity
  refine ⟨c, hcpos, c * (|Real.log (Real.log ρ)| + 1 + k₀) + 1, fun σ hσ hσ2 => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ρ ^ (-(σ - 1)) := ⟨_, rfl⟩
  have hx0 : 0 < x := by rw [hx]; exact Real.rpow_pos_of_pos hρ0 _
  have hx1 : x < 1 := by rw [hx]; exact Real.rpow_lt_one_of_one_lt_of_neg hρ (by linarith)
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rw [abs_of_pos hx0]; exact hx1)
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp
    (hsum.tendsto_sum_nat.eventually (lt_mem_nhds (show -Real.log (1 - x) - 1 <
      -Real.log (1 - x) by linarith)))
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = max K₁ k₀ := ⟨_, rfl⟩
  refine ⟨blockHi ρ K, fun Y hY => ?_⟩
  set blk : ℕ → Finset ℕ :=
    fun k => (Finset.Ico (blockLo ρ k) (blockHi ρ k)).filter (fun n => n % q = a) with hblk
  set U := (Finset.Ico k₀ K).biUnion blk with hU
  set w : ℕ → ℝ := fun n => vonMangoldt n / Real.log n * (n : ℝ) ^ (-σ) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (vonMangoldt_div_log_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- disjoint blocks
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ico k₀ K) : Set ℕ) blk := by
    intro k _ j _ hkj
    rw [Function.onFun, Finset.disjoint_left]
    intro n hnk hnj
    simp only [hblk, Finset.mem_filter, Finset.mem_Ico] at hnk hnj
    rcases lt_or_gt_of_ne hkj with h | h
    · have := blockHi_le_blockLo hρ h; omega
    · have := blockHi_le_blockLo hρ h; omega
  -- block sums
  have hblock : ∀ k ∈ Finset.Ico k₀ K, c * x ^ k / ((k : ℝ) + 1) ≤ ∑ n ∈ blk k, w n := by
    intro k hk
    have hkk₀ : k₀ ≤ k := (Finset.mem_Ico.mp hk).1
    obtain ⟨hA2, _, hmass⟩ := hk₀ k hkk₀
    have := block_weighted_lower (q := q) (a := a) hρ hc₀ hA2 hmass hσ hσ2
    rw [hblk, Finset.sum_filter]
    rw [hc, hx]
    exact this
  have hU_sum : ∑ n ∈ U, w n = ∑ k ∈ Finset.Ico k₀ K, ∑ n ∈ blk k, w n :=
    Finset.sum_biUnion hdisj
  -- the logarithmic series
  have hKK₁ : K₁ ≤ K := by rw [hK]; exact le_max_left _ _
  have hKk₀ : k₀ ≤ K := by rw [hK]; exact le_max_right _ _
  have hser : -Real.log (1 - x) - 1 < ∑ i ∈ Finset.range K, x ^ (i + 1) / ((i : ℝ) + 1) :=
    hK₁ K hKK₁
  have hsplit := Finset.sum_range_add_sum_Ico (fun i => x ^ (i + 1) / ((i : ℝ) + 1)) hKk₀
  have hhead : ∑ i ∈ Finset.range k₀, x ^ (i + 1) / ((i : ℝ) + 1) ≤ k₀ := by
    calc ∑ i ∈ Finset.range k₀, x ^ (i + 1) / ((i : ℝ) + 1)
        ≤ ∑ _i ∈ Finset.range k₀, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [div_le_one (by positivity)]
          have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
          have : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
          linarith
      _ = k₀ := by simp
  have htail : ∑ i ∈ Finset.Ico k₀ K, x ^ (i + 1) / ((i : ℝ) + 1) ≤
      ∑ i ∈ Finset.Ico k₀ K, x ^ i / ((i : ℝ) + 1) := by
    refine Finset.sum_le_sum fun i _ => ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg hx0.le _) hx1.le
  -- `−log(1 − x) ≥ log(1/(σ−1)) − log log ρ`
  have hlogx : Real.log (1 / (σ - 1)) - Real.log (Real.log ρ) ≤ -Real.log (1 - x) := by
    have hx' : x = Real.exp (-((σ - 1) * Real.log ρ)) := by
      rw [hx, Real.rpow_def_of_pos hρ0]; ring_nf
    have h1x : 1 - x ≤ (σ - 1) * Real.log ρ := by
      have := Real.add_one_le_exp (-((σ - 1) * Real.log ρ)); rw [← hx'] at this; linarith
    have hpos : 0 < 1 - x := by linarith
    have hlog := Real.log_le_log hpos h1x
    rw [Real.log_mul (by linarith) hlogρ.ne'] at hlog
    rw [one_div, Real.log_inv]
    linarith
  -- the prime part
  have hUY : ∀ n ∈ U, n < Y := by
    intro n hn
    rw [hU, Finset.mem_biUnion] at hn
    obtain ⟨k, hk, hnk⟩ := hn
    simp only [hblk, Finset.mem_filter, Finset.mem_Ico] at hnk
    have := blockHi_mono hρ (Finset.mem_Ico.mp hk).2.le
    omega
  have hprime : ∑ n ∈ U.filter Nat.Prime, w n ≤
      ∑ p ∈ (Finset.range Y).filter (fun p => p.Prime ∧ p % q = a ∧
        1 / 4 ≤ Int.fract (Real.log p / Real.log ρ) ∧
          Int.fract (Real.log p / Real.log ρ) ≤ 3 / 4), (p : ℝ) ^ (-σ) := by
    have hwp : ∀ n ∈ U.filter Nat.Prime, w n = (n : ℝ) ^ (-σ) := by
      intro n hn
      have hnp := (Finset.mem_filter.mp hn).2
      simp only [hw]
      rw [vonMangoldt_apply_prime hnp, div_self (Real.log_pos (by exact_mod_cast hnp.one_lt)).ne',
        one_mul]
    rw [Finset.sum_congr rfl hwp]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hnU, hnp⟩ := Finset.mem_filter.mp hn
      have hnU' := hnU
      rw [hU, Finset.mem_biUnion] at hnU'
      obtain ⟨k, hk, hnk⟩ := hnU'
      simp only [hblk, Finset.mem_filter] at hnk
      have hfr := fract_mem_of_mem_block hρ hnk.1
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hUY n hnU, hnp, hnk.2, hfr⟩
    · intro n _ _; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcomp : ∑ n ∈ U.filter (fun n => ¬ n.Prime), w n ≤ 1 := by
    have hsub : ∑ n ∈ U.filter (fun n => ¬ n.Prime), w n =
        ∑ n ∈ (U.filter (fun n => ¬ n.Prime)).filter IsPrimePow, w n := by
      refine (Finset.sum_filter_of_ne fun n _ hn => ?_).symm
      by_contra h
      apply hn
      have : vonMangoldt n = 0 := by
        by_contra hne; exact h (vonMangoldt_ne_zero_iff.mp hne)
      simp [hw, this]
    rw [hsub]
    refine le_trans ?_ (sum_compositePrimePow_le_one Y hσ.le)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨Finset.mem_range.mpr (hUY n hn.1.1), hn.2, hn.1.2⟩
    · intro n _ _; exact hw0 n
  have hUsplit := Finset.sum_filter_add_sum_filter_not U Nat.Prime w
  -- assemble
  have hlower : c * (-Real.log (1 - x) - 1 - k₀) ≤ ∑ n ∈ U, w n := by
    rw [hU_sum]
    calc c * (-Real.log (1 - x) - 1 - k₀)
        ≤ c * ∑ i ∈ Finset.Ico k₀ K, x ^ (i + 1) / ((i : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hcpos.le; linarith
      _ ≤ c * ∑ i ∈ Finset.Ico k₀ K, x ^ i / ((i : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left htail hcpos.le
      _ = ∑ i ∈ Finset.Ico k₀ K, c * x ^ i / ((i : ℝ) + 1) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ _ := Finset.sum_le_sum hblock
  have habs : Real.log (Real.log ρ) ≤ |Real.log (Real.log ρ)| := le_abs_self _
  nlinarith

end RHTower.ResidueClassPrimes
