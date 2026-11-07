import GaloisForLFunctions.PrimeTorusTheory.TarryEscottWordsForbidAlignment

/-!
# Non-alignment at every large height

With `L = log |t|` and `ℓ = log L`:

**Theorem** (`exists_not_aligned_of_large`). For every large `|t|` there is an integer `n ≥ 1` with `log n ≤ 50 √L ℓ^{3/2}` such that
`t log n / 2π` is at distance more than `16 ℓ²/L` from the integers.

The length is far below the Vinogradov–Korobov length `exp(L^{2/3})`, and the precision is a negative power of `log |t|`. The
parameters are `M ≍ L/ℓ²` (the length of the word), `E ≍ √(Mℓ)` (its first nonzero moment is no later), and `k ≍ √(M/ℓ)` (its moments up
to `k` vanish). The primes `E/4 < p ≤ E` carry the multiplicity bound, through Chebyshev's two-sided bound for `θ`.
-/

open Finset Real Filter Topology
open scoped Chebyshev

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

theorem two_mul_sum_range_succ (k : ℕ) :
    2 * (∑ j ∈ range (k + 1), (j + 1)) = (k + 1) * (k + 2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- The pigeonhole condition for a word, in logarithmic form. -/
theorem prod_choose_lt_of_log {M k : ℕ}
    (h : ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 2) ≤ (M : ℝ)) :
    ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1) := by
  have hterm : ∀ j ∈ range (k + 1), (M + 1).choose (j + 1) + 1 ≤ (M + 2) ^ (j + 1) := by
    intro j _
    have h1 : (M + 1).choose (j + 1) ≤ (M + 1) ^ (j + 1) := Nat.choose_le_pow _ _
    have h2 : (M + 1) ^ (j + 1) + 1 ≤ (M + 1 + 1) ^ (j + 1) := by
      have := Nat.pow_le_pow_left (Nat.le_succ (M + 1)) (j + 1)
      have hlt : (M + 1) ^ (j + 1) < (M + 1 + 1) ^ (j + 1) :=
        Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by omega)
      omega
    exact (Nat.add_le_add_right h1 1).trans h2
  have hprod : ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) ≤
      ∏ j ∈ range (k + 1), (M + 2) ^ (j + 1) := Finset.prod_le_prod' hterm
  have hsum : ∏ j ∈ range (k + 1), (M + 2) ^ (j + 1) = (M + 2) ^ (∑ j ∈ range (k + 1), (j + 1)) :=
    Finset.prod_pow_eq_pow_sum _ _ _
  refine lt_of_le_of_lt hprod ?_
  rw [hsum]
  have hsumle : 2 * (∑ j ∈ range (k + 1), (j + 1)) = (k + 1) * (k + 2) := two_mul_sum_range_succ k
  have hM2 : (1 : ℝ) < (M : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (M : ℝ) := by positivity
    linarith
  have hlogpos : 0 < Real.log ((M : ℝ) + 2) := Real.log_pos hM2
  set N := ∑ j ∈ range (k + 1), (j + 1) with hN
  have hNR : 2 * (N : ℝ) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    exact_mod_cast hsumle
  have hNle : 2 * (N : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by
    rw [hNR]
    nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℝ))]
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hreal : ((M + 2 : ℕ) : ℝ) ^ N < (2 : ℝ) ^ (M + 1) := by
    have hbase : (0 : ℝ) < ((M + 2 : ℕ) : ℝ) := by positivity
    rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    have hkey : 2 * (N : ℝ) * Real.log ((M : ℝ) + 2) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_right hNle hlogpos.le).trans h
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
    nlinarith
  exact_mod_cast hreal

/-- Chebyshev's bound on a truncated interval: eventually in `E`, `θ(E) − θ(E/4) ≥ E/4`. -/
theorem eventually_theta_sub_ge :
    ∀ᶠ E : ℕ in atTop, (E : ℝ) / 4 ≤ θ (E : ℝ) - θ ((E / 4 : ℕ) : ℝ) := by
  have hsmall : (fun x : ℝ => Real.log (x + 1) + 2 * √x * Real.log x) =o[atTop] (fun x => x) := by
    have h1 : (fun x : ℝ => Real.log (x + 1)) =o[atTop] (fun x => x) := by
      have h2 : Tendsto (fun x : ℝ => x + 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
      have h3 := Real.isLittleO_log_id_atTop.comp_tendsto h2
      refine h3.trans_isBigO ?_
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      simp only [Function.comp, id, norm_eq_abs]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    have h4 : (fun x : ℝ => 2 * √x * Real.log x) =o[atTop] (fun x => x) := by
      have h5 : (fun x : ℝ => Real.log x) =o[atTop] (fun x => √x) := by
        have := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)
        refine this.congr' ?_ ?_
        · exact Eventually.of_forall fun _ => rfl
        · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
          rw [Real.sqrt_eq_rpow]
      have h6 := (Asymptotics.isBigO_refl (fun x : ℝ => 2 * √x) atTop).mul_isLittleO h5
      refine h6.trans_isBigO ?_
      refine Asymptotics.IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [norm_eq_abs]
      rw [show 2 * √x * √x = 2 * (√x * √x) by ring, Real.mul_self_sqrt hx]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hx]
    exact h1.add h4
  have hev := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 16)
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 2] with E hE hE2
  have hE0 : (0 : ℝ) ≤ (E : ℝ) := by positivity
  have hlow := Chebyshev.theta_ge E
  have hup := Chebyshev.theta_le_log4_mul_x (x := ((E / 4 : ℕ) : ℝ)) (by positivity)
  have hdiv : ((E / 4 : ℕ) : ℝ) ≤ (E : ℝ) / 4 := by
    rw [le_div_iff₀ (by norm_num)]
    have : E / 4 * 4 ≤ E := Nat.div_mul_le_self E 4
    exact_mod_cast this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2 := Real.log_two_gt_d9
  have hlog2' := Real.log_two_lt_d9
  have hnonneg : 0 ≤ Real.log ((E : ℝ) + 1) + 2 * √(E : ℝ) * Real.log (E : ℝ) := by
    have h1 : 0 ≤ Real.log ((E : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (E : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ E))
    positivity
  have hb : Real.log ((E : ℝ) + 1) + 2 * √(E : ℝ) * Real.log (E : ℝ) ≤ 1 / 16 * (E : ℝ) := by
    have := hE
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hE0] at this
    exact this
  have hup' : θ ((E / 4 : ℕ) : ℝ) ≤ Real.log 4 * ((E : ℝ) / 4) :=
    hup.trans (mul_le_mul_of_nonneg_left hdiv (Real.log_nonneg (by norm_num)))
  rw [hlog4] at hup'
  nlinarith

/-- The set of primes carrying the multiplicity bound. -/
theorem eventually_exists_prime_set :
    ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → ∀ M : ℕ, 256 * (M + 2) ≤ E ^ 2 →
      32 * (M : ℝ) * Real.log (E : ℝ) < (E : ℝ) ^ 2 →
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, p ≤ E) ∧ (∀ p ∈ S, M + 1 + p < p * p) ∧
        M < ∑ p ∈ S, (p - 1) := by
  classical
  obtain ⟨E₁, hE₁⟩ := eventually_atTop.mp eventually_theta_sub_ge
  refine ⟨max E₁ 16, fun E hE M hM hlog => ?_⟩
  have hE1 : E₁ ≤ E := le_trans (le_max_left _ _) hE
  have hE16 : 16 ≤ E := le_trans (le_max_right _ _) hE
  set S := (Finset.Ioc (E / 4) E).filter Nat.Prime with hS
  have hmem : ∀ p ∈ S, p.Prime ∧ E / 4 < p ∧ p ≤ E := fun p hp => by
    have h1 := Finset.mem_filter.mp hp
    have h2 := Finset.mem_Ioc.mp h1.1
    exact ⟨h1.2, h2.1, h2.2⟩
  refine ⟨S, fun p hp => (hmem p hp).1, fun p hp => (hmem p hp).2.2, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2, _⟩ := hmem p hp
    have h4p : E < 4 * p := by omega
    have hsq : E ^ 2 < 16 * (p * p) := by nlinarith
    have hp2' := hp1.two_le
    have : 16 * (M + 2) < p * p := by omega
    nlinarith
  · have htheta : θ (E : ℝ) - θ ((E / 4 : ℕ) : ℝ) = ∑ p ∈ S, Real.log p := by
      rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
      have hsub : Nat.primesLE (E / 4) ⊆ Nat.primesLE E := by
        intro p hp
        rw [Nat.mem_primesLE] at hp ⊢
        exact ⟨hp.1.trans (Nat.div_le_self _ _), hp.2⟩
      rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext p
      simp only [Finset.mem_sdiff, Nat.mem_primesLE, hS, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨?_, h1⟩, h2⟩
        by_contra hcon
        exact h3 ⟨by omega, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h2, h3⟩, fun h => by omega⟩
    have hEpos : (0 : ℝ) < (E : ℝ) := by
      have : 0 < E := by omega
      exact_mod_cast this
    have hlogE : 0 < Real.log (E : ℝ) := Real.log_pos (by
      have : 1 < E := by omega
      exact_mod_cast this)
    have hcard : (E : ℝ) / 4 ≤ (S.card : ℝ) * Real.log (E : ℝ) := by
      have h1 := hE₁ E hE1
      rw [htheta] at h1
      refine h1.trans ?_
      have := Finset.sum_le_card_nsmul S (fun p => Real.log (p : ℝ)) (Real.log (E : ℝ)) fun p hp =>
        Real.log_le_log (by exact_mod_cast (hmem p hp).1.pos) (by exact_mod_cast (hmem p hp).2.2)
      rwa [nsmul_eq_mul] at this
    have hterm : ∀ p ∈ S, (E : ℝ) / 8 ≤ ((p - 1 : ℕ) : ℝ) := by
      intro p hp
      obtain ⟨_, hp2, _⟩ := hmem p hp
      have h1 : E / 4 ≤ p - 1 := by omega
      have h2 : E ≤ 8 * (E / 4) := by omega
      have h3 : E ≤ 8 * (p - 1) := by omega
      have h4 : (E : ℝ) ≤ 8 * ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h3
      linarith
    have hsum : (S.card : ℝ) * ((E : ℝ) / 8) ≤ ((∑ p ∈ S, (p - 1) : ℕ) : ℝ) := by
      push_cast
      have := Finset.card_nsmul_le_sum S (fun p => ((p - 1 : ℕ) : ℝ)) ((E : ℝ) / 8) hterm
      rwa [nsmul_eq_mul] at this
    have hfinal : (M : ℝ) < ((∑ p ∈ S, (p - 1) : ℕ) : ℝ) := by
      refine lt_of_lt_of_le ?_ hsum
      have h1 : (E : ℝ) ^ 2 ≤ 32 * ((S.card : ℝ) * ((E : ℝ) / 8)) * Real.log (E : ℝ) := by
        nlinarith [hcard, hEpos]
      have h2 : 32 * (M : ℝ) * Real.log (E : ℝ) <
          32 * ((S.card : ℝ) * ((E : ℝ) / 8)) * Real.log (E : ℝ) := lt_of_lt_of_le hlog h1
      have h3 := lt_of_mul_lt_mul_right h2 hlogE.le
      linarith
    exact_mod_cast hfinal

/-- The parameters of the word at height `exp L`, with `ℓ = log L`. -/
structure WordParameters (L ℓ : ℝ) (E₀ M E k : ℕ) : Prop where
  one_le_M : 1 ≤ M
  M_le : (M : ℝ) ≤ L / (256 * ℓ ^ 2)
  le_M : L / (512 * ℓ ^ 2) ≤ (M : ℝ)
  E_sq_ge : 64 * (M : ℝ) * ℓ ≤ (E : ℝ) ^ 2
  E_sq_le : (E : ℝ) ^ 2 ≤ 81 * (M : ℝ) * ℓ
  E₀_le : E₀ ≤ E
  eight_le : 8 ≤ E
  E_le_M : E ≤ M
  k_le : ((k : ℝ) + 2) ^ 2 * ℓ ≤ (M : ℝ)
  le_k : (M : ℝ) ≤ 4 * ((k : ℝ) + 1) ^ 2 * ℓ

/-- The parameters exist at every large `L`. -/
theorem exists_wordParameters {L ℓ : ℝ} {E₀ : ℕ} (hℓ : 12 ≤ ℓ)
    (hL : (41472 + 512 * (E₀ : ℝ) ^ 2) * ℓ ^ 3 ≤ L) :
    ∃ M E k, WordParameters L ℓ E₀ M E k := by
  have hℓpos : 0 < ℓ := by linarith
  have hsq : 0 < ℓ ^ 2 := by positivity
  have hcu : 0 < ℓ ^ 3 := by positivity
  have hE₀nn : (0 : ℝ) ≤ (E₀ : ℝ) ^ 2 := by positivity
  set R : ℝ := L / (256 * ℓ ^ 2) with hR
  have hRL : L = 256 * ℓ ^ 2 * R := by
    rw [hR]
    field_simp
  have hRlow : (162 + 2 * (E₀ : ℝ) ^ 2) * ℓ ≤ R := by
    have h1 : (41472 + 512 * (E₀ : ℝ) ^ 2) * ℓ ^ 3 ≤ 256 * ℓ ^ 2 * R := hRL ▸ hL
    have h2 : 256 * ℓ ^ 2 * ((162 + 2 * (E₀ : ℝ) ^ 2) * ℓ) ≤ 256 * ℓ ^ 2 * R := by
      calc _ = (41472 + 512 * (E₀ : ℝ) ^ 2) * ℓ ^ 3 := by ring
        _ ≤ _ := h1
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hR2 : 2 ≤ R := by nlinarith
  set M := ⌊R⌋₊ with hM
  have hMR : (M : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hMR' : R < (M : ℝ) + 1 := Nat.lt_floor_add_one R
  have hMhalf : R / 2 ≤ (M : ℝ) := by linarith
  have hMlow : (81 + (E₀ : ℝ) ^ 2) * ℓ ≤ (M : ℝ) := by nlinarith
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := by nlinarith
    exact_mod_cast this
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have : 0 < M := by omega
    exact_mod_cast this
  set s : ℝ := √((M : ℝ) * ℓ) with hs
  have hsq' : s ^ 2 = (M : ℝ) * ℓ := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs1 : 2 ≤ s := by
    have : (2 : ℝ) ^ 2 ≤ s ^ 2 := by
      rw [hsq']
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hspos.le (by norm_num)).mp this
  set E := ⌈8 * s⌉₊ with hE
  have hEle : (E : ℝ) < 8 * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hEge : 8 * s ≤ (E : ℝ) := Nat.le_ceil _
  have hEsqge : 64 * (M : ℝ) * ℓ ≤ (E : ℝ) ^ 2 := by
    have : (8 * s) ^ 2 ≤ (E : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hEge 2
    nlinarith
  have hEsqle : (E : ℝ) ^ 2 ≤ 81 * (M : ℝ) * ℓ := by
    have h1 : (E : ℝ) ≤ 9 * s := by linarith
    have h2 : (E : ℝ) ^ 2 ≤ (9 * s) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  have hE₀ : E₀ ≤ E := by
    have h1 : (E₀ : ℝ) ^ 2 ≤ (E : ℝ) ^ 2 := by
      have h2 : (E₀ : ℝ) ^ 2 * ℓ ≤ (M : ℝ) := by nlinarith
      nlinarith
    have h3 : (E₀ : ℝ) ≤ (E : ℝ) := (pow_le_pow_iff_left₀ (by positivity) (by positivity)
      (by norm_num)).mp h1
    exact_mod_cast h3
  have hE8 : 8 ≤ E := by
    have : (8 : ℝ) ≤ (E : ℝ) := by linarith
    exact_mod_cast this
  have hEM : E ≤ M := by
    have h1 : (E : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := by
      have : 81 * ℓ ≤ (M : ℝ) := by nlinarith
      nlinarith
    have h3 : (E : ℝ) ≤ (M : ℝ) := (pow_le_pow_iff_left₀ (by positivity) (by positivity)
      (by norm_num)).mp h1
    exact_mod_cast h3
  set κ : ℝ := √((M : ℝ) / ℓ) with hκ
  have hκsq : κ ^ 2 = (M : ℝ) / ℓ := Real.sq_sqrt (by positivity)
  have hκpos : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ4 : 4 ≤ κ := by
    have h1 : (4 : ℝ) ^ 2 ≤ κ ^ 2 := by
      rw [hκsq, le_div_iff₀ hℓpos]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by norm_num) hκpos (by norm_num)).mp h1
  set K := ⌊κ⌋₊ with hK
  have hKle : (K : ℝ) ≤ κ := Nat.floor_le hκpos
  have hKge : κ < (K : ℝ) + 1 := Nat.lt_floor_add_one κ
  have hK2 : 2 ≤ K := by
    have : (2 : ℝ) < (K : ℝ) := by linarith
    exact_mod_cast this.le
  refine ⟨M, E, K - 2, ⟨hM1, hMR, ?_, hEsqge, hEsqle, hE₀, hE8, hEM, ?_, ?_⟩⟩
  · have e1 : L / (512 * ℓ ^ 2) = R / 2 := by
      rw [hR]
      field_simp
      ring
    rw [e1]
    exact hMhalf
  · have e1 : ((K - 2 : ℕ) : ℝ) + 2 = (K : ℝ) := by
      rw [Nat.cast_sub hK2]
      push_cast
      ring
    rw [e1]
    have h1 : (K : ℝ) ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (by positivity) hKle 2
    rw [hκsq] at h1
    calc (K : ℝ) ^ 2 * ℓ ≤ (M : ℝ) / ℓ * ℓ := mul_le_mul_of_nonneg_right h1 hℓpos.le
      _ = (M : ℝ) := by field_simp
  · have e1 : ((K - 2 : ℕ) : ℝ) + 1 = (K : ℝ) - 1 := by
      rw [Nat.cast_sub hK2]
      push_cast
      ring
    rw [e1]
    have h1 : κ ≤ 2 * ((K : ℝ) - 1) := by linarith
    have h2 : κ ^ 2 ≤ (2 * ((K : ℝ) - 1)) ^ 2 := pow_le_pow_left₀ hκpos h1 2
    rw [hκsq, div_le_iff₀ hℓpos] at h2
    nlinarith

/-- The word parameters give the base point bound `x₀ ≤ 64 m^{E+2}`. -/
theorem log_x₀_le {M E x₀ : ℕ} {ℓ : ℝ} (hM : 1 ≤ M) (hE : E ≤ M) (hE1 : 1 ≤ E)
    (hx₀ : x₀ = 12 * (M + 1) ^ (E + 2) + E ^ 2 + 24 * (E + 1) + 2 * (M + 1) + 1)
    (hmℓ : Real.log ((M + 1 : ℕ) : ℝ) ≤ ℓ) :
    Real.log (x₀ : ℝ) ≤ ((E : ℝ) + 8) * ℓ := by
  set m := M + 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hP : m ^ 2 ≤ m ^ (E + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hmP : m ≤ m ^ 2 := by nlinarith
  have hE2 : E ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hle : x₀ ≤ 64 * m ^ (E + 2) := by
    rw [hx₀]
    have h1 : 24 * (E + 1) ≤ 48 * m := by omega
    have h2 : 1 ≤ m ^ 2 := by nlinarith
    omega
  have hx₀pos : 0 < x₀ := by
    rw [hx₀]
    omega
  have hlogm : Real.log 2 ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log (x₀ : ℝ) ≤ Real.log (64 * (m : ℝ) ^ (E + 2)) := by
    refine Real.log_le_log (by exact_mod_cast hx₀pos) ?_
    exact_mod_cast hle
  have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, h64] at hlog
  have hlogmnn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hEnn : (0 : ℝ) ≤ (E : ℝ) := by positivity
  push_cast at hlog
  calc Real.log (x₀ : ℝ) ≤ 6 * Real.log 2 + ((E : ℝ) + 2) * Real.log (m : ℝ) := hlog
    _ ≤ ((E : ℝ) + 8) * Real.log (m : ℝ) := by nlinarith
    _ ≤ ((E : ℝ) + 8) * ℓ := mul_le_mul_of_nonneg_left hmℓ (by positivity)

/-- Simple consequences of the parameters. -/
theorem WordParameters.M_add_two_le {L ℓ : ℝ} {E₀ M E k : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) : (M : ℝ) + 2 ≤ L := by
  have hLpos : 0 < L := by linarith
  have h2 : L / (256 * ℓ ^ 2) ≤ L / 2 := by
    refine div_le_div_of_nonneg_left hLpos.le (by norm_num) ?_
    nlinarith
  linarith [hP.M_le]

theorem WordParameters.E_le_sqrt {L ℓ : ℝ} {E₀ M E k : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) : (E : ℝ) ≤ √L / 6 := by
  have hLpos : 0 < L := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have h1 : (E : ℝ) ^ 2 ≤ L / 36 := by
    have h2 : 81 * (M : ℝ) * ℓ ≤ 81 * (L / (256 * ℓ ^ 2)) * ℓ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP.M_le (by norm_num)) hℓpos.le
    have h3 : 81 * (L / (256 * ℓ ^ 2)) * ℓ = 81 * L / (256 * ℓ) := by
      field_simp
    have h4 : 81 * L / (256 * ℓ) ≤ L / 36 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith [hP.E_sq_le]
  have h5 : (E : ℝ) ^ 2 ≤ (√L / 6) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hLpos.le]
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h5

/-- The lower end of the height range. -/
theorem three_pi_mul_pow_le {L ℓ : ℝ} {E₀ M E k x₀ : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) (hlogx₀ : Real.log (x₀ : ℝ) ≤ ((E : ℝ) + 8) * ℓ)
    (hx₀pos : (0 : ℝ) < (x₀ : ℝ)) : 3 * π * (x₀ : ℝ) ^ E ≤ Real.exp L := by
  have hℓpos : 0 < ℓ := by linarith
  have hLpos : 0 < L := by linarith
  have h3pi : 3 * π ≤ Real.exp 3 := by
    have hpi := Real.pi_lt_four
    have he := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    nlinarith
  have hx₀pow : (x₀ : ℝ) ^ E = Real.exp ((E : ℝ) * Real.log (x₀ : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hx₀pos]
  have hexp : 3 + (E : ℝ) * Real.log (x₀ : ℝ) ≤ L := by
    have h1 : (E : ℝ) * Real.log (x₀ : ℝ) ≤ (E : ℝ) * (((E : ℝ) + 8) * ℓ) :=
      mul_le_mul_of_nonneg_left hlogx₀ (by positivity)
    have hE8 : (8 : ℝ) ≤ (E : ℝ) := by exact_mod_cast hP.eight_le
    have h2 : (E : ℝ) * (((E : ℝ) + 8) * ℓ) ≤ 2 * (E : ℝ) ^ 2 * ℓ := by
      have h2a : (E : ℝ) * ((E : ℝ) + 8) ≤ 2 * (E : ℝ) ^ 2 := by nlinarith
      calc (E : ℝ) * (((E : ℝ) + 8) * ℓ) = ((E : ℝ) * ((E : ℝ) + 8)) * ℓ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2a hℓpos.le
    have h3 : 2 * (E : ℝ) ^ 2 * ℓ ≤ 2 * (81 * (L / (256 * ℓ ^ 2)) * ℓ) * ℓ := by
      have h4 : (E : ℝ) ^ 2 ≤ 81 * (L / (256 * ℓ ^ 2)) * ℓ := hP.E_sq_le.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP.M_le (by norm_num)) hℓpos.le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num)) hℓpos.le
    have h5 : 2 * (81 * (L / (256 * ℓ ^ 2)) * ℓ) * ℓ = 162 / 256 * L := by
      field_simp
      norm_num
    linarith
  rw [hx₀pow]
  calc 3 * π * Real.exp ((E : ℝ) * Real.log (x₀ : ℝ))
      ≤ Real.exp 3 * Real.exp ((E : ℝ) * Real.log (x₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right h3pi (Real.exp_pos _).le
    _ = Real.exp (3 + (E : ℝ) * Real.log (x₀ : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp L := Real.exp_le_exp.mpr hexp

/-- The upper end of the height range. -/
theorem exp_mul_pow_le {L ℓ : ℝ} {M E k x₂ : ℕ} (hℓpos : 0 < ℓ)
    (hlogm : Real.log ((M + 1 : ℕ) : ℝ) ≤ ℓ)
    (hx₂ge : Real.exp (L / ((k : ℝ) + 1) + ((E : ℝ) + 10) * ℓ) ≤ (x₂ : ℝ)) :
    Real.exp L * ((M + 1 : ℕ) : ℝ) ^ (k + 2) ≤ (x₂ : ℝ) ^ (k + 1) := by
  set Y : ℝ := L / ((k : ℝ) + 1) + ((E : ℝ) + 10) * ℓ with hY
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have h1 : (Real.exp Y) ^ (k + 1) ≤ (x₂ : ℝ) ^ (k + 1) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hx₂ge _
  refine le_trans ?_ h1
  rw [← Real.exp_nat_mul]
  have h2 : ((M + 1 : ℕ) : ℝ) ^ (k + 2) =
      Real.exp (((k + 2 : ℕ) : ℝ) * Real.log ((M + 1 : ℕ) : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hmpos]
  rw [h2, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h3 : ((k + 1 : ℕ) : ℝ) * Y = L + ((k : ℝ) + 1) * (((E : ℝ) + 10) * ℓ) := by
    rw [hY]
    push_cast
    field_simp
  rw [h3]
  have h4 : ((k + 2 : ℕ) : ℝ) * Real.log ((M + 1 : ℕ) : ℝ) ≤ ((k : ℝ) + 2) * ℓ := by
    have e : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlogm (by positivity)
  have hEnn : (0 : ℝ) ≤ (E : ℝ) := by positivity
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have h5 : ((k : ℝ) + 2) * ℓ ≤ ((k : ℝ) + 1) * (((E : ℝ) + 10) * ℓ) := by
    have h6 : (k : ℝ) + 2 ≤ ((k : ℝ) + 1) * ((E : ℝ) + 10) := by
      have h7 : ((k : ℝ) + 1) * 2 ≤ ((k : ℝ) + 1) * ((E : ℝ) + 10) :=
        mul_le_mul_of_nonneg_left (by linarith) hk1pos.le
      linarith
    calc ((k : ℝ) + 2) * ℓ ≤ (((k : ℝ) + 1) * ((E : ℝ) + 10)) * ℓ :=
          mul_le_mul_of_nonneg_right h6 hℓpos.le
      _ = _ := by ring
  linarith

/-- The precision. -/
theorem precision_lt {L ℓ : ℝ} {E₀ M E k : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) : ((M : ℝ) + 1) * (16 * ℓ ^ 2 / L) < 1 / 4 := by
  have hℓpos : 0 < ℓ := by linarith
  have hLpos : 0 < L := by linarith
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hP.one_le_M
  have h1 : (M : ℝ) + 1 ≤ 2 * (L / (256 * ℓ ^ 2)) := by
    have h2 : 1 ≤ L / (256 * ℓ ^ 2) := hM1R.trans hP.M_le
    linarith [hP.M_le]
  have h3 : 2 * (L / (256 * ℓ ^ 2)) * (16 * ℓ ^ 2 / L) = 1 / 8 := by
    field_simp
    norm_num
  have h4 : ((M : ℝ) + 1) * (16 * ℓ ^ 2 / L) ≤ 2 * (L / (256 * ℓ ^ 2)) * (16 * ℓ ^ 2 / L) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

/-- The size of the length parameter. -/
theorem length_le {L ℓ : ℝ} {E₀ M E k : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) :
    L / ((k : ℝ) + 1) + ((E : ℝ) + 10) * ℓ + 2 ≤ 50 * √L * (ℓ * √ℓ) := by
  have hℓpos : 0 < ℓ := by linarith
  have hLpos : 0 < L := by linarith
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set w := √ℓ with hw
  have hwsq : w * w = ℓ := Real.mul_self_sqrt hℓpos.le
  have hw1 : 1 ≤ w := Real.one_le_sqrt.mpr (by linarith)
  set r := √L with hr
  have hrsq : r * r = L := Real.mul_self_sqrt hLpos.le
  have hsqrtL : 12 ≤ r := Real.le_sqrt_of_sq_le (by linarith)
  have hEreal : (E : ℝ) ≤ r / 6 := hP.E_le_sqrt hℓ hL
  have hkey : r ≤ 46 * (ℓ * w) * ((k : ℝ) + 1) := by
    have h1 : L / (512 * ℓ ^ 2) ≤ 4 * ((k : ℝ) + 1) ^ 2 * ℓ := hP.le_M.trans hP.le_k
    rw [div_le_iff₀ (by positivity)] at h1
    have h2 : r ^ 2 ≤ (46 * (ℓ * w) * ((k : ℝ) + 1)) ^ 2 := by
      have e1 : r ^ 2 = L := by rw [sq]; exact hrsq
      have e2 : (46 * (ℓ * w) * ((k : ℝ) + 1)) ^ 2 =
          2116 * ℓ ^ 3 * ((k : ℝ) + 1) ^ 2 := by
        have hw2 : w ^ 2 = ℓ := by rw [sq]; exact hwsq
        calc _ = 2116 * ℓ ^ 2 * w ^ 2 * ((k : ℝ) + 1) ^ 2 := by ring
          _ = _ := by rw [hw2]; ring
      rw [e1, e2]
      have h3 : L ≤ 2048 * ℓ ^ 3 * ((k : ℝ) + 1) ^ 2 := by
        calc L ≤ 4 * ((k : ℝ) + 1) ^ 2 * ℓ * (512 * ℓ ^ 2) := h1
          _ = _ := by ring
      have h4 : 0 ≤ ℓ ^ 3 * ((k : ℝ) + 1) ^ 2 := by positivity
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h2
  have h1 : L / ((k : ℝ) + 1) ≤ 46 * r * (ℓ * w) := by
    rw [div_le_iff₀ hk1pos, ← hrsq]
    have : r * r ≤ r * (46 * (ℓ * w) * ((k : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hkey (by positivity)
    calc r * r ≤ _ := this
      _ = _ := by ring
  have h2 : ((E : ℝ) + 10) * ℓ ≤ r * (ℓ * w) := by
    have h3 : (E : ℝ) + 10 ≤ r := by linarith
    have h4 : ℓ ≤ ℓ * w := le_mul_of_one_le_right hℓpos.le hw1
    calc ((E : ℝ) + 10) * ℓ ≤ r * ℓ := mul_le_mul_of_nonneg_right h3 hℓpos.le
      _ ≤ r * (ℓ * w) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h5 : 2 ≤ r * (ℓ * w) := by
    have h6 : 12 ≤ ℓ * w := by nlinarith
    nlinarith
  linarith

/-- The word condition and the prime set hold at the parameters. -/
theorem word_and_primes {L ℓ : ℝ} {E₀ M E k : ℕ} (hP : WordParameters L ℓ E₀ M E k)
    (hE₀ : ∀ E, E₀ ≤ E → ∀ M : ℕ, 256 * (M + 2) ≤ E ^ 2 →
      32 * (M : ℝ) * Real.log (E : ℝ) < (E : ℝ) ^ 2 →
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, p ≤ E) ∧ (∀ p ∈ S, M + 1 + p < p * p) ∧
        M < ∑ p ∈ S, (p - 1))
    (hℓ : 12 ≤ ℓ) (hL : 144 ≤ L) (hℓlog : ℓ = Real.log L) :
    ∏ j ∈ range (k + 1), ((M + 1).choose (j + 1) + 1) < 2 ^ (M + 1) ∧
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, p ≤ E) ∧ (∀ p ∈ S, M + 1 + p < p * p) ∧
        M < ∑ p ∈ S, (p - 1) := by
  have hℓpos : 0 < ℓ := by linarith
  have hLpos : 0 < L := by linarith
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hP.one_le_M
  have hML := hP.M_add_two_le hℓ hL
  have hlogM2 : Real.log ((M : ℝ) + 2) ≤ ℓ := by
    rw [hℓlog]
    exact Real.log_le_log (by positivity) hML
  constructor
  · refine prod_choose_lt_of_log ?_
    exact (mul_le_mul_of_nonneg_left hlogM2 (by positivity)).trans hP.k_le
  · have hEpos : (1 : ℝ) ≤ (E : ℝ) := by exact_mod_cast (by have := hP.eight_le; omega : 1 ≤ E)
    have hEreal := hP.E_le_sqrt hℓ hL
    have hlogE : Real.log (E : ℝ) ≤ ℓ := by
      rw [hℓlog]
      refine Real.log_le_log (by linarith) ?_
      have h12 : 12 ≤ √L := Real.le_sqrt_of_sq_le (by linarith)
      have : √L ≤ L := by nlinarith [Real.sq_sqrt hLpos.le]
      linarith
    refine hE₀ E hP.E₀_le M ?_ ?_
    · have h1 : 64 * (M : ℝ) * 12 ≤ (E : ℝ) ^ 2 :=
        (mul_le_mul_of_nonneg_left hℓ (by positivity)).trans hP.E_sq_ge
      have h2 : (256 : ℝ) * ((M : ℝ) + 2) ≤ (E : ℝ) ^ 2 := by linarith
      exact_mod_cast h2
    · have h1 : 32 * (M : ℝ) * Real.log (E : ℝ) ≤ 32 * (M : ℝ) * ℓ :=
        mul_le_mul_of_nonneg_left hlogE (by positivity)
      have h2 : 32 * (M : ℝ) * ℓ < 64 * (M : ℝ) * ℓ := by
        have := mul_pos (by linarith : (0 : ℝ) < (M : ℝ)) hℓpos
        linarith
      linarith [hP.E_sq_ge]

/-- **Non-alignment at every large height.** See the module docstring. -/
theorem exists_not_aligned_of_large :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∃ n : ℕ, 1 ≤ n ∧
        Real.log n ≤ 50 * √(Real.log |t|) * (Real.log (Real.log |t|) * √(Real.log (Real.log |t|))) ∧
        ∀ j : ℤ, 16 * Real.log (Real.log |t|) ^ 2 / Real.log |t| < |t * Real.log n / (2 * π) - j| := by
  classical
  obtain ⟨E₀, hE₀⟩ := eventually_exists_prime_set
  set C : ℝ := 41472 + 512 * (E₀ : ℝ) ^ 2 with hC
  have hCpos : 0 < C := by positivity
  have hev1 : ∀ᶠ L : ℝ in atTop, 12 ≤ Real.log L :=
    Real.tendsto_log_atTop.eventually_ge_atTop 12
  have hev2 : ∀ᶠ L : ℝ in atTop, C * Real.log L ^ 3 ≤ L := by
    have h1 := (isLittleO_pow_log_id_atTop (n := 3)).bound
      (show (0 : ℝ) < 1 / C by positivity)
    filter_upwards [h1, hev1, eventually_gt_atTop (0 : ℝ)] with L hL h12 hLpos
    simp only [id, norm_eq_abs] at hL
    rw [abs_of_pos (by positivity : 0 < Real.log L ^ 3), abs_of_pos hLpos] at hL
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hCpos] at hL
    linarith
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hev1.and (hev2.and (eventually_ge_atTop (144 : ℝ))))
  refine ⟨Real.exp L₀, Real.exp_pos _, fun t ht => ?_⟩
  have htpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hLge : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht
  obtain ⟨hℓ12, hLC, hL144⟩ := hL₀ _ hLge
  have hexpL : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize hL : Real.log |t| = L at hℓ12 hLC hL144 hexpL ⊢
  generalize hℓ : Real.log L = ℓ at hℓ12 hLC ⊢
  have hℓpos : 0 < ℓ := by linarith
  have hLpos : 0 < L := by linarith
  obtain ⟨M, E, k, hP⟩ := exists_wordParameters hℓ12 hLC
  obtain ⟨hword, S, hS, hSE, hSM, hsum⟩ := word_and_primes hP hE₀ hℓ12 hL144 hℓ.symm
  have hlogm : Real.log ((M + 1 : ℕ) : ℝ) ≤ ℓ := by
    rw [← hℓ]
    refine Real.log_le_log (by positivity) ?_
    have := hP.M_add_two_le hℓ12 hL144
    push_cast
    linarith
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = 12 * (M + 1) ^ (E + 2) + E ^ 2 + 24 * (E + 1) + 2 * (M + 1) + 1 :=
    ⟨_, rfl⟩
  have hlogx₀ : Real.log (x₀ : ℝ) ≤ ((E : ℝ) + 8) * ℓ :=
    log_x₀_le hP.one_le_M hP.E_le_M (by have := hP.eight_le; omega) hx₀ hlogm
  have hx₀pos : (0 : ℝ) < (x₀ : ℝ) := by
    have : 0 < x₀ := by omega
    exact_mod_cast this
  have ht0 : 3 * π * (x₀ : ℝ) ^ E ≤ |t| := by
    rw [← hexpL]
    exact three_pi_mul_pow_le hP hℓ12 hL144 hlogx₀ hx₀pos
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = L / ((k : ℝ) + 1) + ((E : ℝ) + 10) * ℓ := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ = ⌈Real.exp Y⌉₊ := ⟨_, rfl⟩
  have hx₂ge : Real.exp Y ≤ (x₂ : ℝ) := by
    rw [hx₂]
    exact Nat.le_ceil _
  have hYpos : ((E : ℝ) + 10) * ℓ ≤ Y := by
    have : 0 ≤ L / ((k : ℝ) + 1) := by positivity
    rw [hY]
    linarith
  have hYℓ : ℓ ≤ Y := by
    have hEnn : (0 : ℝ) ≤ (E : ℝ) := by positivity
    have h1 : ℓ ≤ ((E : ℝ) + 10) * ℓ := le_mul_of_one_le_left hℓpos.le (by linarith)
    linarith
  have h12 : x₀ ≤ x₂ := by
    have h1 : (x₀ : ℝ) ≤ (x₂ : ℝ) := by
      refine le_trans ?_ hx₂ge
      rw [← Real.exp_log hx₀pos]
      refine Real.exp_le_exp.mpr (hlogx₀.trans (le_trans ?_ hYpos))
      exact mul_le_mul_of_nonneg_right (by linarith) hℓpos.le
    exact Nat.cast_le.mp h1
  have ht2 : |t| * ((M + 1 : ℕ) : ℝ) ^ (k + 2) ≤ (x₂ : ℝ) ^ (k + 1) := by
    rw [← hexpL]
    exact exp_mul_pow_le hℓpos hlogm (by rw [← hY]; exact hx₂ge)
  have hε := precision_lt hP hℓ12 hL144
  obtain ⟨n, hn1, hn2, hn3⟩ :=
    exists_not_aligned (x₀ := x₀) (x₂ := x₂) hword S hS hSE hSM hsum hx₀ ht0 h12 ht2 hε
  have hn1' : 1 ≤ n := by
    have : 1 ≤ x₀ := by omega
    omega
  refine ⟨n, hn1', ?_, hn3⟩
  have hYexp1 : (1 : ℝ) ≤ Real.exp Y := Real.one_le_exp (by linarith)
  have hMexp : (M : ℝ) ≤ Real.exp Y := by
    have h1 : L ≤ Real.exp Y := by
      rw [← Real.exp_log hLpos, hℓ]
      exact Real.exp_le_exp.mpr hYℓ
    have := hP.M_add_two_le hℓ12 hL144
    linarith
  have hnle : (n : ℝ) ≤ 3 * Real.exp Y := by
    have h1 : (n : ℝ) ≤ (x₂ : ℝ) + (M : ℝ) := by exact_mod_cast hn2
    have h2 : (x₂ : ℝ) < Real.exp Y + 1 := by
      rw [hx₂]
      exact Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1'
  have hlogn : Real.log (n : ℝ) ≤ Y + 2 := by
    have h1 : Real.log (n : ℝ) ≤ Real.log (3 * Real.exp Y) := Real.log_le_log hnpos hnle
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith
  have hlen := length_le hP hℓ12 hL144
  rw [← hY] at hlen
  exact hlogn.trans hlen

end

end GaloisForLFunctions.PrimeTorusTheory
