import GaloisForLFunctions.PrimeTorusTheory.TheMisalignmentBand

/-!
# The mass of misaligned primes

The phase of `n` is the sum over the prime factors of `n`, so the mean distance over `n < N` is carried by the primes with weight `1/p`.
With `L = log |t|` and `ℓ = log L`, for every `N ≥ 48 L² ℓ`,

`Σ_{p < N} ‖t log p/2π‖/p ≥ 1/(10⁵ L⁴ ℓ²)` (`le_sum_primes_phaseDist`).

Hence the critical column sum has the saving

`Σ_{p < N} p^{-1/2} (1 − cos(t log p)) ≥ 4·10⁻¹⁰/(L⁸ ℓ⁴)` (`le_sum_primes_critical`),

a power of `log |t|` at length `L² ℓ`. The same holds at the corner `−1` by doubling the height (`le_sum_primes_liouville`).
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The distance of a phase is subadditive over the prime factors. -/
theorem phaseDist_le_factorization (t : ℝ) (n : ℕ) :
    phaseDist t n ≤ ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * phaseDist t p := by
  have hlog : t * Real.log n / (2 * π) =
      ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * (t * Real.log p / (2 * π)) := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, Finset.mul_sum,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  set J : ℤ := ∑ p ∈ n.primeFactors, (n.factorization p : ℤ) * round (t * Real.log p / (2 * π))
    with hJ
  unfold phaseDist
  refine (dist01_le_abs_sub_int _ J).trans ?_
  have e : t * Real.log n / (2 * π) - J = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
      (t * Real.log p / (2 * π) - round (t * Real.log p / (2 * π))) := by
    rw [hlog, hJ]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  rfl

theorem sum_factorization_range (p N : ℕ) :
    ∑ n ∈ range (N + 1), n.factorization p = (N.factorial).factorization p := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      Nat.factorization_mul (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
    simp only [Finsupp.add_apply]
    ring

/-- Legendre: the total valuation of `n < N` at `p` is at most `2N/p`. -/
theorem sum_factorization_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ n ∈ range N, (n.factorization p : ℝ) ≤ 2 * (N : ℝ) / p := by
  rcases N with _ | N
  · simp
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ∑ n ∈ range (N + 1), (n.factorization p : ℝ) = ((N.factorial).factorization p : ℝ) := by
    rw [← sum_factorization_range]
    push_cast
    rfl
  rw [h1, Nat.factorization_def _ hp]
  have h2 := sub_one_mul_padicValNat_factorial (p := p) N
  have h3 : (p - 1) * padicValNat p N.factorial ≤ N := by
    rw [h2]
    exact Nat.sub_le _ _
  have hp2 : 2 ≤ p := hp.two_le
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have h4 : ((p : ℝ) - 1) * (padicValNat p N.factorial : ℝ) ≤ N := by
    have : (((p - 1) * padicValNat p N.factorial : ℕ) : ℝ) ≤ N := by exact_mod_cast h3
    rw [Nat.cast_mul, Nat.cast_sub hp.one_le] at this
    simpa using this
  have hv : (0 : ℝ) ≤ padicValNat p N.factorial := Nat.cast_nonneg _
  rw [le_div_iff₀ (by linarith)]
  push_cast
  nlinarith

/-- The mean of the distance over integers is carried by the primes with weight `1/p`. -/
theorem sum_phaseDist_le_primes (t : ℝ) (N : ℕ) :
    ∑ n ∈ range N, phaseDist t n ≤
      2 * (N : ℝ) * ∑ p ∈ N.primesBelow, phaseDist t p / p := by
  classical
  have hstep : ∀ n ∈ range N, phaseDist t n ≤
      ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p := by
    intro n hn
    refine (phaseDist_le_factorization t n).trans (le_of_eq ?_)
    refine Finset.sum_subset (fun p hp => ?_) fun p _ hp => ?_
    · rw [Nat.mem_primesBelow]
      have hp' := Nat.mem_primeFactors.mp hp
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1)
        (Finset.mem_range.mp hn), hp'.1⟩
    · have : n.factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp
      rw [this]
      simp
  calc ∑ n ∈ range N, phaseDist t n ≤
        ∑ n ∈ range N, ∑ p ∈ N.primesBelow, (n.factorization p : ℝ) * phaseDist t p :=
        Finset.sum_le_sum hstep
    _ = ∑ p ∈ N.primesBelow, (∑ n ∈ range N, (n.factorization p : ℝ)) * phaseDist t p := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ p ∈ N.primesBelow, (2 * (N : ℝ) / p) * phaseDist t p := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact mul_le_mul_of_nonneg_right
          (sum_factorization_le (Nat.mem_primesBelow.mp hp).2 N) (phaseDist_nonneg t p)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

/-- **The mass of misaligned primes**, for a word of height `H`. -/
theorem WordSetup.one_div_le_sum_primes {H R : ℝ} {M k N₁ N : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : WordSetup H R M k N₁ c t) (hN : 6 * M + 6 ≤ N) :
    1 / (96 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) ≤ ∑ p ∈ N.primesBelow, phaseDist t p / p := by
  have hmean := S.le_sum_phaseDist hN
  have hprimes := sum_phaseDist_le_primes t N
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have e : (N : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) =
      2 * (N : ℝ) * (1 / (96 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
    field_simp
    norm_num
  have hcomb := hmean.trans hprimes
  rw [e] at hcomb
  exact le_of_mul_le_mul_left hcomb (by positivity)

/-- **The mass of misaligned primes.** With `L = log |t|` and `ℓ = log L`, for every `N ≥ 48 L² ℓ`, the primes below `N` have
`Σ ‖t log p/2π‖/p ≥ 1/(10⁵ L⁴ ℓ²)`. -/
theorem le_sum_primes_phaseDist :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      1 / (100000 * Real.log |t| ^ 4 * Real.log (Real.log |t|) ^ 2) ≤
        ∑ p ∈ N.primesBelow, phaseDist t p / p := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize Real.log L = ℓ at h hN ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  obtain ⟨M, k, N₁, c, hS, hNnat, hsq⟩ := h.exists_data hexp hN
  refine le_trans ?_ (hS.one_div_le_sum_primes hNnat)
  refine one_div_le_one_div_of_le (by positivity) ?_
  have hpos : 0 < L ^ 4 * ℓ ^ 2 := by positivity
  norm_num
  nlinarith

/-- The chord of the cosine: `1 − cos(2πθ) ≥ 8 ‖θ‖²`. -/
theorem eight_mul_sq_le_one_sub_cos (θ : ℝ) : 8 * dist01 θ ^ 2 ≤ 1 - Real.cos (2 * π * θ) := by
  set x : ℝ := θ - round θ with hx
  have hxabs : |x| ≤ 1 / 2 := abs_sub_round θ
  have hcos : Real.cos (2 * π * θ) = Real.cos (2 * (π * |x|)) := by
    have e : 2 * π * θ = 2 * π * x + (round θ : ℤ) * (2 * π) := by
      rw [hx]
      ring
    rw [e, Real.cos_add_int_mul_two_pi]
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      ring_nf
    · rw [h, ← Real.cos_neg]
      ring_nf
  have hπ := Real.pi_pos
  have h0 : 0 ≤ π * |x| := by positivity
  have h1 : π * |x| ≤ π / 2 := by nlinarith
  have hsin : 2 / π * (π * |x|) ≤ Real.sin (π * |x|) := Real.mul_le_sin h0 h1
  have e2 : 2 / π * (π * |x|) = 2 * |x| := by
    field_simp
  rw [e2] at hsin
  rw [hcos, Real.cos_two_mul]
  have hs := Real.sin_sq_add_cos_sq (π * |x|)
  have hsq : (2 * |x|) ^ 2 ≤ Real.sin (π * |x|) ^ 2 := pow_le_pow_left₀ (by positivity) hsin 2
  have hd : dist01 θ = |x| := rfl
  rw [hd]
  nlinarith

/-- `Σ_{n ≥ 2} n^{-3/2} ≤ 2`, in the form of a telescoping bound. -/
theorem sum_inv_mul_sqrt_le (N : ℕ) :
    ∑ n ∈ range N, 1 / (((n + 2 : ℕ) : ℝ) * √((n + 2 : ℕ) : ℝ)) ≤ 2 * (1 - 1 / √((N + 1 : ℕ) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    set a : ℝ := √((N + 1 : ℕ) : ℝ) with ha
    set b : ℝ := √((N + 2 : ℕ) : ℝ) with hb
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hbpos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a * a = (N : ℝ) + 1 := by
      rw [ha, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    have hb2 : b * b = (N : ℝ) + 2 := by
      rw [hb, Real.mul_self_sqrt (by positivity)]
      push_cast
      ring
    have hb2' : (((N + 2 : ℕ) : ℝ)) = b * b := by
      rw [hb2]
      push_cast
      ring
    have hab : a ≤ b := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      linarith
    rw [show N + 1 + 1 = N + 2 by ring]
    have hterm : 1 / (((N + 2 : ℕ) : ℝ) * b) ≤ 2 * (1 / a - 1 / b) := by
      rw [hb2']
      have h1 : b * b - a * a = 1 := by rw [ha2, hb2]; ring
      have e : 1 / a - 1 / b = (b - a) / (a * b) := by
        field_simp
      have h2 : b - a = 1 / (a + b) := by
        field_simp
        nlinarith
      rw [e, h2, div_div]
      rw [mul_div_assoc', mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : 0 ≤ (b - a) := by linarith
      have h4 : a * b * (a + b) ≤ 2 * (b * b * b) := by nlinarith [mul_pos hapos hbpos]
      nlinarith
    linarith

/-- `Σ_{p < N} p^{-3/2} ≤ 2`. -/
theorem sum_primes_inv_mul_sqrt_le (N : ℕ) :
    ∑ p ∈ N.primesBelow, 1 / ((p : ℝ) * √(p : ℝ)) ≤ 2 := by
  classical
  have hsub : N.primesBelow ⊆ (range N).image (fun n : ℕ => n + 2) := by
    intro p hp
    have h := Nat.mem_primesBelow.mp hp
    refine Finset.mem_image.mpr ⟨p - 2, Finset.mem_range.mpr ?_, ?_⟩
    · have := h.2.two_le
      omega
    · have := h.2.two_le
      omega
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) * √(n : ℝ)) := fun n => by positivity
  have h1 : ∑ p ∈ N.primesBelow, 1 / ((p : ℝ) * √(p : ℝ)) ≤
      ∑ p ∈ (range N).image (fun n : ℕ => n + 2), 1 / ((p : ℝ) * √(p : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p
  rw [Finset.sum_image (fun a _ b _ h => by omega)] at h1
  have h2 := sum_inv_mul_sqrt_le N
  have h3 : (0 : ℝ) ≤ 1 / √((N + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- The critical column sum is at least four times the square of the mass. -/
theorem four_mul_sq_le_critical (t : ℝ) (N : ℕ) :
    4 * (∑ p ∈ N.primesBelow, phaseDist t p / p) ^ 2 ≤
      ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  set P : ℝ := ∑ p ∈ N.primesBelow, phaseDist t p / p with hP
  set D : ℝ := ∑ p ∈ N.primesBelow, phaseDist t p ^ 2 / √(p : ℝ) with hD
  have hp2 : ∀ p ∈ N.primesBelow, (0 : ℝ) < √(p : ℝ) := fun p hp =>
    Real.sqrt_pos.mpr (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos)
  have hcauchy : P ^ 2 ≤ D * ∑ p ∈ N.primesBelow, 1 / ((p : ℝ) * √(p : ℝ)) := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => by positivity)
      (fun p _ => by positivity) fun p hp => le_of_eq ?_
    have hs := hp2 p hp
    have hss : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
    have hpp : (0 : ℝ) < p := by
      rw [← hss]
      positivity
    field_simp
    nlinarith
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun p _ => by positivity
  have hP2 : P ^ 2 ≤ 2 * D := by
    refine hcauchy.trans ?_
    calc _ ≤ D * 2 := mul_le_mul_of_nonneg_left (sum_primes_inv_mul_sqrt_le N) hDnn
      _ = _ := by ring
  have hcol : 8 * D ≤ ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log p / (2 * π))
    have e : 2 * π * (t * Real.log p / (2 * π)) = t * Real.log p := by
      field_simp
    rw [e] at h1
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 (hp2 p hp).le
  linarith

/-- **The critical column sum has a saving polynomial in `log |t|`.** For every `N ≥ 48 L² ℓ`,
`Σ_{p<N} (1 − cos(t log p))/√p ≥ 4·10⁻¹⁰/(L⁸ ℓ⁴)`. -/
theorem le_sum_primes_critical :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ,
      48 * Real.log |t| ^ 2 * Real.log (Real.log |t|) ≤ N →
      4 / 10 ^ 10 / (Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4) ≤
        ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨T₀, hT₀, hmass⟩ := le_sum_primes_phaseDist
  obtain ⟨T₁, hT₁, hsize⟩ := eventually_heightSize
  refine ⟨max T₀ T₁, lt_of_lt_of_le hT₀ (le_max_left _ _), fun t ht N hN => ?_⟩
  have hm := hmass t ((le_max_left _ _).trans ht) N hN
  have h := hsize t ((le_max_right _ _).trans ht)
  have hcol := four_mul_sq_le_critical t N
  set P : ℝ := ∑ p ∈ N.primesBelow, phaseDist t p / p with hP
  generalize Real.log |t| = L at h hm ⊢
  generalize Real.log L = ℓ at h hm ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hpos : 0 < 1 / (100000 * L ^ 4 * ℓ ^ 2) := by positivity
  have hsq := pow_le_pow_left₀ hpos.le hm 2
  have e : (1 / (100000 * L ^ 4 * ℓ ^ 2)) ^ 2 = 1 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4) := by
    field_simp
    norm_num
  rw [e] at hsq
  have e2 : 4 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4) = 4 * (1 / 10 ^ 10 / (L ^ 8 * ℓ ^ 4)) := by ring
  rw [e2]
  linarith

/-- **The corner `−1`.** Doubling the height sends `−1` to `+1`, so with `L = log(2|t|)` and `ℓ = log L`, for every `N ≥ 48 L² ℓ`,
`Σ_{p<N} (1 + cos(t log p))/√p ≥ 10⁻¹⁰/(L⁸ ℓ⁴)`. -/
theorem le_sum_primes_liouville :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ 2 * |t| → ∀ N : ℕ,
      48 * Real.log (2 * |t|) ^ 2 * Real.log (Real.log (2 * |t|)) ≤ N →
      1 / 10 ^ 10 / (Real.log (2 * |t|) ^ 8 * Real.log (Real.log (2 * |t|)) ^ 4) ≤
        ∑ p ∈ N.primesBelow, (1 + Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨T₀, hT₀, h⟩ := le_sum_primes_critical
  refine ⟨T₀, hT₀, fun t ht N hN => ?_⟩
  have habs : |2 * t| = 2 * |t| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h2 := h (2 * t) (by rw [habs]; exact ht) N (by rw [habs]; exact hN)
  rw [habs] at h2
  have hstep : ∑ p ∈ N.primesBelow, (1 - Real.cos (2 * t * Real.log p)) / √(p : ℝ) ≤
      4 * ∑ p ∈ N.primesBelow, (1 + Real.cos (t * Real.log p)) / √(p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have e : 2 * t * Real.log p = 2 * (t * Real.log p) := by ring
    rw [e, Real.cos_two_mul]
    have h1 := Real.cos_sq_le_one (t * Real.log p)
    have h3 := Real.neg_one_le_cos (t * Real.log p)
    have h4 := Real.cos_le_one (t * Real.log p)
    nlinarith
  have e : 4 / 10 ^ 10 / (Real.log (2 * |t|) ^ 8 * Real.log (Real.log (2 * |t|)) ^ 4) =
      4 * (1 / 10 ^ 10 / (Real.log (2 * |t|) ^ 8 * Real.log (Real.log (2 * |t|)) ^ 4)) := by ring
  rw [e] at h2
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
