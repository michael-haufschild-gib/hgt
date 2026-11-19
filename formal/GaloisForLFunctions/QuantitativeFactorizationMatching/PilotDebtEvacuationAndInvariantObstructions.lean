import GaloisForLFunctions.QuantitativeFactorizationMatching.FactorizationInvolutionAndDoubleUseBookkeeping
import GaloisForLFunctions.QuantitativeFactorizationMatching.DyadicMatchingStripAndRiemannEquivalence
import GaloisForLFunctions.RHTower.MobiusPrimeSemiprimeCellMatching
import GaloisForLFunctions.RHTower.Sieve.GhsOuterBlock

/-!
# Cross-Fibre Evacuation of Deficient Fibres, Persistence Invariants, and Factorization Selectivity

Complete structural and quantitative analysis of cross-fibre `(1 ↔ 2)` involutions on `(X, 2X]`
versus larger invariants that force ordered-cofactor debt to persist:

1. **Unique integer factorization decoding (`maxPrimeStem`) and norm-collision selectivity**:
   Deleting the largest prime factor (`maxPrimeStem`) vs. the two largest prime factors
   (`maxPrimeStem ∘ maxPrimeStem`) injectively decodes `(c, p)` and `(c, q * r)` across all odd-`ω`
   cofactors simultaneously, whereas norm collisions in generalized integer systems break
   cofactor-fibre injectivity.
2. **Cube-root supply and 100% cross-fibre involution evacuation (`rankedCrossFibreInvolution`,
   `eventually_emptyFibres_evacuated_by_involution`)**: Pairing primes and cube-root semiprimes by
   rank across all negative-Möbius cofactors yields an explicit `FactorizationInvolution` on
   `(X, 2X]` that covers **every** negative vertex in an empty-positive ordered cofactor fibre.
3. **Exact `Θ(X / (log X)³)` pilot class and strict global unmatched reduction
   (`eventually_pilotFibreClass_debt_and_strict_drop`)**: The triprime pilot class carries
   `Θ(X / (log X)³)` unmatched vertices under every ordered-cofactor involution, is 100% evacuated
   by `rankedCrossFibreInvolution`, and via `{2, 3, 5}` root-clearing strictly lowers global
   `#unmatchedSet` below **any** ordered-cofactor involution by at least `2 * #(pilotVertices X)`.
4. **Sharp persistence invariants (`fibreUnion_ordered_and_global_bounds`,
   `eventually_roughFibreClass_debt_persists`, `pilotVertices_neighbor_cofactor_sq_lt`)**:
   - Exact ordered-cofactor attainment `∑_{a ∈ A} |#fibrePos - #fibreNeg|` vs. global lower bound
     `|∑_{a ∈ A} (#fibrePos - #fibreNeg)|`;
   - On the cube-root rough fibre class `roughFibreCofactors X`, both positive and negative vertex
     populations have order `≥ c X / (log X)³`, yet `10 * #fibrePos ≤ 9 * #fibreNeg` forces
     `≥ c_pers X / (log X)³` unmatched vertices under every involution confined to that class;
   - Every `GlobalDyadicOneTwoRel` neighbor `m` of `pilotVertices X` satisfies
     `(evenPrefixCofactor m)² < X`, isolating 100% of the pilot debt on any fibre class with
     `a² ≥ X`.
-/

open Finset Topology
open Filter (Tendsto atTop eventually_atTop eventually_ge_atTop tendsto_pow_atTop)
open _root_.RHTower _root_.RHTower.PrimeCells _root_.RHTower.BeurlingDeletion
open _root_.RHTower.Sieve (mertensBlockGapConst mertensFirst_general_block mertensFirst_lower mertensFirst_upper)
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open scoped Classical BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Unique prime factorization decoding (`maxPrimeStem`) and selectivity -/

/-- Cofactor obtained by dividing `n` by its largest prime factor (`0` at `0` and `1`). -/
def maxPrimeStem (n : ℕ) : ℕ :=
  n / n.primeFactors.sup id

theorem maxPrimeStem_mul_prime {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) :
    maxPrimeStem (c * p) = c := by
  have hcp : c * p ≠ 0 := Nat.mul_ne_zero hc hp.ne_zero
  have hmem : p ∈ (c * p).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_left p c, hcp⟩
  have hsup : (c * p).primeFactors.sup id = p := by
    refine le_antisymm (Finset.sup_le fun d hd => ?_) (le_sup (f := id) hmem)
    obtain ⟨hdp, hdvd, _⟩ := Nat.mem_primeFactors.mp hd
    rcases hdp.dvd_mul.mp hdvd with hdc | hdp'
    · exact (htop d (Nat.mem_primeFactors.mpr ⟨hdp, hdc, hc⟩)).le
    · exact Nat.le_of_dvd hp.pos hdp'
  simp only [maxPrimeStem, hsup, Nat.mul_div_cancel _ hp.pos]

theorem primeFactors_lt_of_mul_prime {c q r : ℕ} (hc : c ≠ 0) (hq : q.Prime) (hqr : q < r)
    (htop : ∀ d ∈ c.primeFactors, d < q) :
    ∀ d ∈ (c * q).primeFactors, d < r := by
  intro d hd
  obtain ⟨hdp, hdvd, _⟩ := Nat.mem_primeFactors.mp hd
  rcases hdp.dvd_mul.mp hdvd with hdc | hdq
  · exact (htop d (Nat.mem_primeFactors.mpr ⟨hdp, hdc, hc⟩)).trans hqr
  · exact (Nat.le_of_dvd hq.pos hdq).trans_lt hqr

theorem maxPrimeStem_mul_pair {c q r : ℕ} (hc : c ≠ 0) (hq : q.Prime) (hr : r.Prime)
    (hqr : q < r) (htop : ∀ d ∈ c.primeFactors, d < q) :
    maxPrimeStem (c * (q * r)) = c * q ∧
      maxPrimeStem (maxPrimeStem (c * (q * r))) = c := by
  have hcq : c * q ≠ 0 := Nat.mul_ne_zero hc hq.ne_zero
  have h1 : maxPrimeStem (c * (q * r)) = c * q := by
    rw [← mul_assoc]
    exact maxPrimeStem_mul_prime hcq hr (primeFactors_lt_of_mul_prime hc hq hqr htop)
  exact ⟨h1, h1.symm ▸ maxPrimeStem_mul_prime hc hq htop⟩

theorem moebius_mul_larger_prime {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) :
    μ (c * p) = -μ c := by
  have hndvd : ¬ p ∣ c := fun hd => (htop p (Nat.mem_primeFactors.mpr ⟨hp, hd, hc⟩)).false
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    ((hp.coprime_iff_not_dvd.mpr hndvd).symm),
    ArithmeticFunction.moebius_apply_prime hp, mul_neg_one]

theorem card_primeFactors_mul_larger_prime {c p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (htop : ∀ d ∈ c.primeFactors, d < p) :
    (c * p).primeFactors.card = c.primeFactors.card + 1 := by
  have hnot : p ∉ c.primeFactors := fun hm => (htop p hm).false
  rw [Nat.primeFactors_mul hc hp.ne_zero, hp.primeFactors, union_comm, singleton_union,
    card_insert_of_notMem hnot]

theorem evenPrefixCofactor_eq_maxPrimeStem_of_neg {n : ℕ} (hμ : μ n = -1) :
    evenPrefixCofactor n = maxPrimeStem n := by
  have hsq : Squarefree n := squarefree_iff_moebius_ne_zero.mpr (by omega)
  have hnot_even : ¬ Even n.primeFactors.card := by
    intro he
    rw [moebius_eq_neg_one_pow_omega hsq, he.neg_one_pow] at hμ
    omega
  have hne : n.primeFactors.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty.mp hemp, card_empty] at hnot_even
    exact hnot_even ⟨0, rfl⟩
  have hsup : n.primeFactors.sup id = n.primeFactors.max' hne :=
    le_antisymm (Finset.sup_le fun d hd => le_max' _ d hd) (le_sup (f := id) (max'_mem _ hne))
  simp only [evenPrefixCofactor, dif_pos hne, if_neg hnot_even, maxPrimeStem, hsup]

/-- **Unique integer factorization selectivity**: across all nonzero cofactors, appending one
strictly larger prime `c * p` or two strictly larger primes `c * (q * r)` (`q < r`) uniquely
determines both the cofactor `c` and the appended prime(s), whereas in any integer-norm Beurling
system with two distinct elements sharing the same integer norm, no integer-norm decoder can
injectively recover the generalized integer. -/
theorem unique_factorization_decoding_and_norm_selectivity :
    (∀ {c₁ c₂ p₁ p₂ : ℕ}, c₁ ≠ 0 → c₂ ≠ 0 → p₁.Prime → p₂.Prime →
      (∀ d ∈ c₁.primeFactors, d < p₁) → (∀ d ∈ c₂.primeFactors, d < p₂) →
      c₁ * p₁ = c₂ * p₂ → c₁ = c₂ ∧ p₁ = p₂) ∧
    (∀ {c₁ c₂ q₁ r₁ q₂ r₂ : ℕ}, c₁ ≠ 0 → c₂ ≠ 0 →
      q₁.Prime → r₁.Prime → q₂.Prime → r₂.Prime → q₁ < r₁ → q₂ < r₂ →
      (∀ d ∈ c₁.primeFactors, d < q₁) → (∀ d ∈ c₂.primeFactors, d < q₂) →
      c₁ * (q₁ * r₁) = c₂ * (q₂ * r₂) → c₁ = c₂ ∧ q₁ = q₂ ∧ r₁ = r₂) ∧
    (∀ (B : _root_.RHTower.BeurlingSystem) (hInt : HasIntegerNorms B)
      {g₁ g₂ : B.Integer}, g₁ ≠ g₂ → natIntNorm hInt g₁ = natIntNorm hInt g₂ →
      ¬ ∃ decode : ℕ → B.Integer,
        decode (natIntNorm hInt g₁) = g₁ ∧ decode (natIntNorm hInt g₂) = g₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c₁ c₂ p₁ p₂ hc₁ hc₂ hp₁ hp₂ ht₁ ht₂ heq
    have hc_eq : c₁ = c₂ := by
      have h := congrArg maxPrimeStem heq
      rwa [maxPrimeStem_mul_prime hc₁ hp₁ ht₁, maxPrimeStem_mul_prime hc₂ hp₂ ht₂] at h
    subst hc_eq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc₁) heq⟩
  · intro c₁ c₂ q₁ r₁ q₂ r₂ hc₁ hc₂ hq₁ hr₁ hq₂ hr₂ hqr₁ hqr₂ ht₁ ht₂ heq
    obtain ⟨hs₁, hss₁⟩ := maxPrimeStem_mul_pair hc₁ hq₁ hr₁ hqr₁ ht₁
    obtain ⟨hs₂, hss₂⟩ := maxPrimeStem_mul_pair hc₂ hq₂ hr₂ hqr₂ ht₂
    have hc_eq : c₁ = c₂ := by
      have h := congrArg (fun n => maxPrimeStem (maxPrimeStem n)) heq
      rwa [hss₁, hss₂] at h
    subst hc_eq
    have hcq_eq : c₁ * q₁ = c₁ * q₂ := by
      have h := congrArg maxPrimeStem heq
      rwa [hs₁, hs₂] at h
    have hq_eq : q₁ = q₂ := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc₁) hcq_eq
    subst hq_eq
    have hqr_eq : q₁ * r₁ = q₁ * r₂ :=
      Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc₁) heq
    exact ⟨rfl, rfl, Nat.eq_of_mul_eq_mul_left hq₁.pos hqr_eq⟩
  · rintro B hInt g₁ g₂ hne hnorm ⟨decode, hd₁, hd₂⟩
    rw [hnorm] at hd₁
    exact hne (hd₁.symm.trans hd₂)

/-! ### 2. Cube-root semiprime supply and 100% cross-fibre involution evacuation -/

/-- Semiprime products `q * r ∈ (u, v]` whose smaller factor lies in `(s² / 2, 2 s³]`. -/
def cubeBandProducts (s u v : ℝ) : Finset ℕ :=
  (windowPrimes (s ^ 2 / 2) (2 * s ^ 3)).biUnion fun q =>
    (windowPrimes (u / q) (v / q)).image (q * ·)

theorem windowPrimes_eq_primesLE_sdiff_nat (u v : ℝ) :
    windowPrimes u v = Nat.primesLE ⌊v⌋₊ \ Nat.primesLE ⌊u⌋₊ := by
  ext q
  simp only [windowPrimes, mem_sdiff, Nat.mem_primesLE, mem_filter, mem_Ioc]
  exact ⟨fun ⟨⟨hlo, hhi⟩, hp⟩ => ⟨⟨hhi, hp⟩, fun h => hlo.not_ge h.1⟩,
    fun ⟨⟨hhi, hp⟩, hn⟩ => ⟨⟨lt_of_not_ge fun h => hn ⟨h, hp⟩, hhi⟩, hp⟩⟩

/-- **Mertens' first theorem lower bound on a block**:
`log B - log A - mertensBlockGapConst ≤ ∑_{A < p ≤ B} log p / p`. -/
theorem mertensFirst_general_block_ge {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log B - Real.log A - mertensBlockGapConst ≤
      ∑ p ∈ Nat.primesLE B \ Nat.primesLE A, Real.log (p : ℝ) / (p : ℝ) := by
  have hB : 1 ≤ B := hA.trans hAB
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hAB, (Nat.mem_primesLE.mp hp).2⟩
  have hlow := mertensFirst_lower hB
  have hup := mertensFirst_upper hA
  rw [Finset.sum_sdiff_eq_sub hsub, mertensBlockGapConst]
  linarith

private theorem cubeBand_mertens_le {s : ℝ} (hs : 2 ≤ s)
    (hL : 20 * (Real.log 2 + Real.log 4 + mertensBlockGapConst) ≤ Real.log s) :
    ∑ q ∈ windowPrimes (s ^ 2 / 2) (2 * s ^ 3), Real.log q / q ≤ 21 / 20 * Real.log s := by
  have hs0 : 0 < s := by linarith only [hs]
  have ha : 2 ≤ s ^ 2 / 2 := by nlinarith only [hs, sq_nonneg (s - 2)]
  have hab : s ^ 2 / 2 ≤ 2 * s ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_right hs (sq_nonneg s), sq_nonneg s]
  have haN : 1 ≤ ⌊s ^ 2 / 2⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith only [ha])
  have hA : s ^ 2 / 4 ≤ (⌊s ^ 2 / 2⌋₊ : ℝ) := by
    linarith only [Nat.lt_floor_add_one (s ^ 2 / 2), ha]
  have hB := Nat.floor_le (show 0 ≤ 2 * s ^ 3 by positivity)
  have hBn : 0 < (⌊2 * s ^ 3⌋₊ : ℝ) :=
    by exact_mod_cast lt_of_lt_of_le (Nat.zero_lt_of_lt haN) (Nat.floor_le_floor hab)
  have hu := Real.log_le_log hBn hB
  have hl := Real.log_le_log (show 0 < s ^ 2 / 4 by positivity) hA
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hu
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hl
  norm_num1 at hu hl
  rw [windowPrimes_eq_primesLE_sdiff_nat]
  linarith only [mertensFirst_general_block haN (Nat.floor_le_floor hab), hL, hu, hl]

private theorem cubeBand_log_prod_ge {s : ℝ} (hs : 2 ≤ s) (hL : 10 * Real.log 2 ≤ Real.log s)
    {q : ℕ} (hq : q ∈ windowPrimes (s ^ 2 / 2) (2 * s ^ 3)) :
    Real.log s ≤ Real.log (s ^ 6 / q) ∧
      15 / 2 * Real.log s ^ 2 ≤ Real.log q * Real.log (s ^ 6 / q) := by
  have hs0 : 0 < s := by linarith only [hs]
  obtain ⟨hp, hl, hu⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
  have hlo := Real.log_le_log (show 0 < s ^ 2 / 2 by positivity) hl.le
  have hup := Real.log_le_log hq0 hu
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlo
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hup
  rw [Real.log_div (by positivity) hq0.ne', Real.log_pow]
  norm_num1 at hlo hup ⊢
  have hlog := Real.log_nonneg (show 1 ≤ s by linarith only [hs])
  have h1 : 0 ≤ Real.log q - 19 / 10 * Real.log s := by linarith only [hlo, hL]
  have h2 : 0 ≤ 41 / 10 * Real.log s - Real.log q := by linarith only [hup, hL, hlog]
  exact ⟨by linarith only [hup, hL, hlog],
    by nlinarith only [mul_nonneg h1 h2, sq_nonneg (Real.log s)]⟩

/-- **Nine-tenths cube-root capacity bound**: on `(s⁶, 2 s⁶]`, all semiprimes with smaller prime
factor in `(s² / 2, 2 s³]` occupy at most `9 / 10` of the ordinary prime supply. -/
theorem eventually_cubeBandProducts_nine_tenths :
    ∀ᶠ s : ℝ in atTop,
      10 * (cubeBandProducts s (s ^ 6) (2 * s ^ 6)).card ≤
        9 * (windowPrimes (s ^ 6) (2 * s ^ 6)).card := by
  obtain ⟨A, _, hupper⟩ := exists_card_windowPrimes_le (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 100)
  obtain ⟨H, _, hlower⟩ := exists_card_windowPrimes_div_ge (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 100)
  filter_upwards [eventually_ge_atTop (max 2 (max A H)),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max (10 * Real.log 2) (20 * (Real.log 2 + Real.log 4 + mertensBlockGapConst)))] with s hs hL
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith only [hs2]
  have hs1 : 1 ≤ s := by linarith only [hs2]
  have hlog : 0 < Real.log s := Real.log_pos (by linarith only [hs2])
  have hA : A ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hH : H ≤ s := (le_max_right _ _).trans ((le_max_right _ _).trans hs)
  have hm := cubeBand_mertens_le hs2 ((le_max_right _ _).trans hL)
  have h10 := (le_max_left _ _).trans hL
  have hrow : ∀ q ∈ windowPrimes (s ^ 2 / 2) (2 * s ^ 3),
      ((windowPrimes (s ^ 6 / q) (2 * s ^ 6 / q)).card : ℝ) ≤
        ((101 / 100) * s ^ 6 / (15 / 2 * Real.log s ^ 2)) * (Real.log q / q) := by
    intro q hq
    obtain ⟨hp, _, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
    obtain ⟨hl, hprod⟩ := cubeBand_log_prod_ge hs2 h10 hq
    have hsR : s ≤ s ^ 6 / q := (Real.log_le_log_iff hs0 (by positivity)).mp hl
    have hl_pos : 0 < Real.log (s ^ 6 / q) := hlog.trans_le hl
    have hdiff : 2 * s ^ 6 / (q : ℝ) - s ^ 6 / q = s ^ 6 / q := by ring
    have h := hupper (s ^ 6 / q) (hA.trans hsR) (s ^ 6 / q) (2 * s ^ 6 / q)
      le_rfl (by gcongr; linarith [pow_nonneg hs0.le 6])
      (by rw [mul_div_assoc])
      (by rw [Real.rpow_zero, div_one, hdiff])
    rw [hdiff] at h
    refine h.trans ?_
    rw [mul_div_assoc', div_div, div_mul_div_comm,
      div_le_div_iff₀ (mul_pos hq0 hl_pos) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hprod (mul_nonneg (pow_nonneg hs0.le 6) hq0.le)]
  have hcnt : ((cubeBandProducts s (s ^ 6) (2 * s ^ 6)).card : ℝ) ≤
      ((101 / 100) * s ^ 6 / (15 / 2 * Real.log s ^ 2)) *
        ∑ q ∈ windowPrimes (s ^ 2 / 2) (2 * s ^ 3), Real.log q / q := by
    have hn : (cubeBandProducts s (s ^ 6) (2 * s ^ 6)).card ≤
        ∑ q ∈ windowPrimes (s ^ 2 / 2) (2 * s ^ 3),
          (windowPrimes (s ^ 6 / q) (2 * s ^ 6 / q)).card :=
      card_biUnion_le.trans (sum_le_sum fun q _ => card_image_le)
    refine (Nat.cast_le.mpr hn).trans ?_
    rw [Nat.cast_sum, mul_sum]
    exact sum_le_sum hrow
  have hprice : ((cubeBandProducts s (s ^ 6) (2 * s ^ 6)).card : ℝ) ≤
      s ^ 6 / (7 * Real.log s) := by
    refine hcnt.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans ?_)
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg (pow_nonneg hs0.le 6) (sq_nonneg (Real.log s))]
  have h6 : s ≤ s ^ 6 := by simpa only [pow_one] using pow_le_pow_right₀ hs1 (by decide : 1 ≤ 6)
  have hbig : Real.log (2 * s ^ 6) = Real.log 2 + 6 * Real.log s := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := hlower (2 * s ^ 6) (by linarith only [hH, h6, hs0]) 2 (by norm_num) (by norm_num)
    (2 * s ^ 6) (4 * s ^ 6) le_rfl (by linarith [pow_nonneg hs0.le 6]) (by linarith)
    (by rw [Real.rpow_zero, div_one]; linarith)
  have hdiv1 : (2 * s ^ 6) / 2 = s ^ 6 := by ring
  have hdiv2 : (4 * s ^ 6) / 2 = 2 * s ^ 6 := by ring
  rw [hdiv1, hdiv2] at hlow
  have hratio : 10 * (s ^ 6 / (7 * Real.log s)) ≤
      9 * ((1 - 1 / 100) * (4 * s ^ 6 - 2 * s ^ 6) / (2 * Real.log (2 * s ^ 6))) := by
    rw [← mul_div_assoc, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by rw [hbig]; positivity), hbig]
    nlinarith only [mul_le_mul_of_nonneg_right h10 (pow_nonneg hs0.le 6),
      mul_nonneg (pow_nonneg hs0.le 6) hlog.le]
  exact_mod_cast (mul_le_mul_of_nonneg_left hprice (by norm_num : (0 : ℝ) ≤ 10)).trans
    (hratio.trans (mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 9)))

/-- Primes in `((X : ℝ) / c, 2 * X / c]` exceeding every prime factor of `c`. -/
def cofactorPrimeRow (X c : ℕ) : Finset ℕ :=
  (windowPrimes ((X : ℝ) / c) (2 * (X : ℝ) / c)).filter fun p =>
    ∀ d ∈ c.primeFactors, d < p

/-- Cube-root semiprimes `q * r ∈ ((X : ℝ) / c, 2 * X / c]` (`q < r`) exceeding every prime factor
of `c`. -/
def cofactorCubeRow (X c : ℕ) : Finset ℕ :=
  (cubeBandProducts (((X : ℝ) / c) ^ (1 / 6 : ℝ)) ((X : ℝ) / c) (2 * (X : ℝ) / c)).filter fun w =>
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < r ∧ w = q * r ∧ ∀ d ∈ c.primeFactors, d < q

def finsetEntry (S : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < S.card then (S.orderIsoOfFin rfl ⟨i, hi⟩ : ℕ) else 0

theorem finsetEntry_mem {S : Finset ℕ} {i : ℕ} (hi : i < S.card) :
    finsetEntry S i ∈ S := by
  simpa only [finsetEntry, dif_pos hi] using (S.orderIsoOfFin rfl ⟨i, hi⟩).property

theorem finsetEntry_inj {S : Finset ℕ} {i j : ℕ} (hi : i < S.card) (hj : j < S.card)
    (heq : finsetEntry S i = finsetEntry S j) : i = j := by
  simp only [finsetEntry, dif_pos hi, dif_pos hj] at heq
  exact congrArg Fin.val ((S.orderIsoOfFin rfl).injective (Subtype.ext heq))

def finsetRank (S : Finset ℕ) (n : ℕ) : ℕ :=
  if hn : n ∈ S then ((S.orderIsoOfFin rfl).symm ⟨n, hn⟩).val else S.card

theorem finsetRank_entry {S : Finset ℕ} {i : ℕ} (hi : i < S.card) :
    finsetRank S (finsetEntry S i) = i := by
  rw [finsetRank, dif_pos (finsetEntry_mem hi)]
  simp only [finsetEntry, dif_pos hi]
  exact congrArg Fin.val ((S.orderIsoOfFin rfl).symm_apply_apply ⟨i, hi⟩)

/-- **Explicit simultaneous cross-fibre involution (`rankedCrossFibreInvolution`)**:
pairs the `i`-th prime of `cofactorPrimeRow X c` with the `i`-th cube-root semiprime of
`cofactorCubeRow X c` across all odd-`ω` squarefree cofactors `c ∈ [1, 2X]` simultaneously, using
`maxPrimeStem` unique factorization decoding so no endpoint is used twice across distinct `c`. -/
def rankedCrossFibreInvolution (X : ℕ) :
    FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)) := by
  let rowLen : ℕ → ℕ := fun c =>
    min (cofactorPrimeRow X c).card (cofactorCubeRow X c).card
  let addrs : Finset (ℕ × ℕ) :=
    ((Icc 1 (2 * X)).filter fun c => μ c = -1).biUnion fun c =>
      (range (rowLen c)).image fun i => (c, i)
  have hmem_addrs : ∀ {c i : ℕ},
      (c, i) ∈ addrs ↔ c ∈ Icc 1 (2 * X) ∧ μ c = -1 ∧ i < rowLen c := by
    intro c i
    simp [addrs, and_assoc]
  let fPos : ℕ × ℕ → ℕ := fun a => a.1 * finsetEntry (cofactorPrimeRow X a.1) a.2
  let fNeg : ℕ × ℕ → ℕ := fun a => a.1 * finsetEntry (cofactorCubeRow X a.1) a.2
  have hends : ∀ {c i : ℕ}, (c, i) ∈ addrs →
      fPos (c, i) ∈ posParity (Ioc X (2 * X)) ∧
      fNeg (c, i) ∈ negParity (Ioc X (2 * X)) ∧
      GlobalDyadicOneTwoRel (fPos (c, i)) (fNeg (c, i)) ∧
      maxPrimeStem (fPos (c, i)) = c ∧
      maxPrimeStem (maxPrimeStem (fNeg (c, i))) = c ∧
      (fNeg (c, i)).primeFactors.card = (fPos (c, i)).primeFactors.card + 1 := by
    intro c i ha
    obtain ⟨hcI, hcμ, hi⟩ := hmem_addrs.mp ha
    have hc_pos : 0 < c := (mem_Icc.mp hcI).1
    have hc_ne : c ≠ 0 := hc_pos.ne'
    have hc_r : (0 : ℝ) < c := by exact_mod_cast hc_pos
    have hp_mem := finsetEntry_mem (S := cofactorPrimeRow X c) (hi.trans_le (min_le_left _ _))
    have hw_mem := finsetEntry_mem (S := cofactorCubeRow X c) (hi.trans_le (min_le_right _ _))
    obtain ⟨hp_win, hp_top⟩ := mem_filter.mp hp_mem
    obtain ⟨hpp, hp_lo, hp_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp_win
    obtain ⟨hw_cube, q, r, hqp, hrp, hqr, hweq, hq_top⟩ := mem_filter.mp hw_mem
    obtain ⟨q₀, hq₀_win, hr₀_img⟩ := mem_biUnion.mp hw_cube
    obtain ⟨r₀, hr₀_win, hw_q₀r₀⟩ := mem_image.mp hr₀_img
    have hq₀_p : q₀.Prime := (mem_windowPrimes (by positivity) (by positivity)).mp hq₀_win |>.1
    have hq₀_r : (0 : ℝ) < q₀ := by exact_mod_cast hq₀_p.pos
    obtain ⟨_, hr₀_lo, hr₀_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr₀_win
    have hpos_Ioc : fPos (c, i) ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hc_r] at hp_lo
      rw [le_div_iff₀ hc_r] at hp_hi
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < (c * finsetEntry (cofactorPrimeRow X c) i : ℕ) by
          push_cast; linarith)
      · exact_mod_cast (show ((c * finsetEntry (cofactorPrimeRow X c) i : ℕ) : ℝ) ≤ (2 * X : ℕ) by
          push_cast; linarith)
    have hneg_Ioc : fNeg (c, i) ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hq₀_r, div_lt_iff₀ hc_r] at hr₀_lo
      rw [le_div_iff₀ hq₀_r, le_div_iff₀ hc_r] at hr₀_hi
      have hcw : ((fNeg (c, i) : ℕ) : ℝ) = (r₀ : ℝ) * q₀ * c := by
        dsimp only [fNeg]
        rw [← hw_q₀r₀]; push_cast; ring
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < (fNeg (c, i) : ℕ) by rw [hcw]; linarith)
      · exact_mod_cast (show ((fNeg (c, i) : ℕ) : ℝ) ≤ (2 * X : ℕ) by
          rw [hcw]; push_cast; linarith)
    have hμ_pos : μ (fPos (c, i)) = 1 := by
      dsimp only [fPos]
      rw [moebius_mul_larger_prime hc_ne hpp hp_top, hcμ]; norm_num
    have hcq_ne : c * q ≠ 0 := Nat.mul_ne_zero hc_ne hqp.ne_zero
    have htr := primeFactors_lt_of_mul_prime hc_ne hqp hqr hq_top
    have hμ_neg : μ (fNeg (c, i)) = -1 := by
      dsimp only [fNeg]
      rw [hweq, ← mul_assoc, moebius_mul_larger_prime hcq_ne hrp htr,
        moebius_mul_larger_prime hc_ne hqp hq_top, hcμ]; norm_num
    have hsq_pos : Squarefree (fPos (c, i)) :=
      squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_pos]; decide)
    have hsq_neg : Squarefree (fNeg (c, i)) :=
      squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_neg]; decide)
    refine ⟨mem_filter.mpr ⟨hpos_Ioc, hμ_pos⟩, mem_filter.mpr ⟨hneg_Ioc, hμ_neg⟩,
      ⟨hsq_pos, hsq_neg, by omega, c, finsetEntry (cofactorPrimeRow X c) i, q, r,
        hpp, hqp, hrp, hqr, Or.inl ⟨rfl, congrArg (c * ·) hweq⟩⟩,
      maxPrimeStem_mul_prime hc_ne hpp hp_top, ?_, ?_⟩
    · dsimp only [fNeg]
      rw [hweq]
      exact (maxPrimeStem_mul_pair hc_ne hqp hrp hqr hq_top).2
    · dsimp only [fNeg, fPos]
      rw [hweq, ← mul_assoc, card_primeFactors_mul_larger_prime hcq_ne hrp htr,
        card_primeFactors_mul_larger_prime hc_ne hqp hq_top,
        card_primeFactors_mul_larger_prime hc_ne hpp hp_top]
  let unpair : ℕ → ℕ × ℕ := fun m =>
    (maxPrimeStem m, finsetRank (cofactorPrimeRow X (maxPrimeStem m)) (m / maxPrimeStem m))
  have hunpair : ∀ a ∈ addrs, unpair (fPos a) = a := by
    rintro ⟨c, i⟩ ha
    obtain ⟨hcI, _, hi⟩ := hmem_addrs.mp ha
    have hstem := (hends ha).2.2.2.1
    have hdiv : fPos (c, i) / c = finsetEntry (cofactorPrimeRow X c) i := by
      dsimp only [fPos]
      rw [mul_comm, Nat.mul_div_cancel _ (mem_Icc.mp hcI).1]
    dsimp only [unpair]
    rw [hstem, hdiv, finsetRank_entry (hi.trans_le (min_le_left _ _))]
  have hfNeg_inj : Set.InjOn fNeg ↑addrs := by
    rintro ⟨c₁, i₁⟩ ha₁ ⟨c₂, i₂⟩ ha₂ heq
    obtain ⟨hc₁, _, hi₁⟩ := hmem_addrs.mp ha₁
    obtain ⟨_, _, hi₂⟩ := hmem_addrs.mp ha₂
    have hss₁ := (hends ha₁).2.2.2.2.1
    have hss₂ := (hends ha₂).2.2.2.2.1
    have hc_eq : c₁ = c₂ :=
      hss₁.symm.trans ((congrArg (fun n => maxPrimeStem (maxPrimeStem n)) heq).trans hss₂)
    subst hc_eq
    exact Prod.ext rfl (finsetEntry_inj (hi₁.trans_le (min_le_right _ _))
      (hi₂.trans_le (min_le_right _ _))
      (Nat.eq_of_mul_eq_mul_left (mem_Icc.mp hc₁).1 heq))
  let M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2 * X)) :=
    { sources := addrs.image fPos
      partner := fNeg ∘ unpair
      sources_subset := fun m hm => by
        obtain ⟨⟨c, i⟩, ha, rfl⟩ := mem_image.mp hm
        exact (hends ha).1
      injOn := fun x hx y hy heq => by
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := mem_image.mp hy
        simp only [Function.comp_apply, hunpair a ha, hunpair b hb] at heq
        exact congrArg fPos (hfNeg_inj ha hb heq)
      partner_mem := fun m hm => by
        obtain ⟨⟨c, i⟩, ha, rfl⟩ := mem_image.mp hm
        simp only [Function.comp_apply, hunpair (c, i) ha]
        exact (hends ha).2.1
      adj := fun m hm => by
        obtain ⟨⟨c, i⟩, ha, rfl⟩ := mem_image.mp hm
        simp only [Function.comp_apply, hunpair (c, i) ha]
        exact (hends ha).2.2.1 }
  exact FactorizationInvolution.ofMatching M

theorem rankedCrossFibreInvolution_covers_row {X c w : ℕ}
    (hc : c ∈ Icc 1 (2 * X)) (hμ : μ c = -1)
    (hw : w ∈ cofactorCubeRow X c)
    (hcap : (cofactorCubeRow X c).card ≤ (cofactorPrimeRow X c).card) :
    c * w ∈ (rankedCrossFibreInvolution X).movedNeg := by
  unfold rankedCrossFibreInvolution
  rw [FactorizationInvolution.ofMatching_movedNeg]
  let i := ((cofactorCubeRow X c).orderIsoOfFin rfl).symm ⟨w, hw⟩
  have hi_lt : i.val < min (cofactorPrimeRow X c).card (cofactorCubeRow X c).card := by
    rw [min_eq_right hcap]; exact i.isLt
  let rowLen : ℕ → ℕ := fun c' =>
    min (cofactorPrimeRow X c').card (cofactorCubeRow X c').card
  let addrs : Finset (ℕ × ℕ) :=
    ((Icc 1 (2 * X)).filter fun c' => μ c' = -1).biUnion fun c' =>
      (range (rowLen c')).image fun j => (c', j)
  have ha : (c, i.val) ∈ addrs :=
    mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨hc, hμ⟩,
      mem_image.mpr ⟨i.val, mem_range.mpr hi_lt, rfl⟩⟩
  let fPos : ℕ × ℕ → ℕ := fun a => a.1 * finsetEntry (cofactorPrimeRow X a.1) a.2
  let fNeg : ℕ × ℕ → ℕ := fun a => a.1 * finsetEntry (cofactorCubeRow X a.1) a.2
  let unpair : ℕ → ℕ × ℕ := fun m =>
    (maxPrimeStem m, finsetRank (cofactorPrimeRow X (maxPrimeStem m)) (m / maxPrimeStem m))
  have hp_mem := finsetEntry_mem (S := cofactorPrimeRow X c) (hi_lt.trans_le (min_le_left _ _))
  obtain ⟨hp_win, hp_top⟩ := mem_filter.mp hp_mem
  have hpp : (finsetEntry (cofactorPrimeRow X c) i.val).Prime :=
    ((mem_windowPrimes (by positivity) (by positivity)).mp hp_win).1
  have hc_pos : 0 < c := (mem_Icc.mp hc).1
  have hstem : maxPrimeStem (fPos (c, i.val)) = c :=
    maxPrimeStem_mul_prime hc_pos.ne' hpp hp_top
  have hunp : unpair (fPos (c, i.val)) = (c, i.val) := by
    dsimp only [unpair]
    have hdiv : fPos (c, i.val) / c = finsetEntry (cofactorPrimeRow X c) i.val := by
      dsimp only [fPos]; rw [mul_comm, Nat.mul_div_cancel _ hc_pos]
    rw [hstem, hdiv, finsetRank_entry (hi_lt.trans_le (min_le_left _ _))]
  change c * w ∈ (addrs.image fPos).image (fNeg ∘ unpair)
  refine mem_image.mpr ⟨fPos (c, i.val), mem_image_of_mem fPos ha, ?_⟩
  rw [Function.comp_apply, hunp]
  dsimp only [fNeg]
  simp only [finsetEntry, dif_pos i.isLt]
  exact congrArg (fun x : cofactorCubeRow X c => c * (x : ℕ))
    (((cofactorCubeRow X c).orderIsoOfFin rfl).apply_symm_apply ⟨w, hw⟩)

private theorem cofactorPrimeRow_eq_window_of_cubeRow {X c w : ℕ} (hc : c ≠ 0)
    (hw : w ∈ cofactorCubeRow X c) (hcw : c * w ∈ Ioc X (2 * X)) :
    cofactorPrimeRow X c = windowPrimes ((X : ℝ) / c) (2 * (X : ℝ) / c) := by
  obtain ⟨_, q, r, _, hrp, _, rfl, hq_top⟩ := mem_filter.mp hw
  have hcw2X : c * (q * r) ≤ 2 * X := (mem_Ioc.mp hcw).2
  have hcq_le_X : c * q ≤ X := by
    rw [← mul_assoc] at hcw2X
    have := Nat.mul_le_mul_left (c * q) hrp.two_le
    omega
  have hc_r : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
  have hq_le : (q : ℝ) ≤ (X : ℝ) / c := by
    rw [le_div_iff₀ hc_r, mul_comm]
    exact_mod_cast hcq_le_X
  unfold cofactorPrimeRow
  refine filter_eq_self.mpr fun p hp d hd => ?_
  obtain ⟨_, hp_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp
  exact (hq_top d hd).trans (by exact_mod_cast hq_le.trans_lt hp_lo)

private theorem exists_prime_in_nine_eighths_window :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      ∃ p : ℕ, p.Prime ∧ t < (p : ℝ) ∧ (p : ℝ) ≤ (9 / 8) * t := by
  obtain ⟨C_θ, hC_θ, T_θ, hT_θ, hθ⟩ := exists_abs_theta_sub_le 1
  have hev : ∀ᶠ t : ℝ in atTop, T_θ ≤ t ∧ 4 ≤ t ∧ 36 * C_θ ≤ Real.log t :=
    (eventually_ge_atTop T_θ).and ((eventually_ge_atTop 4).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  refine ⟨max U₀ 4, le_max_right _ _, fun t ht => ?_⟩
  obtain ⟨hTt, ht4, hCt⟩ := hU₀ t ((le_max_left _ _).trans ht)
  have ht0 : 0 < t := by linarith
  have hab : t ≤ (9 / 8) * t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog98 : 0 < Real.log ((9 / 8) * t) := Real.log_pos (by linarith)
  have hinc := abs_theta_increment_le hC_θ.le hT_θ hθ hTt hab
  have herr : 2 * C_θ * ((9 / 8) * t) / Real.log t ^ (1 : ℕ) ≤ (1 / 16) * t := by
    rw [pow_one, div_le_iff₀ hlogt]; nlinarith
  have hθ_ge : (1 / 16) * t ≤ Chebyshev.theta ((9 / 8) * t) - Chebyshev.theta t := by
    have := (abs_le.mp hinc).1; linarith
  have hcard := theta_sub_le_card_mul_log ht0.le hab
  have hpos_r : 0 < ((windowPrimes t ((9 / 8) * t)).card : ℝ) * Real.log ((9 / 8) * t) := by
    linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 16) ht0]
  have hne : (windowPrimes t ((9 / 8) * t)).Nonempty := by
    apply card_pos.mp
    by_contra h0
    have hc0 : (windowPrimes t ((9 / 8) * t)).card = 0 := by omega
    rw [hc0, Nat.cast_zero, zero_mul] at hpos_r
    exact hpos_r.false
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (mem_windowPrimes ht0.le (by positivity)).mp hp⟩

theorem evenPrefixCofactor_mul_ordered_pair {a p q : ℕ} (ha : a ≠ 0)
    (heven : Even a.primeFactors.card) (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (htp : ∀ d ∈ a.primeFactors, d < p) :
    evenPrefixCofactor (a * (p * q)) = a := by
  have hp_not : p ∉ a.primeFactors := fun hm => (htp p hm).false
  have hq_not : q ∉ insert p a.primeFactors := by
    intro hm
    rcases mem_insert.mp hm with rfl | hm'
    · exact hpq.false
    · exact ((htp q hm').trans hpq).false
  have hpf_m : (a * (p * q)).primeFactors = insert q (insert p a.primeFactors) := by
    rw [← mul_assoc, Nat.primeFactors_mul (Nat.mul_ne_zero ha hp.ne_zero) hq.ne_zero,
      Nat.primeFactors_mul ha hp.ne_zero, hp.primeFactors, hq.primeFactors]
    ext d; simp only [mem_union, mem_singleton, mem_insert]; tauto
  have heven_m : Even (a * (p * q)).primeFactors.card := by
    rw [hpf_m, card_insert_of_notMem hq_not, card_insert_of_notMem hp_not]
    obtain ⟨k, hk⟩ := heven
    exact ⟨k + 1, by omega⟩
  have hmax₂ : ∀ hne, (a * (p * q)).primeFactors.max' hne = q := by
    intro hne
    refine le_antisymm (max'_le _ _ _ fun d hd => ?_) (le_max' _ q (by rw [hpf_m]; simp))
    rw [hpf_m] at hd
    rcases mem_insert.mp hd with rfl | hd'
    · exact le_rfl
    · rcases mem_insert.mp hd' with rfl | hd''
      · exact hpq.le
      · exact ((htp d hd'').trans hpq).le
  have hne_m : (a * (p * q)).primeFactors.Nonempty := by rw [hpf_m]; simp
  have hne_er : ((a * (p * q)).primeFactors.erase q).Nonempty := by
    rw [hpf_m, erase_insert hq_not]; simp
  have hmax₁ : ((a * (p * q)).primeFactors.erase q).max' hne_er = p := by
    refine le_antisymm (max'_le _ _ _ fun d hd => ?_)
      (le_max' _ p (by rw [hpf_m, erase_insert hq_not]; simp))
    rw [hpf_m, erase_insert hq_not] at hd
    rcases mem_insert.mp hd with rfl | hd'
    · exact le_rfl
    · exact (htp d hd').le
  unfold evenPrefixCofactor
  simp only [dif_pos hne_m, if_pos heven_m, hmax₂ hne_m, dif_pos hne_er, hmax₁]
  exact Nat.mul_div_cancel a (Nat.mul_pos hp.pos hq.pos)

/-- **100% cross-fibre evacuation of all empty-positive ordered cofactor fibres**:
for all sufficiently large `X`, the single explicit involution `rankedCrossFibreInvolution X`
matches **every** negative-Möbius vertex `n ∈ (X, 2X]` whose ordered cofactor fibre has
`fibrePos X (evenPrefixCofactor n) = ∅`. -/
theorem eventually_emptyFibres_evacuated_by_involution :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (negParity (Ioc X (2 * X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅) ⊆
        (rankedCrossFibreInvolution X).movedNeg ∧
      Disjoint (rankedCrossFibreInvolution X).unmatchedSet
        ((negParity (Ioc X (2 * X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅)) := by
  obtain ⟨S_cap, hS_cap⟩ := eventually_atTop.mp eventually_cubeBandProducts_nine_tenths
  obtain ⟨T_pr, _, hpr98⟩ := exists_prime_in_nine_eighths_window
  obtain ⟨V, hV_def⟩ : ∃ V : ℝ, V = max 4 (max S_cap T_pr) := ⟨_, rfl⟩
  have hV4 : 4 ≤ V := hV_def ▸ le_max_left _ _
  have hVS : S_cap ≤ V := hV_def ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hVT : T_pr ≤ V := hV_def ▸ (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨B_cut, hB_def⟩ : ∃ B_cut : ℕ, B_cut = ⌈2 * V ^ 6⌉₊ := ⟨_, rfl⟩
  obtain ⟨P_prim, hP_def⟩ : ∃ P_prim : ℕ, P_prim = ∏ p ∈ Nat.primesLE B_cut, p := ⟨_, rfl⟩
  refine ⟨max 2 P_prim, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ 2) ((le_max_left _ _).trans hX)
  have hXP : P_prim ≤ X := (le_max_right _ _).trans hX
  have hsub : (negParity (Ioc X (2 * X))).filter
      (fun n => fibrePos X (evenPrefixCofactor n) = ∅) ⊆
        (rankedCrossFibreInvolution X).movedNeg := by
    intro n hn_bad
    obtain ⟨hn_neg, hfib_emp⟩ := mem_filter.mp hn_bad
    let a := evenPrefixCofactor n
    have hn_fib : n ∈ fibreNeg X a := mem_filter.mpr ⟨hn_neg, rfl⟩
    obtain ⟨hsq_a, heven_a, r, hrp, hna, hlt_r⟩ := mem_fibreNeg_structure hX1 hn_fib
    have hn_Ioc := (mem_filter.mp hn_neg).1
    have hn_lo := (mem_Ioc.mp hn_Ioc).1
    have hn_hi := (mem_Ioc.mp hn_Ioc).2
    have hsq_n : Squarefree n :=
      squarefree_iff_moebius_ne_zero.mpr (by rw [(mem_filter.mp hn_neg).2]; decide)
    have ha_pos : 0 < a := Nat.pos_of_ne_zero hsq_a.ne_zero
    have ha_r : (0 : ℝ) < a := by exact_mod_cast ha_pos
    have hXa_ge : V ^ 6 ≤ (X : ℝ) / a := by
      by_contra hlt
      push Not at hlt
      have hr_le : r ≤ B_cut := by
        have hru : (r : ℝ) ≤ 2 * ((X : ℝ) / a) := by
          rw [← mul_div_assoc, le_div_iff₀ ha_r, mul_comm]
          exact_mod_cast (hna ▸ hn_hi : a * r ≤ 2 * X)
        rw [hB_def]
        exact_mod_cast (show (r : ℝ) ≤ 2 * V ^ 6 by linarith).trans (Nat.le_ceil _)
      have hpf_sub : n.primeFactors ⊆ Nat.primesLE B_cut := by
        intro d hd
        refine Nat.mem_primesLE.mpr ⟨?_, Nat.prime_of_mem_primeFactors hd⟩
        rw [hna, Nat.primeFactors_mul hsq_a.ne_zero hrp.ne_zero, hrp.primeFactors] at hd
        rcases mem_union.mp hd with hda | hdr
        · exact (hlt_r d hda).le.trans hr_le
        · exact (mem_singleton.mp hdr) ▸ hr_le
      have hP_pos : 0 < P_prim := by
        rw [hP_def]
        exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primesLE hp).pos
      have hn_le_P : n ≤ P_prim := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq_n]
        refine Nat.le_of_dvd hP_pos ?_
        rw [hP_def]
        exact prod_dvd_prod_of_subset _ _ id hpf_sub
      omega
    let t := Real.sqrt ((X : ℝ) / a)
    have ht_sq : t ^ 2 = (X : ℝ) / a := Real.sq_sqrt (by positivity)
    have hVt : V ≤ t := by
      apply (pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg _) two_ne_zero).mp
      rw [ht_sq]
      exact (pow_le_pow_right₀ (by linarith only [hV4] : 1 ≤ V) (by decide : 2 ≤ 6)).trans hXa_ge
    have hex_d : ∃ d ∈ a.primeFactors, t < (d : ℝ) := by
      by_contra hall
      push Not at hall
      obtain ⟨p₁, hp₁_pr, hp₁_lo, hp₁_hi⟩ := hpr98 t (hVT.trans hVt)
      obtain ⟨p₂, hp₂_pr, hp₂_lo, hp₂_hi⟩ :=
        hpr98 ((9 / 8) * t) (by linarith only [hVT, hVt, hV4])
      have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast hp₁_hi.trans_lt hp₂_lo
      have htp₁ : ∀ d ∈ a.primeFactors, d < p₁ := fun d hd =>
        by exact_mod_cast (hall d hd).trans_lt hp₁_lo
      have htp₂ : ∀ d ∈ (a * p₁).primeFactors, d < p₂ :=
        primeFactors_lt_of_mul_prime hsq_a.ne_zero hp₁_pr hp₁_lt_p₂ htp₁
      have hμ_ap₁p₂ : μ (a * (p₁ * p₂)) = 1 := by
        rw [← mul_assoc, moebius_mul_larger_prime (Nat.mul_ne_zero hsq_a.ne_zero hp₁_pr.ne_zero)
          hp₂_pr htp₂, moebius_mul_larger_prime hsq_a.ne_zero hp₁_pr htp₁,
          moebius_eq_neg_one_pow_omega hsq_a, heven_a.neg_one_pow]; norm_num
      have hlo_prod : (X : ℝ) / a < (p₁ : ℝ) * p₂ := by
        rw [← ht_sq]
        have ht0 : 0 < t := by linarith only [hV4, hVt]
        nlinarith [hp₁_lo, hp₂_lo, ht0]
      have hhi_prod : (p₁ : ℝ) * p₂ ≤ 2 * ((X : ℝ) / a) := by
        rw [← ht_sq]
        calc (p₁ : ℝ) * p₂ ≤ ((9 / 8) * t) * ((9 / 8) * ((9 / 8) * t)) :=
              mul_le_mul hp₁_hi hp₂_hi (Nat.cast_nonneg _) (by positivity)
          _ ≤ 2 * t ^ 2 := by nlinarith [sq_nonneg t]
      have hIoc_m : a * (p₁ * p₂) ∈ Ioc X (2 * X) := by
        rw [div_lt_iff₀ ha_r] at hlo_prod
        rw [← mul_div_assoc, le_div_iff₀ ha_r] at hhi_prod
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < ((a * (p₁ * p₂) : ℕ) : ℝ) by push_cast; linarith)
        · exact_mod_cast (show ((a * (p₁ * p₂) : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)
      have hmem_pos : a * (p₁ * p₂) ∈ fibrePos X a :=
        mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_m, hμ_ap₁p₂⟩,
          evenPrefixCofactor_mul_ordered_pair hsq_a.ne_zero heven_a hp₁_pr hp₂_pr hp₁_lt_p₂ htp₁⟩
      rw [hfib_emp] at hmem_pos
      exact notMem_empty _ hmem_pos
    obtain ⟨d₀, hd₀, hd₀_gt⟩ := hex_d
    have hne_a : a.primeFactors.Nonempty := ⟨d₀, hd₀⟩
    let q := a.primeFactors.max' hne_a
    have hq_mem : q ∈ a.primeFactors := max'_mem _ hne_a
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hqr : q < r := hlt_r q hq_mem
    let c := a / q
    have hcq : c * q = a := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hq_mem)
    obtain ⟨hcop_cq, hsq_c, _⟩ := Nat.squarefree_mul_iff.mp (hcq ▸ hsq_a)
    have hc_pos : 0 < c := Nat.pos_of_ne_zero hsq_c.ne_zero
    have hc_r : (0 : ℝ) < c := by exact_mod_cast hc_pos
    have hq_r : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hq_top : ∀ e ∈ c.primeFactors, e < q := by
      have hndvd : ¬ q ∣ c := hqp.coprime_iff_not_dvd.mp hcop_cq.symm
      intro e he
      have hdvd_e := Nat.dvd_of_mem_primeFactors he
      have he_a : e ∈ a.primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors he, hcq ▸ dvd_mul_of_dvd_left hdvd_e q, hsq_a.ne_zero⟩
      exact lt_of_le_of_ne (le_max' _ e he_a) fun heq => hndvd (heq ▸ hdvd_e)
    have hμ_c : μ c = -1 := by
      have h := moebius_mul_larger_prime hc_pos.ne' hqp hq_top
      rw [hcq, moebius_eq_neg_one_pow_omega hsq_a, heven_a.neg_one_pow] at h
      omega
    have hn_eq : n = c * (q * r) := by rw [← mul_assoc, hcq, hna]
    have hc_le : c ≤ 2 * X :=
      (Nat.le_mul_of_pos_right c (Nat.mul_pos hqp.pos hrp.pos)).trans (hn_eq ▸ hn_hi)
    let z := ((X : ℝ) / c) ^ (1 / 6 : ℝ)
    have hz0 : 0 ≤ z := Real.rpow_nonneg (by positivity) _
    have hz6 : z ^ 6 = (X : ℝ) / c := by
      rw [show z = ((X : ℝ) / c) ^ (1 / 6 : ℝ) from rfl, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      norm_num
    have hz6_aq : z ^ 6 = ((X : ℝ) / a) * q := by
      have hcq_r : (c : ℝ) * q = a := by exact_mod_cast hcq
      rw [hz6, ← hcq_r]; field_simp
    have hVz : V ≤ z := by
      apply (pow_le_pow_iff_left₀ (by positivity) hz0 (by decide : 6 ≠ 0)).mp
      rw [hz6_aq]
      exact hXa_ge.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hqp.pos))
    have hqt : t < (q : ℝ) := hd₀_gt.trans_le (by exact_mod_cast le_max' _ d₀ hd₀)
    have hq_sq : (X : ℝ) / a < (q : ℝ) ^ 2 := by
      rw [← ht_sq]
      exact pow_lt_pow_left₀ hqt (Real.sqrt_nonneg _) two_ne_zero
    have hq_cube : z ^ 6 < (q : ℝ) ^ 3 := by
      rw [hz6_aq]
      nlinarith [mul_lt_mul_of_pos_right hq_sq hq_r]
    have hq_lo : z ^ 2 / 2 < (q : ℝ) := by
      have hz2_lt : z ^ 2 < (q : ℝ) := by
        by_contra hle
        push Not at hle
        have := pow_le_pow_left₀ hq_r.le hle 3
        nlinarith [this, hq_cube]
      linarith [sq_nonneg z]
    have hqr_hi : (q : ℝ) * r ≤ 2 * z ^ 6 := by
      rw [hz6, mul_div_assoc', le_div_iff₀ hc_r]
      exact_mod_cast (show (q * r * c : ℕ) ≤ 2 * X by rw [mul_comm (q * r) c, ← hn_eq]; exact hn_hi)
    have hq_hi : (q : ℝ) ≤ 2 * z ^ 3 := by
      have hq2_le : (q : ℝ) ^ 2 ≤ 2 * z ^ 6 :=
        (show (q : ℝ) ^ 2 ≤ (q : ℝ) * r by rw [sq]; gcongr).trans hqr_hi
      by_contra hgt
      push Not at hgt
      nlinarith [hq2_le, hgt, pow_nonneg hz0 3, pow_nonneg hz0 6]
    have hr_win : r ∈ windowPrimes ((X : ℝ) / c / q) (2 * (X : ℝ) / c / q) := by
      refine (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hrp, ?_, ?_⟩
      · rw [div_lt_iff₀ hq_r, div_lt_iff₀ hc_r]
        exact_mod_cast (show X < r * q * c by rw [show r * q * c = c * (q * r) by ring, ← hn_eq]; exact hn_lo)
      · rw [le_div_iff₀ hq_r, le_div_iff₀ hc_r]
        exact_mod_cast (show r * q * c ≤ 2 * X by rw [show r * q * c = c * (q * r) by ring, ← hn_eq]; exact hn_hi)
    have hw_mem : q * r ∈ cofactorCubeRow X c := by
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨q,
        (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hqp, hq_lo, hq_hi⟩,
        mem_image.mpr ⟨r, hr_win, rfl⟩⟩, q, r, hqp, hrp, hqr, rfl, hq_top⟩
    have hcap_s := hS_cap z (hVS.trans hVz)
    have h2z6 : 2 * (X : ℝ) / c = 2 * z ^ 6 := by rw [hz6]; ring
    have hcap_row : (cofactorCubeRow X c).card ≤ (cofactorPrimeRow X c).card := by
      rw [cofactorPrimeRow_eq_window_of_cubeRow hc_pos.ne' hw_mem (hn_eq ▸ hn_Ioc)]
      have hsub_cube : cofactorCubeRow X c ⊆ cubeBandProducts z (z ^ 6) (2 * z ^ 6) := by
        rw [← h2z6, hz6]
        exact filter_subset _ _
      have h10 := (Nat.mul_le_mul_left 10 (card_le_card hsub_cube)).trans hcap_s
      rw [← h2z6, hz6] at h10
      omega
    rw [hn_eq]
    exact rankedCrossFibreInvolution_covers_row (mem_Icc.mpr ⟨hc_pos, hc_le⟩) hμ_c hw_mem hcap_row
  refine ⟨hsub, disjoint_left.mpr fun n hunm hbad => ?_⟩
  exact (mem_filter.mp (hsub hbad)).2 (mem_filter.mp hunm).2

/-! ### 3. Exact `Θ(X / (log X)³)` pilot class and strict global unmatched reduction -/

/-- Union of complete ordered cofactor fibres `F_X(a) = fibrePos X a ∪ fibreNeg X a` over `a ∈ A`. -/
def fibreUnion (X : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun a => fibrePos X a ∪ fibreNeg X a

/-- The pilot class of deficient even-prefix cofactors `a = p₁ * p₂` at cube-root scale `Y = X^{1/3}`
with `p₁ ∈ (Y/8, Y/6]` and `p₂ ∈ (2Y, 9Y/4]`. -/
def pilotCofactors (X : ℕ) : Finset ℕ :=
  let Y : ℝ := (X : ℝ) ^ (1 / 3 : ℝ)
  (windowPrimes (Y / 8) (4 / 3 * (Y / 8)) ×ˢ
    windowPrimes (2 * Y) (9 / 8 * (2 * Y))).image fun pq => pq.1 * pq.2

/-- Total squarefree vertex set of the pilot class of ordered cofactor fibres. -/
def pilotVertices (X : ℕ) : Finset ℕ :=
  fibreUnion X (pilotCofactors X)

lemma exists_const_ratio_windowPrimes_bounds {α : ℝ} (hα : 1 < α) :
    ∃ U_α : ℝ, 4 ≤ U_α ∧ ∀ u : ℝ, U_α ≤ u →
      ((α - 1) / 2) * u / Real.log (α * u) ≤ ((windowPrimes u (α * u)).card : ℝ) ∧
      ((windowPrimes u (α * u)).card : ℝ) ≤ (2 * (α - 1)) * u / Real.log u := by
  obtain ⟨C_θ, hC_θ, T_θ, hT_θ, hθ⟩ := exists_abs_theta_sub_le 1
  have hα0 : 0 < α - 1 := by linarith only [hα]
  have hev : ∀ᶠ u : ℝ in atTop,
      T_θ ≤ u ∧ 4 ≤ u ∧ 4 * C_θ * α / (α - 1) ≤ Real.log u :=
    (eventually_ge_atTop T_θ).and ((eventually_ge_atTop 4).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  refine ⟨max U₀ 4, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨hTu, hu4, hCu⟩ := hU₀ u ((le_max_left _ _).trans hu)
  have hu0 : 0 < u := by linarith
  have hab : u ≤ α * u := by nlinarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogαu : 0 < Real.log (α * u) := Real.log_pos (by linarith)
  have hinc := abs_theta_increment_le hC_θ.le hT_θ hθ hTu hab
  have herr : 2 * C_θ * (α * u) / Real.log u ^ (1 : ℕ) ≤ ((α - 1) / 2) * u := by
    rw [pow_one, div_le_iff₀ hlogu]
    rw [div_le_iff₀ hα0] at hCu
    nlinarith
  constructor
  · have hθ_ge : ((α - 1) / 2) * u ≤ Chebyshev.theta (α * u) - Chebyshev.theta u := by
      have := (abs_le.mp hinc).1; linarith
    have hcard := theta_sub_le_card_mul_log hu0.le hab
    rw [div_le_iff₀ hlogαu]; linarith
  · have hθ_le : Chebyshev.theta (α * u) - Chebyshev.theta u ≤ (2 * (α - 1)) * u := by
      have := (abs_le.mp hinc).2; linarith
    have hcard := card_windowPrimes_mul_log_le (by linarith) hab
    rw [le_div_iff₀ hlogu]; linarith

private lemma pilot_cofactor_fibre_structure (X : ℕ) (Y : ℝ) (W₁ W₂ : Finset ℕ)
    (hX1 : 1 ≤ X) (hY64 : 64 ≤ Y) (hY3 : Y ^ (3 : ℕ) = (X : ℝ))
    (hW₁_sub : ∀ p ∈ W₁, p.Prime ∧ Y / 8 < (p : ℝ) ∧ (p : ℝ) ≤ 4 / 3 * (Y / 8))
    (hW₂_sub : ∀ p ∈ W₂, p.Prime ∧ 2 * Y < (p : ℝ) ∧ (p : ℝ) ≤ 9 / 8 * (2 * Y))
    (hpc_eq : pilotCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2) :
    Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) ↑(W₁ ×ˢ W₂) ∧
    (∀ pq ∈ W₁ ×ˢ W₂,
      fibrePos X (pq.1 * pq.2) = ∅ ∧
      fibreNeg X (pq.1 * pq.2) =
        (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).image
          (fun p₃ => pq.1 * pq.2 * p₃)) ∧
    (∀ a ∈ pilotCofactors X, fibrePos X a = ∅) := by
  have hinj_pq : Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) ↑(W₁ ×ˢ W₂) := by
    rintro ⟨p₁, p₂⟩ hpq₁ ⟨q₁, q₂⟩ hpq₂ heq
    dsimp only at heq
    obtain ⟨hp₁, hp₂⟩ := mem_product.mp hpq₁
    obtain ⟨hq₁, hq₂⟩ := mem_product.mp hpq₂
    dsimp only at hp₁ hp₂ hq₁ hq₂
    obtain ⟨hp₁_pr, _, hp₁_hi⟩ := hW₁_sub p₁ hp₁
    obtain ⟨hp₂_pr, hp₂_lo, _⟩ := hW₂_sub p₂ hp₂
    obtain ⟨hq₁_pr, _, _⟩ := hW₁_sub q₁ hq₁
    obtain ⟨hq₂_pr, hq₂_lo, _⟩ := hW₂_sub q₂ hq₂
    have hp₁_lt_q₂ : p₁ < q₂ := by exact_mod_cast (by linarith only [hp₁_hi, hq₂_lo, hY64] : (p₁ : ℝ) < q₂)
    have hp₁_eq_q₁ : p₁ = q₁ := by
      have hdvd : p₁ ∣ q₁ * q₂ := heq ▸ dvd_mul_right p₁ p₂
      rcases hp₁_pr.dvd_mul.mp hdvd with h1 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hp₁_pr hq₁_pr).mp h1
      · exact False.elim (hp₁_lt_q₂.ne ((Nat.prime_dvd_prime_iff_eq hp₁_pr hq₂_pr).mp h2))
    subst hp₁_eq_q₁
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hp₁_pr.pos heq)
  have hfib_info : ∀ pq ∈ W₁ ×ˢ W₂,
      fibrePos X (pq.1 * pq.2) = ∅ ∧
        fibreNeg X (pq.1 * pq.2) =
          (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).image
            (fun p₃ => pq.1 * pq.2 * p₃) := by
    rintro ⟨p₁, p₂⟩ hpq
    dsimp only
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    dsimp only at hp₁W hp₂W
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := hW₁_sub p₁ hp₁W
    obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := hW₂_sub p₂ hp₂W
    have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast (by linarith only [hp₁_hi, hp₂_lo, hY64] : (p₁ : ℝ) < p₂)
    have hpq_pos : 0 < p₁ * p₂ := Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hpq_r : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast hpq_pos
    have hpq_up : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) := by
      calc (p₁ : ℝ) * p₂ ≤ (4 / 3 * (Y / 8)) * (9 / 8 * (2 * Y)) :=
            mul_le_mul hp₁_hi hp₂_hi (Nat.cast_nonneg _) (by positivity)
        _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
    have hXpq_low : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
      rw [le_div_iff₀ hpq_r]
      calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hpq_up (by positivity)
        _ = X := by rw [← hY3]; ring
    have hpos_emp : fibrePos X (p₁ * p₂) = ∅ := by
      apply fibrePos_eq_empty_of_primeFactor_sq_ge hX1
        (Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ p₁, hpq_pos.ne'⟩)
      have hp₂_cube : 8 * Y ^ (3 : ℕ) ≤ (p₂ : ℝ) ^ (3 : ℕ) := by
        calc 8 * Y ^ (3 : ℕ) = (2 * Y) ^ (3 : ℕ) := by ring
          _ ≤ (p₂ : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) hp₂_lo.le 3
      have hgt : 2 * (X : ℝ) ≤ ((p₁ * p₂ * p₂ ^ 2 : ℕ) : ℝ) := by
        push_cast
        calc 2 * (X : ℝ) = 2 * Y ^ (3 : ℕ) := by rw [← hY3]
          _ ≤ Y * Y ^ (3 : ℕ) :=
              mul_le_mul_of_nonneg_right (by linarith only [hY64]) (by positivity)
          _ = (Y / 8) * (8 * Y ^ (3 : ℕ)) := by ring
          _ ≤ (p₁ : ℝ) * (p₂ : ℝ) ^ (3 : ℕ) :=
              mul_le_mul hp₁_lo.le hp₂_cube (by positivity) (Nat.cast_nonneg _)
          _ = (p₁ : ℝ) * p₂ * (p₂ : ℝ) ^ 2 := by ring
      exact_mod_cast hgt
    refine ⟨hpos_emp, ?_⟩
    ext n
    simp only [mem_image]
    constructor
    · intro hn
      obtain ⟨_, _, p₃, hp₃_pr, hna, _⟩ := mem_fibreNeg_structure hX1 hn
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      refine ⟨p₃, (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hp₃_pr, ?_, ?_⟩, hna.symm⟩
      · rw [div_lt_iff₀ hpq_r]
        have hn_lo_r : (X : ℝ) < ((p₁ * p₂ * p₃ : ℕ) : ℝ) := by exact_mod_cast hna ▸ hn_lo
        push_cast at hn_lo_r; linarith only [hn_lo_r]
      · rw [mul_div_assoc', le_div_iff₀ hpq_r]
        have hn_hi_r : ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by exact_mod_cast hna ▸ hn_hi
        push_cast at hn_hi_r; linarith only [hn_hi_r]
    · rintro ⟨p₃, hp₃_win, rfl⟩
      obtain ⟨hp₃_pr, hp₃_lo, hp₃_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₃_win
      have hp₂_lt_p₃ : p₂ < p₃ := by
        exact_mod_cast (show (p₂ : ℝ) < p₃ by linarith only [hp₂_hi, hXpq_low, hp₃_lo, hY64])
      have htop1 : ∀ d ∈ p₁.primeFactors, d < p₂ := fun d hd =>
        (Nat.le_of_dvd hp₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hp₁_lt_p₂
      have htop2 : ∀ d ∈ (p₁ * p₂).primeFactors, d < p₃ :=
        primeFactors_lt_of_mul_prime hp₁_pr.ne_zero hp₂_pr hp₂_lt_p₃ htop1
      have hμ_n : μ (p₁ * p₂ * p₃) = -1 := by
        rw [moebius_mul_larger_prime hpq_pos.ne' hp₃_pr htop2,
          moebius_mul_larger_prime hp₁_pr.ne_zero hp₂_pr htop1,
          ArithmeticFunction.moebius_apply_prime hp₁_pr]; norm_num
      have hIoc_n : p₁ * p₂ * p₃ ∈ Ioc X (2 * X) := by
        rw [div_lt_iff₀ hpq_r] at hp₃_lo
        rw [mul_div_assoc', le_div_iff₀ hpq_r] at hp₃_hi
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < ((p₁ * p₂ * p₃ : ℕ) : ℝ) by push_cast; linarith only [hp₃_lo])
        · exact_mod_cast (show ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith only [hp₃_hi])
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_n, hμ_n⟩, ?_⟩
      rw [evenPrefixCofactor_eq_maxPrimeStem_of_neg hμ_n]
      exact maxPrimeStem_mul_prime hpq_pos.ne' hp₃_pr htop2
  refine ⟨hinj_pq, hfib_info, fun a ha => ?_⟩
  rw [hpc_eq] at ha
  obtain ⟨pq, hpq, rfl⟩ := mem_image.mp ha
  exact (hfib_info pq hpq).1

private lemma pilot_fibre_and_vertex_bounds (X : ℕ) (Y : ℝ) (W₁ W₂ : Finset ℕ)
    (hX1 : 1 ≤ X) (hX216 : 216 ≤ (X : ℝ)) (hY64 : 64 ≤ Y)
    (hY3 : Y ^ (3 : ℕ) = (X : ℝ)) (hY2 : Y ^ (2 : ℕ) = (X : ℝ) ^ (2 / 3 : ℝ))
    (hL8 : 12 * Real.log 8 ≤ Real.log X)
    (hW₁_sub : ∀ p ∈ W₁, p.Prime ∧ Y / 8 < (p : ℝ) ∧ (p : ℝ) ≤ 4 / 3 * (Y / 8))
    (hW₂_sub : ∀ p ∈ W₂, p.Prime ∧ 2 * Y < (p : ℝ) ∧ (p : ℝ) ≤ 9 / 8 * (2 * Y))
    (hpc_eq : pilotCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2)
    (hw₁ : ((4 / 3 - 1) / 2) * (Y / 8) / Real.log (4 / 3 * (Y / 8)) ≤ (W₁.card : ℝ) ∧
      (W₁.card : ℝ) ≤ (2 * (4 / 3 - 1)) * (Y / 8) / Real.log (Y / 8))
    (hw₂ : ((9 / 8 - 1) / 2) * (2 * Y) / Real.log (9 / 8 * (2 * Y)) ≤ (W₂.card : ℝ) ∧
      (W₂.card : ℝ) ≤ (2 * (9 / 8 - 1)) * (2 * Y) / Real.log (2 * Y))
    (hw₃ : ∀ u : ℝ, (8 / 3) * Y ≤ u →
      ((2 - 1) / 2) * u / Real.log (2 * u) ≤ ((windowPrimes u (2 * u)).card : ℝ) ∧
      ((windowPrimes u (2 * u)).card : ℝ) ≤ (2 * (2 - 1)) * u / Real.log u) :
    (1 / 48) * (1 / 8) * (X : ℝ) ^ (2 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
      ((pilotCofactors X).card : ℝ) ∧
    (W₂.card : ℝ) ≤ 3 * Y / Real.log X ∧
    (∀ pq ∈ W₁ ×ˢ W₂,
      fibrePos X (pq.1 * pq.2) = ∅ ∧
      fibreNeg X (pq.1 * pq.2) =
        (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).image
          (fun p₃ => pq.1 * pq.2 * p₃)) ∧
    (∀ a ∈ pilotCofactors X, fibrePos X a = ∅) ∧
    (1 / 48) * (1 / 8) * (4 / 3) * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
      ((pilotVertices X).card : ℝ) ∧
    ((pilotVertices X).card : ℝ) ≤ 5184 * (X : ℝ) / Real.log X ^ (3 : ℕ) := by
  obtain ⟨hinj_pq, hfib_info, hall_emp⟩ :=
    pilot_cofactor_fibre_structure X Y W₁ W₂ hX1 hY64 hY3 hW₁_sub hW₂_sub hpc_eq
  have hX0 : (0 : ℝ) < X := by linarith only [hX216]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX216])
  have hY0 : 0 < Y := by linarith only [hY64]
  have hlogY : Real.log Y = Real.log X / 3 := by
    have : Real.log (Y ^ (3 : ℕ)) = Real.log X := by rw [hY3]
    rw [Real.log_pow] at this; push_cast at this; linarith only [this]
  have hY_le_X : 9 / 8 * (2 * Y) ≤ X := by
    have : 9 / 4 ≤ Y ^ (2 : ℕ) := by nlinarith only [hY64]
    calc 9 / 8 * (2 * Y) = (9 / 4) * Y := by ring
      _ ≤ Y ^ (2 : ℕ) * Y := mul_le_mul_of_nonneg_right this hY0.le
      _ = X := by rw [← hY3]; ring
  have hlog_Y8_ge : Real.log X / 6 ≤ Real.log (Y / 8) := by
    rw [Real.log_div hY0.ne' (by norm_num), hlogY]
    have hlog8_pos : 0 < Real.log 8 := Real.log_pos (by norm_num)
    linarith only [hL8, hlog8_pos]
  have hW₁_lo : (1 / 48) * Y / Real.log X ≤ (W₁.card : ℝ) := by
    have hlog_le : Real.log (4 / 3 * (Y / 8)) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by linarith only [hY_le_X, hY0])
    calc (1 / 48) * Y / Real.log X
        ≤ (1 / 48) * Y / Real.log (4 / 3 * (Y / 8)) :=
          div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by linarith only [hY64])) hlog_le
      _ = ((4 / 3 - 1) / 2) * (Y / 8) / Real.log (4 / 3 * (Y / 8)) := by ring
      _ ≤ (W₁.card : ℝ) := hw₁.1
  have hW₁_hi : (W₁.card : ℝ) ≤ (1 / 2) * Y / Real.log X := by
    calc (W₁.card : ℝ) ≤ (2 * (4 / 3 - 1)) * (Y / 8) / Real.log (Y / 8) := hw₁.2
      _ ≤ (2 * (4 / 3 - 1)) * (Y / 8) / (Real.log X / 6) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_Y8_ge
      _ = (1 / 2) * Y / Real.log X := by ring
  have hW₂_lo : (1 / 8) * Y / Real.log X ≤ (W₂.card : ℝ) := by
    have hlog_le : Real.log (9 / 8 * (2 * Y)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hY_le_X
    calc (1 / 8) * Y / Real.log X
        ≤ (1 / 8) * Y / Real.log (9 / 8 * (2 * Y)) :=
          div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by linarith only [hY64])) hlog_le
      _ = ((9 / 8 - 1) / 2) * (2 * Y) / Real.log (9 / 8 * (2 * Y)) := by ring
      _ ≤ (W₂.card : ℝ) := hw₂.1
  have hW₂_hi : (W₂.card : ℝ) ≤ 3 * Y / Real.log X := by
    have hlog2Y : Real.log X / 6 ≤ Real.log (2 * Y) :=
      hlog_Y8_ge.trans (Real.log_le_log (by positivity) (by linarith only [hY0]))
    calc (W₂.card : ℝ) ≤ (2 * (9 / 8 - 1)) * (2 * Y) / Real.log (2 * Y) := hw₂.2
      _ ≤ (2 * (9 / 8 - 1)) * (2 * Y) / (Real.log X / 6) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog2Y
      _ = 3 * Y / Real.log X := by ring
  have hpc_card : (pilotCofactors X).card = W₁.card * W₂.card := by
    rw [hpc_eq, card_image_of_injOn hinj_pq, card_product]
  have hfib_card_ge :
      (1 / 48) * (1 / 8) * (X : ℝ) ^ (2 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤
        ((pilotCofactors X).card : ℝ) := by
    rw [hpc_card, Nat.cast_mul]
    calc (1 / 48) * (1 / 8) * (X : ℝ) ^ (2 / 3 : ℝ) / Real.log X ^ (2 : ℕ)
        = ((1 / 48) * Y / Real.log X) * ((1 / 8) * Y / Real.log X) := by rw [← hY2]; ring
      _ ≤ (W₁.card : ℝ) * (W₂.card : ℝ) :=
          mul_le_mul hW₁_lo hW₂_lo (by positivity) (Nat.cast_nonneg _)
  have hpv_card_eq : (pilotVertices X).card =
      ∑ pq ∈ W₁ ×ˢ W₂,
        (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).card := by
    unfold pilotVertices fibreUnion
    rw [card_biUnion]
    · rw [hpc_eq, sum_image hinj_pq]
      refine sum_congr rfl fun pq hpq => ?_
      obtain ⟨hemp, hneg_eq⟩ := hfib_info pq hpq
      rw [hemp, empty_union, hneg_eq, card_image_of_injOn]
      intro r₁ _ r₂ _ heq
      obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
      have hp₁_pos := (hW₁_sub pq.1 hp₁W).1.pos
      have hp₂_pos := (hW₂_sub pq.2 hp₂W).1.pos
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp₁_pos hp₂_pos) heq
    · intro a₁ _ a₂ _ hne
      have hdis := (evenPrefixCofactor_complete_bipartite_fibres hX1).1 hne
      exact disjoint_left.mpr fun n hn₁ hn₂ => by
        rcases mem_union.mp hn₁ with hp₁ | hn₁' <;> rcases mem_union.mp hn₂ with hp₂ | hn₂'
        · exact disjoint_left.mp hdis.1 hp₁ hp₂
        · exact disjoint_left.mp (disjoint_posParity_negParity _)
            ((mem_filter.mp hp₁).1) ((mem_filter.mp hn₂').1)
        · exact disjoint_right.mp (disjoint_posParity_negParity _)
            ((mem_filter.mp hn₁').1) ((mem_filter.mp hp₂).1)
        · exact disjoint_left.mp hdis.2 hn₁' hn₂'
  have hW₃_bounds : ∀ pq ∈ W₁ ×ˢ W₂,
      (4 / 3) * Y / Real.log X ≤
        ((windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).card : ℝ) ∧
      ((windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).card : ℝ) ≤
        48 * Y / Real.log X := by
    rintro ⟨p₁, p₂⟩ hpq
    dsimp only
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    dsimp only at hp₁W hp₂W
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := hW₁_sub p₁ hp₁W
    obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := hW₂_sub p₂ hp₂W
    have hpq_r : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hpq_up : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) := by
      calc (p₁ : ℝ) * p₂ ≤ (4 / 3 * (Y / 8)) * (9 / 8 * (2 * Y)) :=
            mul_le_mul hp₁_hi hp₂_hi (Nat.cast_nonneg _) (by positivity)
        _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
    have hpq_lo : (1 / 4) * Y ^ (2 : ℕ) ≤ (p₁ : ℝ) * p₂ := by
      calc (1 / 4) * Y ^ (2 : ℕ) = (Y / 8) * (2 * Y) := by ring
        _ ≤ (p₁ : ℝ) * p₂ := mul_le_mul hp₁_lo.le hp₂_lo.le (by positivity) (Nat.cast_nonneg _)
    have hXpq_lo : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
      rw [le_div_iff₀ hpq_r]
      calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hpq_up (by positivity)
        _ = X := by rw [← hY3]; ring
    have hXpq_hi : (X : ℝ) / ((p₁ : ℝ) * p₂) ≤ 4 * Y := by
      rw [div_le_iff₀ hpq_r]
      calc (X : ℝ) = 4 * Y * ((1 / 4) * Y ^ (2 : ℕ)) := by rw [← hY3]; ring
        _ ≤ 4 * Y * ((p₁ : ℝ) * p₂) := mul_le_mul_of_nonneg_left hpq_lo (by positivity)
    have hw := hw₃ ((X : ℝ) / ((p₁ : ℝ) * p₂)) hXpq_lo
    constructor
    · have h2leX : 2 * ((X : ℝ) / ((p₁ : ℝ) * p₂)) ≤ X := by
        rw [mul_div_assoc', div_le_iff₀ hpq_r, mul_comm (2 : ℝ) X]
        have hpq2 : (2 : ℝ) ≤ (p₁ : ℝ) * p₂ := by nlinarith only [hpq_lo, hY64]
        exact mul_le_mul_of_nonneg_left hpq2 hX0.le
      have hlog_le : Real.log (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂))) ≤ Real.log X :=
        Real.log_le_log (by positivity) h2leX
      calc (4 / 3) * Y / Real.log X
          ≤ ((2 - 1) / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) / Real.log X :=
            div_le_div_of_nonneg_right (by linarith only [hXpq_lo]) hLX.le
        _ ≤ ((2 - 1) / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) /
              Real.log (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂))) :=
            div_le_div_of_nonneg_left (by positivity)
              (Real.log_pos (by linarith only [hXpq_lo, hY64])) hlog_le
        _ ≤ _ := hw.1
    · have hlog_ge : Real.log X / 6 ≤ Real.log ((X : ℝ) / ((p₁ : ℝ) * p₂)) :=
        hlog_Y8_ge.trans (Real.log_le_log (by positivity) (by linarith only [hXpq_lo, hY0]))
      calc ((windowPrimes ((X : ℝ) / ((p₁ : ℝ) * p₂)) (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂)))).card : ℝ)
          ≤ (2 * (2 - 1)) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) /
              Real.log ((X : ℝ) / ((p₁ : ℝ) * p₂)) := hw.2
        _ ≤ (2 * (2 - 1)) * (4 * Y) / (Real.log X / 6) :=
            (div_le_div_of_nonneg_right (by linarith only [hXpq_hi]) (by linarith only [hlog_ge, hLX])).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_ge)
        _ = 48 * Y / Real.log X := by ring
  have hpv_lo :
      (1 / 48) * (1 / 8) * (4 / 3) * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
        ((pilotVertices X).card : ℝ) := by
    rw [hpv_card_eq, Nat.cast_sum]
    calc (1 / 48) * (1 / 8) * (4 / 3) * (X : ℝ) / Real.log X ^ (3 : ℕ)
        = (((1 / 48) * Y / Real.log X) * ((1 / 8) * Y / Real.log X)) *
            ((4 / 3) * Y / Real.log X) := by rw [← hY3]; ring
      _ ≤ ((W₁.card : ℝ) * (W₂.card : ℝ)) * ((4 / 3) * Y / Real.log X) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hW₁_lo hW₂_lo (by positivity) (Nat.cast_nonneg _)) (by positivity)
      _ = ∑ _pq ∈ W₁ ×ˢ W₂, ((4 / 3) * Y / Real.log X) := by
          rw [sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ _ := sum_le_sum fun pq hpq => (hW₃_bounds pq hpq).1
  have hpv_hi : ((pilotVertices X).card : ℝ) ≤ 5184 * (X : ℝ) / Real.log X ^ (3 : ℕ) := by
    rw [hpv_card_eq, Nat.cast_sum]
    calc (∑ pq ∈ W₁ ×ˢ W₂,
            ((windowPrimes ((X : ℝ) / (pq.1 * pq.2))
              (2 * ((X : ℝ) / (pq.1 * pq.2)))).card : ℝ))
        ≤ ∑ _pq ∈ W₁ ×ˢ W₂, (48 * Y / Real.log X) :=
          sum_le_sum fun pq hpq => (hW₃_bounds pq hpq).2
      _ = ((W₁.card : ℝ) * (W₂.card : ℝ)) * (48 * Y / Real.log X) := by
          rw [sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ (((1 / 2) * Y / Real.log X) * (3 * Y / Real.log X)) * (48 * Y / Real.log X) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hW₁_hi hW₂_hi (Nat.cast_nonneg _) (by positivity)) (by positivity)
      _ ≤ 5184 * (X : ℝ) / Real.log X ^ (3 : ℕ) := by
          have h1 : (((1 / 2) * Y / Real.log X) * (3 * Y / Real.log X)) * (48 * Y / Real.log X) =
              72 * Y ^ (3 : ℕ) / Real.log X ^ (3 : ℕ) := by ring
          rw [h1, hY3]
          exact div_le_div_of_nonneg_right (by linarith only [hX0]) (by positivity)
  exact ⟨hfib_card_ge, hW₂_hi, hfib_info, hall_emp, hpv_lo, hpv_hi⟩

private lemma pilot_root_clearing_step (X : ℕ) (Y : ℝ) (W₁ W₂ : Finset ℕ)
    (hX216 : 216 ≤ (X : ℝ)) (hY64 : 64 ≤ Y)
    (hY3 : Y ^ (3 : ℕ) = (X : ℝ)) (hY2 : Y ^ (2 : ℕ) = (X : ℝ) ^ (2 / 3 : ℝ))
    (hL80 : 80 ≤ Real.log X)
    (hW₁_sub : ∀ p ∈ W₁, p.Prime ∧ Y / 8 < (p : ℝ) ∧ (p : ℝ) ≤ 4 / 3 * (Y / 8))
    (hW₂_sub : ∀ p ∈ W₂, p.Prime ∧ 2 * Y < (p : ℝ) ∧ (p : ℝ) ≤ 9 / 8 * (2 * Y))
    (hW₂_hi : (W₂.card : ℝ) ≤ 3 * Y / Real.log X)
    (hpc_eq : pilotCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2)
    (hfib_info : ∀ pq ∈ W₁ ×ˢ W₂,
      fibrePos X (pq.1 * pq.2) = ∅ ∧
      fibreNeg X (pq.1 * pq.2) =
        (windowPrimes ((X : ℝ) / (pq.1 * pq.2)) (2 * ((X : ℝ) / (pq.1 * pq.2)))).image
          (fun p₃ => pq.1 * pq.2 * p₃))
    (hall_emp : ∀ a ∈ pilotCofactors X, fibrePos X a = ∅)
    (hup_win : ∀ R : ℝ, 2 * Y ≤ R → ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R →
      R / Real.log R ^ (0 : ℝ) ≤ v - u →
      ((windowPrimes u v).card : ℝ) ≤ (1 + 1 / 2) * (v - u) / Real.log R)
    (hlo_win : ∀ R : ℝ, 12 * (X : ℝ) ^ (2 / 3 : ℝ) ≤ R → ∀ q : ℝ, 2 ≤ q → q ≤ 5 →
      ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ (0 : ℝ) ≤ v - u →
      (1 - 1 / 2) * (v - u) / (q * Real.log R) ≤ ((windowPrimes (u / q) (v / q)).card : ℝ))
    (φ : ℕ → ℕ)
    (hφ_inj : Set.InjOn φ ↑(windowPrimes X (2 * X)))
    (hφ_shape : ∀ p ∈ windowPrimes X (2 * X),
      X < φ p ∧ φ p ≤ 2 * X ∧ ∃ q r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧ φ p = q * r)
    (hφ_sign : ∀ p ∈ windowPrimes X (2 * X), μ p = -1 ∧ μ (φ p) = 1)
    (τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X))) :
    pilotVertices X ⊆ τ₀.unmatchedSet ∧
    ∃ τ_star : FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)),
      τ₀.movedSet ∪ pilotVertices X ⊆ τ_star.movedSet ∧
      Disjoint τ_star.unmatchedSet (pilotVertices X) ∧
      τ_star.unmatchedSet.card + 2 * (pilotVertices X).card ≤ τ₀.unmatchedSet.card := by
  have hX0 : (0 : ℝ) < X := by linarith only [hX216]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX216])
  have hY0 : 0 < Y := by linarith only [hY64]
  have hlogY : Real.log Y = Real.log X / 3 := by
    have : Real.log (Y ^ (3 : ℕ)) = Real.log X := by rw [hY3]
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hpv_neg : ∀ n ∈ pilotVertices X,
      n ∈ negParity (Ioc X (2 * X)) ∧ fibrePos X (evenPrefixCofactor n) = ∅ := by
    intro n hn
    unfold pilotVertices fibreUnion at hn
    obtain ⟨a, ha, hna⟩ := mem_biUnion.mp hn
    rw [hall_emp a ha, empty_union] at hna
    exact ⟨(mem_filter.mp hna).1, (mem_filter.mp hna).2.symm ▸ hall_emp a ha⟩
  have hpv_unm : pilotVertices X ⊆ τ₀.unmatchedSet := by
    intro n hn
    obtain ⟨hn_neg, hemp⟩ := hpv_neg n hn
    have hn_sq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_right _ hn_neg
    rw [τ₀.unmatchedSet_eq_sdiff, mem_sdiff]
    refine ⟨hn_sq, fun hmv => ?_⟩
    rw [τ₀.movedSet_eq_union, mem_union] at hmv
    rcases hmv with hpos | hneg
    · exact disjoint_left.mp (disjoint_posParity_negParity _) (τ₀.movedPos_subset hpos) hn_neg
    · obtain ⟨m, hm_pos, rfl⟩ := mem_image.mp (τ₀.image_movedPos.symm ▸ hneg)
      have hadj := τ₀.adj_pos m (mem_filter.mp hm_pos).2
        (mem_filter.mp (τ₀.movedPos_subset hm_pos)).2
      have hm_fib : m ∈ fibrePos X (evenPrefixCofactor (τ₀ m)) :=
        mem_filter.mpr ⟨τ₀.movedPos_subset hm_pos, hadj.2⟩
      rw [hemp] at hm_fib
      exact notMem_empty m hm_fib
  let D_p₁ : ℕ → Finset ℕ := fun p₁ =>
    W₂.biUnion fun p₂ =>
      (windowPrimes ((X : ℝ) / (p₁ * p₂)) (2 * ((X : ℝ) / (p₁ * p₂)))).image (p₂ * ·)
  have hD_cap : ∀ p₁ ∈ W₁, (D_p₁ p₁).card ≤
      (windowPrimes ((X : ℝ) / p₁) (2 * ((X : ℝ) / p₁))).card := by
    intro p₁ hp₁W
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := hW₁_sub p₁ hp₁W
    have hp₁_r : (0 : ℝ) < p₁ := by exact_mod_cast hp₁_pr.pos
    have hXp₁_lo : 6 * Y ^ (2 : ℕ) ≤ (X : ℝ) / p₁ := by
      rw [le_div_iff₀ hp₁_r]
      calc 6 * Y ^ (2 : ℕ) * p₁ ≤ 6 * Y ^ (2 : ℕ) * (Y / 6) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = X := by rw [← hY3]; ring
    have hD_le : ((D_p₁ p₁).card : ℝ) ≤
        (W₂.card : ℝ) * (6 * (X : ℝ) / (p₁ * Y * Real.log X)) := by
      have hn : (D_p₁ p₁).card ≤
          ∑ p₂ ∈ W₂, (windowPrimes ((X : ℝ) / (p₁ * p₂)) (2 * ((X : ℝ) / (p₁ * p₂)))).card :=
        card_biUnion_le.trans (sum_le_sum fun p₂ _ => card_image_le)
      refine (Nat.cast_le.mpr hn).trans ?_
      rw [Nat.cast_sum]
      refine (sum_le_sum fun p₂ hp₂W => ?_).trans_eq (by rw [sum_const, nsmul_eq_mul])
      obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := hW₂_sub p₂ hp₂W
      have hpq_r : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
      have hU_lo : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
        rw [le_div_iff₀ hpq_r]
        have : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) :=
          calc (p₁ : ℝ) * p₂ ≤ (Y / 6) * (9 / 4 * Y) :=
                mul_le_mul (by linarith only [hp₁_hi]) (by linarith only [hp₂_hi])
                  (Nat.cast_nonneg _) (by positivity)
            _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
        calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = X := by rw [← hY3]; ring
      have hup := hup_win ((X : ℝ) / ((p₁ : ℝ) * p₂)) (by linarith only [hU_lo, hY0])
        ((X : ℝ) / ((p₁ : ℝ) * p₂)) (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂)))
        le_rfl (by linarith [div_pos hX0 hpq_r]) le_rfl
        (by rw [Real.rpow_zero, div_one]; linarith [div_pos hX0 hpq_r])
      have hlog_ge : Real.log X / 3 ≤ Real.log ((X : ℝ) / ((p₁ : ℝ) * p₂)) := by
        rw [← hlogY]
        exact Real.log_le_log hY0 (by linarith only [hU_lo, hY0])
      calc ((windowPrimes ((X : ℝ) / ((p₁ : ℝ) * p₂)) (2 * ((X : ℝ) / ((p₁ : ℝ) * p₂)))).card : ℝ)
          ≤ (3 / 2) * ((X : ℝ) / ((p₁ : ℝ) * p₂)) /
              Real.log ((X : ℝ) / ((p₁ : ℝ) * p₂)) := hup.trans_eq (by ring)
        _ ≤ (3 / 2) * ((X : ℝ) / ((p₁ : ℝ) * (2 * Y))) / (Real.log X / 3) := by
            refine (div_le_div_of_nonneg_right ?_ (by linarith only [hlog_ge, hLX])).trans
              (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog_ge)
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left hX0.le (by positivity)
                (mul_le_mul_of_nonneg_left hp₂_lo.le hp₁_r.le))
              (by positivity)
        _ = 6 * (X : ℝ) / (p₁ * Y * Real.log X) * (3 / 8) := by ring
        _ ≤ 6 * (X : ℝ) / (p₁ * Y * Real.log X) := by
            have hnn : 0 ≤ 6 * (X : ℝ) / (p₁ * Y * Real.log X) := by positivity
            linarith only [hnn]
    have hwin_ge : (1 / 4) * ((X : ℝ) / p₁) / Real.log X ≤
        ((windowPrimes ((X : ℝ) / p₁) (2 * ((X : ℝ) / p₁))).card : ℝ) := by
      have h2R : 12 * (X : ℝ) ^ (2 / 3 : ℝ) ≤ 2 * ((X : ℝ) / p₁) := by
        rw [← hY2]; linarith only [hXp₁_lo]
      have hXp₁_pos : 0 < (X : ℝ) / p₁ := div_pos hX0 hp₁_r
      have hlo := hlo_win (2 * ((X : ℝ) / p₁)) h2R 2 (by norm_num) (by norm_num)
        (2 * ((X : ℝ) / p₁)) (4 * ((X : ℝ) / p₁))
        le_rfl (by linarith only [hXp₁_pos]) (by linarith only [hXp₁_pos])
        (by rw [Real.rpow_zero, div_one]; linarith only [hXp₁_pos])
      have hd1 : 2 * ((X : ℝ) / p₁) / 2 = (X : ℝ) / p₁ := by ring
      have hd2 : 4 * ((X : ℝ) / p₁) / 2 = 2 * ((X : ℝ) / p₁) := by ring
      rw [hd1, hd2] at hlo
      have h2leX : 2 * ((X : ℝ) / p₁) ≤ X := by
        rw [mul_div_assoc', div_le_iff₀ hp₁_r, mul_comm (2 : ℝ) X]
        have hp₁_2 : (2 : ℝ) ≤ p₁ := by linarith only [hp₁_lo, hY64]
        exact mul_le_mul_of_nonneg_left hp₁_2 hX0.le
      have hlog_le : Real.log (2 * ((X : ℝ) / p₁)) ≤ Real.log X :=
        Real.log_le_log (by positivity) h2leX
      have h2Xp₁_gt1 : 1 < 2 * ((X : ℝ) / p₁) := by nlinarith only [hXp₁_lo, hY64]
      calc (1 / 4) * ((X : ℝ) / p₁) / Real.log X
          ≤ (1 - 1 / 2) * (4 * ((X : ℝ) / p₁) - 2 * ((X : ℝ) / p₁)) /
              (2 * Real.log (2 * ((X : ℝ) / p₁))) := by
            have hnum : (1 - 1 / 2) * (4 * ((X : ℝ) / p₁) - 2 * ((X : ℝ) / p₁)) /
                (2 * Real.log (2 * ((X : ℝ) / p₁))) =
                (1 / 2) * ((X : ℝ) / p₁) / Real.log (2 * ((X : ℝ) / p₁)) := by ring
            rw [hnum]
            exact (div_le_div_of_nonneg_right (by linarith only [hXp₁_pos]) hLX.le).trans
              (div_le_div_of_nonneg_left (by positivity) (Real.log_pos h2Xp₁_gt1) hlog_le)
        _ ≤ _ := hlo
    have hcomp : ((D_p₁ p₁).card : ℝ) ≤
        ((windowPrimes ((X : ℝ) / p₁) (2 * ((X : ℝ) / p₁))).card : ℝ) := by
      have hfac : 18 / Real.log X ≤ 1 / 4 := by
        rw [div_le_iff₀ hLX]; linarith only [hL80]
      calc ((D_p₁ p₁).card : ℝ)
          ≤ (3 * Y / Real.log X) * (6 * (X : ℝ) / (p₁ * Y * Real.log X)) :=
            hD_le.trans (mul_le_mul_of_nonneg_right hW₂_hi (by positivity))
        _ = (18 / Real.log X) * (((X : ℝ) / p₁) / Real.log X) := by field_simp; ring
        _ ≤ (1 / 4) * (((X : ℝ) / p₁) / Real.log X) :=
            mul_le_mul_of_nonneg_right hfac (by positivity)
        _ = (1 / 4) * ((X : ℝ) / p₁) / Real.log X := by ring
        _ ≤ _ := hwin_ge
    exact_mod_cast hcomp
  let P_root := windowPrimes X (2 * X)
  let I_pil : Finset (ℕ × ℕ) :=
    W₁.biUnion fun p₁ => (range (D_p₁ p₁).card).image fun i => (p₁, i)
  let W_sup : ℕ → Finset ℕ := fun p₁ => windowPrimes ((X : ℝ) / p₁) (2 * ((X : ℝ) / p₁))
  let f₁ : P_root ⊕ I_pil → ℕ := Sum.elim
    (fun p => φ p.1)
    (fun idx => idx.1.1 * finsetEntry (W_sup idx.1.1) idx.1.2)
  let g₁ : P_root ⊕ I_pil → ℕ := Sum.elim
    (fun p => p.1)
    (fun idx => idx.1.1 * finsetEntry (D_p₁ idx.1.1) idx.1.2)
  have hroot_stem : ∀ p : P_root,
      maxPrimeStem (φ p.1) ≤ 5 ∧ (φ p.1).primeFactors.card = 2 := by
    intro p
    obtain ⟨_, _, q, r, hq235, hrp, h5r, heq⟩ := hφ_shape p.1 p.2
    have hqp : q.Prime := by rcases hq235 with rfl | rfl | rfl <;> decide
    have htop : ∀ d ∈ q.primeFactors, d < r := fun d hd =>
      (Nat.le_of_dvd hqp.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt (by omega)
    rw [heq, maxPrimeStem_mul_prime hqp.ne_zero hrp htop,
      card_primeFactors_mul_larger_prime hqp.ne_zero hrp htop, hqp.primeFactors, card_singleton]
    rcases hq235 with rfl | rfl | rfl <;> omega
  have hpil_info : ∀ idx : I_pil,
      let p₁ := idx.1.1; let i := idx.1.2
      let p := finsetEntry (W_sup p₁) i
      let w := finsetEntry (D_p₁ p₁) i
      5 < p₁ ∧ p₁.Prime ∧ p.Prime ∧ p₁ < p ∧
        maxPrimeStem (p₁ * p) = p₁ ∧ (p₁ * p).primeFactors.card = 2 ∧
        maxPrimeStem (maxPrimeStem (p₁ * w)) = p₁ ∧
        p₁ * p ∈ posParity (Ioc X (2 * X)) ∧
        p₁ * w ∈ negParity (Ioc X (2 * X)) ∧
        GlobalDyadicOneTwoRel (p₁ * p) (p₁ * w) ∧
        ¬ (p₁ * w).Prime := by
    intro idx
    obtain ⟨p₁, hp₁W, hmem_i⟩ := mem_biUnion.mp idx.2
    obtain ⟨i, hi_rng, hpair⟩ := mem_image.mp hmem_i
    have hp₁_eq : idx.1.1 = p₁ := (Prod.ext_iff.mp hpair.symm).1
    have hi_eq : idx.1.2 = i := (Prod.ext_iff.mp hpair.symm).2
    dsimp only
    rw [hp₁_eq, hi_eq]
    have hi_lt : i < (D_p₁ p₁).card := mem_range.mp hi_rng
    have hi_sup : i < (W_sup p₁).card := hi_lt.trans_le (hD_cap p₁ hp₁W)
    obtain ⟨hp₁_pr, hp₁_lo, hp₁_hi⟩ := hW₁_sub p₁ hp₁W
    have h5_p₁ : 5 < p₁ := by exact_mod_cast (by linarith [hY64, hp₁_lo] : (5 : ℝ) < p₁)
    have hp₁_r : (0 : ℝ) < p₁ := by exact_mod_cast hp₁_pr.pos
    have hp_win := finsetEntry_mem hi_sup
    obtain ⟨hpp, hp_lo, hp_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp_win
    have hXp₁_gt : (p₁ : ℝ) ≤ (X : ℝ) / p₁ := by
      rw [le_div_iff₀ hp₁_r]
      calc (p₁ : ℝ) * p₁ ≤ (Y / 6) * (Y / 6) :=
            mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg _) (by positivity)
        _ ≤ X := by rw [← hY3]; nlinarith [hY64]
    have hp₁_lt_p : p₁ < finsetEntry (W_sup p₁) i :=
      by exact_mod_cast hXp₁_gt.trans_lt hp_lo
    have htop_p : ∀ d ∈ p₁.primeFactors, d < finsetEntry (W_sup p₁) i := fun d hd =>
      (Nat.le_of_dvd hp₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hp₁_lt_p
    have hw_mem := finsetEntry_mem hi_lt
    obtain ⟨p₂, hp₂W, hr_img⟩ := mem_biUnion.mp hw_mem
    obtain ⟨p₃, hp₃_win, hw_eq⟩ := mem_image.mp hr_img
    obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := hW₂_sub p₂ hp₂W
    obtain ⟨hp₃_pr, hp₃_lo, hp₃_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₃_win
    have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast (by linarith : (p₁ : ℝ) < p₂)
    have hpq_r : (0 : ℝ) < (p₁ : ℝ) * p₂ := by exact_mod_cast Nat.mul_pos hp₁_pr.pos hp₂_pr.pos
    have hp₂_lt_p₃ : p₂ < p₃ := by
      have hlow_pq : (8 / 3) * Y ≤ (X : ℝ) / ((p₁ : ℝ) * p₂) := by
        rw [le_div_iff₀ hpq_r]
        have : (p₁ : ℝ) * p₂ ≤ (3 / 8) * Y ^ (2 : ℕ) :=
          calc (p₁ : ℝ) * p₂ ≤ (Y / 6) * (9 / 4 * Y) :=
                mul_le_mul (by linarith) (by linarith) (Nat.cast_nonneg _) (by positivity)
            _ = (3 / 8) * Y ^ (2 : ℕ) := by ring
        calc (8 / 3) * Y * ((p₁ : ℝ) * p₂) ≤ (8 / 3) * Y * ((3 / 8) * Y ^ (2 : ℕ)) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = X := by rw [← hY3]; ring
      exact_mod_cast (show (p₂ : ℝ) < p₃ by linarith)
    have htop_p₂ : ∀ d ∈ p₁.primeFactors, d < p₂ := fun d hd =>
      (Nat.le_of_dvd hp₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hp₁_lt_p₂
    have hpos_Ioc : p₁ * finsetEntry (W_sup p₁) i ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hp₁_r] at hp_lo
      rw [mul_div_assoc', le_div_iff₀ hp₁_r] at hp_hi
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < ((p₁ * finsetEntry (W_sup p₁) i : ℕ) : ℝ) by push_cast; linarith)
      · exact_mod_cast (show ((p₁ * finsetEntry (W_sup p₁) i : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)
    have hneg_Ioc : p₁ * finsetEntry (D_p₁ p₁) i ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hpq_r] at hp₃_lo
      rw [mul_div_assoc', le_div_iff₀ hpq_r] at hp₃_hi
      rw [← hw_eq, ← mul_assoc]
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < ((p₁ * p₂ * p₃ : ℕ) : ℝ) by push_cast; linarith)
      · exact_mod_cast (show ((p₁ * p₂ * p₃ : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith)
    have hμ_pos : μ (p₁ * finsetEntry (W_sup p₁) i) = 1 := by
      rw [moebius_mul_larger_prime hp₁_pr.ne_zero hpp htop_p,
        ArithmeticFunction.moebius_apply_prime hp₁_pr]; norm_num
    have hμ_neg : μ (p₁ * finsetEntry (D_p₁ p₁) i) = -1 := by
      rw [← hw_eq, ← mul_assoc,
        moebius_mul_larger_prime (Nat.mul_ne_zero hp₁_pr.ne_zero hp₂_pr.ne_zero) hp₃_pr
          (primeFactors_lt_of_mul_prime hp₁_pr.ne_zero hp₂_pr hp₂_lt_p₃ htop_p₂),
        moebius_mul_larger_prime hp₁_pr.ne_zero hp₂_pr htop_p₂,
        ArithmeticFunction.moebius_apply_prime hp₁_pr]; norm_num
    refine ⟨h5_p₁, hp₁_pr, hpp, hp₁_lt_p,
      maxPrimeStem_mul_prime hp₁_pr.ne_zero hpp htop_p,
      by rw [card_primeFactors_mul_larger_prime hp₁_pr.ne_zero hpp htop_p,
          hp₁_pr.primeFactors, card_singleton],
      by rw [← hw_eq]; exact (maxPrimeStem_mul_pair hp₁_pr.ne_zero hp₂_pr hp₃_pr hp₂_lt_p₃ htop_p₂).2,
      mem_filter.mpr ⟨hpos_Ioc, hμ_pos⟩,
      mem_filter.mpr ⟨hneg_Ioc, hμ_neg⟩,
      ⟨squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_pos]; decide),
        squarefree_iff_moebius_ne_zero.mpr (by rw [hμ_neg]; decide),
        by omega, p₁, finsetEntry (W_sup p₁) i, p₂, p₃, hpp, hp₂_pr, hp₃_pr, hp₂_lt_p₃,
        Or.inl ⟨rfl, congrArg (p₁ * ·) hw_eq.symm⟩⟩,
      ?_⟩
    rw [← hw_eq]
    have hw_gt1 : 1 < p₂ * p₃ := by
      have := hp₂_pr.two_le; have := hp₃_pr.two_le; nlinarith
    exact Nat.not_prime_mul hp₁_pr.ne_one hw_gt1.ne'
  have hf₁_inj : Function.Injective f₁ := by
    rintro (p | idx₁) (p' | idx₂) heq
    · exact congrArg Sum.inl (Subtype.ext (hφ_inj p.2 p'.2 heq))
    · dsimp [f₁] at heq
      have h1 := (hroot_stem p).1
      have h2 := (hpil_info idx₂).2.2.2.2.1
      have h5 := (hpil_info idx₂).1
      rw [heq, h2] at h1; omega
    · dsimp [f₁] at heq
      have h1 := (hroot_stem p').1
      have h2 := (hpil_info idx₁).2.2.2.2.1
      have h5 := (hpil_info idx₁).1
      rw [← heq, h2] at h1; omega
    · dsimp [f₁] at heq
      have hs₁ := (hpil_info idx₁).2.2.2.2.1
      have hs₂ := (hpil_info idx₂).2.2.2.2.1
      have hp₁_eq : idx₁.1.1 = idx₂.1.1 := hs₁.symm.trans ((congrArg maxPrimeStem heq).trans hs₂)
      obtain ⟨p₁, hp₁W, hm₁⟩ := mem_biUnion.mp idx₁.2
      obtain ⟨i₁, hi₁, hp₁_pair⟩ := mem_image.mp hm₁
      obtain ⟨p₁', _, hm₂⟩ := mem_biUnion.mp idx₂.2
      obtain ⟨i₂, hi₂, hp₂_pair⟩ := mem_image.mp hm₂
      have h_p1 : idx₁.1.1 = p₁ := (Prod.ext_iff.mp hp₁_pair.symm).1
      have h_i1 : idx₁.1.2 = i₁ := (Prod.ext_iff.mp hp₁_pair.symm).2
      have h_p2 : idx₂.1.1 = p₁' := (Prod.ext_iff.mp hp₂_pair.symm).1
      have h_i2 : idx₂.1.2 = i₂ := (Prod.ext_iff.mp hp₂_pair.symm).2
      have hp_same : p₁ = p₁' := h_p1.symm.trans (hp₁_eq.trans h_p2)
      subst hp_same
      rw [h_p1, h_p2, h_i1, h_i2] at heq
      have hi₁_sup := (mem_range.mp hi₁).trans_le (hD_cap p₁ hp₁W)
      have hi₂_sup := (mem_range.mp hi₂).trans_le (hD_cap p₁ hp₁W)
      have hi_eq := finsetEntry_inj hi₁_sup hi₂_sup
        (Nat.eq_of_mul_eq_mul_left (hpil_info idx₁).2.1.pos (h_p1 ▸ heq))
      subst hi_eq
      exact congrArg Sum.inr (Subtype.ext (hp₁_pair.symm.trans hp₂_pair))
  have hg₁_inj : Function.Injective g₁ := by
    rintro (p | idx₁) (p' | idx₂) heq
    · exact congrArg Sum.inl (Subtype.ext heq)
    · dsimp [g₁] at heq
      have hp_pr := ((mem_windowPrimes (by positivity) (by positivity)).mp p.2).1
      exact False.elim ((hpil_info idx₂).2.2.2.2.2.2.2.2.2.2 (heq ▸ hp_pr))
    · dsimp [g₁] at heq
      have hp_pr := ((mem_windowPrimes (by positivity) (by positivity)).mp p'.2).1
      exact False.elim ((hpil_info idx₁).2.2.2.2.2.2.2.2.2.2 (heq.symm ▸ hp_pr))
    · dsimp [g₁] at heq
      have hs₁ := (hpil_info idx₁).2.2.2.2.2.2.1
      have hs₂ := (hpil_info idx₂).2.2.2.2.2.2.1
      have hp₁_eq : idx₁.1.1 = idx₂.1.1 :=
        hs₁.symm.trans ((congrArg (fun n => maxPrimeStem (maxPrimeStem n)) heq).trans hs₂)
      obtain ⟨p₁, _, hm₁⟩ := mem_biUnion.mp idx₁.2
      obtain ⟨i₁, hi₁, hp₁_pair⟩ := mem_image.mp hm₁
      obtain ⟨p₁', _, hm₂⟩ := mem_biUnion.mp idx₂.2
      obtain ⟨i₂, hi₂, hp₂_pair⟩ := mem_image.mp hm₂
      have h_p1 : idx₁.1.1 = p₁ := (Prod.ext_iff.mp hp₁_pair.symm).1
      have h_i1 : idx₁.1.2 = i₁ := (Prod.ext_iff.mp hp₁_pair.symm).2
      have h_p2 : idx₂.1.1 = p₁' := (Prod.ext_iff.mp hp₂_pair.symm).1
      have h_i2 : idx₂.1.2 = i₂ := (Prod.ext_iff.mp hp₂_pair.symm).2
      have hp_same : p₁ = p₁' := h_p1.symm.trans (hp₁_eq.trans h_p2)
      subst hp_same
      rw [h_p1, h_p2, h_i1, h_i2] at heq
      have hi_eq := finsetEntry_inj (mem_range.mp hi₁) (mem_range.mp hi₂)
        (Nat.eq_of_mul_eq_mul_left (hpil_info idx₁).2.1.pos (h_p1 ▸ heq))
      subst hi_eq
      exact congrArg Sum.inr (Subtype.ext (hp₁_pair.symm.trans hp₂_pair))
  let partner₁ : ℕ → ℕ := fun m =>
    if hex : ∃ u : P_root ⊕ I_pil, f₁ u = m then g₁ hex.choose else 0
  have hpart₁_eq : ∀ u : P_root ⊕ I_pil, partner₁ (f₁ u) = g₁ u := by
    intro u
    have hex : ∃ v : P_root ⊕ I_pil, f₁ v = f₁ u := ⟨u, rfl⟩
    simp only [partner₁, dif_pos hex]
    exact congrArg g₁ (hf₁_inj hex.choose_spec)
  have hend₁ : ∀ u : P_root ⊕ I_pil,
      f₁ u ∈ posParity (Ioc X (2 * X)) ∧
      g₁ u ∈ negParity (Ioc X (2 * X)) ∧
      GlobalDyadicOneTwoRel (f₁ u) (g₁ u) := by
    rintro (p | idx)
    · obtain ⟨hlo, hhi, q, r, hq235, hrp, h5r, heq⟩ := hφ_shape p.1 p.2
      obtain ⟨hpp, hp_lo, hp_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp p.2
      obtain ⟨hμp, hμφ⟩ := hφ_sign p.1 p.2
      have hqp : q.Prime := by rcases hq235 with rfl | rfl | rfl <;> decide
      have hqr : q < r := by rcases hq235 with rfl | rfl | rfl <;> omega
      exact ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlo, hhi⟩, hμφ⟩,
        mem_filter.mpr ⟨mem_Ioc.mpr ⟨by exact_mod_cast hp_lo, by exact_mod_cast hp_hi⟩, hμp⟩,
        ⟨squarefree_iff_moebius_ne_zero.mpr (by dsimp [f₁]; rw [hμφ]; decide),
          Irreducible.squarefree hpp, by dsimp [f₁, g₁]; omega,
          1, p.1, q, r, hpp, hqp, hrp, hqr,
          Or.inr ⟨by simp [g₁], by simpa [f₁] using heq⟩⟩⟩
    · have hi := hpil_info idx
      exact ⟨hi.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.1, hi.2.2.2.2.2.2.2.2.2.1⟩
  let M₁ : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2 * X)) :=
    { sources := Finset.univ.image f₁
      partner := partner₁
      sources_subset := fun x hx => by
        obtain ⟨u, _, rfl⟩ := mem_image.mp hx
        exact (hend₁ u).1
      injOn := fun x hx y hy heq => by
        obtain ⟨u, _, rfl⟩ := mem_image.mp hx
        obtain ⟨v, _, rfl⟩ := mem_image.mp hy
        rw [hpart₁_eq, hpart₁_eq] at heq
        exact congrArg f₁ (hg₁_inj heq)
      partner_mem := fun x hx => by
        obtain ⟨u, _, rfl⟩ := mem_image.mp hx
        rw [hpart₁_eq]; exact (hend₁ u).2.1
      adj := fun x hx => by
        obtain ⟨u, _, rfl⟩ := mem_image.mp hx
        rw [hpart₁_eq]; exact (hend₁ u).2.2 }
  let τ₁ := FactorizationInvolution.ofMatching M₁
  have hτ₁_targets : τ₁.movedNeg = Finset.univ.image g₁ := by
    change (FactorizationInvolution.ofMatching M₁).movedNeg = _
    rw [FactorizationInvolution.ofMatching_movedNeg]
    change (Finset.univ.image f₁).image partner₁ = Finset.univ.image g₁
    rw [image_image]
    exact image_congr fun u _ => hpart₁_eq u
  have hsemi₁ : ∀ m ∈ τ₁.movedPos, m.primeFactors.card = 2 := by
    intro m hm
    change m ∈ (FactorizationInvolution.ofMatching M₁).movedPos at hm
    rw [FactorizationInvolution.ofMatching_movedPos] at hm
    obtain ⟨p | idx, _, rfl⟩ := mem_image.mp hm
    · exact (hroot_stem p).2
    · exact (hpil_info idx).2.2.2.2.2.1
  have hprimes₁ : ∀ p ∈ τ₀.movedNeg, p.Prime → p ∈ τ₁.movedNeg := by
    intro p hp hpp
    obtain ⟨hp_Ioc, _⟩ := mem_filter.mp (τ₀.movedNeg_subset hp)
    obtain ⟨hp_lo, hp_hi⟩ := mem_Ioc.mp hp_Ioc
    have hp_root : p ∈ P_root :=
      (mem_windowPrimes (by positivity) (by positivity)).mpr
        ⟨hpp, by exact_mod_cast hp_lo, by exact_mod_cast hp_hi⟩
    rw [hτ₁_targets]
    exact mem_image.mpr ⟨Sum.inl ⟨p, hp_root⟩, mem_univ _, rfl⟩
  have hpv_in_τ₁ : pilotVertices X ⊆ τ₁.movedNeg := by
    intro n hn
    unfold pilotVertices fibreUnion at hn
    obtain ⟨a, ha_pc, hna⟩ := mem_biUnion.mp hn
    rw [hpc_eq] at ha_pc
    obtain ⟨⟨p₁, p₂⟩, hpq, rfl⟩ := mem_image.mp ha_pc
    obtain ⟨hemp, hneg_eq⟩ := hfib_info (p₁, p₂) hpq
    rw [hemp, empty_union, hneg_eq] at hna
    obtain ⟨p₃, hp₃_win, rfl⟩ := mem_image.mp hna
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    have hw_D : p₂ * p₃ ∈ D_p₁ p₁ :=
      mem_biUnion.mpr ⟨p₂, hp₂W, mem_image.mpr ⟨p₃, hp₃_win, rfl⟩⟩
    let j := ((D_p₁ p₁).orderIsoOfFin rfl).symm ⟨p₂ * p₃, hw_D⟩
    have hj_mem : (p₁, j.val) ∈ I_pil :=
      mem_biUnion.mpr ⟨p₁, hp₁W, mem_image.mpr ⟨j.val, mem_range.mpr j.isLt, rfl⟩⟩
    rw [hτ₁_targets]
    refine mem_image.mpr ⟨Sum.inr ⟨(p₁, j.val), hj_mem⟩, mem_univ _, ?_⟩
    dsimp [g₁]
    rw [mul_assoc]
    simp only [finsetEntry, dif_pos j.isLt]
    exact congrArg (fun x : D_p₁ p₁ => p₁ * (x : ℕ))
      (((D_p₁ p₁).orderIsoOfFin rfl).apply_symm_apply ⟨p₂ * p₃, hw_D⟩)
  obtain ⟨hpos_sub, hneg_sub, hred⟩ := resolveDoubleUse_unmatched_reduction τ₀ τ₁ hsemi₁ hprimes₁
  let τ_star := resolveDoubleUse (τ₀.mono fun h => h.1) τ₁
  have hpv_sdiff : pilotVertices X ⊆ τ₁.movedNeg \ τ₀.movedNeg := by
    intro n hn
    refine mem_sdiff.mpr ⟨hpv_in_τ₁ hn, fun hn0 => ?_⟩
    exact (mem_filter.mp hn0).2 (mem_filter.mp (hpv_unm hn)).2
  have hpv_card_le : (pilotVertices X).card ≤ (τ₁.movedNeg \ τ₀.movedNeg).card :=
    card_le_card hpv_sdiff
  have hcov : τ₀.movedSet ∪ pilotVertices X ⊆ τ_star.movedSet := by
    rw [τ₀.movedSet_eq_union, τ_star.movedSet_eq_union]
    refine union_subset (union_subset (hpos_sub.trans subset_union_left)
      ((subset_union_left.trans hneg_sub).trans subset_union_right)) ?_
    exact (hpv_in_τ₁.trans (subset_union_right.trans hneg_sub)).trans subset_union_right
  refine ⟨hpv_unm, τ_star, hcov, ?_, by dsimp only [τ_star]; omega⟩
  exact disjoint_left.mpr fun n hunm hpv =>
    (mem_filter.mp (hcov (mem_union_right _ hpv))).2 (mem_filter.mp hunm).2

/-- **Exact `Θ(X / (log X)³)` pilot debt, empty positive fibres, and strict global drop**:
there exist explicit constants `0 < c_fib`, `0 < c₁ < c₂`, and `X₀` such that for all `X ≥ X₀`:
1. `#(pilotCofactors X) ≥ c_fib * X^{2/3} / (log X)²` and `fibrePos X a = ∅` for all
   `a ∈ pilotCofactors X`;
2. `c₁ * X / (log X)³ ≤ #(pilotVertices X) ≤ c₂ * X / (log X)³`;
3. Every `OrderedFibreRel` involution `τ₀` on `(X, 2X]` leaves `pilotVertices X ⊆ τ₀.unmatchedSet`;
4. Combining `τ₀` with `{2, 3, 5}` root-prime clearing and cofactor-`p₁` cross-fibre pairing gives
   an explicit `FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X))` `τ_*` covering all
   of `τ₀.movedSet ∪ pilotVertices X` and satisfying
   `τ_*.unmatchedSet.card + 2 * (pilotVertices X).card ≤ τ₀.unmatchedSet.card`. -/
theorem eventually_pilotFibreClass_debt_and_strict_drop :
    ∃ (c_fib c₁ c₂ : ℝ), 0 < c_fib ∧ 0 < c₁ ∧ c₁ < c₂ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c_fib * (X : ℝ) ^ (2 / 3 : ℝ) / Real.log X ^ (2 : ℕ) ≤ ((pilotCofactors X).card : ℝ) ∧
      (∀ a ∈ pilotCofactors X, fibrePos X a = ∅) ∧
      c₁ * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ ((pilotVertices X).card : ℝ) ∧
      ((pilotVertices X).card : ℝ) ≤ c₂ * (X : ℝ) / Real.log X ^ (3 : ℕ) ∧
      (∀ τ₀ : FactorizationInvolution OrderedFibreRel (Ioc X (2 * X)),
        pilotVertices X ⊆ τ₀.unmatchedSet ∧
        ∃ τ_star : FactorizationInvolution GlobalDyadicOneTwoRel (Ioc X (2 * X)),
          τ₀.movedSet ∪ pilotVertices X ⊆ τ_star.movedSet ∧
          Disjoint τ_star.unmatchedSet (pilotVertices X) ∧
          τ_star.unmatchedSet.card + 2 * (pilotVertices X).card ≤ τ₀.unmatchedSet.card) := by
  obtain ⟨U₁, _, hw_43⟩ := exists_const_ratio_windowPrimes_bounds (α := 4 / 3) (by norm_num)
  obtain ⟨U₂, _, hw_98⟩ := exists_const_ratio_windowPrimes_bounds (α := 9 / 8) (by norm_num)
  obtain ⟨U₃, _, hw_2⟩ := exists_const_ratio_windowPrimes_bounds (α := 2) (by norm_num)
  obtain ⟨_, _, R₀_semi, hsemi_match⟩ := exists_prime_semiprime_matching (B := 1) (by norm_num)
  obtain ⟨R₀_up, _, hup_win⟩ := exists_card_windowPrimes_le (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨R₀_lo, _, hlo_win⟩ := exists_card_windowPrimes_div_ge (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hrpow3 : Tendsto (fun x : ℝ => x ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop,
      216 ≤ x ∧ 8 * U₁ ≤ x ^ (1 / 3 : ℝ) ∧ U₂ ≤ 2 * x ^ (1 / 3 : ℝ) ∧
      U₃ ≤ (8 / 3) * x ^ (1 / 3 : ℝ) ∧ 64 ≤ x ^ (1 / 3 : ℝ) ∧
      R₀_up ≤ 2 * x ^ (1 / 3 : ℝ) ∧ R₀_lo ≤ 12 * x ^ (2 / 3 : ℝ) ∧
      max (12 * Real.log 8) 80 ≤ Real.log x :=
    (eventually_ge_atTop 216).and ((hrpow3.eventually_ge_atTop _).and
      (((hrpow3.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually_ge_atTop _).and
        (((hrpow3.const_mul_atTop (by norm_num : (0 : ℝ) < 8 / 3)).eventually_ge_atTop _).and
          ((hrpow3.eventually_ge_atTop 64).and
            (((hrpow3.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).eventually_ge_atTop _).and
              ((((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
                  (by norm_num : (0 : ℝ) < 12)).eventually_ge_atTop _).and
                (Real.tendsto_log_atTop.eventually_ge_atTop _)))))))
  obtain ⟨X_cut, hX_cut⟩ := eventually_atTop.mp hev
  refine ⟨(1 / 48) * (1 / 8), (1 / 48) * (1 / 8) * (4 / 3), 5184,
    by positivity, by positivity, by norm_num,
    max (max 2 R₀_semi) ⌈X_cut⌉₊, fun X hX => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hX1 : 1 ≤ X := by omega
  have hX_semi : R₀_semi ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hX)
  have hX_ge : X_cut ≤ (X : ℝ) :=
    (Nat.le_ceil X_cut).trans (by exact_mod_cast (le_max_right _ _).trans hX)
  obtain ⟨hX216, hU1, hU2, hU3, hY64, hRup, hRlo, hLmax⟩ := hX_cut X hX_ge
  have hL8 : 12 * Real.log 8 ≤ Real.log X := (le_max_left _ _).trans hLmax
  have hL80 : 80 ≤ Real.log X := (le_max_right _ _).trans hLmax
  have hX0 : (0 : ℝ) < X := by linarith only [hX216]
  obtain ⟨Y, hY_def⟩ : ∃ Y : ℝ, Y = (X : ℝ) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hY_def] at hU1 hU2 hU3 hY64 hRup
  have hY0 : 0 < Y := by linarith only [hY64]
  have hY3 : Y ^ (3 : ℕ) = (X : ℝ) := by
    rw [hY_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  have hY2 : Y ^ (2 : ℕ) = (X : ℝ) ^ (2 / 3 : ℝ) := by
    rw [hY_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  obtain ⟨W₁, hW₁_def⟩ : ∃ W₁ : Finset ℕ, W₁ = windowPrimes (Y / 8) (4 / 3 * (Y / 8)) := ⟨_, rfl⟩
  obtain ⟨W₂, hW₂_def⟩ : ∃ W₂ : Finset ℕ, W₂ = windowPrimes (2 * Y) (9 / 8 * (2 * Y)) := ⟨_, rfl⟩
  have hpc_eq : pilotCofactors X = (W₁ ×ˢ W₂).image fun pq => pq.1 * pq.2 := by
    dsimp only [pilotCofactors]; rw [← hY_def, ← hW₁_def, ← hW₂_def]
  have hW₁_sub : ∀ p ∈ W₁, p.Prime ∧ Y / 8 < (p : ℝ) ∧ (p : ℝ) ≤ 4 / 3 * (Y / 8) := fun p hp => by
    rw [hW₁_def] at hp; exact (mem_windowPrimes (by positivity) (by positivity)).mp hp
  have hW₂_sub : ∀ p ∈ W₂, p.Prime ∧ 2 * Y < (p : ℝ) ∧ (p : ℝ) ≤ 9 / 8 * (2 * Y) := fun p hp => by
    rw [hW₂_def] at hp; exact (mem_windowPrimes (by positivity) (by positivity)).mp hp
  have hw₁ := hW₁_def ▸ hw_43 (Y / 8) (by linarith)
  have hw₂ := hW₂_def ▸ hw_98 (2 * Y) hU2
  obtain ⟨hfib_card_ge, hW₂_hi, hfib_info, hall_emp, hpv_lo, hpv_hi⟩ :=
    pilot_fibre_and_vertex_bounds X Y W₁ W₂ hX1 hX216 hY64 hY3 hY2 hL8 hW₁_sub hW₂_sub hpc_eq
      hw₁ hw₂ (fun u hu => hw_2 u (hU3.trans hu))
  obtain ⟨φ, hφ_inj, hφ_shape, _, hφ_sign, _, _, _, _⟩ := hsemi_match X hX_semi
  refine ⟨hfib_card_ge, hall_emp, hpv_lo, hpv_hi, fun τ₀ => ?_⟩
  exact pilot_root_clearing_step X Y W₁ W₂ hX216 hY64 hY3 hY2 hL80 hW₁_sub hW₂_sub hW₂_hi hpc_eq
    hfib_info hall_emp (fun R hR => hup_win R (hRup.trans hR))
    (fun R hR => hlo_win R (hRlo.trans hR)) φ hφ_inj hφ_shape hφ_sign τ₀

/-! ### 4. Larger invariants forcing debt persistence on restricted fibre classes -/

/-- **General fibre-class ordered attainment and signed-imbalance lower bound**:
for any `X ≥ 1` and any finite set `A` of ordered cofactors:
1. Every `OrderedFibreRel` involution on `fibreUnion X A` leaves at least
   `∑_{a ∈ A} |#fibrePos(X, a) - #fibreNeg(X, a)|` unmatched vertices, and an explicit rank-paired
   involution attains equality;
2. Every opposite-parity involution (along any relation `R`) confined to `fibreUnion X A` leaves at
   least `|∑_{a ∈ A} (#fibrePos(X, a) - #fibreNeg(X, a))|` unmatched vertices. -/
theorem fibreUnion_ordered_and_global_bounds {X : ℕ} (hX1 : 1 ≤ X) (A : Finset ℕ) :
    (∀ τ₀ : FactorizationInvolution OrderedFibreRel (fibreUnion X A),
      ∑ a ∈ A, |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| ≤
        (τ₀.unmatchedSet.card : ℤ)) ∧
    (∃ τ_opt : FactorizationInvolution OrderedFibreRel (fibreUnion X A),
      (τ_opt.unmatchedSet.card : ℤ) =
        ∑ a ∈ A, |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)|) ∧
    (∀ {R : ℕ → ℕ → Prop} (τ : FactorizationInvolution R (fibreUnion X A)),
      |∑ a ∈ A, (((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ))| ≤
        (τ.unmatchedSet.card : ℤ)) := by
  let F : ℕ → Finset ℕ := fun a => fibrePos X a ∪ fibreNeg X a
  have hdisj_F : (A : Set ℕ).PairwiseDisjoint F := by
    intro a₁ _ a₂ _ hne
    have h := (evenPrefixCofactor_complete_bipartite_fibres hX1).1 hne
    exact disjoint_left.mpr fun n hn₁ hn₂ => by
      rcases mem_union.mp hn₁ with hp₁ | hn₁' <;> rcases mem_union.mp hn₂ with hp₂ | hn₂'
      · exact disjoint_left.mp h.1 hp₁ hp₂
      · exact disjoint_left.mp (disjoint_posParity_negParity _)
          ((mem_filter.mp hp₁).1) ((mem_filter.mp hn₂').1)
      · exact disjoint_right.mp (disjoint_posParity_negParity _)
          ((mem_filter.mp hn₁').1) ((mem_filter.mp hp₂).1)
      · exact disjoint_left.mp h.2 hn₁' hn₂'
  have hsq_F : ∀ a : ℕ, squarefreeOf (F a) = F a := by
    intro a
    ext n
    simp only [squarefreeOf, mem_filter, F, mem_union]
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    rcases h with hp | hn
    · exact squarefree_iff_moebius_ne_zero.mpr (by rw [(mem_filter.mp (mem_filter.mp hp).1).2]; decide)
    · exact squarefree_iff_moebius_ne_zero.mpr (by rw [(mem_filter.mp (mem_filter.mp hn).1).2]; decide)
  have hpos_F : ∀ a : ℕ, posParity (F a) = fibrePos X a := by
    intro a; ext n; simp only [posParity, F, mem_filter, mem_union]
    constructor
    · rintro ⟨hp | hn, hμ⟩
      · exact hp
      · have := (mem_filter.mp (mem_filter.mp hn).1).2; omega
    · intro hp; exact ⟨Or.inl hp, (mem_filter.mp (mem_filter.mp hp).1).2⟩
  have hneg_F : ∀ a : ℕ, negParity (F a) = fibreNeg X a := by
    intro a; ext n; simp only [negParity, F, mem_filter, mem_union]
    constructor
    · rintro ⟨hp | hn, hμ⟩
      · have := (mem_filter.mp (mem_filter.mp hp).1).2; omega
      · exact hn
    · intro hn; exact ⟨Or.inr hn, (mem_filter.mp (mem_filter.mp hn).1).2⟩
  have hsum_F : ∀ a : ℕ,
      ∑ n ∈ F a, μ n = ((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ) := by
    intro a
    rw [sum_moebius_eq_card_pos_sub_neg, hpos_F, hneg_F]
  have hsub_Ioc : fibreUnion X A ⊆ Ioc X (2 * X) := by
    intro k hk
    obtain ⟨b, _, hkb⟩ := mem_biUnion.mp hk
    rcases mem_union.mp hkb with hbp | hbn
    · exact (mem_filter.mp (mem_filter.mp hbp).1).1
    · exact (mem_filter.mp (mem_filter.mp hbn).1).1
  refine ⟨?_, ?_, ?_⟩
  · intro τ₀
    have hunm_part : A.biUnion (fun a => τ₀.unmatchedSet ∩ F a) ⊆ τ₀.unmatchedSet :=
      biUnion_subset.mpr fun a _ => inter_subset_left
    have hdisj_unm : (A : Set ℕ).PairwiseDisjoint (fun a => τ₀.unmatchedSet ∩ F a) :=
      fun a₁ ha₁ a₂ ha₂ hne => Disjoint.mono inter_subset_right inter_subset_right (hdisj_F ha₁ ha₂ hne)
    have hcard_ge : ∑ a ∈ A, (τ₀.unmatchedSet ∩ F a).card ≤ τ₀.unmatchedSet.card := by
      rw [← card_biUnion hdisj_unm]
      exact card_le_card hunm_part
    have hcard_ge_z : (∑ a ∈ A, ((τ₀.unmatchedSet ∩ F a).card : ℤ)) ≤ (τ₀.unmatchedSet.card : ℤ) := by
      rw [← Nat.cast_sum]; exact_mod_cast hcard_ge
    refine (sum_le_sum fun a ha => ?_).trans hcard_ge_z
    have hmv_closed : ∀ m ∈ τ₀.movedSet ∩ F a, τ₀ m ∈ τ₀.movedSet ∩ F a := by
      intro m hm
      obtain ⟨hm_mv, hm_Fa⟩ := mem_inter.mp hm
      have hne := (mem_filter.mp hm_mv).2
      have hmv' : τ₀ m ∈ τ₀.movedSet := τ₀.mem_movedSet.mpr (τ₀.moved_apply hne)
      refine mem_inter.mpr ⟨hmv', ?_⟩
      rcases mem_union.mp hm_Fa with hp | hn
      · have hm_pos : m ∈ τ₀.movedPos :=
          mem_filter.mpr ⟨mem_filter.mpr ⟨subset_biUnion_of_mem F ha hm_Fa,
            (mem_filter.mp (mem_filter.mp hp).1).2⟩, hne⟩
        have hadj := τ₀.adj_pos m hne (mem_filter.mp (mem_filter.mp hp).1).2
        have hm'_neg := τ₀.movedNeg_subset (τ₀.apply_mem_movedNeg_of_mem_movedPos hm_pos)
        have hneg_Ioc : τ₀ m ∈ negParity (Ioc X (2 * X)) :=
          mem_filter.mpr ⟨hsub_Ioc (mem_filter.mp hm'_neg).1, (mem_filter.mp hm'_neg).2⟩
        exact mem_union_right _ (mem_filter.mpr ⟨hneg_Ioc, hadj.2.symm.trans (mem_filter.mp hp).2⟩)
      · have hm_neg : m ∈ τ₀.movedNeg :=
          mem_filter.mpr ⟨mem_filter.mpr ⟨subset_biUnion_of_mem F ha hm_Fa,
            (mem_filter.mp (mem_filter.mp hn).1).2⟩, hne⟩
        have hm'_pos : τ₀ m ∈ τ₀.movedPos := τ₀.apply_mem_movedPos_of_mem_movedNeg hm_neg
        have hadj := τ₀.adj_pos (τ₀ m) (mem_filter.mp hm'_pos).2
          (mem_filter.mp (τ₀.movedPos_subset hm'_pos)).2
        rw [τ₀.apply_apply] at hadj
        have hm'_sub := τ₀.movedPos_subset hm'_pos
        have hpos_Ioc : τ₀ m ∈ posParity (Ioc X (2 * X)) :=
          mem_filter.mpr ⟨hsub_Ioc (mem_filter.mp hm'_sub).1, (mem_filter.mp hm'_sub).2⟩
        exact mem_union_left _ (mem_filter.mpr ⟨hpos_Ioc, hadj.2.trans (mem_filter.mp hn).2⟩)
    -- Paired elements in `τ₀.movedSet ∩ F a` have zero Möbius sum
    let P_a := (τ₀.movedSet ∩ F a).filter fun n => μ n = 1
    let N_a := (τ₀.movedSet ∩ F a).filter fun n => μ n = -1
    have hPN_union : τ₀.movedSet ∩ F a = P_a ∪ N_a := by
      ext n; simp only [P_a, N_a, mem_union, mem_filter]
      refine ⟨fun hn => ?_, fun h => h.elim And.left And.left⟩
      have hsq : Squarefree n := (mem_filter.mp (mem_filter.mp (mem_inter.mp hn).1).1).2
      rcases moebius_eq_one_or_neg_one_of_squarefree hsq with h1 | h1
      · exact Or.inl ⟨hn, h1⟩
      · exact Or.inr ⟨hn, h1⟩
    have hPN_disj : Disjoint P_a N_a := by
      rw [disjoint_left]; intro n h1 h2
      have := (mem_filter.mp h1).2; have := (mem_filter.mp h2).2; omega
    have hPN_img : P_a.image τ₀ = N_a := by
      ext b; simp only [mem_image, P_a, N_a, mem_filter]
      constructor
      · rintro ⟨m, ⟨hm, hμm⟩, rfl⟩
        have hne := (mem_filter.mp (mem_inter.mp hm).1).2
        exact ⟨hmv_closed m hm, by have := τ₀.sign_flip m hne; omega⟩
      · rintro ⟨hb, hμb⟩
        have hne := (mem_filter.mp (mem_inter.mp hb).1).2
        refine ⟨τ₀ b, ⟨hmv_closed b hb, by have := τ₀.sign_flip b hne; omega⟩, τ₀.apply_apply b⟩
    have hsum_mv0 : ∑ n ∈ τ₀.movedSet ∩ F a, μ n = 0 := by
      rw [hPN_union, sum_union hPN_disj, ← hPN_img,
        sum_image (fun _ _ _ _ h => τ₀.injective h)]
      have h1 : ∑ m ∈ P_a, μ m = (P_a.card : ℤ) :=
        (sum_congr rfl fun m hm => (mem_filter.mp hm).2).trans
          (by rw [sum_const, Int.nsmul_eq_mul, mul_one])
      have h2 : ∑ m ∈ P_a, μ (τ₀ m) = -(P_a.card : ℤ) := by
        calc ∑ m ∈ P_a, μ (τ₀ m) = ∑ _m ∈ P_a, (-1 : ℤ) :=
              sum_congr rfl fun m hm => by
                have := τ₀.sign_flip m (mem_filter.mp (mem_inter.mp (mem_filter.mp hm).1).1).2
                have := (mem_filter.mp hm).2; omega
          _ = -(P_a.card : ℤ) := by rw [sum_const, Int.nsmul_eq_mul, mul_neg_one]
      omega
    have hFa_split : F a = (τ₀.movedSet ∩ F a) ∪ (τ₀.unmatchedSet ∩ F a) := by
      ext n; simp only [mem_union, mem_inter]
      constructor
      · intro hn
        have hn_sq : n ∈ squarefreeOf (fibreUnion X A) := by
          rw [← hsq_F a] at hn
          exact mem_filter.mpr ⟨subset_biUnion_of_mem F ha (mem_filter.mp hn).1, (mem_filter.mp hn).2⟩
        rw [← τ₀.movedSet_union_unmatchedSet] at hn_sq
        exact (mem_union.mp hn_sq).imp (fun h => ⟨h, hn⟩) (fun h => ⟨h, hn⟩)
      · exact fun h => h.elim And.right And.right
    have hFa_disj : Disjoint (τ₀.movedSet ∩ F a) (τ₀.unmatchedSet ∩ F a) :=
      Disjoint.mono inter_subset_left inter_subset_left τ₀.disjoint_movedSet_unmatchedSet
    have hsum_eq : ∑ n ∈ F a, μ n = ∑ n ∈ τ₀.unmatchedSet ∩ F a, μ n := by
      conv_lhs => rw [hFa_split]
      rw [sum_union hFa_disj, hsum_mv0, zero_add]
    rw [← hsum_F a, hsum_eq]
    calc |∑ n ∈ τ₀.unmatchedSet ∩ F a, μ n|
        ≤ ∑ n ∈ τ₀.unmatchedSet ∩ F a, |μ n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ τ₀.unmatchedSet ∩ F a, (1 : ℤ) :=
          sum_le_sum fun n _ => ArithmeticFunction.abs_moebius_le_one
      _ = ((τ₀.unmatchedSet ∩ F a).card : ℤ) := by rw [sum_const, Int.nsmul_eq_mul, mul_one]
  · -- Construct explicit rank-paired `OrderedFibreRel` involution on each `F a` and glue
    have hex_loc : ∀ a : ℕ, ∃ τ_a : FactorizationInvolution OrderedFibreRel (F a),
        (τ_a.unmatchedSet.card : ℤ) = |((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)| := by
      intro a
      obtain ⟨M_full, hM_full⟩ := exists_fullOppositeParityMatching_unmatched_eq_abs_sum (F a)
      let M_ord : OppositeParityMatching OrderedFibreRel (F a) :=
        { sources := M_full.sources
          partner := M_full.partner
          sources_subset := M_full.sources_subset
          injOn := M_full.injOn
          partner_mem := M_full.partner_mem
          adj := fun m hm => by
            have hm_pos : m ∈ fibrePos X a := hpos_F a ▸ M_full.sources_subset hm
            have hn_neg : M_full.partner m ∈ fibreNeg X a := hneg_F a ▸ M_full.partner_mem m hm
            exact ⟨(evenPrefixCofactor_complete_bipartite_fibres hX1).2 hm_pos hn_neg,
              (mem_filter.mp hm_pos).2.trans (mem_filter.mp hn_neg).2.symm⟩ }
      refine ⟨FactorizationInvolution.ofMatching M_ord, ?_⟩
      rw [FactorizationInvolution.ofMatching_unmatchedSet]
      change (M_full.unmatchedSet.card : ℤ) = _
      rw [hM_full, hsum_F a]
    let fam : ∀ a : ℕ, FactorizationInvolution OrderedFibreRel (F a) := fun a => (hex_loc a).choose
    have hcover_F : A.biUnion F = fibreUnion X A := rfl
    refine ⟨FactorizationInvolution.glueDisjoint A F hdisj_F
      (fun _ ha => hcover_F ▸ subset_biUnion_of_mem F ha) fam, ?_⟩
    rw [FactorizationInvolution.glueDisjoint_unmatchedSet_eq_biUnion A F hdisj_F hcover_F fam,
      card_biUnion]
    · rw [Nat.cast_sum]
      exact sum_congr rfl fun a _ => (hex_loc a).choose_spec
    · intro a₁ ha₁ a₂ ha₂ hne
      exact Disjoint.mono ((filter_subset _ _).trans (filter_subset _ _))
        ((filter_subset _ _).trans (filter_subset _ _)) (hdisj_F ha₁ ha₂ hne)
  · intro R τ
    have htot_sum : ∑ n ∈ fibreUnion X A, μ n =
        ∑ a ∈ A, (((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)) := by
      unfold fibreUnion
      rw [sum_biUnion hdisj_F]
      exact sum_congr rfl fun a _ => hsum_F a
    rw [← htot_sum]
    exact τ.abs_sum_moebius_le_unmatched

/-- Cube-root rough fibre cofactors `b = q₁ * q₂` with `q₁ ∈ (Z⁴, 5/4 Z⁴]` and
`q₂ ∈ (2 Z¹⁰, 9/4 Z¹⁰]` (`Z = X^{1/36}`). -/
def roughFibreCofactors (X : ℕ) : Finset ℕ :=
  let Z : ℝ := (X : ℝ) ^ (1 / 36 : ℝ)
  (windowPrimes (Z ^ 4) (5 / 4 * Z ^ 4) ×ˢ
    windowPrimes (2 * Z ^ 10) (9 / 8 * (2 * Z ^ 10))).image fun pq => pq.1 * pq.2

private lemma roughFibre_neg_and_cap_bounds (X q₁ q₂ : ℕ) (Z S_cap : ℝ)
    (hX1 : 1 ≤ X) (hX64 : 64 ≤ (X : ℝ)) (hZ8 : 8 ≤ Z) (hZ36 : Z ^ (36 : ℕ) = (X : ℝ))
    (hScap : (3 * S_cap) ^ 6 ≤ Z)
    (hq₁ : q₁.Prime ∧ Z ^ 4 < (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ 5 / 4 * Z ^ 4)
    (hq₂ : q₂.Prime ∧ 2 * Z ^ 10 < (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ 9 / 8 * (2 * Z ^ 10))
    (hw_2 : ∀ u : ℝ, Z ≤ u → ((2 - 1) / 2) * u / Real.log (2 * u) ≤
      ((windowPrimes u (2 * u)).card : ℝ))
    (hS_cap : ∀ b : ℝ, S_cap ≤ b →
      10 * (cubeBandProducts b (b ^ 6) (2 * b ^ 6)).card ≤
        9 * (windowPrimes (b ^ 6) (2 * b ^ 6)).card) :
    10 * (fibrePos X (q₁ * q₂)).card ≤ 9 * (fibreNeg X (q₁ * q₂)).card ∧
    (8 / 45) * Z ^ 22 / Real.log X ≤ ((fibreNeg X (q₁ * q₂)).card : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith only [hX64]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  have hZ0 : 0 < Z := by linarith only [hZ8]
  have hZ1 : 1 ≤ Z := by linarith only [hZ8]
  obtain ⟨hq₁_pr, hq₁_lo, hq₁_hi⟩ := hq₁
  obtain ⟨hq₂_pr, hq₂_lo, hq₂_hi⟩ := hq₂
  have hq₁_lt_q₂ : q₁ < q₂ := by
    have h410 : 5 / 4 * Z ^ 4 < 2 * Z ^ 10 := by
      have hle := pow_le_pow_right₀ hZ1 (by decide : 4 ≤ 10)
      linarith [pow_pos hZ0 4, hle]
    exact_mod_cast (by linarith only [hq₁_hi, hq₂_lo, h410] : (q₁ : ℝ) < q₂)
  have hb_pos : 0 < q₁ * q₂ := Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < (q₁ * q₂ : ℕ) := by exact_mod_cast hb_pos
  have hb_cast : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; rfl
  have hsq_b : Squarefree (q₁ * q₂) :=
    Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁_pr hq₂_pr).mpr hq₁_lt_q₂.ne,
      Irreducible.squarefree hq₁_pr, Irreducible.squarefree hq₂_pr⟩
  have heven_b : Even (q₁ * q₂).primeFactors.card := by
    have htop : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁_lt_q₂
    rw [card_primeFactors_mul_larger_prime hq₁_pr.ne_zero hq₂_pr htop,
      hq₁_pr.primeFactors, card_singleton]
    exact ⟨1, rfl⟩
  have hb_lo : 2 * Z ^ 14 < ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [hb_cast]
    calc 2 * Z ^ 14 = Z ^ 4 * (2 * Z ^ 10) := by ring
      _ < (q₁ : ℝ) * q₂ := mul_lt_mul'' hq₁_lo hq₂_lo (by positivity) (by positivity)
  have hb_hi : ((q₁ * q₂ : ℕ) : ℝ) ≤ (45 / 16) * Z ^ 14 := by
    rw [hb_cast]
    calc (q₁ : ℝ) * q₂ ≤ (5 / 4 * Z ^ 4) * (9 / 8 * (2 * Z ^ 10)) :=
          mul_le_mul hq₁_hi hq₂_hi (Nat.cast_nonneg _) (by positivity)
      _ = (45 / 16) * Z ^ 14 := by ring
  obtain ⟨T_b, hTb_def⟩ : ∃ T_b : ℝ, T_b = (X : ℝ) / (q₁ * q₂ : ℕ) := ⟨_, rfl⟩
  have hTb0 : 0 < T_b := by rw [hTb_def]; positivity
  have hTb_lo : (16 / 45) * Z ^ 22 ≤ T_b := by
    rw [hTb_def, le_div_iff₀ hb_r]
    calc (16 / 45) * Z ^ 22 * (q₁ * q₂ : ℕ)
        ≤ (16 / 45) * Z ^ 22 * ((45 / 16) * Z ^ 14) :=
          mul_le_mul_of_nonneg_left hb_hi (by positivity)
      _ = X := by rw [← hZ36]; ring
  have hTb_hi : T_b < (1 / 2) * Z ^ 22 := by
    rw [hTb_def, div_lt_iff₀ hb_r]
    calc (X : ℝ) = (1 / 2) * Z ^ 22 * (2 * Z ^ 14) := by rw [← hZ36]; ring
      _ < (1 / 2) * Z ^ 22 * (q₁ * q₂ : ℕ) :=
          mul_lt_mul_of_pos_left hb_lo (by positivity)
  have hTb_gt_q₂ : (q₂ : ℝ) < T_b := by
    have h8 : 8 * Z ^ 10 ≤ Z ^ 22 := by
      calc 8 * Z ^ 10 ≤ Z * Z ^ 10 := mul_le_mul_of_nonneg_right hZ8 (by positivity)
        _ = Z ^ 11 := by ring
        _ ≤ Z ^ 22 := pow_le_pow_right₀ hZ1 (by decide)
    linarith only [hq₂_hi, h8, hTb_lo, pow_pos hZ0 10]
  have htop_b_le : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ (q₁ * q₂).primeFactors, d < p := by
    intro p hp_gt d hd
    rw [Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero, hq₁_pr.primeFactors,
      hq₂_pr.primeFactors] at hd
    rcases mem_union.mp hd with hd₁ | hd₂
    · rw [mem_singleton.mp hd₁]; exact hq₁_lt_q₂.trans hp_gt
    · rw [mem_singleton.mp hd₂]; exact hp_gt
  have hneg_eq : (windowPrimes T_b (2 * T_b)).image ((q₁ * q₂) * ·) = fibreNeg X (q₁ * q₂) := by
    ext n; simp only [mem_image]
    constructor
    · rintro ⟨p, hp_win, rfl⟩
      obtain ⟨hpp, hp_lo, hp_hi⟩ := (mem_windowPrimes hTb0.le (by positivity)).mp hp_win
      have htop_b := htop_b_le (by exact_mod_cast hTb_gt_q₂.trans hp_lo)
      have hμ_n : μ ((q₁ * q₂) * p) = -1 := by
        rw [moebius_mul_larger_prime hb_pos.ne' hpp htop_b,
          moebius_eq_neg_one_pow_omega hsq_b, heven_b.neg_one_pow]
      have hIoc_n : (q₁ * q₂) * p ∈ Ioc X (2 * X) := by
        rw [hTb_def, div_lt_iff₀ hb_r] at hp_lo
        rw [hTb_def, mul_div_assoc', le_div_iff₀ hb_r] at hp_hi
        have hcomm : (((q₁ * q₂) * p : ℕ) : ℝ) = (p : ℝ) * (q₁ * q₂ : ℕ) := by
          push_cast; ring
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < (((q₁ * q₂) * p : ℕ) : ℝ) by rw [hcomm]; exact hp_lo)
        · exact_mod_cast (show (((q₁ * q₂) * p : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) by
            rw [hcomm, Nat.cast_mul 2 X, Nat.cast_ofNat]; exact hp_hi)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_n, hμ_n⟩, ?_⟩
      rw [evenPrefixCofactor_eq_maxPrimeStem_of_neg hμ_n]
      exact maxPrimeStem_mul_prime hb_pos.ne' hpp htop_b
    · intro hn
      obtain ⟨_, _, p, hpp, hna, _⟩ := mem_fibreNeg_structure hX1 hn
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hn).1).1
      refine ⟨p, (mem_windowPrimes hTb0.le (by positivity)).mpr ⟨hpp, ?_, ?_⟩, hna.symm⟩
      · rw [hTb_def, div_lt_iff₀ hb_r]
        exact_mod_cast (show X < p * (q₁ * q₂) by rw [mul_comm, ← hna]; exact hn_lo)
      · rw [hTb_def, mul_div_assoc', le_div_iff₀ hb_r]
        exact_mod_cast (show p * (q₁ * q₂) ≤ 2 * X by rw [mul_comm, ← hna]; exact hn_hi)
  have hneg_card : (fibreNeg X (q₁ * q₂)).card = (windowPrimes T_b (2 * T_b)).card := by
    rw [← hneg_eq, card_image_of_injOn fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hb_pos h]
  obtain ⟨s_b, hsb_def⟩ : ∃ s_b : ℝ, s_b = T_b ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
  have hsb0 : 0 ≤ s_b := by rw [hsb_def]; exact Real.rpow_nonneg hTb0.le _
  have hsb6 : s_b ^ 6 = T_b := by
    rw [hsb_def, ← Real.rpow_natCast, ← Real.rpow_mul hTb0.le]; norm_num
  have hsb_ge : S_cap ≤ s_b := by
    by_cases hS0 : S_cap ≤ 0
    · exact hS0.trans hsb0
    · push Not at hS0
      apply (pow_le_pow_iff_left₀ hS0.le hsb0 (by decide : 6 ≠ 0)).mp
      rw [hsb6]
      have hZ1_22 : Z ≤ Z ^ 22 := by
        simpa only [pow_one] using pow_le_pow_right₀ hZ1 (by decide : 1 ≤ 22)
      calc S_cap ^ 6 ≤ (3 * S_cap) ^ 6 / 729 := by ring_nf; exact le_rfl
        _ ≤ Z / 729 := by gcongr
        _ ≤ (16 / 45) * Z ^ 22 := by linarith only [hZ1_22, hZ0]
        _ ≤ T_b := hTb_lo
  have hsb2_lt_q₂ : s_b ^ 2 / 2 < (q₂ : ℝ) := by
    have hsb2_lt_Z8 : s_b ^ 2 < Z ^ 8 := by
      apply (pow_lt_pow_iff_left₀ (sq_nonneg s_b) (by positivity) (by decide : 3 ≠ 0)).mp
      have h1 : (s_b ^ 2) ^ 3 = s_b ^ 6 := by ring
      have h2 : (Z ^ 8) ^ 3 = Z ^ 24 := by ring
      rw [h1, h2, hsb6]
      have hlt24 : Z ^ 22 < Z ^ 24 := pow_lt_pow_right₀ (by linarith only [hZ8]) (by decide)
      linarith [pow_pos hZ0 22, hlt24, hTb_hi]
    have h810 : Z ^ 8 ≤ Z ^ 10 := pow_le_pow_right₀ hZ1 (by decide)
    linarith [sq_nonneg s_b, hq₂_lo, hsb2_lt_Z8, h810]
  have hpos_inj : (fibrePos X (q₁ * q₂)).image (· / (q₁ * q₂)) ⊆
      cubeBandProducts s_b (s_b ^ 6) (2 * s_b ^ 6) := by
    intro w hw
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hw
    obtain ⟨_, _, r₁, r₂, hr₁_pr, hr₂_pr, hr₁_lt_r₂, hmb, hlt_r₁⟩ := mem_fibrePos_structure hX1 hm
    obtain ⟨hm_lo, hm_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hm).1).1
    have hdiv_eq : m / (q₁ * q₂) = r₁ * r₂ := by
      rw [hmb, mul_comm (q₁ * q₂), Nat.mul_div_cancel _ hb_pos]
    rw [hdiv_eq]
    have hq₂_mem_b : q₂ ∈ (q₁ * q₂).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq₂_pr, dvd_mul_left q₂ q₁, hb_pos.ne'⟩
    have hr₁_lo : s_b ^ 2 / 2 < (r₁ : ℝ) :=
      hsb2_lt_q₂.trans (by exact_mod_cast hlt_r₁ q₂ hq₂_mem_b)
    have hprod_hi : (r₁ : ℝ) * r₂ ≤ 2 * s_b ^ 6 := by
      rw [hsb6, hTb_def, mul_div_assoc', le_div_iff₀ hb_r]
      exact_mod_cast (show (r₁ * r₂) * (q₁ * q₂) ≤ 2 * X by rw [mul_comm, ← hmb]; exact hm_hi)
    have hr₁_hi : (r₁ : ℝ) ≤ 2 * s_b ^ 3 := by
      have hr₁_sq : (r₁ : ℝ) ^ 2 ≤ 2 * s_b ^ 6 :=
        (show (r₁ : ℝ) ^ 2 ≤ (r₁ : ℝ) * r₂ by rw [sq]; gcongr).trans hprod_hi
      by_contra hgt; push Not at hgt
      nlinarith only [hr₁_sq, hgt, pow_nonneg hsb0 3, pow_nonneg hsb0 6]
    have hr₁_0 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pr.pos
    refine mem_biUnion.mpr ⟨r₁,
      (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hr₁_pr, hr₁_lo, hr₁_hi⟩,
      mem_image.mpr ⟨r₂,
        (mem_windowPrimes (by positivity) (by positivity)).mpr ⟨hr₂_pr, ?_, ?_⟩, rfl⟩⟩
    · rw [hsb6, hTb_def, div_lt_iff₀ hr₁_0, div_lt_iff₀ hb_r]
      exact_mod_cast (show X < r₂ * r₁ * (q₁ * q₂) by
        rw [show r₂ * r₁ * (q₁ * q₂) = (q₁ * q₂) * (r₁ * r₂) by ring, ← hmb]; exact hm_lo)
    · rw [hsb6, hTb_def, le_div_iff₀ hr₁_0, mul_div_assoc', le_div_iff₀ hb_r]
      exact_mod_cast (show r₂ * r₁ * (q₁ * q₂) ≤ 2 * X by
        rw [show r₂ * r₁ * (q₁ * q₂) = (q₁ * q₂) * (r₁ * r₂) by ring, ← hmb]; exact hm_hi)
  have hpos_div_inj : Set.InjOn (· / (q₁ * q₂)) ↑(fibrePos X (q₁ * q₂)) := by
    intro m₁ hm₁ m₂ hm₂ heq
    dsimp only at heq
    obtain ⟨_, _, r₁, r₂, _, _, _, hmb₁, _⟩ := mem_fibrePos_structure hX1 hm₁
    obtain ⟨_, _, r₁', r₂', _, _, _, hmb₂, _⟩ := mem_fibrePos_structure hX1 hm₂
    have hd₁ : m₁ / (q₁ * q₂) = r₁ * r₂ := by rw [hmb₁, mul_comm, Nat.mul_div_cancel _ hb_pos]
    have hd₂ : m₂ / (q₁ * q₂) = r₁' * r₂' := by rw [hmb₂, mul_comm, Nat.mul_div_cancel _ hb_pos]
    rw [hmb₁, hmb₂, ← hd₁, ← hd₂, heq]
  have h10_9 : 10 * (fibrePos X (q₁ * q₂)).card ≤ 9 * (fibreNeg X (q₁ * q₂)).card := by
    rw [hneg_card, ← hsb6, ← card_image_of_injOn hpos_div_inj]
    exact (Nat.mul_le_mul_left 10 (card_le_card hpos_inj)).trans (hS_cap s_b hsb_ge)
  have h2Tb_le_X : 2 * T_b ≤ X := by
    rw [hTb_def, mul_div_assoc', div_le_iff₀ hb_r, mul_comm (2 : ℝ) X]
    have hb2 : (2 : ℝ) ≤ (q₁ * q₂ : ℕ) := by
      have : (1 : ℝ) ≤ Z ^ 14 := one_le_pow₀ hZ1
      linarith only [hb_lo, this]
    exact mul_le_mul_of_nonneg_left hb2 hX0.le
  have hneg_lo : (8 / 45) * Z ^ 22 / Real.log X ≤ ((fibreNeg X (q₁ * q₂)).card : ℝ) := by
    rw [hneg_card]
    have hZ_le_Tb : Z ≤ T_b := by
      calc Z ≤ (16 / 45) * (8 * Z) := by linarith only [hZ0]
        _ ≤ (16 / 45) * (Z * Z) := by gcongr
        _ = (16 / 45) * Z ^ 2 := by ring
        _ ≤ (16 / 45) * Z ^ 22 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by decide)) (by positivity)
        _ ≤ T_b := hTb_lo
    have hw := hw_2 T_b hZ_le_Tb
    have hlog_le : Real.log (2 * T_b) ≤ Real.log X := Real.log_le_log (by positivity) h2Tb_le_X
    calc (8 / 45) * Z ^ 22 / Real.log X
        ≤ ((2 - 1) / 2) * T_b / Real.log X :=
          div_le_div_of_nonneg_right (by linarith only [hTb_lo]) hLX.le
      _ ≤ ((2 - 1) / 2) * T_b / Real.log (2 * T_b) :=
          div_le_div_of_nonneg_left (by positivity)
            (Real.log_pos (by linarith only [hZ_le_Tb, hZ8, hTb0])) hlog_le
      _ ≤ _ := hw
  exact ⟨h10_9, hneg_lo⟩

private lemma roughFibre_pos_lower_bound (X q₁ q₂ : ℕ) (Z : ℝ) (Q_pos : Finset ℕ)
    (hX64 : 64 ≤ (X : ℝ)) (hZ8 : 8 ≤ Z) (hZ36 : Z ^ (36 : ℕ) = (X : ℝ))
    (hq₁ : q₁.Prime ∧ Z ^ 4 < (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ 5 / 4 * Z ^ 4)
    (hq₂ : q₂.Prime ∧ 2 * Z ^ 10 < (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ 9 / 8 * (2 * Z ^ 10))
    (hQ_sub : ∀ r₁ ∈ Q_pos, r₁.Prime ∧ 3 * Z ^ 10 < (r₁ : ℝ) ∧ (r₁ : ℝ) ≤ Z ^ 11 / 2)
    (hQ_recip : (1 / 24 : ℝ) ≤ ∑ r₁ ∈ Q_pos, 1 / (r₁ : ℝ))
    (hw_2 : ∀ u : ℝ, Z ≤ u → ((2 - 1) / 2) * u / Real.log (2 * u) ≤
      ((windowPrimes u (2 * u)).card : ℝ)) :
    (1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X) ≤ ((fibrePos X (q₁ * q₂)).card : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith only [hX64]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  have hZ0 : 0 < Z := by linarith only [hZ8]
  have hZ1 : 1 ≤ Z := by linarith only [hZ8]
  obtain ⟨hq₁_pr, hq₁_lo, hq₁_hi⟩ := hq₁
  obtain ⟨hq₂_pr, hq₂_lo, hq₂_hi⟩ := hq₂
  have hq₁_lt_q₂ : q₁ < q₂ := by
    have h410 : 5 / 4 * Z ^ 4 < 2 * Z ^ 10 := by
      have hle := pow_le_pow_right₀ hZ1 (by decide : 4 ≤ 10)
      linarith [pow_pos hZ0 4, hle]
    exact_mod_cast (by linarith only [hq₁_hi, hq₂_lo, h410] : (q₁ : ℝ) < q₂)
  have hb_pos : 0 < q₁ * q₂ := Nat.mul_pos hq₁_pr.pos hq₂_pr.pos
  have hb_r : (0 : ℝ) < (q₁ * q₂ : ℕ) := by exact_mod_cast hb_pos
  have hb_cast : ((q₁ * q₂ : ℕ) : ℝ) = (q₁ : ℝ) * q₂ := by push_cast; rfl
  have hsq_b : Squarefree (q₁ * q₂) :=
    Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hq₁_pr hq₂_pr).mpr hq₁_lt_q₂.ne,
      Irreducible.squarefree hq₁_pr, Irreducible.squarefree hq₂_pr⟩
  have heven_b : Even (q₁ * q₂).primeFactors.card := by
    have htop : ∀ d ∈ q₁.primeFactors, d < q₂ := fun d hd =>
      (Nat.le_of_dvd hq₁_pr.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hq₁_lt_q₂
    rw [card_primeFactors_mul_larger_prime hq₁_pr.ne_zero hq₂_pr htop,
      hq₁_pr.primeFactors, card_singleton]
    exact ⟨1, rfl⟩
  have hb_lo : 2 * Z ^ 14 < ((q₁ * q₂ : ℕ) : ℝ) := by
    rw [hb_cast]
    calc 2 * Z ^ 14 = Z ^ 4 * (2 * Z ^ 10) := by ring
      _ < (q₁ : ℝ) * q₂ := mul_lt_mul'' hq₁_lo hq₂_lo (by positivity) (by positivity)
  have hb_hi : ((q₁ * q₂ : ℕ) : ℝ) ≤ (45 / 16) * Z ^ 14 := by
    rw [hb_cast]
    calc (q₁ : ℝ) * q₂ ≤ (5 / 4 * Z ^ 4) * (9 / 8 * (2 * Z ^ 10)) :=
          mul_le_mul hq₁_hi hq₂_hi (Nat.cast_nonneg _) (by positivity)
      _ = (45 / 16) * Z ^ 14 := by ring
  obtain ⟨T_b, hTb_def⟩ : ∃ T_b : ℝ, T_b = (X : ℝ) / (q₁ * q₂ : ℕ) := ⟨_, rfl⟩
  have hTb0 : 0 < T_b := by rw [hTb_def]; positivity
  have hTb_lo : (16 / 45) * Z ^ 22 ≤ T_b := by
    rw [hTb_def, le_div_iff₀ hb_r]
    calc (16 / 45) * Z ^ 22 * (q₁ * q₂ : ℕ)
        ≤ (16 / 45) * Z ^ 22 * ((45 / 16) * Z ^ 14) :=
          mul_le_mul_of_nonneg_left hb_hi (by positivity)
      _ = X := by rw [← hZ36]; ring
  have h2Tb_le_X : 2 * T_b ≤ X := by
    rw [hTb_def, mul_div_assoc', div_le_iff₀ hb_r, mul_comm (2 : ℝ) X]
    have hb2 : (2 : ℝ) ≤ (q₁ * q₂ : ℕ) := by
      have : (1 : ℝ) ≤ Z ^ 14 := one_le_pow₀ hZ1
      linarith only [hb_lo, this]
    exact mul_le_mul_of_nonneg_left hb2 hX0.le
  have htop_b_le : ∀ {p : ℕ}, q₂ < p → ∀ d ∈ (q₁ * q₂).primeFactors, d < p := by
    intro p hp_gt d hd
    rw [Nat.primeFactors_mul hq₁_pr.ne_zero hq₂_pr.ne_zero, hq₁_pr.primeFactors,
      hq₂_pr.primeFactors] at hd
    rcases mem_union.mp hd with hd₁ | hd₂
    · rw [mem_singleton.mp hd₁]; exact hq₁_lt_q₂.trans hp_gt
    · rw [mem_singleton.mp hd₂]; exact hp_gt
  let rowPos : ℕ → Finset ℕ := fun r₁ =>
    (windowPrimes (T_b / r₁) (2 * T_b / r₁)).image fun r₂ => (q₁ * q₂) * (r₁ * r₂)
  have hrow_spec : ∀ r₁ ∈ Q_pos,
      rowPos r₁ ⊆ fibrePos X (q₁ * q₂) ∧
      (∀ m ∈ rowPos r₁, maxPrimeStem m = (q₁ * q₂) * r₁) ∧
      (1 / (r₁ : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X) ≤ ((rowPos r₁).card : ℝ) := by
    intro r₁ hr₁Q
    obtain ⟨hr₁_pr, hr₁_lo, hr₁_hi⟩ := hQ_sub r₁ hr₁Q
    have hr₁_0 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pr.pos
    have hq₂_lt_r₁ : q₂ < r₁ := by
      exact_mod_cast (by linarith [hq₂_hi, hr₁_lo, pow_pos hZ0 10] : (q₂ : ℝ) < r₁)
    have htop_r₁ := htop_b_le hq₂_lt_r₁
    have hTbr₁_lo : (32 / 45) * Z ^ 11 ≤ T_b / r₁ := by
      rw [le_div_iff₀ hr₁_0]
      calc (32 / 45) * Z ^ 11 * r₁ ≤ (32 / 45) * Z ^ 11 * (Z ^ 11 / 2) :=
            mul_le_mul_of_nonneg_left hr₁_hi (by positivity)
        _ = (16 / 45) * Z ^ 22 := by ring
        _ ≤ T_b := hTb_lo
    have hr₁_lt_Tbr₁ : (r₁ : ℝ) < T_b / r₁ := by linarith [pow_pos hZ0 11, hr₁_hi, hTbr₁_lo]
    have hsub_pos : rowPos r₁ ⊆ fibrePos X (q₁ * q₂) := by
      intro m hm
      obtain ⟨r₂, hr₂_win, rfl⟩ := mem_image.mp hm
      obtain ⟨hr₂_pr, hr₂_lo, hr₂_hi⟩ :=
        (mem_windowPrimes (by positivity) (by positivity)).mp hr₂_win
      have hr₁_lt_r₂ : r₁ < r₂ := by exact_mod_cast hr₁_lt_Tbr₁.trans hr₂_lo
      have htop_r₂ := primeFactors_lt_of_mul_prime hb_pos.ne' hr₁_pr hr₁_lt_r₂ htop_r₁
      have hμ_m : μ ((q₁ * q₂) * (r₁ * r₂)) = 1 := by
        rw [← mul_assoc,
          moebius_mul_larger_prime (Nat.mul_ne_zero hb_pos.ne' hr₁_pr.ne_zero) hr₂_pr htop_r₂,
          moebius_mul_larger_prime hb_pos.ne' hr₁_pr htop_r₁,
          moebius_eq_neg_one_pow_omega hsq_b, heven_b.neg_one_pow]; norm_num
      have hIoc_m : (q₁ * q₂) * (r₁ * r₂) ∈ Ioc X (2 * X) := by
        rw [hTb_def, div_lt_iff₀ hr₁_0, div_lt_iff₀ hb_r] at hr₂_lo
        rw [hTb_def, mul_div_assoc', le_div_iff₀ hr₁_0, le_div_iff₀ hb_r] at hr₂_hi
        have hcomm : (((q₁ * q₂) * (r₁ * r₂) : ℕ) : ℝ) = (r₂ : ℝ) * r₁ * (q₁ * q₂ : ℕ) := by
          push_cast; ring
        refine mem_Ioc.mpr ⟨?_, ?_⟩
        · exact_mod_cast (show (X : ℝ) < (((q₁ * q₂) * (r₁ * r₂) : ℕ) : ℝ) by rw [hcomm]; exact hr₂_lo)
        · exact_mod_cast (show (((q₁ * q₂) * (r₁ * r₂) : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) by
            rw [hcomm, Nat.cast_mul 2 X, Nat.cast_ofNat]; exact hr₂_hi)
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨hIoc_m, hμ_m⟩,
        evenPrefixCofactor_mul_ordered_pair hb_pos.ne' heven_b hr₁_pr hr₂_pr hr₁_lt_r₂ htop_r₁⟩
    have hstems : ∀ m ∈ rowPos r₁, maxPrimeStem m = (q₁ * q₂) * r₁ := by
      intro m hm
      obtain ⟨r₂, hr₂_win, rfl⟩ := mem_image.mp hm
      obtain ⟨hr₂_pr, hr₂_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hr₂_win
      have hr₁_lt_r₂ : r₁ < r₂ := by exact_mod_cast hr₁_lt_Tbr₁.trans hr₂_lo
      exact (maxPrimeStem_mul_pair hb_pos.ne' hr₁_pr hr₂_pr hr₁_lt_r₂ htop_r₁).1
    have hcard_row : (rowPos r₁).card = (windowPrimes (T_b / r₁) (2 * T_b / r₁)).card :=
      card_image_of_injOn fun x _ y _ heq =>
        Nat.eq_of_mul_eq_mul_left hr₁_pr.pos (Nat.eq_of_mul_eq_mul_left hb_pos heq)
    refine ⟨hsub_pos, hstems, ?_⟩
    rw [hcard_row]
    have hZ_le_Tbr₁ : Z ≤ T_b / r₁ := by
      calc Z ≤ (32 / 45) * (8 * Z) := by linarith only [hZ0]
        _ ≤ (32 / 45) * (Z * Z) := by gcongr
        _ = (32 / 45) * Z ^ 2 := by ring
        _ ≤ (32 / 45) * Z ^ 11 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by decide)) (by positivity)
        _ ≤ T_b / r₁ := hTbr₁_lo
    have hw := hw_2 (T_b / r₁) hZ_le_Tbr₁
    have h2leX : 2 * (T_b / r₁) ≤ X := by
      have hdiv_le : T_b / r₁ ≤ T_b := div_le_self hTb0.le (by exact_mod_cast hr₁_pr.pos)
      linarith only [hdiv_le, h2Tb_le_X]
    have hlog_le : Real.log (2 * (T_b / r₁)) ≤ Real.log X :=
      Real.log_le_log (by positivity) h2leX
    have heq_2 : 2 * T_b / (r₁ : ℝ) = 2 * (T_b / r₁) := by ring
    rw [heq_2]
    calc (1 / (r₁ : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X)
        ≤ ((2 - 1) / 2) * (T_b / r₁) / Real.log X := by
          have : (1 / (r₁ : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X) =
              ((1 / 2) * ((16 / 45) * Z ^ 22 / r₁)) / Real.log X := by ring
          rw [this]
          refine div_le_div_of_nonneg_right ?_ hLX.le
          have h16 := div_le_div_of_nonneg_right hTb_lo hr₁_0.le
          linarith only [h16]
      _ ≤ ((2 - 1) / 2) * (T_b / r₁) / Real.log (2 * (T_b / r₁)) :=
          div_le_div_of_nonneg_left (by positivity)
            (Real.log_pos (by linarith only [hZ_le_Tbr₁, hZ8])) hlog_le
      _ ≤ _ := hw
  have hdisj_rows : (Q_pos : Set ℕ).PairwiseDisjoint rowPos := by
    intro r₁ hr₁ r₁' hr₁' hne
    refine disjoint_left.mpr fun m hm₁ hm₂ => ?_
    have hs₁ := (hrow_spec r₁ hr₁).2.1 m hm₁
    have hs₂ := (hrow_spec r₁' hr₁').2.1 m hm₂
    exact hne (Nat.eq_of_mul_eq_mul_left hb_pos (hs₁.symm.trans hs₂))
  have hbiU_sub : Q_pos.biUnion rowPos ⊆ fibrePos X (q₁ * q₂) :=
    biUnion_subset.mpr fun r₁ hr₁ => (hrow_spec r₁ hr₁).1
  have hcard_ge : ∑ r₁ ∈ Q_pos, (rowPos r₁).card ≤ (fibrePos X (q₁ * q₂)).card := by
    rw [← card_biUnion hdisj_rows]
    exact card_le_card hbiU_sub
  calc (1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X)
      ≤ (∑ r₁ ∈ Q_pos, 1 / (r₁ : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X) :=
        mul_le_mul_of_nonneg_right hQ_recip (by positivity)
    _ = ∑ r₁ ∈ Q_pos, (1 / (r₁ : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X) := sum_mul _ _ _
    _ ≤ ∑ r₁ ∈ Q_pos, ((rowPos r₁).card : ℝ) :=
        sum_le_sum fun r₁ hr₁ => (hrow_spec r₁ hr₁).2.2
    _ ≤ ((fibrePos X (q₁ * q₂)).card : ℝ) := by exact_mod_cast hcard_ge

/-- **Cube-root rough fibre-class persistence theorem**:
on `V_rough(X) = fibreUnion X (roughFibreCofactors X)`, both positive (`μ = 1`) and negative
(`μ = -1`) vertex populations have order at least `c * X / (log X)³`, yet the cube-root rough
surplus law `10 * #fibrePos(X, b) ≤ 9 * #fibreNeg(X, b)` forces **every** involution confined to
`V_rough(X)` (along any edge relation `R`) to leave at least `c_pers * X / (log X)³` unmatched
vertices. -/
theorem eventually_roughFibreClass_debt_persists :
    ∃ (c_pos c_neg c_pers : ℝ), 0 < c_pos ∧ 0 < c_neg ∧ 0 < c_pers ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        c_pos * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
          ((posParity (fibreUnion X (roughFibreCofactors X))).card : ℝ) ∧
        c_neg * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
          ((negParity (fibreUnion X (roughFibreCofactors X))).card : ℝ) ∧
        ∀ {R : ℕ → ℕ → Prop} (τ : FactorizationInvolution R (fibreUnion X (roughFibreCofactors X))),
          c_pers * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤ (τ.unmatchedSet.card : ℝ) := by
  obtain ⟨U₁, _, hw_54⟩ := exists_const_ratio_windowPrimes_bounds (α := 5 / 4) (by norm_num)
  obtain ⟨U₂, _, hw_98⟩ := exists_const_ratio_windowPrimes_bounds (α := 9 / 8) (by norm_num)
  obtain ⟨U₃, _, hw_2⟩ := exists_const_ratio_windowPrimes_bounds (α := 2) (by norm_num)
  obtain ⟨S_cap, hS_cap⟩ := eventually_atTop.mp eventually_cubeBandProducts_nine_tenths
  set c_neg : ℝ := (1 / 8) * (1 / 8) * (8 / 45)
  set c_pers : ℝ := c_neg / 10
  set c_pos : ℝ := c_neg * (1 / 24)
  have hrpow36 : Tendsto (fun x : ℝ => x ^ (1 / 36 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop,
      64 ≤ x ∧ 8 ≤ x ^ (1 / 36 : ℝ) ∧ U₁ ≤ (x ^ (1 / 36 : ℝ)) ^ 4 ∧
      U₂ ≤ 2 * (x ^ (1 / 36 : ℝ)) ^ 10 ∧ U₃ ≤ x ^ (1 / 36 : ℝ) ∧
      (3 * S_cap) ^ 6 ≤ x ^ (1 / 36 : ℝ) ∧
      2 * (Real.log 3 + Real.log 4 + mertensBlockGapConst) ≤ Real.log (x ^ (1 / 36 : ℝ)) := by
    have hz4 : Tendsto (fun x : ℝ => (x ^ (1 / 36 : ℝ)) ^ 4) atTop atTop :=
      (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp hrpow36
    have hz10 : Tendsto (fun x : ℝ => 2 * (x ^ (1 / 36 : ℝ)) ^ 10) atTop atTop :=
      ((tendsto_pow_atTop (by decide : 10 ≠ 0)).comp hrpow36).const_mul_atTop (by norm_num)
    exact (eventually_ge_atTop 64).and ((hrpow36.eventually_ge_atTop 8).and
      ((hz4.eventually_ge_atTop U₁).and ((hz10.eventually_ge_atTop U₂).and
        ((hrpow36.eventually_ge_atTop U₃).and ((hrpow36.eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.comp hrpow36).eventually_ge_atTop _))))))
  obtain ⟨X_cut, hX_cut⟩ := eventually_atTop.mp hev
  refine ⟨c_pos, c_neg, c_pers, by positivity, by positivity, by positivity,
    max 2 ⌈X_cut⌉₊, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (by decide : 1 ≤ 2) ((le_max_left _ _).trans hX)
  have hX_ge : X_cut ≤ (X : ℝ) :=
    (Nat.le_ceil X_cut).trans (by exact_mod_cast (le_max_right _ _).trans hX)
  obtain ⟨hX64, hZ8, hU1, hU2, hU3, hScap, hLmert⟩ := hX_cut X hX_ge
  have hX0 : (0 : ℝ) < X := by linarith only [hX64]
  have hLX : 0 < Real.log X := Real.log_pos (by linarith only [hX64])
  obtain ⟨Z, hZ_def⟩ : ∃ Z : ℝ, Z = (X : ℝ) ^ (1 / 36 : ℝ) := ⟨_, rfl⟩
  rw [← hZ_def] at hZ8 hU1 hU2 hU3 hScap hLmert
  have hZ0 : 0 < Z := by linarith only [hZ8]
  have hZ1 : 1 ≤ Z := by linarith only [hZ8]
  have hZ36 : Z ^ (36 : ℕ) = (X : ℝ) := by
    rw [hZ_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
  obtain ⟨R₁, hR₁_def⟩ : ∃ R₁ : Finset ℕ, R₁ = windowPrimes (Z ^ 4) (5 / 4 * Z ^ 4) := ⟨_, rfl⟩
  obtain ⟨R₂, hR₂_def⟩ :
    ∃ R₂ : Finset ℕ, R₂ = windowPrimes (2 * Z ^ 10) (9 / 8 * (2 * Z ^ 10)) := ⟨_, rfl⟩
  have hrc_eq : roughFibreCofactors X = (R₁ ×ˢ R₂).image fun pq => pq.1 * pq.2 := by
    dsimp only [roughFibreCofactors]; rw [← hZ_def, ← hR₁_def, ← hR₂_def]
  have hR₁_sub : ∀ q ∈ R₁, q.Prime ∧ Z ^ 4 < (q : ℝ) ∧ (q : ℝ) ≤ 5 / 4 * Z ^ 4 := fun q hq => by
    rw [hR₁_def] at hq; exact (mem_windowPrimes (by positivity) (by positivity)).mp hq
  have hR₂_sub : ∀ q ∈ R₂, q.Prime ∧ 2 * Z ^ 10 < (q : ℝ) ∧ (q : ℝ) ≤ 9 / 8 * (2 * Z ^ 10) :=
    fun q hq => by
      rw [hR₂_def] at hq; exact (mem_windowPrimes (by positivity) (by positivity)).mp hq
  have hinj_rc : Set.InjOn (fun pq : ℕ × ℕ => pq.1 * pq.2) ↑(R₁ ×ˢ R₂) := by
    rintro ⟨q₁, q₂⟩ hpq₁ ⟨q₁', q₂'⟩ hpq₂ heq
    dsimp only at heq
    obtain ⟨hq₁, hq₂⟩ := mem_product.mp hpq₁
    obtain ⟨hq₁', hq₂'⟩ := mem_product.mp hpq₂
    dsimp only at hq₁ hq₂ hq₁' hq₂'
    obtain ⟨hq₁_pr, _, hq₁_hi⟩ := hR₁_sub q₁ hq₁
    obtain ⟨hq₂_pr, _, _⟩ := hR₂_sub q₂ hq₂
    obtain ⟨hq₁'_pr, _, _⟩ := hR₁_sub q₁' hq₁'
    obtain ⟨hq₂'_pr, hq₂'_lo, _⟩ := hR₂_sub q₂' hq₂'
    have hlt : q₁ < q₂' := by
      have h410 : 5 / 4 * Z ^ 4 < 2 * Z ^ 10 := by
        have : Z ^ 4 ≤ Z ^ 10 := pow_le_pow_right₀ hZ1 (by decide)
        linarith [pow_pos hZ0 4]
      exact_mod_cast (by linarith : (q₁ : ℝ) < q₂')
    have heq1 : q₁ = q₁' := by
      rcases hq₁_pr.dvd_mul.mp (heq ▸ dvd_mul_right q₁ q₂) with h1 | h2
      · exact (Nat.prime_dvd_prime_iff_eq hq₁_pr hq₁'_pr).mp h1
      · exact False.elim (hlt.ne ((Nat.prime_dvd_prime_iff_eq hq₁_pr hq₂'_pr).mp h2))
    subst heq1
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left hq₁_pr.pos heq)
  have hR₁_lo : (1 / 8) * Z ^ 4 / Real.log X ≤ (R₁.card : ℝ) := by
    have h1 := (hw_54 (Z ^ 4) hU1).1
    rw [← hR₁_def] at h1
    have hleX : 5 / 4 * Z ^ 4 ≤ X := by
      have : Z ^ 5 ≤ Z ^ 36 := pow_le_pow_right₀ hZ1 (by decide)
      have h5 : 5 / 4 * Z ^ 4 ≤ Z * Z ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith only [hZ8]) (by positivity)
      rw [← hZ36]; linarith [show Z * Z ^ 4 = Z ^ 5 by ring]
    have hlog_le : Real.log (5 / 4 * Z ^ 4) ≤ Real.log X := Real.log_le_log (by positivity) hleX
    calc (1 / 8) * Z ^ 4 / Real.log X
        ≤ ((5 / 4 - 1) / 2) * Z ^ 4 / Real.log (5 / 4 * Z ^ 4) := by
          have : (1 / 8 : ℝ) * Z ^ 4 = ((5 / 4 - 1) / 2) * Z ^ 4 := by ring
          rw [this]
          exact div_le_div_of_nonneg_left (by positivity)
            (Real.log_pos (by nlinarith [pow_pos hZ0 4, hZ1])) hlog_le
      _ ≤ (R₁.card : ℝ) := h1
  have hR₂_lo : (1 / 8) * Z ^ 10 / Real.log X ≤ (R₂.card : ℝ) := by
    have h1 := (hw_98 (2 * Z ^ 10) hU2).1
    rw [← hR₂_def] at h1
    have hleX : 9 / 8 * (2 * Z ^ 10) ≤ X := by
      have : Z ^ 11 ≤ Z ^ 36 := pow_le_pow_right₀ hZ1 (by decide)
      have h11 : 9 / 8 * (2 * Z ^ 10) ≤ Z * Z ^ 10 := by
        calc 9 / 8 * (2 * Z ^ 10) = (9 / 4) * Z ^ 10 := by ring
          _ ≤ Z * Z ^ 10 := mul_le_mul_of_nonneg_right (by linarith only [hZ8]) (by positivity)
      rw [← hZ36]; linarith [show Z * Z ^ 10 = Z ^ 11 by ring]
    have hlog_le : Real.log (9 / 8 * (2 * Z ^ 10)) ≤ Real.log X :=
      Real.log_le_log (by positivity) hleX
    calc (1 / 8) * Z ^ 10 / Real.log X
        ≤ ((9 / 8 - 1) / 2) * (2 * Z ^ 10) / Real.log (9 / 8 * (2 * Z ^ 10)) := by
          have : (1 / 8 : ℝ) * Z ^ 10 = ((9 / 8 - 1) / 2) * (2 * Z ^ 10) := by ring
          rw [this]
          exact div_le_div_of_nonneg_left (by positivity)
            (Real.log_pos (by nlinarith [pow_pos hZ0 10, hZ1])) hlog_le
      _ ≤ (R₂.card : ℝ) := h1
  obtain ⟨Q_pos, hQ_def⟩ : ∃ Q_pos : Finset ℕ, Q_pos = windowPrimes (3 * Z ^ 10) (Z ^ 11 / 2) :=
    ⟨_, rfl⟩
  have hQ_sub : ∀ r₁ ∈ Q_pos, r₁.Prime ∧ 3 * Z ^ 10 < (r₁ : ℝ) ∧ (r₁ : ℝ) ≤ Z ^ 11 / 2 :=
    fun r₁ hr₁ => by
      rw [hQ_def] at hr₁; exact (mem_windowPrimes (by positivity) (by positivity)).mp hr₁
  have hQ_recip : (1 / 24 : ℝ) ≤ ∑ r₁ ∈ Q_pos, 1 / (r₁ : ℝ) := by
    let A_n := ⌊3 * Z ^ 10⌋₊
    let B_n := ⌊Z ^ 11 / 2⌋₊
    have h3Z10_ge2 : 2 ≤ 3 * Z ^ 10 := by
      have : 1 ≤ Z ^ 10 := one_le_pow₀ hZ1
      linarith
    have hZ11_ge : 8 * Z ^ 10 ≤ Z ^ 11 := by
      calc 8 * Z ^ 10 ≤ Z * Z ^ 10 := mul_le_mul_of_nonneg_right hZ8 (by positivity)
        _ = Z ^ 11 := by ring
    have hA1 : 1 ≤ A_n := (Nat.one_le_floor_iff _).mpr (by linarith)
    have hAB : A_n ≤ B_n := Nat.floor_le_floor (by linarith)
    have hmert := mertensFirst_general_block_ge hA1 hAB
    rw [← windowPrimes_eq_primesLE_sdiff_nat, ← hQ_def] at hmert
    have hlogA : Real.log A_n ≤ Real.log (3 * Z ^ 10) :=
      Real.log_le_log (by exact_mod_cast hA1) (Nat.floor_le (by positivity))
    have hB_ge : Z ^ 11 / 4 ≤ (B_n : ℝ) := by
      have := Nat.lt_floor_add_one (Z ^ 11 / 2)
      dsimp [B_n]; linarith
    have hlogB : Real.log (Z ^ 11 / 4) ≤ Real.log B_n :=
      Real.log_le_log (by positivity) hB_ge
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogA
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlogB
    norm_num1 at hlogA hlogB
    have hsum_log : (1 / 2) * Real.log Z ≤ ∑ r₁ ∈ Q_pos, Real.log r₁ / r₁ := by
      linarith [hmert, hlogA, hlogB, hLmert]
    have hsum_le : ∑ r₁ ∈ Q_pos, Real.log r₁ / r₁ ≤
        (11 * Real.log Z) * ∑ r₁ ∈ Q_pos, 1 / (r₁ : ℝ) := by
      rw [mul_sum]
      refine sum_le_sum fun r₁ hr₁ => ?_
      obtain ⟨hr₁_pr, _, hr₁_hi⟩ := hQ_sub r₁ hr₁
      have hr₁_0 : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pr.pos
      have hlr₁ : Real.log r₁ ≤ 11 * Real.log Z := by
        have h := Real.log_le_log hr₁_0 (hr₁_hi.trans (by linarith [pow_pos hZ0 11] : Z ^ 11 / 2 ≤ Z ^ 11))
        rw [Real.log_pow] at h; norm_num1 at h; exact h
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right hlr₁ (inv_nonneg.mpr hr₁_0.le)
    have hlogZ_pos : 0 < Real.log Z := Real.log_pos (by linarith only [hZ8])
    apply le_of_mul_le_mul_left _ (show (0 : ℝ) < 24 * Real.log Z by positivity)
    have hnonneg : 0 ≤ ∑ r₁ ∈ Q_pos, 1 / (r₁ : ℝ) := sum_nonneg fun _ _ => by positivity
    nlinarith [hsum_log.trans hsum_le, hlogZ_pos, hnonneg]
  have hfib_rough : ∀ pq ∈ R₁ ×ˢ R₂,
      10 * (fibrePos X (pq.1 * pq.2)).card ≤ 9 * (fibreNeg X (pq.1 * pq.2)).card ∧
      (8 / 45) * Z ^ 22 / Real.log X ≤ ((fibreNeg X (pq.1 * pq.2)).card : ℝ) ∧
      (1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X) ≤ ((fibrePos X (pq.1 * pq.2)).card : ℝ) := by
    rintro ⟨q₁, q₂⟩ hpq
    dsimp only
    obtain ⟨hq₁R, hq₂R⟩ := mem_product.mp hpq
    dsimp only at hq₁R hq₂R
    obtain ⟨h10, hneg_b⟩ := roughFibre_neg_and_cap_bounds X q₁ q₂ Z S_cap hX1 hX64 hZ8 hZ36 hScap
      (hR₁_sub q₁ hq₁R) (hR₂_sub q₂ hq₂R) (fun u hu => (hw_2 u (hU3.trans hu)).1) hS_cap
    exact ⟨h10, hneg_b, roughFibre_pos_lower_bound X q₁ q₂ Z Q_pos hX64 hZ8 hZ36
      (hR₁_sub q₁ hq₁R) (hR₂_sub q₂ hq₂R) hQ_sub hQ_recip
      (fun u hu => (hw_2 u (hU3.trans hu)).1)⟩
  let A_rc := roughFibreCofactors X
  have hpos_union : posParity (fibreUnion X A_rc) = A_rc.biUnion (fibrePos X) := by
    ext n; simp only [posParity, fibreUnion, mem_filter, mem_biUnion, mem_union]
    constructor
    · rintro ⟨⟨a, ha, hp | hn⟩, hμ⟩
      · exact ⟨a, ha, hp⟩
      · have := (mem_filter.mp (mem_filter.mp hn).1).2; omega
    · rintro ⟨a, ha, hp⟩
      exact ⟨⟨a, ha, Or.inl hp⟩, (mem_filter.mp (mem_filter.mp hp).1).2⟩
  have hneg_union : negParity (fibreUnion X A_rc) = A_rc.biUnion (fibreNeg X) := by
    ext n; simp only [negParity, fibreUnion, mem_filter, mem_biUnion, mem_union]
    constructor
    · rintro ⟨⟨a, ha, hp | hn⟩, hμ⟩
      · have := (mem_filter.mp (mem_filter.mp hp).1).2; omega
      · exact ⟨a, ha, hn⟩
    · rintro ⟨a, ha, hn⟩
      exact ⟨⟨a, ha, Or.inr hn⟩, (mem_filter.mp (mem_filter.mp hn).1).2⟩
  have hdisj_pos : (A_rc : Set ℕ).PairwiseDisjoint (fibrePos X) :=
    fun _ _ _ _ hne => ((evenPrefixCofactor_complete_bipartite_fibres hX1).1 hne).1
  have hdisj_neg : (A_rc : Set ℕ).PairwiseDisjoint (fibreNeg X) :=
    fun _ _ _ _ hne => ((evenPrefixCofactor_complete_bipartite_fibres hX1).1 hne).2
  have hcard_pos_eq : (posParity (fibreUnion X A_rc)).card =
      ∑ pq ∈ R₁ ×ˢ R₂, (fibrePos X (pq.1 * pq.2)).card := by
    rw [hpos_union, card_biUnion hdisj_pos]
    dsimp only [A_rc]
    rw [hrc_eq, sum_image hinj_rc]
  have hcard_neg_eq : (negParity (fibreUnion X A_rc)).card =
      ∑ pq ∈ R₁ ×ˢ R₂, (fibreNeg X (pq.1 * pq.2)).card := by
    rw [hneg_union, card_biUnion hdisj_neg]
    dsimp only [A_rc]
    rw [hrc_eq, sum_image hinj_rc]
  have hneg_tot : c_neg * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
      ((negParity (fibreUnion X A_rc)).card : ℝ) := by
    rw [hcard_neg_eq, Nat.cast_sum]
    calc c_neg * (X : ℝ) / Real.log X ^ (3 : ℕ)
        = (((1 / 8) * Z ^ 4 / Real.log X) * ((1 / 8) * Z ^ 10 / Real.log X)) *
            ((8 / 45) * Z ^ 22 / Real.log X) := by
          rw [← hZ36]; dsimp [c_neg]; ring
      _ ≤ ((R₁.card : ℝ) * (R₂.card : ℝ)) * ((8 / 45) * Z ^ 22 / Real.log X) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hR₁_lo hR₂_lo (by positivity) (Nat.cast_nonneg _)) (by positivity)
      _ = ∑ _pq ∈ R₁ ×ˢ R₂, ((8 / 45) * Z ^ 22 / Real.log X) := by
          rw [sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ _ := sum_le_sum fun pq hpq => (hfib_rough pq hpq).2.1
  have hpos_tot : c_pos * (X : ℝ) / Real.log X ^ (3 : ℕ) ≤
      ((posParity (fibreUnion X A_rc)).card : ℝ) := by
    rw [hcard_pos_eq, Nat.cast_sum]
    calc c_pos * (X : ℝ) / Real.log X ^ (3 : ℕ)
        = (((1 / 8) * Z ^ 4 / Real.log X) * ((1 / 8) * Z ^ 10 / Real.log X)) *
            ((1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X)) := by
          rw [← hZ36]; dsimp [c_pos, c_neg]; ring
      _ ≤ ((R₁.card : ℝ) * (R₂.card : ℝ)) *
            ((1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hR₁_lo hR₂_lo (by positivity) (Nat.cast_nonneg _)) (by positivity)
      _ = ∑ _pq ∈ R₁ ×ˢ R₂, ((1 / 24) * ((8 / 45) * Z ^ 22 / Real.log X)) := by
          rw [sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
      _ ≤ _ := sum_le_sum fun pq hpq => (hfib_rough pq hpq).2.2
  refine ⟨hpos_tot, hneg_tot, fun {R} τ => ?_⟩
  have hglob := (fibreUnion_ordered_and_global_bounds hX1 A_rc).2.2 τ
  have hsum_eq : ∑ a ∈ A_rc, (((fibrePos X a).card : ℤ) - ((fibreNeg X a).card : ℤ)) =
      ((posParity (fibreUnion X A_rc)).card : ℤ) -
        ((negParity (fibreUnion X A_rc)).card : ℤ) := by
    rw [sum_sub_distrib, hpos_union, card_biUnion hdisj_pos, hneg_union, card_biUnion hdisj_neg,
      Nat.cast_sum, Nat.cast_sum]
  have h10_tot : 10 * (posParity (fibreUnion X A_rc)).card ≤
      9 * (negParity (fibreUnion X A_rc)).card := by
    rw [hcard_pos_eq, hcard_neg_eq, mul_sum, mul_sum]
    exact sum_le_sum fun pq hpq => (hfib_rough pq hpq).1
  have hunm_10 : (negParity (fibreUnion X A_rc)).card ≤ 10 * τ.unmatchedSet.card := by
    rw [hsum_eq] at hglob
    have hneg_abs := neg_le_abs
      (((posParity (fibreUnion X A_rc)).card : ℤ) - ((negParity (fibreUnion X A_rc)).card : ℤ))
    have hdiff : ((negParity (fibreUnion X A_rc)).card : ℤ) -
        ((posParity (fibreUnion X A_rc)).card : ℤ) ≤ (τ.unmatchedSet.card : ℤ) := by
      linarith only [hneg_abs, hglob]
    omega
  have hunm_r : ((negParity (fibreUnion X A_rc)).card : ℝ) / 10 ≤ (τ.unmatchedSet.card : ℝ) := by
    have : ((negParity (fibreUnion X A_rc)).card : ℝ) ≤ 10 * (τ.unmatchedSet.card : ℝ) :=
      by exact_mod_cast hunm_10
    linarith
  calc c_pers * (X : ℝ) / Real.log X ^ (3 : ℕ)
      = (c_neg * (X : ℝ) / Real.log X ^ (3 : ℕ)) / 10 := by dsimp [c_pers]; ring
    _ ≤ ((negParity (fibreUnion X A_rc)).card : ℝ) / 10 := by linarith
    _ ≤ (τ.unmatchedSet.card : ℝ) := hunm_r

/-- Every squarefree semiprime (`ω(m) = 2`) has `evenPrefixCofactor m = 1`. -/
theorem evenPrefixCofactor_eq_one_of_card_primeFactors_eq_two {m : ℕ}
    (hsq : Squarefree m) (hcard : m.primeFactors.card = 2) :
    evenPrefixCofactor m = 1 := by
  have hne : m.primeFactors.Nonempty := card_pos.mp (by omega)
  have heven : Even m.primeFactors.card := by rw [hcard]; exact ⟨1, rfl⟩
  let d₂ := m.primeFactors.max' hne
  have hd₂ : d₂ ∈ m.primeFactors := max'_mem _ hne
  have hcard_er : (m.primeFactors.erase d₂).card = 1 := by
    rw [card_erase_of_mem hd₂, hcard]
  obtain ⟨d₁, hd₁_eq⟩ := card_eq_one.mp hcard_er
  have hne_er : (m.primeFactors.erase d₂).Nonempty := by rw [hd₁_eq]; simp
  have hmax_er : (m.primeFactors.erase d₂).max' hne_er = d₁ := by
    simp [hd₁_eq]
  have hd₁_not_d₂ : d₁ ≠ d₂ := fun heq => by
    have hm : d₂ ∈ m.primeFactors.erase d₂ := by rw [hd₁_eq, heq]; simp
    exact notMem_erase d₂ _ hm
  have hpf_eq : m.primeFactors = {d₁, d₂} := by
    ext x
    constructor
    · intro hx
      by_cases hxd₂ : x = d₂
      · simp [hxd₂]
      · have hxer : x ∈ m.primeFactors.erase d₂ := mem_erase.mpr ⟨hxd₂, hx⟩
        rw [hd₁_eq] at hxer
        simp [mem_singleton.mp hxer]
    · intro hx
      rcases mem_insert.mp hx with rfl | hx'
      · exact mem_of_mem_erase (by rw [hd₁_eq]; simp)
      · rwa [mem_singleton.mp hx']
  have hm_eq : m = d₁ * d₂ := by
    rw [← Nat.prod_primeFactors_of_squarefree hsq, hpf_eq, prod_pair hd₁_not_d₂]
  unfold evenPrefixCofactor
  simp only [dif_pos hne, if_pos heven, show m.primeFactors.max' hne = d₂ from rfl,
    dif_pos hne_er, hmax_er]
  rw [hm_eq]
  exact Nat.div_self (Nat.pos_of_ne_zero (hm_eq ▸ hsq.ne_zero))

/-- Every squarefree `4`-prime product (`ω(m) = 4`) has `evenPrefixCofactor m ≤ u * v` for any two
distinct prime factors `u ≠ v` of `m`. -/
theorem evenPrefixCofactor_le_mul_of_card_primeFactors_eq_four {m u v : ℕ}
    (hsq : Squarefree m) (hcard : m.primeFactors.card = 4)
    (hu : u ∈ m.primeFactors) (hv : v ∈ m.primeFactors) (huv : u ≠ v) :
    evenPrefixCofactor m ≤ u * v := by
  have hne : m.primeFactors.Nonempty := card_pos.mp (by omega)
  have heven : Even m.primeFactors.card := by rw [hcard]; exact ⟨2, rfl⟩
  let d₄ := m.primeFactors.max' hne
  have hd₄ : d₄ ∈ m.primeFactors := max'_mem _ hne
  have hcard_er1 : (m.primeFactors.erase d₄).card = 3 := by
    rw [card_erase_of_mem hd₄, hcard]
  have hne_er : (m.primeFactors.erase d₄).Nonempty := card_pos.mp (by omega)
  let d₃ := (m.primeFactors.erase d₄).max' hne_er
  have hd₃_er : d₃ ∈ m.primeFactors.erase d₄ := max'_mem _ hne_er
  have hd₃ : d₃ ∈ m.primeFactors := mem_of_mem_erase hd₃_er
  have hd₃_ne_d₄ : d₃ ≠ d₄ := (mem_erase.mp hd₃_er).1
  let S₂ := (m.primeFactors.erase d₄).erase d₃
  have hcard_S₂ : S₂.card = 2 := by
    rw [card_erase_of_mem hd₃_er, hcard_er1]
  obtain ⟨x₁, x₂, hx_ne, hS₂_eq⟩ := card_eq_two.mp hcard_S₂
  have hm_prod : (∏ p ∈ S₂, p) * (d₃ * d₄) = m := by
    have hdisj : Disjoint S₂ {d₃, d₄} := by
      rw [disjoint_left]
      intro x hx htop
      rcases mem_insert.mp htop with rfl | hx4
      · exact notMem_erase d₃ _ hx
      · rw [mem_singleton.mp hx4] at hx
        exact notMem_erase d₄ _ (mem_of_mem_erase hx)
    have hunion : S₂ ∪ {d₃, d₄} = m.primeFactors := by
      ext x; simp only [S₂, mem_union, mem_erase, mem_insert, mem_singleton]
      exact ⟨fun h => h.elim (fun h1 => h1.2.2)
          (fun h2 => h2.elim (fun e => e ▸ hd₃) (fun e => e ▸ hd₄)),
        fun hx => by tauto⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq, ← hunion, prod_union hdisj,
      prod_pair hd₃_ne_d₄]
  have hepc_eq : evenPrefixCofactor m = x₁ * x₂ := by
    unfold evenPrefixCofactor
    simp only [dif_pos hne, if_pos heven, show m.primeFactors.max' hne = d₄ from rfl,
      dif_pos hne_er, show (m.primeFactors.erase d₄).max' hne_er = d₃ from rfl]
    have hpos : 0 < d₃ * d₄ := Nat.mul_pos (Nat.prime_of_mem_primeFactors hd₃).pos
      (Nat.prime_of_mem_primeFactors hd₄).pos
    rw [← hm_prod, Nat.mul_div_cancel _ hpos, hS₂_eq, prod_pair hx_ne]
  have hle_out : ∀ x ∈ S₂, ∀ y ∈ m.primeFactors, y ∉ S₂ → x ≤ y := by
    intro x hx y hy hynot
    by_cases hy4 : y = d₄
    · exact hy4 ▸ le_max' _ x (mem_of_mem_erase (mem_of_mem_erase hx))
    · have hy3 : y = d₃ := by
        by_contra hy3
        exact hynot (mem_erase.mpr ⟨hy3, mem_erase.mpr ⟨hy4, hy⟩⟩)
      exact hy3 ▸ le_max' _ x (mem_of_mem_erase hx)
  rw [hepc_eq]
  have hx₁S : x₁ ∈ S₂ := by rw [hS₂_eq]; simp
  have hx₂S : x₂ ∈ S₂ := by rw [hS₂_eq]; simp
  by_cases huS : u ∈ S₂ <;> by_cases hvS : v ∈ S₂
  · rw [hS₂_eq] at huS hvS
    rcases mem_insert.mp huS with rfl | hu' <;> rcases mem_insert.mp hvS with rfl | hv'
    · exact False.elim (huv rfl)
    · rw [mem_singleton.mp hv']
    · rw [mem_singleton.mp hu', mul_comm]
    · exact False.elim (huv ((mem_singleton.mp hu').trans (mem_singleton.mp hv').symm))
  · rw [hS₂_eq] at huS
    rcases mem_insert.mp huS with rfl | hu'
    · exact Nat.mul_le_mul_left _ (hle_out x₂ hx₂S v hv hvS)
    · rw [mem_singleton.mp hu', mul_comm]
      exact Nat.mul_le_mul_left _ (hle_out x₁ hx₁S v hv hvS)
  · rw [hS₂_eq] at hvS
    rcases mem_insert.mp hvS with rfl | hv'
    · rw [mul_comm u]
      exact Nat.mul_le_mul_left _ (hle_out x₂ hx₂S u hu huS)
    · rw [mem_singleton.mp hv']
      exact Nat.mul_le_mul_right _ (hle_out x₁ hx₁S u hu huS)
  · exact Nat.mul_le_mul (hle_out x₁ hx₁S u hu huS) (hle_out x₂ hx₂S v hv hvS)

/-- **Cofactor-scale jump barrier (`(evenPrefixCofactor m)² < X`)**:
for every `X : ℕ`, every pilot vertex `n ∈ pilotVertices X`, and every `m ∈ (X, 2X]` adjacent to
`n` under `GlobalDyadicOneTwoRel`, the even-prefix cofactor of `m` satisfies
`(evenPrefixCofactor m)² < X`. -/
theorem pilotVertices_neighbor_cofactor_sq_lt {X m n : ℕ}
    (hn : n ∈ pilotVertices X) (hm : m ∈ Ioc X (2 * X))
    (hadj : GlobalDyadicOneTwoRel m n) :
    (evenPrefixCofactor m) ^ 2 < X := by
  let Y : ℝ := (X : ℝ) ^ (1 / 3 : ℝ)
  unfold pilotVertices fibreUnion pilotCofactors at hn
  obtain ⟨a, ha_pc, hna⟩ := mem_biUnion.mp hn
  obtain ⟨⟨p₁, p₂⟩, hpq, rfl⟩ := mem_image.mp ha_pc
  dsimp only at hna
  obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
  dsimp only at hp₁W hp₂W
  obtain ⟨hp₁_pr_raw, hp₁_lo_raw, hp₁_hi_raw⟩ :=
    (mem_windowPrimes (by positivity) (by positivity)).mp hp₁W
  change Y / 8 < (p₁ : ℝ) at hp₁_lo_raw
  change (p₁ : ℝ) ≤ 4 / 3 * (Y / 8) at hp₁_hi_raw
  have hY12 : 12 ≤ Y := by
    have : (2 : ℝ) ≤ p₁ := by exact_mod_cast hp₁_pr_raw.two_le
    linarith
  have hY0 : 0 < Y := by linarith
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hY3 : Y ^ (3 : ℕ) = (X : ℝ) := by
    rw [show Y = (X : ℝ) ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_natCast, ← Real.rpow_mul hX0]
    norm_num
  have hX1728 : 1728 ≤ (X : ℝ) := by
    rw [← hY3]
    calc (1728 : ℝ) = 12 ^ (3 : ℕ) := by norm_num
      _ ≤ Y ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hY12 3
  have hX1 : 1 ≤ X := by exact_mod_cast (by linarith : (1 : ℝ) ≤ X)
  obtain ⟨hp₂_pr, hp₂_lo, hp₂_hi⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂W
  have hpq_pos : 0 < p₁ * p₂ := Nat.mul_pos hp₁_pr_raw.pos hp₂_pr.pos
  have hpos_emp : fibrePos X (p₁ * p₂) = ∅ := by
    apply fibrePos_eq_empty_of_primeFactor_sq_ge hX1
      (Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ p₁, hpq_pos.ne'⟩)
    have hp₂_cube : 8 * Y ^ (3 : ℕ) ≤ (p₂ : ℝ) ^ (3 : ℕ) := by
      calc 8 * Y ^ (3 : ℕ) = (2 * Y) ^ (3 : ℕ) := by ring
        _ ≤ (p₂ : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) hp₂_lo.le 3
    have hgt : 2 * (X : ℝ) ≤ ((p₁ * p₂ * p₂ ^ 2 : ℕ) : ℝ) := by
      push_cast
      calc 2 * (X : ℝ) ≤ (Y / 8) * (8 * Y ^ (3 : ℕ)) := by rw [hY3]; nlinarith [hY12]
        _ ≤ (p₁ : ℝ) * (p₂ : ℝ) ^ (3 : ℕ) :=
            mul_le_mul hp₁_lo_raw.le hp₂_cube (by positivity) (Nat.cast_nonneg _)
        _ = (p₁ : ℝ) * p₂ * (p₂ : ℝ) ^ 2 := by ring
    exact_mod_cast hgt
  rw [hpos_emp, empty_union] at hna
  obtain ⟨_, _, p₃, hp₃_pr, hna_eq, hlt_p₃⟩ := mem_fibreNeg_structure hX1 hna
  obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hna).1).1
  have hp₁_lt_p₂ : p₁ < p₂ := by exact_mod_cast (by linarith : (p₁ : ℝ) < p₂)
  have hp₂_lt_p₃ : p₂ < p₃ := hlt_p₃ p₂ (Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ p₁, hpq_pos.ne'⟩)
  have hn_pf : n.primeFactors = {p₁, p₂, p₃} := by
    rw [hna_eq, Nat.primeFactors_mul hpq_pos.ne' hp₃_pr.ne_zero,
      Nat.primeFactors_mul hp₁_pr_raw.ne_zero hp₂_pr.ne_zero,
      hp₁_pr_raw.primeFactors, hp₂_pr.primeFactors, hp₃_pr.primeFactors]
    ext d; simp only [mem_union, mem_singleton, mem_insert]; tauto
  have hn_card : n.primeFactors.card = 3 := by
    rw [hn_pf, card_insert_of_notMem (by simp [hp₁_lt_p₂.ne, (hp₁_lt_p₂.trans hp₂_lt_p₃).ne]),
      card_pair hp₂_lt_p₃.ne]
  obtain ⟨hsq_m, hsq_n, hμ_sum, c, p, q, r, hpp, hqp, hrp, hqr, hbr⟩ := hadj
  have hμ_n : μ n = -1 := (mem_filter.mp (mem_filter.mp hna).1).2
  have hμ_m : μ m = 1 := by omega
  rcases hbr with ⟨hm_cp, hn_cqr⟩ | ⟨hn_cp, hm_cqr⟩
  · -- Branch 1 (`m = c * p`, `n = c * (q * r)`): `m` is squarefree with `ω(m) = 2`
    have hc_ne : c ≠ 0 := fun h0 => by rw [h0, zero_mul] at hn_cqr; omega
    obtain ⟨hcop_c_qr, _, _⟩ := Nat.squarefree_mul_iff.mp (hn_cqr ▸ hsq_n)
    have hdisj_c_qr : Disjoint c.primeFactors (q * r).primeFactors :=
      Nat.Coprime.disjoint_primeFactors hcop_c_qr
    have hqr_card : (q * r).primeFactors.card = 2 := by
      rw [Nat.primeFactors_mul hqp.ne_zero hrp.ne_zero, hqp.primeFactors, hrp.primeFactors,
        union_comm, singleton_union, card_pair hqr.ne']
    have hc_card : c.primeFactors.card = 1 := by
      have h3 := hn_card
      rw [hn_cqr, Nat.primeFactors_mul hc_ne (Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero),
        card_union_of_disjoint hdisj_c_qr, hqr_card] at h3
      omega
    obtain ⟨hcop_c_p, _, _⟩ := Nat.squarefree_mul_iff.mp (hm_cp ▸ hsq_m)
    have hm_card : m.primeFactors.card = 2 := by
      rw [hm_cp, Nat.primeFactors_mul hc_ne hpp.ne_zero,
        card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hcop_c_p),
        hc_card, hpp.primeFactors, card_singleton]
    rw [evenPrefixCofactor_eq_one_of_card_primeFactors_eq_two hsq_m hm_card]
    exact_mod_cast (show (1 : ℝ) < X by linarith)
  · -- Branch 2 (`n = c * p`, `m = c * (q * r)`): `m` is squarefree with `ω(m) = 4`
    have hc_ne : c ≠ 0 := fun h0 => by rw [h0, zero_mul] at hn_cp; omega
    obtain ⟨hcop_c_p, _, _⟩ := Nat.squarefree_mul_iff.mp (hn_cp ▸ hsq_n)
    have hc_card : c.primeFactors.card = 2 := by
      have h3 := hn_card
      rw [hn_cp, Nat.primeFactors_mul hc_ne hpp.ne_zero,
        card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hcop_c_p),
        hpp.primeFactors, card_singleton] at h3
      omega
    obtain ⟨hcop_c_qr, _, _⟩ := Nat.squarefree_mul_iff.mp (hm_cqr ▸ hsq_m)
    have hqr_card : (q * r).primeFactors.card = 2 := by
      rw [Nat.primeFactors_mul hqp.ne_zero hrp.ne_zero, hqp.primeFactors, hrp.primeFactors,
        union_comm, singleton_union, card_pair hqr.ne']
    have hm_card : m.primeFactors.card = 4 := by
      rw [hm_cqr, Nat.primeFactors_mul hc_ne (Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero),
        card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hcop_c_qr), hc_card, hqr_card]
    have hp_mem_n : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hn_cp ▸ dvd_mul_left p c, hsq_n.ne_zero⟩
    have hq_mem_m : q ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hm_cqr ▸ dvd_mul_of_dvd_right (dvd_mul_right q r) c, hsq_m.ne_zero⟩
    have hr_mem_m : r ∈ m.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hrp, hm_cqr ▸ dvd_mul_of_dvd_right (dvd_mul_left r q) c, hsq_m.ne_zero⟩
    have hm_hi : (m : ℝ) ≤ 2 * X := by exact_mod_cast (mem_Ioc.mp hm).2
    have hnq_r : (X : ℝ) < n := by exact_mod_cast hn_lo
    have hc_r : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc_ne
    have hqr_le_div : (q : ℝ) * r ≤ 2 * (X : ℝ) / c := by
      rw [le_div_iff₀ hc_r]
      have : ((m : ℕ) : ℝ) = (q : ℝ) * r * c := by rw [hm_cqr]; push_cast; ring
      linarith
    have hq_sq_lt : (q : ℝ) ^ 2 < (q : ℝ) * r := by
      rw [sq]; exact mul_lt_mul_of_pos_left (by exact_mod_cast hqr) (by exact_mod_cast hqp.pos)
    have hp₁_sq_le : (p₁ : ℝ) ^ 2 ≤ Y ^ 2 / 36 := by
      have hp₁_6 : (p₁ : ℝ) ≤ Y / 6 := by linarith
      calc (p₁ : ℝ) ^ 2 ≤ (Y / 6) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hp₁_6 2
        _ = Y ^ 2 / 36 := by ring
    have hq_qr : q ∈ (q * r).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, dvd_mul_right q r, Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero⟩
    rw [hn_pf] at hp_mem_n
    rcases mem_insert.mp hp_mem_n with hp_eq | hp_rest
    · -- Subcase `p = p₁`: `c = p₂ * p₃`, `evenPrefixCofactor m ≤ q * r`
      rw [hp_eq] at hn_cp
      have hc_eq : c = p₂ * p₃ :=
        Nat.eq_of_mul_eq_mul_right hp₁_pr_raw.pos (by rw [← hn_cp, hna_eq]; ring)
      have hc_gt : 6 * Y ^ 2 < (c : ℝ) := by
        have hp₁_6 : (p₁ : ℝ) ≤ Y / 6 := by linarith
        have hcp₁ : (c : ℝ) * p₁ = n := by exact_mod_cast hn_cp.symm
        have : 6 * Y ^ 2 * (p₁ : ℝ) ≤ X := by
          calc 6 * Y ^ 2 * (p₁ : ℝ) ≤ 6 * Y ^ 2 * (Y / 6) :=
                mul_le_mul_of_nonneg_left hp₁_6 (by positivity)
            _ = X := by rw [← hY3]; ring
        have hlt : 6 * Y ^ 2 * (p₁ : ℝ) < (c : ℝ) * p₁ := by linarith
        exact lt_of_mul_lt_mul_right hlt (Nat.cast_nonneg p₁)
      have hqr_lt : (q : ℝ) * r < Y / 3 := by
        refine hqr_le_div.trans_lt ?_
        rw [div_lt_iff₀ hc_r]
        calc 2 * (X : ℝ) = (Y / 3) * (6 * Y ^ 2) := by rw [← hY3]; ring
          _ < (Y / 3) * c := mul_lt_mul_of_pos_left hc_gt (by positivity)
      have hepc_le := evenPrefixCofactor_le_mul_of_card_primeFactors_eq_four
        hsq_m hm_card hq_mem_m hr_mem_m hqr.ne
      have hepc_r : (evenPrefixCofactor m : ℝ) < Y / 3 :=
        (show (evenPrefixCofactor m : ℝ) ≤ (q : ℝ) * r by exact_mod_cast hepc_le).trans_lt hqr_lt
      have hsq_lt : ((evenPrefixCofactor m : ℝ)) ^ 2 < X := by
        calc (evenPrefixCofactor m : ℝ) ^ 2 < (Y / 3) ^ 2 :=
              pow_lt_pow_left₀ hepc_r (Nat.cast_nonneg _) two_ne_zero
          _ ≤ Y ^ 3 := by nlinarith [hY12, sq_nonneg Y]
          _ = X := hY3
      exact_mod_cast hsq_lt
    · rcases mem_insert.mp hp_rest with hp_eq | hp_p₃
      · -- Subcase `p = p₂`: `c = p₁ * p₃`, `p₁ ∈ c.primeFactors`, `evenPrefixCofactor m ≤ p₁ * q`
        rw [hp_eq] at hn_cp
        have hc_eq : c = p₁ * p₃ :=
          Nat.eq_of_mul_eq_mul_right hp₂_pr.pos (by rw [← hn_cp, hna_eq]; ring)
        have hp₁_mem_c : p₁ ∈ c.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp₁_pr_raw, hc_eq ▸ dvd_mul_right p₁ p₃, hc_ne⟩
        have hp₁_mem_m : p₁ ∈ m.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp₁_pr_raw,
            hm_cqr ▸ dvd_mul_of_dvd_left (hc_eq ▸ dvd_mul_right p₁ p₃) _, hsq_m.ne_zero⟩
        have hp₁_ne_q : p₁ ≠ q := fun heq => by
          rw [heq] at hp₁_mem_c
          exact disjoint_left.mp (Nat.Coprime.disjoint_primeFactors hcop_c_qr) hp₁_mem_c hq_qr
        have hc_gt : (4 / 9) * Y ^ 2 < (c : ℝ) := by
          have hp₂_94 : (p₂ : ℝ) ≤ (9 / 4) * Y := by linarith
          have hcp₂ : (c : ℝ) * p₂ = n := by exact_mod_cast hn_cp.symm
          have : (4 / 9) * Y ^ 2 * (p₂ : ℝ) ≤ X := by
            calc (4 / 9) * Y ^ 2 * (p₂ : ℝ) ≤ (4 / 9) * Y ^ 2 * ((9 / 4) * Y) :=
                  mul_le_mul_of_nonneg_left hp₂_94 (by positivity)
              _ = X := by rw [← hY3]; ring
          exact lt_of_mul_lt_mul_right (by linarith : (4 / 9) * Y ^ 2 * (p₂ : ℝ) < (c : ℝ) * p₂)
            (Nat.cast_nonneg p₂)
        have hq_sq_hi : (q : ℝ) ^ 2 < (9 / 2) * Y := by
          refine hq_sq_lt.trans (hqr_le_div.trans_lt ?_)
          rw [div_lt_iff₀ hc_r]
          calc 2 * (X : ℝ) = ((9 / 2) * Y) * ((4 / 9) * Y ^ 2) := by rw [← hY3]; ring
            _ < ((9 / 2) * Y) * c := mul_lt_mul_of_pos_left hc_gt (by positivity)
        have hepc_le := evenPrefixCofactor_le_mul_of_card_primeFactors_eq_four
          hsq_m hm_card hp₁_mem_m hq_mem_m hp₁_ne_q
        have hepc_r : (evenPrefixCofactor m : ℝ) ≤ (p₁ : ℝ) * q := by exact_mod_cast hepc_le
        have hsq_lt : (evenPrefixCofactor m : ℝ) ^ 2 < X := by
          calc (evenPrefixCofactor m : ℝ) ^ 2 ≤ ((p₁ : ℝ) * q) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hepc_r 2
            _ = (p₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 := by ring
            _ ≤ (Y ^ 2 / 36) * ((9 / 2) * Y) :=
                mul_le_mul hp₁_sq_le hq_sq_hi.le (sq_nonneg _) (by positivity)
            _ = (1 / 8) * X := by rw [← hY3]; ring
            _ < X := by linarith
        exact_mod_cast hsq_lt
      · -- Subcase `p = p₃`: `c = p₁ * p₂`, `p₁ ∈ c.primeFactors`, `evenPrefixCofactor m ≤ p₁ * q`
        rw [mem_singleton.mp hp_p₃] at hn_cp
        have hc_eq : c = p₁ * p₂ :=
          Nat.eq_of_mul_eq_mul_right hp₃_pr.pos (by rw [← hn_cp, hna_eq])
        have hp₁_mem_c : p₁ ∈ c.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp₁_pr_raw, hc_eq ▸ dvd_mul_right p₁ p₂, hc_ne⟩
        have hp₁_mem_m : p₁ ∈ m.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp₁_pr_raw,
            hm_cqr ▸ dvd_mul_of_dvd_left (hc_eq ▸ dvd_mul_right p₁ p₂) _, hsq_m.ne_zero⟩
        have hp₁_ne_q : p₁ ≠ q := fun heq => by
          rw [heq] at hp₁_mem_c
          exact disjoint_left.mp (Nat.Coprime.disjoint_primeFactors hcop_c_qr) hp₁_mem_c hq_qr
        have hc_gt : (1 / 4) * Y ^ 2 < (c : ℝ) := by
          rw [hc_eq]; push_cast
          calc (1 / 4) * Y ^ 2 = (Y / 8) * (2 * Y) := by ring
            _ < (p₁ : ℝ) * p₂ := mul_lt_mul'' hp₁_lo_raw hp₂_lo (by positivity) (by positivity)
        have hq_sq_hi : (q : ℝ) ^ 2 < 8 * Y := by
          refine hq_sq_lt.trans (hqr_le_div.trans_lt ?_)
          rw [div_lt_iff₀ hc_r]
          calc 2 * (X : ℝ) = (8 * Y) * ((1 / 4) * Y ^ 2) := by rw [← hY3]; ring
            _ < (8 * Y) * c := mul_lt_mul_of_pos_left hc_gt (by positivity)
        have hepc_le := evenPrefixCofactor_le_mul_of_card_primeFactors_eq_four
          hsq_m hm_card hp₁_mem_m hq_mem_m hp₁_ne_q
        have hepc_r : (evenPrefixCofactor m : ℝ) ≤ (p₁ : ℝ) * q := by exact_mod_cast hepc_le
        have hsq_lt : (evenPrefixCofactor m : ℝ) ^ 2 < X := by
          calc (evenPrefixCofactor m : ℝ) ^ 2 ≤ ((p₁ : ℝ) * q) ^ 2 :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hepc_r 2
            _ = (p₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 := by ring
            _ ≤ (Y ^ 2 / 36) * (8 * Y) :=
                mul_le_mul hp₁_sq_le hq_sq_hi.le (sq_nonneg _) (by positivity)
            _ = (2 / 9) * X := by rw [← hY3]; ring
            _ < X := by linarith
        exact_mod_cast hsq_lt

/-- **100% pilot debt isolation on large-cofactor fibre classes (`a² ≥ X`)**:
every `pilotCofactors X` element satisfies `X ≤ a²` once `4096 ≤ X`, and for **any** `X : ℕ`,
**any** cofactor class `A` with `∀ a ∈ A, X ≤ a²` (`pilotCofactors X ⊆ A`), and **any**
`GlobalDyadicOneTwoRel` involution `τ` confined to `fibreUnion X A`, **100%** of `pilotVertices X`
remains in `τ.unmatchedSet`. -/
theorem pilotVertices_isolated_on_large_cofactor_class {X : ℕ} {A : Finset ℕ}
    (hA_large : ∀ a ∈ A, X ≤ a ^ 2) (hA_pil : pilotCofactors X ⊆ A)
    (τ : FactorizationInvolution GlobalDyadicOneTwoRel (fibreUnion X A)) :
    pilotVertices X ⊆ τ.unmatchedSet ∧
      (4096 ≤ X → ∀ a ∈ pilotCofactors X, X ≤ a ^ 2) := by
  refine ⟨fun n hn => ?_, fun hX4096 a ha => ?_⟩
  · have hn_sub : pilotVertices X ⊆ fibreUnion X A := fun k hk => by
      obtain ⟨b, hb, hkb⟩ := mem_biUnion.mp hk
      exact mem_biUnion.mpr ⟨b, hA_pil hb, hkb⟩
    have hn_in_A : n ∈ fibreUnion X A := hn_sub hn
    have hn_orig := hn
    unfold pilotVertices fibreUnion at hn
    obtain ⟨a₀, ha₀_pc, hna₀⟩ := mem_biUnion.mp hn
    have hn_neg : μ n = -1 := by
      rcases mem_union.mp hna₀ with hp | hneg
      · unfold pilotCofactors at ha₀_pc
        obtain ⟨⟨p₁, p₂⟩, hpq, rfl⟩ := mem_image.mp ha₀_pc
        obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
        dsimp only at hp₁W hp₂W hp
        obtain ⟨hp₁_pr, hp₁_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁W
        have hY12 : 12 ≤ (X : ℝ) ^ (1 / 3 : ℝ) := by
          have : (2 : ℝ) ≤ p₁ := by exact_mod_cast hp₁_pr.two_le
          linarith
        have hY3 : ((X : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (X : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg X)]; norm_num
        have hX1 : 1 ≤ X := by
          have : (1728 : ℝ) ≤ X := by
            rw [← hY3]
            exact (show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num) ▸
              pow_le_pow_left₀ (by norm_num) hY12 3
          exact_mod_cast (by linarith : (1 : ℝ) ≤ X)
        obtain ⟨hp₂_pr, hp₂_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂W
        have hemp : fibrePos X (p₁ * p₂) = ∅ := by
          apply fibrePos_eq_empty_of_primeFactor_sq_ge hX1
            (Nat.mem_primeFactors.mpr ⟨hp₂_pr, dvd_mul_left p₂ p₁,
              (Nat.mul_pos hp₁_pr.pos hp₂_pr.pos).ne'⟩)
          have hp₂_cube : 8 * ((X : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) ≤ (p₂ : ℝ) ^ (3 : ℕ) := by
            calc 8 * ((X : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) =
                  (2 * (X : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by ring
              _ ≤ (p₂ : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (by positivity) hp₂_lo.le 3
          have hgt : 2 * (X : ℝ) ≤ ((p₁ * p₂ * p₂ ^ 2 : ℕ) : ℝ) := by
            push_cast
            calc 2 * (X : ℝ) ≤ ((X : ℝ) ^ (1 / 3 : ℝ) / 8) *
                  (8 * ((X : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ)) := by rw [hY3]; nlinarith [hY12]
              _ ≤ (p₁ : ℝ) * (p₂ : ℝ) ^ (3 : ℕ) :=
                  mul_le_mul hp₁_lo.le hp₂_cube (by positivity) (Nat.cast_nonneg _)
              _ = (p₁ : ℝ) * p₂ * (p₂ : ℝ) ^ 2 := by ring
          exact_mod_cast hgt
        rw [hemp] at hp
        exact False.elim (notMem_empty _ hp)
      · exact (mem_filter.mp (mem_filter.mp hneg).1).2
    have hsq_n : Squarefree n := squarefree_iff_moebius_ne_zero.mpr (by rw [hn_neg]; decide)
    rw [τ.unmatchedSet_eq_sdiff, mem_sdiff]
    refine ⟨mem_filter.mpr ⟨hn_in_A, hsq_n⟩, fun hmv => ?_⟩
    rw [τ.movedSet_eq_union, mem_union] at hmv
    rcases hmv with hpos | hneg_mv
    · have := (mem_filter.mp (τ.movedPos_subset hpos)).2; omega
    · obtain ⟨m, hm_pos, rfl⟩ := mem_image.mp (τ.image_movedPos.symm ▸ hneg_mv)
      have hm_A := (mem_filter.mp (τ.movedPos_subset hm_pos)).1
      have hμ_m := (mem_filter.mp (τ.movedPos_subset hm_pos)).2
      have hadj := τ.adj_pos m (mem_filter.mp hm_pos).2 hμ_m
      obtain ⟨b, hbA, hmb⟩ := mem_biUnion.mp hm_A
      have hm_fib : m ∈ fibrePos X b := by
        rcases mem_union.mp hmb with hp | hn'
        · exact hp
        · have := (mem_filter.mp (mem_filter.mp hn').1).2; omega
      have hm_Ioc : m ∈ Ioc X (2 * X) := (mem_filter.mp (mem_filter.mp hm_fib).1).1
      have hepc_b : evenPrefixCofactor m = b := (mem_filter.mp hm_fib).2
      have hlt_X := pilotVertices_neighbor_cofactor_sq_lt hn_orig hm_Ioc hadj
      rw [hepc_b] at hlt_X
      exact (hA_large b hbA).not_gt hlt_X
  · unfold pilotCofactors at ha
    obtain ⟨⟨p₁, p₂⟩, hpq, rfl⟩ := mem_image.mp ha
    obtain ⟨hp₁W, hp₂W⟩ := mem_product.mp hpq
    dsimp only at hp₁W hp₂W
    obtain ⟨_, hp₁_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₁W
    obtain ⟨_, hp₂_lo, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp₂W
    let Y : ℝ := (X : ℝ) ^ (1 / 3 : ℝ)
    change Y / 8 < (p₁ : ℝ) at hp₁_lo
    change 2 * Y < (p₂ : ℝ) at hp₂_lo
    have hY0 : 0 ≤ Y := Real.rpow_nonneg (Nat.cast_nonneg X) _
    have hY3 : Y ^ (3 : ℕ) = (X : ℝ) := by
      rw [show Y = (X : ℝ) ^ (1 / 3 : ℝ) from rfl, ← Real.rpow_natCast,
        ← Real.rpow_mul (Nat.cast_nonneg X)]; norm_num
    have hY16 : 16 ≤ Y := by
      apply (pow_le_pow_iff_left₀ (by norm_num) hY0 (by decide : 3 ≠ 0)).mp
      rw [hY3]; norm_num1; exact_mod_cast hX4096
    have ha_gt : Y ^ 2 / 4 < ((p₁ * p₂ : ℕ) : ℝ) := by
      push_cast
      calc Y ^ 2 / 4 = (Y / 8) * (2 * Y) := by ring
        _ < (p₁ : ℝ) * p₂ := mul_lt_mul'' hp₁_lo hp₂_lo (by positivity) (by positivity)
    have hsq_ge : (X : ℝ) ≤ (((p₁ * p₂) ^ 2 : ℕ) : ℝ) := by
      push_cast
      calc (X : ℝ) = Y ^ 3 := hY3.symm
        _ ≤ (Y ^ 2 / 4) ^ 2 := by nlinarith [hY16, pow_nonneg hY0 3]
        _ ≤ ((p₁ : ℝ) * p₂) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by exact_mod_cast ha_gt.le) 2
    exact_mod_cast hsq_ge

end GaloisForLFunctions.QuantitativeFactorizationMatching
