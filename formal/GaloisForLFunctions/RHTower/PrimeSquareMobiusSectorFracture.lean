import GaloisForLFunctions.RHTower.PrimeSquareMobiusComplementaryRecord
import GaloisForLFunctions.RHTower.MertensThirdTheorem

/-!
# CRT tensorization and the infinite-sector fracture of the Möbius clocks

This file formalizes §6 of the card `prime-square-mobius-fourier-complementary-record-law`:
the finite Euler clocks `m_P` built from the literal local Möbius factors converge pointwise to
`μ` (equation (4)) while their exact Gram matrix (equation (40)) shows that they become
asymptotically orthogonal to one another.
-/

open Complex Finset

namespace RHTower

noncomputable section

/-! ## The local Möbius clock as an arithmetic function -/

/-- The local Möbius factor of `p` at a natural number, equation (1). -/
def localMobiusNat (p n : ℕ) : ℤ := if p ^ 2 ∣ n then 0 else if p ∣ n then -1 else 1

/-- The finite Euler--Möbius clock of a finite prime set, equation (2). -/
def eulerClockNat (P : Finset ℕ) (n : ℕ) : ℤ := ∏ p ∈ P, localMobiusNat p n

/-- **Equation (4).**  As soon as `P` consists of primes and contains every prime divisor of a
nonzero `n`, the finite Euler clock agrees with the Möbius function at `n`. -/
theorem eulerClockNat_eq_moebius {P : Finset ℕ} {n : ℕ} (hn : n ≠ 0)
    (hP : ∀ p ∈ P, Nat.Prime p) (hcov : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ P) :
    eulerClockNat P n = ArithmeticFunction.moebius n := by
  classical
  by_cases hsq : Squarefree n
  · have hval : ∀ p ∈ P, localMobiusNat p n = if p ∣ n then -1 else 1 := by
      intro p hpP
      have hp2 : ¬ p ^ 2 ∣ n := by
        intro hcon
        have hpp : Nat.Prime p := hP p hpP
        have : p * p ∣ n := by
          rw [show p * p = p ^ 2 by ring]
          exact hcon
        exact hpp.not_isUnit (hsq p this)
      simp [localMobiusNat, hp2]
    have hfilter : P.filter (fun p => p ∣ n) = n.primeFactors := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primeFactors]
      constructor
      · rintro ⟨hpP, hpn⟩
        exact ⟨hP p hpP, hpn, hn⟩
      · rintro ⟨hpp, hpn, -⟩
        exact ⟨hcov p hpp hpn, hpn⟩
    have hprod : eulerClockNat P n = (-1 : ℤ) ^ (n.primeFactors.card) := by
      rw [eulerClockNat, Finset.prod_congr rfl hval, Finset.prod_ite, hfilter]
      simp
    rw [hprod, ArithmeticFunction.moebius_apply_of_squarefree hsq,
      ArithmeticFunction.cardFactors_apply]
    congr 1
    rw [show n.primeFactors = n.primeFactorsList.toFinset from rfl]
    exact List.toFinset_card_of_nodup ((Nat.squarefree_iff_nodup_primeFactorsList hn).mp hsq)
  · obtain ⟨p, hpp, hpdvd⟩ : ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ n := by
      by_contra hcon
      push Not at hcon
      exact hsq (Nat.squarefree_iff_prime_squarefree.mpr fun x hx => hcon x hx)
    have hpP : p ∈ P := hcov p hpp (dvd_trans (dvd_mul_left p p) hpdvd)
    have hzero : localMobiusNat p n = 0 := by
      have : p ^ 2 ∣ n := by rw [show p ^ 2 = p * p by ring]; exact hpdvd
      simp [localMobiusNat, this]
    rw [eulerClockNat, Finset.prod_eq_zero hpP hzero,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-! ## Local means of the prime-square clock -/

section LocalMeans

variable {p : ℕ} [NeZero p]

theorem conj_primeSquareLocalMobius (x : ZMod (p ^ 2)) :
    (starRingEnd ℂ) (primeSquareLocalMobius p x) = primeSquareLocalMobius p x := by
  simp only [primeSquareLocalMobius, strataVec, map_add, map_mul, map_one, map_neg, map_zero,
    conj_unitIndicator, conj_valOneVec, conj_deltaZero]

theorem primeSquareLocalMobius_mul_self (x : ZMod (p ^ 2)) :
    primeSquareLocalMobius p x * primeSquareLocalMobius p x
      = unitIndicator p x + valOneVec p x := by
  simp only [primeSquareLocalMobius, strataVec]
  have h1 := unitIndicator_mul_self p x
  have h2 := valOneVec_mul_self p x
  have h3 := unitIndicator_mul_valOneVec p x
  linear_combination h1 + h2 - 2 * h3

/-- **Equation (39), first moment.**  `E m_p = (1 − 1/p)²` before normalization. -/
theorem sum_primeSquareLocalMobius (hp : 1 < p) :
    ∑ y : ZMod (p ^ 2), primeSquareLocalMobius p y = ((p : ℂ) - 1) ^ 2 := by
  simp only [primeSquareLocalMobius, strataVec]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_unitIndicator hp, sum_valOneVec hp, sum_deltaZero]
  ring

/-- **Equation (39), second moment.**  `E m_p² = 1 − p^(−2)` before normalization. -/
theorem sum_primeSquareLocalMobius_sq (hp : 1 < p) :
    ∑ y : ZMod (p ^ 2), primeSquareLocalMobius p y * primeSquareLocalMobius p y
      = (p : ℂ) ^ 2 - 1 := by
  simp only [primeSquareLocalMobius_mul_self]
  rw [Finset.sum_add_distrib, sum_unitIndicator hp, sum_valOneVec hp]
  ring

theorem sum_one_zmod_prime_sq : ∑ _y : ZMod (p ^ 2), (1 : ℂ) = (p : ℂ) ^ 2 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  push_cast [nsmul_eq_mul]
  ring

end LocalMeans

/-! ## CRT tensorization and the exact Gram matrix -/

section Tensor

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) [∀ i, NeZero (a i)]

/-- **Equation (31).**  Chinese remainder: the product of the local prime-square clocks is
exactly the single clock modulo `M = ∏ (a i)²`. -/
def eulerClockCRT (hco : Pairwise (Function.onFun Nat.Coprime fun i => (a i) ^ 2)) :
    ZMod (∏ i, (a i) ^ 2) ≃+* (∀ i, ZMod ((a i) ^ 2)) := ZMod.prodEquivPi _ hco

/-- The finite Euler--Möbius clock of the subset `S`, on the product of local prime-square
clocks, equation (2). -/
def eulerClockProd (S : Finset ι) (x : ∀ i, ZMod ((a i) ^ 2)) : ℂ :=
  ∏ i, (if i ∈ S then primeSquareLocalMobius (a i) (x i) else 1)

/-- **Equation (40), unnormalized.**  The exact Gram matrix of two finite Euler clocks. -/
theorem sum_eulerClockProd_mul (ha : ∀ i, 1 < a i) (S T : Finset ι) :
    ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a T x
      = ∏ i, (if i ∈ S then (if i ∈ T then ((a i : ℂ) ^ 2 - 1) else ((a i : ℂ) - 1) ^ 2)
          else (if i ∈ T then ((a i : ℂ) - 1) ^ 2 else ((a i : ℂ)) ^ 2)) := by
  classical
  set F : ∀ i : ι, ZMod ((a i) ^ 2) → ℂ := fun i y =>
    (if i ∈ S then primeSquareLocalMobius (a i) y else 1)
      * (if i ∈ T then primeSquareLocalMobius (a i) y else 1) with hFdef
  have hterm : ∀ x : (∀ i, ZMod ((a i) ^ 2)),
      (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a T x
        = ∏ i, F i (x i) := by
    intro x
    rw [eulerClockProd, eulerClockProd, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hFdef]
    by_cases hS : i ∈ S
    · simp [hS, conj_primeSquareLocalMobius]
    · simp [hS]
  simp only [hterm]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun i : ι => (Finset.univ : Finset (ZMod ((a i) ^ 2)))) F]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hFdef]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp only [hS, hT, if_true, if_false, one_mul, mul_one]
  · rw [sum_primeSquareLocalMobius_sq (ha i)]
  · rw [sum_primeSquareLocalMobius (ha i)]
  · rw [sum_primeSquareLocalMobius (ha i)]
  · rw [sum_one_zmod_prime_sq]

/-- **Equation (40).**  The normalized Gram matrix of two finite Euler clocks factors over the
primes: shared primes contribute the safe squarefree mass `1 − p^(−2)`, and unshared primes
contribute the singular record factor `(1 − p^(−1))²`. -/
theorem eulerClockProd_gram (ha : ∀ i, 1 < a i) (S T : Finset ι) :
    (∏ i, ((a i : ℂ) ^ 2))⁻¹ * ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a T x
      = ∏ i, (if i ∈ S then (if i ∈ T then 1 - ((a i : ℂ) ^ 2)⁻¹ else (1 - ((a i : ℂ))⁻¹) ^ 2)
          else (if i ∈ T then (1 - ((a i : ℂ))⁻¹) ^ 2 else 1)) := by
  classical
  have hne : ∀ i : ι, ((a i : ℂ)) ≠ 0 := by
    intro i
    have : 0 < a i := lt_trans Nat.zero_lt_one (ha i)
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [sum_eulerClockProd_mul a ha S T, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := hne i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp only [hS, hT, if_true, if_false]
  · field_simp
  · field_simp
  · field_simp
  · field_simp

/-- **Equation (40), the `P ⊆ Q` form.**  Against the full clock the Gram entry splits into the
safe squarefree mass over `P` and the singular record factor over `Q \ P`. -/
theorem eulerClockProd_gram_univ (ha : ∀ i, 1 < a i) (S : Finset ι) :
    (∏ i, ((a i : ℂ) ^ 2))⁻¹ * ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a Finset.univ x
      = (∏ i ∈ S, (1 - ((a i : ℂ) ^ 2)⁻¹)) * ∏ i ∈ Sᶜ, (1 - ((a i : ℂ))⁻¹) ^ 2 := by
  classical
  rw [eulerClockProd_gram a ha S Finset.univ]
  simp only [Finset.mem_univ, if_true]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
  congr 1
  · refine Finset.prod_congr ?_ ?_
    · ext i; simp
    · intro i hi
      have : i ∈ S := by simpa using hi
      simp [this]
  · refine Finset.prod_congr ?_ ?_
    · ext i; simp
    · intro i hi
      have : i ∉ S := by simpa using hi
      simp [this]

/-- The normalized squared length of a finite Euler clock. -/
theorem eulerClockProd_normSq (ha : ∀ i, 1 < a i) (S : Finset ι) :
    (∏ i, ((a i : ℂ) ^ 2))⁻¹ * ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a S x
      = ∏ i ∈ S, (1 - ((a i : ℂ) ^ 2)⁻¹) := by
  classical
  rw [eulerClockProd_gram a ha S S]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ S)]
  have h1 : (Finset.univ.filter fun i => i ∈ S) = S := by ext i; simp
  have h2 : ∀ i ∈ Finset.univ.filter (fun i => ¬ i ∈ S),
      (if i ∈ S then (if i ∈ S then 1 - ((a i : ℂ) ^ 2)⁻¹ else (1 - ((a i : ℂ))⁻¹) ^ 2)
        else (if i ∈ S then (1 - ((a i : ℂ))⁻¹) ^ 2 else 1)) = 1 := by
    intro i hi
    have : i ∉ S := by simpa using hi
    simp [this]
  rw [Finset.prod_congr rfl h2, Finset.prod_const_one, mul_one]
  refine Finset.prod_congr h1 ?_
  intro i hi
  have : i ∈ S := by simpa using hi
  simp [this]

/-- **Equation (41), exact finite form.**  The squared `L²` distance between the clock of `P`
and the full clock of `Q`. -/
theorem eulerClockProd_dist_sq (ha : ∀ i, 1 < a i) (S : Finset ι) :
    (∏ i, ((a i : ℂ) ^ 2))⁻¹ * ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x - eulerClockProd a Finset.univ x)
          * (eulerClockProd a S x - eulerClockProd a Finset.univ x)
      = (∏ i ∈ S, (1 - ((a i : ℂ) ^ 2)⁻¹)) + (∏ i, (1 - ((a i : ℂ) ^ 2)⁻¹))
        - 2 * ((∏ i ∈ S, (1 - ((a i : ℂ) ^ 2)⁻¹)) * ∏ i ∈ Sᶜ, (1 - ((a i : ℂ))⁻¹) ^ 2) := by
  classical
  have hexpand : ∀ x : (∀ i, ZMod ((a i) ^ 2)),
      (starRingEnd ℂ) (eulerClockProd a S x - eulerClockProd a Finset.univ x)
          * (eulerClockProd a S x - eulerClockProd a Finset.univ x)
        = (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a S x
          + (starRingEnd ℂ) (eulerClockProd a Finset.univ x)
              * eulerClockProd a Finset.univ x
          - (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a Finset.univ x
          - (starRingEnd ℂ) (eulerClockProd a Finset.univ x) * eulerClockProd a S x := by
    intro x
    rw [map_sub]
    ring
  have hsymm : ∑ x : (∀ i, ZMod ((a i) ^ 2)),
      (starRingEnd ℂ) (eulerClockProd a Finset.univ x) * eulerClockProd a S x
      = ∑ x : (∀ i, ZMod ((a i) ^ 2)),
        (starRingEnd ℂ) (eulerClockProd a S x) * eulerClockProd a Finset.univ x := by
    rw [sum_eulerClockProd_mul a ha Finset.univ S, sum_eulerClockProd_mul a ha S Finset.univ]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hS : i ∈ S <;> simp [hS]
  simp only [hexpand]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsymm]
  have huniv : (Finset.univ : Finset ι)ᶜ = (∅ : Finset ι) := by simp
  have hprodS := eulerClockProd_normSq a ha S
  have hprodU := eulerClockProd_normSq a ha Finset.univ
  have hcross := eulerClockProd_gram_univ a ha S
  have hUprod : ∏ i ∈ (Finset.univ : Finset ι), (1 - ((a i : ℂ) ^ 2)⁻¹)
      = ∏ i, (1 - ((a i : ℂ) ^ 2)⁻¹) := rfl
  rw [mul_sub, mul_sub, mul_add, hprodS, hcross, hprodU, hUprod]
  ring

end Tensor


/-! ## The two prime products and the infinite-sector fracture -/

section Limits

open Filter Topology

/-- `n ↦ (n : ℝ)^(-2)` as a completely multiplicative weight. -/
def invSqWeight : ℕ →*₀ ℝ where
  toFun n := ((n : ℝ) ^ 2)⁻¹
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intro x y
    push_cast
    rw [mul_pow, mul_inv]

theorem invSqWeight_apply (n : ℕ) : invSqWeight n = ((n : ℝ) ^ 2)⁻¹ := rfl

theorem summable_norm_invSqWeight : Summable fun n => ‖invSqWeight n‖ := by
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine hsum.congr fun n => ?_
  rw [invSqWeight_apply, Real.norm_eq_abs, one_div]
  exact (abs_of_nonneg (by positivity)).symm

theorem tsum_invSqWeight : (∑' n : ℕ, invSqWeight n) = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two
  have hcongr : (fun n : ℕ => 1 / (n : ℝ) ^ 2) = fun n : ℕ => invSqWeight n := by
    funext n
    rw [invSqWeight_apply, one_div]
  rw [hcongr] at h
  exact h.tsum_eq

/-- **Equation (42).**  The safe squarefree Euler product converges to `1/ζ(2) = 6/π²`. -/
theorem tendsto_squarefreeSafeProduct :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹)) atTop
      (nhds (6 / Real.pi ^ 2)) := by
  have h := EulerProduct.eulerProduct_completely_multiplicative
    (f := invSqWeight) summable_norm_invSqWeight
  rw [tsum_invSqWeight] at h
  have hinv : (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 - invSqWeight p)⁻¹)
      = fun N : ℕ => (∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))⁻¹ := by
    funext N
    rw [← Finset.prod_inv_distrib]
    rfl
  rw [hinv] at h
  have hpi : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have h2 := h.inv₀ (ne_of_gt hpi)
  have hval : (Real.pi ^ 2 / 6)⁻¹ = 6 / Real.pi ^ 2 := by
    rw [inv_div]
  rw [hval] at h2
  refine h2.congr fun N => ?_
  rw [inv_inv]

/-- The Mertens product over the primes below `N`. -/
theorem primesBelow_prod_eq_mertensPrimeProduct (N : ℕ) :
    ∏ p ∈ (N + 1).primesBelow, (1 - ((p : ℝ))⁻¹) = mertensPrimeProduct N := by
  classical
  rw [mertensPrimeProduct, show (N + 1).primesBelow
      = (Finset.range (N + 1)).filter Nat.Prime from rfl,
    ← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext n
  simp

/-- **Equation (41), record factor.**  The singular Möbius record product vanishes in the
limit: the finite Euler clocks leave every fixed Hilbert sector. -/
theorem tendsto_primeRecordProduct_zero :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 - ((p : ℝ))⁻¹)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hquot : Tendsto (fun N : ℕ => (mertensPrimeProduct N * Real.log N) / Real.log N)
      atTop (nhds 0) := tendsto_mertensPrimeProduct_mul_log.div_atTop hlog
  have hmertens : Tendsto (fun N : ℕ => mertensPrimeProduct N) atTop (nhds 0) := by
    refine hquot.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogN : Real.log (N : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    field_simp
  have hshift : Tendsto (fun N : ℕ => ∏ p ∈ (N + 1).primesBelow, (1 - ((p : ℝ))⁻¹))
      atTop (nhds 0) := by
    refine hmertens.congr fun N => ?_
    exact (primesBelow_prod_eq_mertensPrimeProduct N).symm
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hshift


theorem prod_primesBelow_one_sub_inv_ne_zero (N : ℕ) :
    ∏ p ∈ N.primesBelow, (1 - ((p : ℝ))⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hprime : Nat.Prime p := Nat.prime_of_mem_primesBelow hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have : ((p : ℝ))⁻¹ ≤ 1 / 2 := by
    rw [one_div, inv_le_inv₀ (by linarith) (by norm_num)]
    exact h2
  intro hcon
  have : ((p : ℝ))⁻¹ = 1 := by linarith [hcon]
  linarith

private theorem primesBelow_subset {N M : ℕ} (h : N ≤ M) : N.primesBelow ⊆ M.primesBelow := by
  intro p hp
  rw [show N.primesBelow = (Finset.range N).filter Nat.Prime from rfl,
    Finset.mem_filter, Finset.mem_range] at hp
  rw [show M.primesBelow = (Finset.range M).filter Nat.Prime from rfl,
    Finset.mem_filter, Finset.mem_range]
  exact ⟨lt_of_lt_of_le hp.1 h, hp.2⟩

/-- The record product over the primes newly added between `N` and `M` vanishes as `M → ∞`. -/
theorem tendsto_primeRecordProduct_sdiff (N : ℕ) :
    Tendsto (fun M : ℕ => ∏ q ∈ M.primesBelow \ N.primesBelow, (1 - ((q : ℝ))⁻¹))
      atTop (nhds 0) := by
  have hc := prod_primesBelow_one_sub_inv_ne_zero N
  have hdiv : Tendsto
      (fun M : ℕ => (∏ p ∈ M.primesBelow, (1 - ((p : ℝ))⁻¹))
        / ∏ p ∈ N.primesBelow, (1 - ((p : ℝ))⁻¹)) atTop (nhds 0) := by
    have := tendsto_primeRecordProduct_zero.div_const
      (∏ p ∈ N.primesBelow, (1 - ((p : ℝ))⁻¹))
    simpa using this
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with M hM
  have hsub : N.primesBelow ⊆ M.primesBelow := primesBelow_subset hM
  have hsplit := Finset.prod_sdiff (f := fun p : ℕ => (1 - ((p : ℝ))⁻¹)) hsub
  rw [div_eq_iff hc]
  exact hsplit.symm

/-- **Equation (41).**  For a fixed finite prime set the squared distance between its Euler
clock and the full clock converges to `∏_{p ∈ P}(1 − p^(−2)) + 1/ζ(2)`: the cross term dies. -/
theorem tendsto_sectorFracture (N : ℕ) :
    Tendsto (fun M : ℕ =>
        (∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))
          + (∏ p ∈ M.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))
          - 2 * ((∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))
              * (∏ q ∈ M.primesBelow \ N.primesBelow, (1 - ((q : ℝ))⁻¹)) ^ 2))
      atTop (nhds ((∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹)) + 6 / Real.pi ^ 2)) := by
  have h1 : Tendsto (fun M : ℕ =>
      (∏ q ∈ M.primesBelow \ N.primesBelow, (1 - ((q : ℝ))⁻¹)) ^ 2) atTop (nhds 0) := by
    have := (tendsto_primeRecordProduct_sdiff N).pow 2
    simpa using this
  have h2 := tendsto_squarefreeSafeProduct
  have := ((tendsto_const_nhds (x := ∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))
      (f := (atTop : Filter ℕ))).add h2).sub
    (((tendsto_const_nhds (x := (2 : ℝ)) (f := (atTop : Filter ℕ))).mul
      (tendsto_const_nhds (x := ∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹))
        (f := (atTop : Filter ℕ)))).mul h1)
  simpa [mul_assoc] using this

/-- **Equation (41), iterated limit.**  Letting the fixed prime set grow, the limiting squared
distance is `2/ζ(2)`: the finite Euler clocks are not `L²`-Cauchy, and the entire limiting
Hilbert sector changes. -/
theorem tendsto_sectorFracture_iterated :
    Tendsto (fun N : ℕ => (∏ p ∈ N.primesBelow, (1 - ((p : ℝ) ^ 2)⁻¹)) + 6 / Real.pi ^ 2)
      atTop (nhds (12 / Real.pi ^ 2)) := by
  have h := tendsto_squarefreeSafeProduct.add_const (6 / Real.pi ^ 2)
  have hval : 6 / Real.pi ^ 2 + 6 / Real.pi ^ 2 = 12 / Real.pi ^ 2 := by ring
  rw [hval] at h
  exact h

end Limits

end

end RHTower
