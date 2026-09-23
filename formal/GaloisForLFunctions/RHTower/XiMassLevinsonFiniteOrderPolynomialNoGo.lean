import GaloisForLFunctions.RHTower.XiMassLevinsonRoughTailHorizon
import GaloisForLFunctions.RHTower.Sieve.VinogradovBertrandReservoir
import Mathlib.Algebra.Polynomial.Roots

/-!
# Finite-order Levinson--Conrey prime-projection no-go

A finite-order differential head has positive-natural coefficient `P(log n) / sqrt n` for a
polynomial `P`. Convolving with any mollifier supported through `M` retains only its unit
coefficient on the `M`-rough tail: every supported divisor except one is forbidden. A finite sum
of multi-piece mollifiers therefore collapses to one unit-weighted combined polynomial there.

Agreement with logarithmic prime half-density at enough exterior primes forces the combined
polynomial to be `X`. It then assigns the same nonzero logarithmic coefficient to exterior prime
squares, where true-prime half-density vanishes. An iterated Bertrand reservoir places enough
primes and their squares inside the literal T1 window `M = N^(49 : ℕ)`, `L = N^(100 : ℕ)` once
`2^(d+2) <= N`, for every fixed residual degree `d`.

Thus no fixed finite derivative order, no finite-support mollifier, and no finite
multi-piece sum of them can provide coefficient-faithful true-prime LAND in T1's actual AFE
schedule. Surviving representations must use growing derivative order, explicit nonlinear
prime-power subtraction, or leave finite log-jet factorization.
-/

open Complex Finset Polynomial

namespace RHTower.Sieve

noncomputable section

def finiteOrderCriticalHeadCoeff (P : ℂ[X]) (n : ℕ) : ℂ :=
  P.eval (Real.log n : ℂ) * (((1 / Real.sqrt n : ℝ)) : ℂ)

def finiteOrderMollifiedCriticalDetectorCoeff
    (P : ℂ[X]) (moll : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ q ∈ n.divisors, finiteOrderCriticalHeadCoeff P (n / q) * moll q

/-- On the rough tail, an arbitrary finite-support mollifier retains only its unit coefficient. -/
theorem finiteOrderMollifiedCriticalDetectorCoeff_eq_scaledHead_of_rough
    {P : ℂ[X]} {moll : ℕ → ℂ} {M n : ℕ}
    (hsupport : ∀ q, M < q → moll q = 0)
    (hn : 0 < n) (hrough : IsApertureRough M n) :
    finiteOrderMollifiedCriticalDetectorCoeff P moll n =
      finiteOrderCriticalHeadCoeff (Polynomial.C (moll 1) * P) n := by
  rw [finiteOrderMollifiedCriticalDetectorCoeff]
  rw [Finset.sum_eq_single 1]
  · simp [finiteOrderCriticalHeadCoeff]
    ring
  · intro q hqmem hqne
    by_cases hqM : q ≤ M
    · exact (hqne (apertureRough_divisor_eq_one hn hrough
        (Nat.dvd_of_mem_divisors hqmem) hqM)).elim
    · simp [hsupport q (by omega)]
  · simp [Nat.one_mem_divisors.mpr hn.ne']

theorem finiteOrderMollifiedCriticalDetectorCoeff_eq_head_of_rough
    {P : ℂ[X]} {moll : ℕ → ℂ} {M n : ℕ}
    (hmoll_one : moll 1 = 1) (hsupport : ∀ q, M < q → moll q = 0)
    (hn : 0 < n) (hrough : IsApertureRough M n) :
    finiteOrderMollifiedCriticalDetectorCoeff P moll n =
      finiteOrderCriticalHeadCoeff P n := by
  rw [finiteOrderMollifiedCriticalDetectorCoeff_eq_scaledHead_of_rough
    hsupport hn hrough, hmoll_one]
  simp

/-- Finite sum of finite-order detector heads, allowing a different mollifier in each piece. -/
def finiteOrderMollifiedCriticalDetectorCombinationCoeff
    {ι : Type*} (S : Finset ι) (P : ι → ℂ[X])
    (moll : ι → ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ S, finiteOrderMollifiedCriticalDetectorCoeff (P i) (moll i) n

/-- On the common rough tail, an arbitrary finite multi-piece detector is exactly the head of the
unit-weighted sum polynomial. Every other mollifier coefficient disappears. -/
theorem finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_head_of_rough
    {ι : Type*} {S : Finset ι} {P : ι → ℂ[X]}
    {moll : ι → ℕ → ℂ} {M n : ℕ}
    (hsupport : ∀ i ∈ S, ∀ q, M < q → moll i q = 0)
    (hn : 0 < n) (hrough : IsApertureRough M n) :
    finiteOrderMollifiedCriticalDetectorCombinationCoeff S P moll n =
      finiteOrderCriticalHeadCoeff
        (∑ i ∈ S, Polynomial.C (moll i 1) * P i) n := by
  classical
  rw [finiteOrderMollifiedCriticalDetectorCombinationCoeff]
  calc
    ∑ i ∈ S, finiteOrderMollifiedCriticalDetectorCoeff (P i) (moll i) n =
        ∑ i ∈ S, finiteOrderCriticalHeadCoeff
          (Polynomial.C (moll i 1) * P i) n := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [finiteOrderMollifiedCriticalDetectorCoeff_eq_scaledHead_of_rough
        (hsupport i hi) hn hrough]
    _ = finiteOrderCriticalHeadCoeff
        (∑ i ∈ S, Polynomial.C (moll i 1) * P i) n := by
      simp only [finiteOrderCriticalHeadCoeff, Polynomial.eval_finsetSum]
      rw [Finset.sum_mul]

theorem log_vinogradovBertrandPrimeReservoir_injective (M K : ℕ) :
    Function.Injective (fun i : Fin K =>
      (Real.log (vinogradovBertrandPrimeReservoir M K i) : ℂ)) := by
  intro i j hij
  apply vinogradovBertrandPrimeReservoir_injective M K
  have hlog :
      Real.log (vinogradovBertrandPrimeReservoir M K i) =
        Real.log (vinogradovBertrandPrimeReservoir M K j) := by
    exact Complex.ofReal_injective hij
  have hi : (0 : ℝ) < vinogradovBertrandPrimeReservoir M K i := by
    exact_mod_cast (vinogradovBertrandPrimeReservoir_prime M K i).pos
  have hj : (0 : ℝ) < vinogradovBertrandPrimeReservoir M K j := by
    exact_mod_cast (vinogradovBertrandPrimeReservoir_prime M K j).pos
  have hcast :
      (vinogradovBertrandPrimeReservoir M K i : ℝ) =
        (vinogradovBertrandPrimeReservoir M K j : ℝ) :=
    Real.strictMonoOn_log.injOn hi hj hlog
  exact_mod_cast hcast

theorem finiteOrderCriticalPolynomial_eq_X_of_reservoir_match
    {P : ℂ[X]} {M d : ℕ}
    (hdeg : (P - X).natDegree < d + 1)
    (hmatch : ∀ i : Fin (d + 1),
      P.eval (Real.log (vinogradovBertrandPrimeReservoir M (d + 1) i) : ℂ) =
        (Real.log (vinogradovBertrandPrimeReservoir M (d + 1) i) : ℂ)) :
    P = X := by
  classical
  let f : Fin (d + 1) → ℂ := fun i =>
    (Real.log (vinogradovBertrandPrimeReservoir M (d + 1) i) : ℂ)
  let S : Finset ℂ := Finset.univ.image f
  have hinj : Function.Injective f := by
    simpa only [f] using log_vinogradovBertrandPrimeReservoir_injective M (d + 1)
  have hcard : S.card = d + 1 := by
    change (Finset.univ.image f).card = d + 1
    rw [Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hroots : ∀ x ∈ S, (P - X).eval x = 0 := by
    intro x hx
    change x ∈ Finset.univ.image f at hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp only [Polynomial.eval_sub, Polynomial.eval_X, f, hmatch i, sub_self]
  have hzero : P - X = 0 := by
    by_contra hne
    have hsub : S ⊆ (P - X).roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hne, hroots x hx⟩
    have h1 : S.card ≤ (P - X).roots.toFinset.card := Finset.card_le_card hsub
    have h2 : (P - X).roots.toFinset.card ≤ Multiset.card (P - X).roots :=
      Multiset.toFinset_card_le _
    have h3 : Multiset.card (P - X).roots ≤ (P - X).natDegree :=
      Polynomial.card_roots' _
    omega
  exact sub_eq_zero.mp hzero

/-- A uniform degree bound survives a finite polynomial sum. -/
theorem natDegree_finset_sum_le_of_forall
    {ι : Type*} {S : Finset ι} {F : ι → ℂ[X]} {d : ℕ}
    (hF : ∀ i ∈ S, (F i).natDegree ≤ d) :
    (∑ i ∈ S, F i).natDegree ≤ d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (hF a (Finset.mem_insert_self a S))
          (ih fun i hi => hF i (Finset.mem_insert_of_mem hi)))

/-- Scalar unit weights and subtraction of the target linear profile do not exceed a fixed
positive derivative-order budget. -/
theorem natDegree_unitWeightedSum_sub_X_lt_succ
    {ι : Type*} {S : Finset ι} {P : ι → ℂ[X]}
    {moll : ι → ℕ → ℂ} {d : ℕ}
    (hd : 1 ≤ d) (hPdeg : ∀ i ∈ S, (P i).natDegree ≤ d) :
    ((∑ i ∈ S, Polynomial.C (moll i 1) * P i) - X).natDegree < d + 1 := by
  have hweighted : ∀ i ∈ S,
      (Polynomial.C (moll i 1) * P i).natDegree ≤ d := by
    intro i hi
    have hmul : (Polynomial.C (moll i 1) * P i).natDegree ≤
        (Polynomial.C (moll i 1)).natDegree + (P i).natDegree :=
      Polynomial.natDegree_mul_le
    exact hmul.trans (by simpa using hPdeg i hi)
  have hsum :
      (∑ i ∈ S, Polynomial.C (moll i 1) * P i).natDegree ≤ d :=
    natDegree_finset_sum_le_of_forall hweighted
  have hsub := Polynomial.natDegree_sub_le
    (∑ i ∈ S, Polynomial.C (moll i 1) * P i) X
  rw [Polynomial.natDegree_X] at hsub
  omega

/-- At the literal T1 schedule `M = N^(49 : ℕ)`, `L = N^(100 : ℕ)`, every fixed residual degree has enough
room for its Bertrand prime reservoir and the associated prime-square obstruction once
`2^(d+2) ≤ N`. -/
theorem finiteOrderBertrandReservoir_square_le_t1AfeWindow
    {d N : ℕ} (hN : 2 ^ (d + 2) ≤ N) :
    (2 ^ (d + 1) * (N ^ (49 : ℕ) + 2)) ^ (2 : ℕ) ≤ N ^ (100 : ℕ) := by
  have htwoN : 2 ≤ N := by
    exact (Nat.le_pow (by omega : 0 < d + 2)).trans hN
  have htwoPow : 2 ≤ N ^ (49 : ℕ) :=
    htwoN.trans (Nat.le_pow (by omega : 0 < 49))
  have hsum : N ^ (49 : ℕ) + 2 ≤ 2 * N ^ (49 : ℕ) := by omega
  have hreassoc : 2 ^ (d + 1) * (2 * N ^ (49 : ℕ)) = 2 ^ (d + 2) * N ^ (49 : ℕ) := by
    calc
      2 ^ (d + 1) * (2 * N ^ (49 : ℕ)) = (2 ^ (d + 1) * 2) * N ^ (49 : ℕ) := by
        ac_rfl
      _ = 2 ^ (d + 2) * N ^ (49 : ℕ) := by congr 1
  calc
    (2 ^ (d + 1) * (N ^ (49 : ℕ) + 2)) ^ (2 : ℕ) ≤
        (2 ^ (d + 1) * (2 * N ^ (49 : ℕ))) ^ (2 : ℕ) :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hsum) 2
    _ = (2 ^ (d + 2)) ^ (2 : ℕ) * N ^ (98 : ℕ) := by
      rw [hreassoc, mul_pow]
      congr 1
      rw [← pow_mul]
    _ ≤ N ^ (2 : ℕ) * N ^ (98 : ℕ) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hN 2)
    _ = N ^ (100 : ℕ) := by rw [← pow_add]

/-- Any coefficient system with a fixed finite log-polynomial rough profile fails true-prime
half-density on a window containing a Bertrand reservoir and its prime squares. -/
theorem not_forall_coeff_eq_truePrime_of_finiteOrderRoughProfile_reservoir
    {P : ℂ[X]} {coeff : ℕ → ℂ} {M L d : ℕ}
    (hprofile : ∀ n, 0 < n → IsApertureRough M n →
      coeff n = finiteOrderCriticalHeadCoeff P n)
    (hdeg : (P - X).natDegree < d + 1)
    (hwindow : (2 ^ (d + 1) * (M + 2)) ^ (2 : ℕ) ≤ L) :
    ¬ ∀ n : ℕ, 0 < n → IsApertureRough M n → n ≤ L →
      coeff n = truePrimeLogHalfDensityCoeff n := by
  intro hall
  have hmatch : ∀ i : Fin (d + 1),
      P.eval (Real.log (vinogradovBertrandPrimeReservoir M (d + 1) i) : ℂ) =
        (Real.log (vinogradovBertrandPrimeReservoir M (d + 1) i) : ℂ) := by
    intro i
    let p := vinogradovBertrandPrimeReservoir M (d + 1) i
    have hp : p.Prime := by
      simpa only [p] using vinogradovBertrandPrimeReservoir_prime M (d + 1) i
    have hMp : M < p := by
      simpa only [p] using lt_vinogradovBertrandPrimeReservoir M (d + 1) i
    have hpR : p ≤ 2 ^ (d + 1) * (M + 2) := by
      have := vinogradovBertrandPrimeReservoir_add_two_le M (d + 1) i
      exact (Nat.le_add_right p 2).trans (by simpa only [p] using this)
    have hp2L : p ^ (2 : ℕ) ≤ L :=
      (Nat.pow_le_pow_left hpR 2).trans hwindow
    have hpL : p ≤ L := by
      exact (show p ≤ p ^ (2 : ℕ) by nlinarith [hp.two_le]).trans hp2L
    have heq := hall p hp.pos (prime_isApertureRough hp hMp) hpL
    rw [hprofile p hp.pos (prime_isApertureRough hp hMp),
      finiteOrderCriticalHeadCoeff, truePrimeLogHalfDensityCoeff, if_pos hp] at heq
    exact mul_right_cancel₀ (one_div_sqrt_nat_cast_ne_zero hp.pos) heq
  have hPX : P = X :=
    finiteOrderCriticalPolynomial_eq_X_of_reservoir_match hdeg hmatch
  let i : Fin (d + 1) := ⟨0, by omega⟩
  let p := vinogradovBertrandPrimeReservoir M (d + 1) i
  have hp : p.Prime := by
    simpa only [p, i] using vinogradovBertrandPrimeReservoir_prime M (d + 1) i
  have hMp : M < p := by
    simpa only [p, i] using lt_vinogradovBertrandPrimeReservoir M (d + 1) i
  have hpR : p ≤ 2 ^ (d + 1) * (M + 2) := by
    have := vinogradovBertrandPrimeReservoir_add_two_le M (d + 1) i
    exact (Nat.le_add_right p 2).trans (by simpa only [p, i] using this)
  have hp2L : p ^ (2 : ℕ) ≤ L :=
    (Nat.pow_le_pow_left hpR 2).trans hwindow
  have hp2pos : 0 < p ^ (2 : ℕ) := pow_pos hp.pos 2
  have hp2rough : IsApertureRough M (p ^ (2 : ℕ)) :=
    prime_sq_isApertureRough hp hMp
  have hp2not : ¬(p ^ (2 : ℕ)).Prime := Nat.Prime.not_prime_pow (by norm_num)
  have heq := hall (p ^ (2 : ℕ)) hp2pos hp2rough hp2L
  rw [hprofile (p ^ (2 : ℕ)) hp2pos hp2rough,
    finiteOrderCriticalHeadCoeff, hPX, Polynomial.eval_X,
    truePrimeLogHalfDensityCoeff, if_neg hp2not] at heq
  have hlogpos : 0 < Real.log (((p ^ (2 : ℕ) : ℕ) : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < p ^ (2 : ℕ) by nlinarith [hp.two_le]))
  exact (mul_ne_zero (by exact_mod_cast (ne_of_gt hlogpos))
    (one_div_sqrt_nat_cast_ne_zero hp2pos)) heq

/-- No normalized finite-support mollifier convolved with a fixed finite-order differential head
is coefficient-faithful to true-prime half-density on such a rough window. -/
theorem not_forall_finiteOrderMollifiedCriticalDetectorCoeff_eq_truePrime_of_reservoir
    {P : ℂ[X]} {moll : ℕ → ℂ} {M L d : ℕ}
    (hmoll_one : moll 1 = 1) (hsupport : ∀ q, M < q → moll q = 0)
    (hdeg : (P - X).natDegree < d + 1)
    (hwindow : (2 ^ (d + 1) * (M + 2)) ^ (2 : ℕ) ≤ L) :
    ¬ ∀ n : ℕ, 0 < n → IsApertureRough M n → n ≤ L →
      finiteOrderMollifiedCriticalDetectorCoeff P moll n =
        truePrimeLogHalfDensityCoeff n :=
  not_forall_coeff_eq_truePrime_of_finiteOrderRoughProfile_reservoir
    (fun n hn hrough =>
      finiteOrderMollifiedCriticalDetectorCoeff_eq_head_of_rough
        (n := n) hmoll_one hsupport hn hrough)
    hdeg hwindow

/-- The finite-window obstruction survives arbitrary finite sums and multi-piece mollifiers. -/
theorem not_forall_finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_truePrime_of_reservoir
    {ι : Type*} {S : Finset ι} {P : ι → ℂ[X]}
    {moll : ι → ℕ → ℂ} {M L d : ℕ}
    (hsupport : ∀ i ∈ S, ∀ q, M < q → moll i q = 0)
    (hdeg : ((∑ i ∈ S, Polynomial.C (moll i 1) * P i) - X).natDegree < d + 1)
    (hwindow : (2 ^ (d + 1) * (M + 2)) ^ (2 : ℕ) ≤ L) :
    ¬ ∀ n : ℕ, 0 < n → IsApertureRough M n → n ≤ L →
      finiteOrderMollifiedCriticalDetectorCombinationCoeff S P moll n =
        truePrimeLogHalfDensityCoeff n :=
  not_forall_coeff_eq_truePrime_of_finiteOrderRoughProfile_reservoir
    (fun n hn hrough =>
      finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_head_of_rough
        (n := n) hsupport hn hrough)
    hdeg hwindow

/-- **T1 fixed-finite-order LAND no-go at the actual AFE schedule.** Once `N` dominates the fixed
residual degree, no finite sum of mollifiers supported through `N^(49 : ℕ)`, paired with any
fixed finite differential polynomials, can equal true-prime half-density on every `N^(49 : ℕ)`-rough
source index through `N^(100 : ℕ)`. -/
theorem not_forall_finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_truePrime_t1AfeWindow
    {ι : Type*} {S : Finset ι} {P : ι → ℂ[X]}
    {moll : ι → ℕ → ℂ} {N d : ℕ}
    (hsupport : ∀ i ∈ S, ∀ q, N ^ (49 : ℕ) < q → moll i q = 0)
    (hd : 1 ≤ d) (hPdeg : ∀ i ∈ S, (P i).natDegree ≤ d)
    (hN : 2 ^ (d + 2) ≤ N) :
    ¬ ∀ n : ℕ, 0 < n → IsApertureRough (N ^ (49 : ℕ)) n → n ≤ N ^ (100 : ℕ) →
      finiteOrderMollifiedCriticalDetectorCombinationCoeff S P moll n =
        truePrimeLogHalfDensityCoeff n :=
  not_forall_finiteOrderMollifiedCriticalDetectorCombinationCoeff_eq_truePrime_of_reservoir
    hsupport (natDegree_unitWeightedSum_sub_X_lt_succ hd hPdeg)
      (finiteOrderBertrandReservoir_square_le_t1AfeWindow hN)

end

end RHTower.Sieve
