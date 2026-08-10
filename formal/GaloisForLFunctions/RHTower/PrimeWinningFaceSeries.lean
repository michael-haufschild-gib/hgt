import GaloisForLFunctions.RHTower.PrimeWinningFaceUnit
import GaloisForLFunctions.RHTower.MFreeLadder
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The winner-face Dirichlet series and its Euler product

The winner face of a maximum-exponent shell is cut out by two local conditions: every prime of the
face carries exponent exactly `m`, and no prime carries more.  Because the first condition fails at
`n = 1`, the face coefficient is not a multiplicative arithmetic function; dividing by the fixed
winner block `A = ∏_{p ∈ F} p^m` removes it, and what is left — no prime of `F` divides `n`, and no
prime exponent exceeds `m` — is multiplicative.  Its Euler factors are `1` on the face and the
truncated geometric sum `∑_{e ≤ m} q^{-es}` off it, so the face series is the winner block times
that Euler product.
-/

open Complex

noncomputable section

namespace RHTower

/-! ## The maximum prime exponent -/

/-- The largest exponent occurring in the factorization of `n`. -/
def maxPrimeExponent (n : ℕ) : ℕ := n.factorization.support.sup n.factorization

theorem factorization_le_maxPrimeExponent (n q : ℕ) :
    n.factorization q ≤ maxPrimeExponent n := by
  by_cases hq : q ∈ n.factorization.support
  · exact Finset.le_sup hq
  · have : n.factorization q = 0 := by
      simpa using Finsupp.notMem_support_iff.mp hq
    simp [this]

theorem maxPrimeExponent_le {n m : ℕ} (h : ∀ q, n.factorization q ≤ m) :
    maxPrimeExponent n ≤ m :=
  Finset.sup_le fun q _ => h q

/-! ## The winner-face and reduced conditions -/

/-- Every prime of the face has exponent exactly `m`, and no prime exceeds `m`. -/
def IsWinnerFace (F : Finset Nat.Primes) (m n : ℕ) : Prop :=
  (∀ p ∈ F, n.factorization (p : ℕ) = m) ∧ ∀ q : ℕ, n.factorization q ≤ m

/-- No prime of the face divides `n`, and no prime exceeds `m`. -/
def IsReducedFace (F : Finset Nat.Primes) (m n : ℕ) : Prop :=
  (∀ p ∈ F, n.factorization (p : ℕ) = 0) ∧ ∀ q : ℕ, n.factorization q ≤ m

/-- **Faithfulness to the card's winner description.**  For a nonempty face and a positive shell
radius, the two local conditions say exactly that the maximal exponent is `m` and that the face
consists of winners. -/
theorem isWinnerFace_iff_maxPrimeExponent {F : Finset Nat.Primes} (hF : F.Nonempty) {m : ℕ}
    (_hm : 1 ≤ m) (n : ℕ) :
    IsWinnerFace F m n ↔
      maxPrimeExponent n = m ∧ ∀ p ∈ F, n.factorization (p : ℕ) = maxPrimeExponent n := by
  constructor
  · rintro ⟨hface, hcap⟩
    obtain ⟨p₀, hp₀⟩ := hF
    have hle : maxPrimeExponent n ≤ m := maxPrimeExponent_le hcap
    have hge : m ≤ maxPrimeExponent n := by
      rw [← hface p₀ hp₀]
      exact factorization_le_maxPrimeExponent n _
    have hmax : maxPrimeExponent n = m := le_antisymm hle hge
    exact ⟨hmax, fun p hp => by rw [hface p hp, hmax]⟩
  · rintro ⟨hmax, hface⟩
    refine ⟨fun p hp => by rw [hface p hp, hmax], fun q => ?_⟩
    rw [← hmax]
    exact factorization_le_maxPrimeExponent n q

/-! ## Multiplicativity of the reduced condition -/

theorem factorization_add_le_iff {a b : ℕ} (hab : Nat.Coprime a b) (q m : ℕ) :
    a.factorization q + b.factorization q ≤ m ↔
      a.factorization q ≤ m ∧ b.factorization q ≤ m := by
  constructor
  · intro h
    omega
  · rintro ⟨ha, hb⟩
    have hdisj : a.factorization q = 0 ∨ b.factorization q = 0 := by
      by_contra hcon
      obtain ⟨hane, hbne⟩ := not_or.mp hcon
      have hqa : q ∣ a := Nat.dvd_of_factorization_pos hane
      have hqb : q ∣ b := Nat.dvd_of_factorization_pos hbne
      have hq1 : q ∣ 1 := hab ▸ Nat.dvd_gcd hqa hqb
      have hq : q = 1 := Nat.dvd_one.mp hq1
      apply hane
      rw [hq]
      simp
    rcases hdisj with h | h <;> omega

theorem isReducedFace_mul_iff {F : Finset Nat.Primes} {m a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    IsReducedFace F m (a * b) ↔ IsReducedFace F m a ∧ IsReducedFace F m b := by
  have hfac := Nat.factorization_mul ha hb
  constructor
  · rintro ⟨hface, hcap⟩
    refine ⟨⟨fun p hp => ?_, fun q => ?_⟩, ⟨fun p hp => ?_, fun q => ?_⟩⟩
    · have := hface p hp
      rw [hfac] at this
      simpa using (Nat.add_eq_zero_iff.mp this).1
    · have := hcap q
      rw [hfac] at this
      simp only [Finsupp.add_apply] at this
      omega
    · have := hface p hp
      rw [hfac] at this
      simpa using (Nat.add_eq_zero_iff.mp this).2
    · have := hcap q
      rw [hfac] at this
      simp only [Finsupp.add_apply] at this
      omega
  · rintro ⟨⟨hfa, hca⟩, ⟨hfb, hcb⟩⟩
    refine ⟨fun p hp => ?_, fun q => ?_⟩
    · rw [hfac]
      simp [hfa p hp, hfb p hp]
    · rw [hfac]
      simp only [Finsupp.add_apply]
      exact (factorization_add_le_iff hab q m).mpr ⟨hca q, hcb q⟩

theorem isReducedFace_one (F : Finset Nat.Primes) (m : ℕ) : IsReducedFace F m 1 := by
  refine ⟨fun p _ => ?_, fun q => ?_⟩ <;> simp

/-! ## The reduced arithmetic function and its Euler product -/

open Classical in
/-- The reduced face coefficient as an arithmetic function. -/
def reducedFaceCpow (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ IsReducedFace F m n then (n : ℂ) ^ (-s) else 0, by simp⟩

open Classical in
theorem reducedFaceCpow_apply (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) (n : ℕ) :
    reducedFaceCpow F m s n =
      if n ≠ 0 ∧ IsReducedFace F m n then (n : ℂ) ^ (-s) else 0 := rfl

theorem isMultiplicative_reducedFaceCpow (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    (reducedFaceCpow F m s).IsMultiplicative := by
  classical
  refine ⟨?_, ?_⟩
  · rw [reducedFaceCpow_apply, if_pos ⟨one_ne_zero, isReducedFace_one F m⟩]
    simp
  · intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · simp [reducedFaceCpow_apply]
    rcases eq_or_ne b 0 with rfl | hb
    · simp [reducedFaceCpow_apply]
    have hne : a * b ≠ 0 := Nat.mul_ne_zero ha hb
    rw [reducedFaceCpow_apply, reducedFaceCpow_apply, reducedFaceCpow_apply]
    by_cases hred : IsReducedFace F m (a * b)
    · obtain ⟨hra, hrb⟩ := (isReducedFace_mul_iff hab ha hb).mp hred
      rw [if_pos ⟨hne, hred⟩, if_pos ⟨ha, hra⟩, if_pos ⟨hb, hrb⟩]
      exact natCast_mul_cpow a b (-s)
    · rw [if_neg (fun h : a * b ≠ 0 ∧ IsReducedFace F m (a * b) => hred h.2)]
      by_cases hra : IsReducedFace F m a
      · have hrb : ¬ IsReducedFace F m b := fun hrb =>
          hred ((isReducedFace_mul_iff hab ha hb).mpr ⟨hra, hrb⟩)
        rw [if_neg (fun h : b ≠ 0 ∧ IsReducedFace F m b => hrb h.2), mul_zero]
      · rw [if_neg (fun h : a ≠ 0 ∧ IsReducedFace F m a => hra h.2), zero_mul]

theorem summable_norm_reducedFaceCpow {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ‖reducedFaceCpow F m s n‖ := by
  classical
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_rpow.mpr hs)
  rw [reducedFaceCpow_apply]
  have hnn : (0 : ℝ) ≤ 1 / ((n : ℝ)) ^ s.re :=
    div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_neg (by simp), norm_zero]
    exact hnn
  · split_ifs with h
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), neg_re,
        Real.rpow_neg (Nat.cast_nonneg n), one_div]
    · rw [norm_zero]
      exact hnn

/-- **Euler product of the reduced face series.** -/
theorem tprod_reducedFaceCpow {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    ∏' q : Nat.Primes, ∑' e : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ e) =
      ∑' n : ℕ, reducedFaceCpow F m s n :=
  (isMultiplicative_reducedFaceCpow F m s).eulerProduct_tprod (summable_norm_reducedFaceCpow hs)

/-! ## The local factors -/

theorem isReducedFace_prime_pow_iff (F : Finset Nat.Primes) (m : ℕ) (q : Nat.Primes) (e : ℕ) :
    IsReducedFace F m ((q : ℕ) ^ e) ↔ ((q ∈ F → e = 0) ∧ e ≤ m) := by
  classical
  have hfac : ((q : ℕ) ^ e).factorization = Finsupp.single (q : ℕ) e :=
    q.prop.factorization_pow
  constructor
  · rintro ⟨hface, hcap⟩
    refine ⟨fun hq => ?_, ?_⟩
    · have := hface q hq
      rw [hfac, Finsupp.single_eq_same] at this
      exact this
    · have := hcap (q : ℕ)
      rw [hfac, Finsupp.single_eq_same] at this
      exact this
  · rintro ⟨hq, hem⟩
    refine ⟨fun p hp => ?_, fun r => ?_⟩
    · rw [hfac]
      by_cases hpq : (p : ℕ) = (q : ℕ)
      · have hp' : p = q := Subtype.ext hpq
        rw [hpq, Finsupp.single_eq_same]
        exact hq (hp' ▸ hp)
      · exact Finsupp.single_eq_of_ne hpq
    · rw [hfac]
      by_cases hrq : r = (q : ℕ)
      · rw [hrq, Finsupp.single_eq_same]
        exact hem
      · rw [Finsupp.single_eq_of_ne hrq]
        exact Nat.zero_le m

/-- On the face the local Euler factor is trivial. -/
theorem tsum_reducedFaceCpow_prime_pow_of_mem {F : Finset Nat.Primes} {m : ℕ} {s : ℂ}
    {q : Nat.Primes} (hq : q ∈ F) :
    ∑' e : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ e) = 1 := by
  classical
  rw [tsum_eq_single 0]
  · rw [pow_zero, reducedFaceCpow_apply, if_pos ⟨one_ne_zero, isReducedFace_one F m⟩]
    simp
  · intro e he
    rw [reducedFaceCpow_apply, if_neg]
    rintro ⟨-, hred⟩
    exact he (((isReducedFace_prime_pow_iff F m q e).mp hred).1 hq)

/-- Off the face the local Euler factor is the truncated geometric sum. -/
theorem tsum_reducedFaceCpow_prime_pow_of_notMem {F : Finset Nat.Primes} {m : ℕ} {s : ℂ}
    {q : Nat.Primes} (hq : q ∉ F) :
    ∑' e : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ e) =
      ∑ e ∈ Finset.range (m + 1), (((q : ℕ) : ℂ) ^ (-s)) ^ e := by
  classical
  rw [tsum_eq_sum (s := Finset.range (m + 1))]
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.mem_range] at he
    have hred : IsReducedFace F m ((q : ℕ) ^ e) :=
      (isReducedFace_prime_pow_iff F m q e).mpr ⟨fun h => absurd h hq, by omega⟩
    rw [reducedFaceCpow_apply, if_pos ⟨pow_ne_zero e q.prop.ne_zero, hred⟩]
    exact natCast_pow_cpow (q : ℕ) e (-s)
  · intro e he
    rw [Finset.mem_range, not_lt] at he
    rw [reducedFaceCpow_apply, if_neg]
    rintro ⟨-, hred⟩
    have := ((isReducedFace_prime_pow_iff F m q e).mp hred).2
    omega



/-! ## The winner block -/

/-- The fixed winner block `A = ∏_{p ∈ F} p^m` of a face. -/
def faceBlock (F : Finset Nat.Primes) (m : ℕ) : ℕ := ∏ p ∈ F, (p : ℕ) ^ m

theorem faceBlock_ne_zero (F : Finset Nat.Primes) (m : ℕ) : faceBlock F m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.prop.ne_zero

theorem faceBlock_factorization (F : Finset Nat.Primes) (m : ℕ) (q : ℕ) :
    (faceBlock F m).factorization q = ∑ p ∈ F, if (p : ℕ) = q then m else 0 := by
  classical
  rw [faceBlock, Nat.factorization_prod (fun p _ => pow_ne_zero _ p.prop.ne_zero),
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [p.prop.factorization_pow]
  simp [Finsupp.single_apply]

theorem faceBlock_factorization_mem {F : Finset Nat.Primes} {m : ℕ} {p : Nat.Primes}
    (hp : p ∈ F) : (faceBlock F m).factorization (p : ℕ) = m := by
  classical
  rw [faceBlock_factorization, Finset.sum_eq_single p]
  · exact if_pos rfl
  · exact fun b _ hbp => if_neg fun h => hbp (Subtype.ext h)
  · exact fun h => absurd hp h

theorem faceBlock_factorization_of_notMem {F : Finset Nat.Primes} {m : ℕ} {q : ℕ}
    (hq : ∀ p ∈ F, (p : ℕ) ≠ q) : (faceBlock F m).factorization q = 0 := by
  classical
  rw [faceBlock_factorization]
  exact Finset.sum_eq_zero fun p hp => if_neg (hq p hp)

/-! ## The winner face is the block times a reduced number -/

theorem isWinnerFace_faceBlock_mul_iff (F : Finset Nat.Primes) (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    IsWinnerFace F m (faceBlock F m * n) ↔ IsReducedFace F m n := by
  classical
  have hfac := Nat.factorization_mul (faceBlock_ne_zero F m) hn
  constructor
  · rintro ⟨hface, hcap⟩
    refine ⟨fun p hp => ?_, fun q => ?_⟩
    · have h := hface p hp
      rw [hfac] at h
      simp only [Finsupp.add_apply, faceBlock_factorization_mem hp] at h
      omega
    · have h := hcap q
      rw [hfac] at h
      simp only [Finsupp.add_apply] at h
      omega
  · rintro ⟨hface, hcap⟩
    refine ⟨fun p hp => ?_, fun q => ?_⟩
    · rw [hfac]
      simp only [Finsupp.add_apply, faceBlock_factorization_mem hp, hface p hp, Nat.add_zero]
    · rw [hfac]
      simp only [Finsupp.add_apply]
      by_cases hq : ∃ p ∈ F, (p : ℕ) = q
      · obtain ⟨p, hp, rfl⟩ := hq
        rw [faceBlock_factorization_mem hp, hface p hp]
        omega
      · rw [faceBlock_factorization_of_notMem (fun p hp h => hq ⟨p, hp, h⟩)]
        simpa using hcap q

theorem faceBlock_dvd_of_isWinnerFace {F : Finset Nat.Primes} {m N : ℕ} (hN : N ≠ 0)
    (h : IsWinnerFace F m N) : faceBlock F m ∣ N := by
  classical
  refine (Nat.factorization_le_iff_dvd (faceBlock_ne_zero F m) hN).mp ?_
  rw [Finsupp.le_def]
  intro q
  by_cases hq : ∃ p ∈ F, (p : ℕ) = q
  · obtain ⟨p, hp, rfl⟩ := hq
    exact le_of_eq ((faceBlock_factorization_mem hp).trans (h.1 p hp).symm)
  · rw [faceBlock_factorization_of_notMem (fun p hp hpq => hq ⟨p, hp, hpq⟩)]
    exact Nat.zero_le _

/-! ## The winner-face Dirichlet series -/

open Classical in
/-- The winner-face coefficient. -/
def faceCpow (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  if n ≠ 0 ∧ IsWinnerFace F m n then (n : ℂ) ^ (-s) else 0

/-- The winner-face Dirichlet series `B_{F,m}(s)`. -/
def faceSeries (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) : ℂ := ∑' n : ℕ, faceCpow F m s n

theorem faceCpow_faceBlock_mul (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) (n : ℕ) :
    faceCpow F m s (faceBlock F m * n) =
      ((faceBlock F m : ℕ) : ℂ) ^ (-s) * reducedFaceCpow F m s n := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp [faceCpow]
  · rw [faceCpow, reducedFaceCpow_apply]
    by_cases hred : IsReducedFace F m n
    · rw [if_pos ⟨Nat.mul_ne_zero (faceBlock_ne_zero F m) hn,
        (isWinnerFace_faceBlock_mul_iff F m hn).mpr hred⟩, if_pos ⟨hn, hred⟩]
      exact natCast_mul_cpow _ _ _
    · rw [if_neg (fun h : n ≠ 0 ∧ IsReducedFace F m n => hred h.2), mul_zero, if_neg]
      rintro ⟨-, hw⟩
      exact hred ((isWinnerFace_faceBlock_mul_iff F m hn).mp hw)

/-- **Reindexing by the winner block.**  The winner-face series is the block factor times the
reduced series. -/
theorem faceSeries_eq_faceBlock_mul (F : Finset Nat.Primes) (m : ℕ) (s : ℂ) :
    faceSeries F m s =
      ((faceBlock F m : ℕ) : ℂ) ^ (-s) * ∑' n : ℕ, reducedFaceCpow F m s n := by
  classical
  have hinj : Function.Injective fun n : ℕ => faceBlock F m * n := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (faceBlock_ne_zero F m)) h
  have hsupp : Function.support (faceCpow F m s) ⊆ Set.range fun n : ℕ => faceBlock F m * n := by
    intro N hN
    have hval : faceCpow F m s N ≠ 0 := hN
    have hcond : N ≠ 0 ∧ IsWinnerFace F m N := by
      by_contra hc
      exact hval (by rw [faceCpow, if_neg hc])
    obtain ⟨k, hk⟩ := faceBlock_dvd_of_isWinnerFace hcond.1 hcond.2
    exact ⟨k, hk.symm⟩
  calc faceSeries F m s = ∑' n : ℕ, faceCpow F m s (faceBlock F m * n) :=
        (hinj.tsum_eq hsupp).symm
    _ = ∑' n : ℕ, ((faceBlock F m : ℕ) : ℂ) ^ (-s) * reducedFaceCpow F m s n :=
        tsum_congr fun n => faceCpow_faceBlock_mul F m s n
    _ = _ := tsum_mul_left

/-! ## Assembling the Euler product -/

theorem hasProd_reducedFaceCpow {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun q : Nat.Primes => ∑' k : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ k))
      (∑' n : ℕ, reducedFaceCpow F m s n) :=
  (isMultiplicative_reducedFaceCpow F m s).eulerProduct_hasProd (summable_norm_reducedFaceCpow hs)

theorem one_lt_re_succ_mul_of_one_lt (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    1 < ((((m : ℂ) + 1) * s)).re := by
  have hcast : ((((m : ℂ) + 1) * s)).re = ((m : ℝ) + 1) * s.re := by
    simp [Complex.mul_re, Complex.add_re, Complex.natCast_re, Complex.add_im,
      Complex.natCast_im]
  rw [hcast]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem primeCpow_neg_natMul (p : Nat.Primes) (m : ℕ) (s : ℂ) :
    ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)) = (((p : ℕ) : ℂ) ^ (-s)) ^ m := by
  rw [show -((m : ℂ) * s) = ((m : ℕ) : ℂ) * (-s) by ring, Complex.cpow_nat_mul]

theorem primeCpow_neg_succ_mul (p : Nat.Primes) (m : ℕ) (s : ℂ) :
    ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)) = (((p : ℕ) : ℂ) ^ (-s)) ^ (m + 1) := by
  rw [show -(((m : ℂ) + 1) * s) = ((m + 1 : ℕ) : ℂ) * (-s) by push_cast; ring,
    Complex.cpow_nat_mul]

theorem natCast_finsetProd_cpow {ι : Type*} (S : Finset ι) (f : ι → ℕ) (r : ℂ) :
    ((∏ i ∈ S, f i : ℕ) : ℂ) ^ r = ∏ i ∈ S, ((f i : ℕ) : ℂ) ^ r := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, natCast_mul_cpow, ih, Finset.prod_insert ha]

theorem geomTrunc_mul_inv {x : ℂ} (hx : 1 - x ≠ 0) (k : ℕ) (hxk : 1 - x ^ (k + 1) ≠ 0) :
    (∑ i ∈ Finset.range (k + 1), x ^ i) * (1 - x ^ (k + 1))⁻¹ = (1 - x)⁻¹ := by
  have hx1 : x ≠ 1 := fun h => hx (by rw [h]; ring)
  rw [geom_sum_eq hx1, show x ^ (k + 1) - 1 = -(1 - x ^ (k + 1)) by ring,
    show x - 1 = -(1 - x) by ring, neg_div_neg_eq, div_mul_eq_mul_div,
    mul_inv_cancel₀ hxk, one_div]

/-- **The reduced face series against the doubled zeta.**  Multiplying the reduced series by
`ζ((m+1)s)` turns its Euler product into the zeta Euler product corrected on the face. -/
theorem tsum_reducedFaceCpow_mul_zeta {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, reducedFaceCpow F m s n) * riemannZeta (((m : ℂ) + 1) * s) =
      riemannZeta s * ∏ p ∈ F,
        (1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹ := by
  classical
  have hs0 : 0 < s.re := by linarith
  have hms := one_lt_re_succ_mul_of_one_lt m hs
  have hZ1 := riemannZeta_eulerProduct_hasProd hs
  have hZ2 := riemannZeta_eulerProduct_hasProd hms
  have hL := hasProd_reducedFaceCpow (F := F) (m := m) hs
  set e : Nat.Primes → ℂ := fun q =>
    if q ∈ F then (1 - ((q : ℕ) : ℂ) ^ (-s)) * (1 - ((q : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹
    else 1 with he
  have hE : HasProd e (∏ p ∈ F, e p) := hasProd_prod_of_ne_finset_one fun q hq => by
    rw [he]; exact if_neg hq
  have hEprod : (∏ p ∈ F, e p) =
      ∏ p ∈ F, (1 - ((p : ℕ) : ℂ) ^ (-s)) * (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹ :=
    Finset.prod_congr rfl fun p hp => by rw [he]; exact if_pos hp
  have hfam : (fun q : Nat.Primes =>
      (∑' k : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ k)) *
        (1 - ((q : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹)
      = fun q : Nat.Primes => (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹ * e q := by
    funext q
    have hne1 : (1 - ((q : ℕ) : ℂ) ^ (-s)) ≠ 0 := one_sub_primeCpow_neg_ne_zero hs0 q
    have hne2 : (1 - ((q : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s))) ≠ 0 :=
      one_sub_primeCpow_neg_ne_zero (by linarith) q
    by_cases hq : q ∈ F
    · rw [tsum_reducedFaceCpow_prime_pow_of_mem hq, he]
      simp only [if_pos hq, one_mul]
      rw [inv_mul_cancel_left₀ hne1]
    · rw [tsum_reducedFaceCpow_prime_pow_of_notMem hq, he]
      simp only [if_neg hq, mul_one]
      rw [primeCpow_neg_succ_mul] at hne2 ⊢
      exact geomTrunc_mul_inv hne1 m hne2
  have h1 : HasProd (fun q : Nat.Primes =>
      (∑' k : ℕ, reducedFaceCpow F m s ((q : ℕ) ^ k)) *
        (1 - ((q : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹)
      ((∑' n : ℕ, reducedFaceCpow F m s n) * riemannZeta (((m : ℂ) + 1) * s)) := hL.mul hZ2
  rw [hfam] at h1
  rw [← hEprod]
  exact h1.unique (hZ1.mul hE)

/-- **The analytic face Euler product.**  On the Euler half-plane the winner-face Dirichlet series
of a face is the Riemann zeta function times the face unit. -/
theorem faceSeries_eq_zeta_mul_faceUnit {F : Finset Nat.Primes} {m : ℕ} {s : ℂ} (hs : 1 < s.re) :
    faceSeries F m s = riemannZeta s * faceUnit F m s := by
  classical
  have hms := one_lt_re_succ_mul_of_one_lt m hs
  have hζ2 : riemannZeta (((m : ℂ) + 1) * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hms
  have hC := (eq_mul_inv_iff_mul_eq₀ hζ2).mpr (tsum_reducedFaceCpow_mul_zeta (F := F) (m := m) hs)
  have hprod : (∏ p ∈ F, (((p : ℕ) ^ m : ℕ) : ℂ) ^ (-s)) *
      (∏ p ∈ F, (1 - ((p : ℕ) : ℂ) ^ (-s)) *
        (1 - ((p : ℕ) : ℂ) ^ (-(((m : ℂ) + 1) * s)))⁻¹)
      = ∏ p ∈ F, faceTransitionUnit p m s := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [faceTransitionUnit, natCast_pow_cpow, primeCpow_neg_natMul, div_eq_mul_inv]
    ring
  rw [faceSeries_eq_faceBlock_mul, hC, faceUnit, faceBlock, natCast_finsetProd_cpow, ← hprod]
  ring

end RHTower
