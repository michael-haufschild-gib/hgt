import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Reduced-frequency CRT root lifting

The reducible quadratic root packet `r * (r + h) = 0` factors under the Chinese remainder
equivalence.  More sharply, multiplying a frequency by a coprime complementary modulus makes its
standard additive character constant on that complementary root coordinate.  Consequently the
root sum at `(q * d, a * d)` is exactly the root count at `d` times the primitive response at
`(q, a)`.

This is the finite arithmetic engine behind reduced-frequency Möbius alias collapse.  It is an
unconditional finite theorem; no estimate or hypothesis about zeta zeros occurs here.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Roots of the fixed-gap reducible quadratic `r * (r + h)` modulo `n`. -/
def quadraticCongruenceRoots (n : ℕ) [NeZero n] (h : ℤ) :=
  {r : ZMod n // r * (r + (h : ZMod n)) = 0}

noncomputable instance quadraticCongruenceRootsFintype
    (n : ℕ) [NeZero n] (h : ℤ) : Fintype (quadraticCongruenceRoots n h) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Number of roots of `r * (r + h) = 0` modulo `n`. -/
noncomputable def quadraticCongruenceRootCount
    (n : ℕ) [NeZero n] (h : ℤ) : ℕ :=
  Fintype.card (quadraticCongruenceRoots n h)

/-- Standard additive-character sum over the roots of `r * (r + h) = 0` modulo `n`. -/
noncomputable def quadraticCongruenceRootSum
    (n : ℕ) [NeZero n] (h a : ℤ) : ℂ :=
  ∑ r : quadraticCongruenceRoots n h,
    ZMod.stdAddChar ((a : ZMod n) * r.1)

/-- Totalized root count, defined to vanish at the degenerate modulus `0`. -/
noncomputable def quadraticCongruenceRootCountTotal (n : ℕ) (h : ℤ) : ℕ :=
  if hn : n = 0 then 0 else
    @quadraticCongruenceRootCount n ⟨hn⟩ h

/-- Totalized root sum, defined to vanish at the degenerate modulus `0`. -/
noncomputable def quadraticCongruenceRootSumTotal (n : ℕ) (h a : ℤ) : ℂ :=
  if hn : n = 0 then 0 else
    @quadraticCongruenceRootSum n ⟨hn⟩ h a

@[simp] theorem quadraticCongruenceRootCountTotal_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) (h : ℤ) :
    quadraticCongruenceRootCountTotal n h = @quadraticCongruenceRootCount n ⟨hn⟩ h := by
  simp [quadraticCongruenceRootCountTotal, hn]

@[simp] theorem quadraticCongruenceRootSumTotal_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) (h a : ℤ) :
    quadraticCongruenceRootSumTotal n h a = @quadraticCongruenceRootSum n ⟨hn⟩ h a := by
  simp [quadraticCongruenceRootSumTotal, hn]

/-- Every nondegenerate quadratic root packet contains the zero residue. -/
theorem quadraticCongruenceRootCount_pos
    (n : ℕ) [NeZero n] (h : ℤ) :
    0 < quadraticCongruenceRootCount n h := by
  unfold quadraticCongruenceRootCount
  rw [Fintype.card_pos_iff]
  exact ⟨⟨0, by simp⟩⟩

/-- The root response is bounded by the number of roots. -/
theorem norm_quadraticCongruenceRootSum_le_count
    (n : ℕ) [NeZero n] (h a : ℤ) :
    ‖quadraticCongruenceRootSum n h a‖ ≤ quadraticCongruenceRootCount n h := by
  unfold quadraticCongruenceRootSum quadraticCongruenceRootCount
  calc
    ‖∑ r : quadraticCongruenceRoots n h,
        ZMod.stdAddChar ((a : ZMod n) * r.1)‖ ≤
        ∑ r : quadraticCongruenceRoots n h,
          ‖ZMod.stdAddChar ((a : ZMod n) * r.1)‖ := norm_sum_le _ _
    _ = Fintype.card (quadraticCongruenceRoots n h) := by simp

/-- Totalized root-response bound. -/
theorem norm_quadraticCongruenceRootSumTotal_le_count
    (n : ℕ) (h a : ℤ) :
    ‖quadraticCongruenceRootSumTotal n h a‖ ≤ quadraticCongruenceRootCountTotal n h := by
  by_cases hn : n = 0
  · subst n
    simp [quadraticCongruenceRootSumTotal, quadraticCongruenceRootCountTotal]
  · letI : NeZero n := ⟨hn⟩
    rw [quadraticCongruenceRootSumTotal_of_ne_zero hn,
      quadraticCongruenceRootCountTotal_of_ne_zero hn]
    exact norm_quadraticCongruenceRootSum_le_count n h a

/-- Every normalized quadratic root response lies in the closed unit disk. -/
theorem norm_quadraticCongruenceNormalizedRootSum_le_one
    (n : ℕ) (h a : ℤ) :
    ‖quadraticCongruenceRootSumTotal n h a /
        (quadraticCongruenceRootCountTotal n h : ℂ)‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [quadraticCongruenceRootSumTotal, quadraticCongruenceRootCountTotal]
  · letI : NeZero n := ⟨hn⟩
    rw [quadraticCongruenceRootSumTotal_of_ne_zero hn,
      quadraticCongruenceRootCountTotal_of_ne_zero hn, norm_div]
    have hcount : 0 < quadraticCongruenceRootCount n h :=
      quadraticCongruenceRootCount_pos n h
    rw [Complex.norm_natCast, div_le_one (Nat.cast_pos.mpr hcount)]
    exact norm_quadraticCongruenceRootSum_le_count n h a

/-- The reducible quadratic root condition splits componentwise under CRT. -/
theorem quadraticCongruenceRoot_iff_chineseRemainder
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h : ℤ) (x : ZMod (q * d)) :
    x * (x + (h : ZMod (q * d))) = 0 ↔
      (ZMod.chineseRemainder hcop x).1 *
          ((ZMod.chineseRemainder hcop x).1 + (h : ZMod q)) = 0 ∧
        (ZMod.chineseRemainder hcop x).2 *
          ((ZMod.chineseRemainder hcop x).2 + (h : ZMod d)) = 0 := by
  let e := ZMod.chineseRemainder hcop
  constructor
  · intro hx
    have heq := congrArg e hx
    constructor
    · have := congrArg Prod.fst heq
      simpa [e] using this
    · have := congrArg Prod.snd heq
      simpa [e] using this
  · intro hx
    apply e.injective
    apply Prod.ext
    · simpa [e] using hx.1
    · simpa [e] using hx.2

/-- CRT equivalence between the full reducible root set and its two root coordinates. -/
noncomputable def quadraticCongruenceRootChineseRemainderEquiv
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h : ℤ) :
    quadraticCongruenceRoots (q * d) h ≃
      quadraticCongruenceRoots q h × quadraticCongruenceRoots d h :=
  ((ZMod.chineseRemainder hcop).toEquiv.subtypeEquiv
    (quadraticCongruenceRoot_iff_chineseRemainder hcop h)).trans
      Equiv.subtypeProdEquivProd

/-- Pulling the standard character at frequency `a * d` through CRT deletes the coprime `d`
coordinate exactly.  No coprimality assumption on `a` and `q` is needed. -/
theorem stdAddChar_mul_complement_chineseRemainder
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (a : ℤ) (x : ZMod (q * d)) :
    ZMod.stdAddChar (((a * (d : ℤ) : ℤ) : ZMod (q * d)) * x) =
      ZMod.stdAddChar ((a : ZMod q) * (ZMod.chineseRemainder hcop x).1) := by
  rw [show x = (x.val : ZMod (q * d)) by exact (ZMod.natCast_zmod_val x).symm]
  have hxq :
      (ZMod.chineseRemainder hcop (x.val : ZMod (q * d))).1 = (x.val : ZMod q) := by
    simp [ZMod.chineseRemainder]
  rw [hxq]
  have hlhs :
      ((a * (d : ℤ) : ℤ) : ZMod (q * d)) * (x.val : ZMod (q * d)) =
        ((a * (d : ℤ) * (x.val : ℤ) : ℤ) : ZMod (q * d)) := by
    push_cast
    ring
  have hrhs :
      (a : ZMod q) * (x.val : ZMod q) =
        ((a * (x.val : ℤ) : ℤ) : ZMod q) := by
    push_cast
    ring
  rw [hlhs, hrhs]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  field_simp [hdC, hqC]

/-- Root counts are multiplicative on coprime moduli. -/
theorem quadraticCongruenceRootCount_mul
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h : ℤ) :
    quadraticCongruenceRootCount (q * d) h =
      quadraticCongruenceRootCount q h * quadraticCongruenceRootCount d h := by
  unfold quadraticCongruenceRootCount
  rw [Fintype.card_congr (quadraticCongruenceRootChineseRemainderEquiv hcop h),
    Fintype.card_prod]

/-- **Reduced-frequency alias lifting.** A complementary modulus inserted simultaneously into the
modulus and the frequency contributes only its number of quadratic roots.  The active character
response remains entirely on `q`. -/
theorem quadraticCongruenceRootSum_mul_alias
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h a : ℤ) :
    quadraticCongruenceRootSum (q * d) h (a * d) =
      quadraticCongruenceRootCount d h * quadraticCongruenceRootSum q h a := by
  unfold quadraticCongruenceRootSum quadraticCongruenceRootCount
  let e := quadraticCongruenceRootChineseRemainderEquiv hcop h
  calc
    (∑ r : quadraticCongruenceRoots (q * d) h,
        ZMod.stdAddChar ((((a * (d : ℕ) : ℤ) : ℤ) : ZMod (q * d)) * r.1)) =
        ∑ r : quadraticCongruenceRoots (q * d) h,
          ZMod.stdAddChar ((a : ZMod q) * (e r).1.1) := by
            apply Fintype.sum_congr
            intro r
            simpa [e, quadraticCongruenceRootChineseRemainderEquiv] using
              stdAddChar_mul_complement_chineseRemainder hcop a r.1
    _ = ∑ r : quadraticCongruenceRoots q h × quadraticCongruenceRoots d h,
          ZMod.stdAddChar ((a : ZMod q) * r.1.1) := by
            simpa only using e.sum_comp
              (fun r : quadraticCongruenceRoots q h × quadraticCongruenceRoots d h =>
                ZMod.stdAddChar ((a : ZMod q) * r.1.1))
    _ = ∑ r : quadraticCongruenceRoots q h, ∑ _s : quadraticCongruenceRoots d h,
          ZMod.stdAddChar ((a : ZMod q) * r.1) := Fintype.sum_prod_type _
    _ = Fintype.card (quadraticCongruenceRoots d h) *
          ∑ r : quadraticCongruenceRoots q h,
            ZMod.stdAddChar ((a : ZMod q) * r.1) := by
              simp [Finset.mul_sum]

/-- Complementary alias insertion leaves the normalized root response exactly unchanged.  Hence
all aliases in one reduced-frequency fibre carry the same point of the closed unit disk. -/
theorem quadraticCongruenceNormalizedRootSum_mul_alias
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q * d)] (hcop : q.Coprime d)
    (h a : ℤ) :
    quadraticCongruenceRootSum (q * d) h (a * d) /
        (quadraticCongruenceRootCount (q * d) h : ℂ) =
      quadraticCongruenceRootSum q h a /
        (quadraticCongruenceRootCount q h : ℂ) := by
  rw [quadraticCongruenceRootSum_mul_alias hcop h a,
    quadraticCongruenceRootCount_mul hcop h]
  have hqcount : (quadraticCongruenceRootCount q h : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (quadraticCongruenceRootCount_pos q h).ne'
  have hdcount : (quadraticCongruenceRootCount d h : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (quadraticCongruenceRootCount_pos d h).ne'
  push_cast
  field_simp [hqcount, hdcount]

/-- The totalized root count is multiplicative on nonzero coprime moduli. -/
theorem quadraticCongruenceRootCountTotal_mul
    {q d : ℕ} (hq : q ≠ 0) (hd : d ≠ 0) (hcop : q.Coprime d) (h : ℤ) :
    quadraticCongruenceRootCountTotal (q * d) h =
      quadraticCongruenceRootCountTotal q h * quadraticCongruenceRootCountTotal d h := by
  letI : NeZero q := ⟨hq⟩
  letI : NeZero d := ⟨hd⟩
  letI : NeZero (q * d) := ⟨Nat.mul_ne_zero hq hd⟩
  simp only [quadraticCongruenceRootCountTotal, hq, hd, Nat.mul_ne_zero hq hd,
    ↓reduceDIte]
  exact quadraticCongruenceRootCount_mul hcop h

/-- There is exactly one reducible quadratic root modulo `1`. -/
@[simp] theorem quadraticCongruenceRootCountTotal_one (h : ℤ) :
    quadraticCongruenceRootCountTotal 1 h = 1 := by
  simp only [quadraticCongruenceRootCountTotal, one_ne_zero, ↓reduceDIte,
    quadraticCongruenceRootCount]
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨0, by simp⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩

/-- The normalized quadratic root count as an arithmetic function. -/
noncomputable def quadraticCongruenceRootDensity (h : ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ),
    by simp [quadraticCongruenceRootCountTotal]⟩

@[simp] theorem quadraticCongruenceRootDensity_apply (h : ℤ) (n : ℕ) :
    quadraticCongruenceRootDensity h n =
      (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ) := rfl

/-- The normalized quadratic root density is multiplicative. -/
theorem quadraticCongruenceRootDensity_isMultiplicative (h : ℤ) :
    (quadraticCongruenceRootDensity h).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rw [quadraticCongruenceRootDensity_apply]
    norm_num only [Nat.cast_one, div_one]
    exact_mod_cast quadraticCongruenceRootCountTotal_one h
  · intro m n hm hn hcop
    rw [quadraticCongruenceRootDensity_apply, quadraticCongruenceRootDensity_apply,
      quadraticCongruenceRootDensity_apply,
      quadraticCongruenceRootCountTotal_mul hm hn hcop h]
    push_cast
    field_simp [hm, hn]

/-- On a squarefree modulus, the Möbius-weighted root density is exactly the Euler product of
local survival factors. -/
theorem quadraticCongruenceRootDensity_squarefree_euler
    {N : ℕ} (hN : Squarefree N) (h : ℤ) :
    ∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ((quadraticCongruenceRootCountTotal d h : ℂ) / (d : ℂ)) =
      ∏ p ∈ N.primeFactors,
        (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ)) := by
  simpa only [quadraticCongruenceRootDensity_apply] using
    ((quadraticCongruenceRootDensity_isMultiplicative h).prodPrimeFactors_one_sub_of_squarefree
      (quadraticCongruenceRootDensity h) hN).symm

/-- At prime modulus the root equation is the union of its two linear branches. -/
theorem quadraticCongruenceRoot_iff_eq_zero_or_eq_neg_of_prime
    {p : ℕ} (hp : p.Prime) (h : ℤ) (r : ZMod p) :
    r * (r + (h : ZMod p)) = 0 ↔ r = 0 ∨ r = -(h : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [mul_eq_zero, add_eq_zero_iff_eq_neg]

/-- At a prime modulus, the reducible quadratic has one root when the prime divides the gap and
exactly two roots otherwise.  This includes `p = 2`. -/
theorem quadraticCongruenceRootCount_prime
    {p : ℕ} [NeZero p] (hp : p.Prime) (h : ℤ) :
    quadraticCongruenceRootCount p h = if (p : ℤ) ∣ h then 1 else 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold quadraticCongruenceRootCount
  let e : quadraticCongruenceRoots p h ≃
      {r : ZMod p // r ∈ ({0, -(h : ZMod p)} : Finset (ZMod p))} :=
    Equiv.subtypeEquivRight fun r => by
      rw [quadraticCongruenceRoot_iff_eq_zero_or_eq_neg_of_prime hp h]
      simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [Fintype.card_congr e, Fintype.card_coe]
  by_cases hph : (p : ℤ) ∣ h
  · rw [if_pos hph]
    have hh : (h : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd h p).mpr hph
    simp [hh]
  · rw [if_neg hph]
    have hh : (h : ZMod p) ≠ 0 := fun hh0 =>
      hph ((ZMod.intCast_zmod_eq_zero_iff_dvd h p).mp hh0)
    simp [hh]

/-- Totalized prime root count. -/
theorem quadraticCongruenceRootCountTotal_prime
    {p : ℕ} (hp : p.Prime) (h : ℤ) :
    quadraticCongruenceRootCountTotal p h = if (p : ℤ) ∣ h then 1 else 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp only [quadraticCongruenceRootCountTotal, hp.ne_zero, ↓reduceDIte]
  exact quadraticCongruenceRootCount_prime hp h

/-- Exact local survival factor at a prime. -/
theorem quadraticCongruencePrimeSurvivalFactor
    {p : ℕ} (hp : p.Prime) (h : ℤ) :
    1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ) =
      if (p : ℤ) ∣ h then ((p : ℂ) - 1) / (p : ℂ)
      else ((p : ℂ) - 2) / (p : ℂ) := by
  rw [quadraticCongruenceRootCountTotal_prime hp h]
  split_ifs <;> push_cast <;> field_simp [hp.ne_zero]

/-- A prime-local survival factor vanishes exactly at the unmerged `2`-adic root pair. -/
theorem quadraticCongruencePrimeSurvivalFactor_eq_zero_iff
    {p : ℕ} (hp : p.Prime) (h : ℤ) :
    1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ) = 0 ↔
      p = 2 ∧ ¬(p : ℤ) ∣ h := by
  rw [quadraticCongruencePrimeSurvivalFactor hp h]
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  split_ifs with hph
  · constructor
    · intro hz
      have hnum : (p : ℂ) - 1 = 0 := (div_eq_zero_iff.mp hz).resolve_right hpC
      have hp1C : (p : ℂ) = 1 := sub_eq_zero.mp hnum
      have hp1 : p = 1 := Nat.cast_inj.mp (by simpa using hp1C)
      exact (hp.ne_one hp1).elim
    · rintro ⟨_, hnot⟩
      exact (hnot hph).elim
  · constructor
    · intro hz
      have hnum : (p : ℂ) - 2 = 0 := (div_eq_zero_iff.mp hz).resolve_right hpC
      have hp2C : (p : ℂ) = 2 := sub_eq_zero.mp hnum
      exact ⟨Nat.cast_inj.mp (by simpa using hp2C), hph⟩
    · rintro ⟨rfl, _⟩
      norm_num

/-- For a finite set of primes, the survival product vanishes exactly when it contains `2` and
the gap is odd. -/
theorem quadraticCongruencePrimeSurvivalProduct_eq_zero_iff
    (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) (h : ℤ) :
    (∏ p ∈ s,
      (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ))) = 0 ↔
      2 ∈ s ∧ ¬(2 : ℤ) ∣ h := by
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hpmem, hpzero⟩
    rcases (quadraticCongruencePrimeSurvivalFactor_eq_zero_iff
      (hprime p hpmem) h).mp hpzero with ⟨rfl, h2⟩
    exact ⟨hpmem, h2⟩
  · rintro ⟨h2mem, h2⟩
    exact ⟨2, h2mem,
      (quadraticCongruencePrimeSurvivalFactor_eq_zero_iff Nat.prime_two h).mpr
        ⟨rfl, h2⟩⟩

/-- Prime-factor specialization of the exact parity-vanishing law; squarefreeness is unnecessary. -/
theorem quadraticCongruencePrimeFactorsSurvivalProduct_eq_zero_iff
    {N : ℕ} (hN : N ≠ 0) (h : ℤ) :
    (∏ p ∈ N.primeFactors,
      (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ))) = 0 ↔
      2 ∣ N ∧ ¬(2 : ℤ) ∣ h := by
  rw [quadraticCongruencePrimeSurvivalProduct_eq_zero_iff N.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) h]
  simp [Nat.mem_primeFactors_of_ne_zero hN, Nat.prime_two]

/-- The squarefree Möbius-density Euler sum has no exact local annihilation beyond parity. -/
theorem quadraticCongruenceRootDensity_squarefree_euler_eq_zero_iff
    {N : ℕ} (hN : Squarefree N) (h : ℤ) :
    (∑ d ∈ N.divisors, (ArithmeticFunction.moebius d : ℂ) *
      ((quadraticCongruenceRootCountTotal d h : ℂ) / (d : ℂ))) = 0 ↔
      2 ∣ N ∧ ¬(2 : ℤ) ∣ h := by
  rw [quadraticCongruenceRootDensity_squarefree_euler hN h,
    quadraticCongruencePrimeFactorsSurvivalProduct_eq_zero_iff hN.ne_zero h]

/-- The quadratic root packet never has more elements than its ambient residue space. -/
theorem quadraticCongruenceRootCountTotal_le (n : ℕ) (h : ℤ) :
    quadraticCongruenceRootCountTotal n h ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp [quadraticCongruenceRootCountTotal]
  · letI : NeZero n := ⟨hn⟩
    rw [quadraticCongruenceRootCountTotal_of_ne_zero hn,
      quadraticCongruenceRootCount]
    calc
      Fintype.card (quadraticCongruenceRoots n h) ≤ Fintype.card (ZMod n) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = n := ZMod.card n

/-- Bernoulli weight of an active coordinate packet `t` inside `s`: active coordinates contribute
their quadratic root density, while inactive coordinates contribute their survival factor. -/
noncomputable def quadraticCongruenceAliasSurvivalWeight
    (s t : Finset ℕ) (h : ℤ) : ℝ :=
  (∏ n ∈ t, (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ)) *
    ∏ n ∈ s \ t,
      (1 - (quadraticCongruenceRootCountTotal n h : ℝ) / (n : ℝ))

/-- **Alias probability law.** The active/inactive quadratic root weights on the Boolean
coordinate cube sum exactly to one.  No primality or squarefreeness assumption is needed. -/
theorem quadraticCongruenceAliasSurvivalWeights_sum_eq_one
    (s : Finset ℕ) (h : ℤ) :
    ∑ t ∈ s.powerset, quadraticCongruenceAliasSurvivalWeight s t h = 1 := by
  unfold quadraticCongruenceAliasSurvivalWeight
  rw [← Finset.prod_add]
  simp

/-- Alias probability weights are nonnegative on nonzero coordinate packets. -/
theorem quadraticCongruenceAliasSurvivalWeight_nonneg
    (s t : Finset ℕ) (hnz : ∀ n ∈ s, n ≠ 0) (h : ℤ) :
    0 ≤ quadraticCongruenceAliasSurvivalWeight s t h := by
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro n _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Finset.prod_nonneg
    intro n hnrest
    apply sub_nonneg.mpr
    rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (hnz n (Finset.mem_sdiff.mp hnrest).1)))]
    exact_mod_cast quadraticCongruenceRootCountTotal_le n h

/-- **Alias contraction.** Averaging arbitrary responses against the exact active/survival weights
cannot exceed the worst response norm.  The constant response attains equality by
`quadraticCongruenceAliasSurvivalWeights_sum_eq_one`, so the source-independent contraction norm
is exactly one. -/
theorem quadraticCongruenceAliasSurvivalContraction
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ℕ) (hnz : ∀ n ∈ s, n ≠ 0) (h : ℤ)
    (response : Finset ℕ → E) (C : ℝ)
    (hresponse : ∀ t ∈ s.powerset, ‖response t‖ ≤ C) :
    ‖∑ t ∈ s.powerset,
        quadraticCongruenceAliasSurvivalWeight s t h • response t‖ ≤ C := by
  calc
    ‖∑ t ∈ s.powerset,
        quadraticCongruenceAliasSurvivalWeight s t h • response t‖ ≤
        ∑ t ∈ s.powerset,
          ‖quadraticCongruenceAliasSurvivalWeight s t h • response t‖ :=
      norm_sum_le _ _
    _ = ∑ t ∈ s.powerset,
          quadraticCongruenceAliasSurvivalWeight s t h * ‖response t‖ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      exact quadraticCongruenceAliasSurvivalWeight_nonneg s t hnz h
    _ ≤ ∑ t ∈ s.powerset,
          quadraticCongruenceAliasSurvivalWeight s t h * C := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left (hresponse t ht)
        (quadraticCongruenceAliasSurvivalWeight_nonneg s t hnz h)
    _ = C := by
      rw [← Finset.sum_mul, quadraticCongruenceAliasSurvivalWeights_sum_eq_one]
      simp

/-- Root counts factor over any finite family of pairwise coprime nonzero moduli. -/
theorem quadraticCongruenceRootCountTotal_prod
    (s : Finset ℕ) (hpair : (s : Set ℕ).Pairwise Nat.Coprime)
    (hnz : ∀ n ∈ s, n ≠ 0) (h : ℤ) :
    quadraticCongruenceRootCountTotal (∏ n ∈ s, n) h =
      ∏ n ∈ s, quadraticCongruenceRootCountTotal n h := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, quadraticCongruenceRootCountTotal_one]
  | @insert n s hns ih =>
      have hn : n ≠ 0 := hnz n (Finset.mem_insert_self n s)
      have hs : ∀ m ∈ s, m ≠ 0 := fun m hm => hnz m (Finset.mem_insert_of_mem hm)
      have hprod : (∏ m ∈ s, m) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
      have hcop : n.Coprime (∏ m ∈ s, m) := by
        rw [Nat.coprime_prod_right_iff]
        intro m hm
        exact hpair (Finset.mem_insert_self n s) (Finset.mem_insert_of_mem hm) (by aesop)
      have hpair_s : (s : Set ℕ).Pairwise Nat.Coprime := hpair.mono (by simp)
      simp only [Finset.prod_insert hns]
      rw [quadraticCongruenceRootCountTotal_mul hn hprod hcop h, ih hpair_s hs]

/-- Totalized form of reduced-frequency alias lifting. -/
theorem quadraticCongruenceRootSumTotal_mul_alias
    {q d : ℕ} (hq : q ≠ 0) (hd : d ≠ 0) (hcop : q.Coprime d) (h a : ℤ) :
    quadraticCongruenceRootSumTotal (q * d) h (a * d) =
      quadraticCongruenceRootCountTotal d h * quadraticCongruenceRootSumTotal q h a := by
  letI : NeZero q := ⟨hq⟩
  letI : NeZero d := ⟨hd⟩
  letI : NeZero (q * d) := ⟨Nat.mul_ne_zero hq hd⟩
  simp only [quadraticCongruenceRootCountTotal, quadraticCongruenceRootSumTotal, hq, hd,
    Nat.mul_ne_zero hq hd, ↓reduceDIte]
  exact quadraticCongruenceRootSum_mul_alias hcop h a

/-- **Causally anchored alias lifting.** Complementary factors `d ∣ m` can be collapsed without
reducing any factor belonging to the anchor `c`.  Thus a first-crossing prime carried by `c`
remains active even when it divides the Fourier frequency `a * d`. -/
theorem quadraticCongruenceRootSumTotal_causalAnchor
    {c m d : ℕ} (hc : c ≠ 0) (hm : Squarefree m) (hd : d ∣ m)
    (hcm : c.Coprime m) (h a : ℤ) :
    quadraticCongruenceRootSumTotal (c * m) h (a * d) =
      quadraticCongruenceRootCountTotal d h *
        quadraticCongruenceRootSumTotal (c * (m / d)) h a := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hm.ne_zero hd
  have hdm : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm.ne_zero) hd
  have hquot0 : m / d ≠ 0 :=
    (Nat.div_pos hdm (Nat.pos_of_ne_zero hd0)).ne'
  have hc_d : c.Coprime d := hcm.coprime_dvd_right hd
  have hquot_d : (m / d).Coprime d := by
    apply Nat.coprime_of_squarefree_mul
    rwa [Nat.div_mul_cancel hd]
  have hcop : (c * (m / d)).Coprime d := hc_d.mul_left hquot_d
  have hq0 : c * (m / d) ≠ 0 := Nat.mul_ne_zero hc hquot0
  simpa only [mul_assoc, Nat.div_mul_cancel hd] using
    quadraticCongruenceRootSumTotal_mul_alias hq0 hd0 hcop h a

/-- **Unique causal gcd reduction.** Remove exactly the complementary factors of `m` dividing the
Fourier frequency, while every factor of the causal anchor `c` remains in the active modulus.
The resulting frequency may still be nonprimitive along `c`; the unrestricted-frequency CRT
identity is precisely what makes this reduction possible. -/
theorem quadraticCongruenceRootSumTotal_causalGCDReduction
    {c m : ℕ} (hc : c ≠ 0) (hm : Squarefree m) (hcm : c.Coprime m)
    (h k : ℤ) :
    let d := m.gcd k.natAbs
    quadraticCongruenceRootSumTotal (c * m) h k =
      quadraticCongruenceRootCountTotal d h *
        quadraticCongruenceRootSumTotal (c * (m / d)) h (k / (d : ℤ)) := by
  let d := m.gcd k.natAbs
  change quadraticCongruenceRootSumTotal (c * m) h k =
    quadraticCongruenceRootCountTotal d h *
      quadraticCongruenceRootSumTotal (c * (m / d)) h (k / (d : ℤ))
  have hd : d ∣ m := by
    dsimp only [d]
    exact Nat.gcd_dvd_left m k.natAbs
  have hdk : (d : ℤ) ∣ k := by
    rw [Int.natCast_dvd]
    dsimp only [d]
    exact Nat.gcd_dvd_right m k.natAbs
  calc
    quadraticCongruenceRootSumTotal (c * m) h k =
        quadraticCongruenceRootSumTotal (c * m) h ((k / (d : ℤ)) * d) := by
      rw [Int.ediv_mul_cancel hdk]
    _ = quadraticCongruenceRootCountTotal d h *
        quadraticCongruenceRootSumTotal (c * (m / d)) h (k / (d : ℤ)) :=
      quadraticCongruenceRootSumTotal_causalAnchor hc hm hd hcm h (k / (d : ℤ))

/-- The causal gcd reduction is maximal on the complementary coordinates: after extraction, the
remaining complementary modulus is coprime to the reduced frequency.  Any common factor left in
the full active modulus must therefore belong to the protected causal anchor. -/
theorem causalGCDReduction_complement_coprime
    {m : ℕ} (hm : m ≠ 0) (k : ℤ) :
    let d := m.gcd k.natAbs
    (m / d).Coprime (k / (d : ℤ)).natAbs := by
  let d := m.gcd k.natAbs
  change (m / d).Coprime (k / (d : ℤ)).natAbs
  have hdk : (d : ℤ) ∣ k := by
    rw [Int.natCast_dvd]
    dsimp only [d]
    exact Nat.gcd_dvd_right m k.natAbs
  rw [Int.natAbs_ediv_of_dvd hdk]
  change (m / m.gcd k.natAbs).Coprime (k.natAbs / m.gcd k.natAbs)
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left k.natAbs (Nat.pos_of_ne_zero hm))

/-- **Reduced-frequency Möbius alias collapse.** With a complementary squarefree modulus `N`,
the full classical Möbius divisor sum is a primitive root response times the exact local survival
Euler product. -/
theorem quadraticCongruence_reducedFrequencyAliasCollapse
    {q N : ℕ} (hq : q ≠ 0) (hN : Squarefree N) (hqN : q.Coprime N)
    (h a : ℤ) :
    ∑ d ∈ N.divisors,
        ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d) =
      ((ArithmeticFunction.moebius q : ℂ) / (q : ℂ)) *
        quadraticCongruenceRootSumTotal q h a *
          ∏ p ∈ N.primeFactors,
            (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ)) := by
  have hterm : ∀ d ∈ N.divisors,
      ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d) =
        (((ArithmeticFunction.moebius q : ℂ) / (q : ℂ)) *
          quadraticCongruenceRootSumTotal q h a) *
            ((ArithmeticFunction.moebius d : ℂ) *
              ((quadraticCongruenceRootCountTotal d h : ℂ) / (d : ℂ))) := by
    intro d hd
    have hdvd : d ∣ N := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hcop : q.Coprime d := hqN.coprime_dvd_right hdvd
    rw [quadraticCongruenceRootSumTotal_mul_alias hq hd0 hcop h a]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    push_cast
    field_simp [hq, hd0]
  rw [Finset.sum_congr rfl (fun d hd => hterm d hd), ← Finset.mul_sum,
    quadraticCongruenceRootDensity_squarefree_euler hN h]

/-- If the complementary squarefree packet contains `2` while the gap is odd, every complete
reduced-frequency Möbius alias family cancels exactly. -/
theorem quadraticCongruence_reducedFrequencyAliasCollapse_eq_zero_of_parity
    {q N : ℕ} (hq : q ≠ 0) (hN : Squarefree N) (hqN : q.Coprime N)
    (h2N : 2 ∣ N) {h : ℤ} (h2h : ¬(2 : ℤ) ∣ h) (a : ℤ) :
    ∑ d ∈ N.divisors,
        ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d) = 0 := by
  rw [quadraticCongruence_reducedFrequencyAliasCollapse hq hN hqN h a]
  have hzero :
      (∏ p ∈ N.primeFactors,
        (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ))) = 0 :=
    (quadraticCongruencePrimeFactorsSurvivalProduct_eq_zero_iff hN.ne_zero h).mpr
      ⟨h2N, h2h⟩
  rw [hzero, mul_zero]

/-- **Odd-gap physical-cutoff balance.** When parity annihilates the complete alias family, its
physically active and inactive divisor pieces are exact negatives.  Thus any surviving odd-gap
contribution is localized entirely at the support cutoff, rather than in the completed Euler
packet. -/
theorem quadraticCongruence_oddGapAliasPhysicalCutoffBalance
    {q N : ℕ} (hq : q ≠ 0) (hN : Squarefree N) (hqN : q.Coprime N)
    (h2N : 2 ∣ N) {h : ℤ} (h2h : ¬(2 : ℤ) ∣ h) (a : ℤ) (H : ℕ) :
    (∑ d ∈ N.divisors with q * d ≤ H,
        ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d)) =
      -(∑ d ∈ N.divisors with H < q * d,
        ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d)) := by
  let term : ℕ → ℂ := fun d =>
    ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
      quadraticCongruenceRootSumTotal (q * d) h (a * d)
  have hfull : ∑ d ∈ N.divisors, term d = 0 := by
    exact quadraticCongruence_reducedFrequencyAliasCollapse_eq_zero_of_parity
      hq hN hqN h2N h2h a
  have hsplit := Finset.sum_filter_add_sum_filter_not N.divisors
    (fun d => q * d ≤ H) term
  rw [hfull] at hsplit
  simpa only [not_le] using eq_neg_of_add_eq_zero_left hsplit

/-- Paper form of reduced-frequency Möbius alias collapse, with complementary modulus `Q / q`. -/
theorem quadraticCongruence_reducedFrequencyAliasCollapse_of_dvd_squarefree
    {Q q : ℕ} (hQ : Squarefree Q) (hqQ : q ∣ Q) (h a : ℤ) :
    ∑ d ∈ (Q / q).divisors,
        ((ArithmeticFunction.moebius (q * d) : ℂ) / ((q * d : ℕ) : ℂ)) *
          quadraticCongruenceRootSumTotal (q * d) h (a * d) =
      ((ArithmeticFunction.moebius q : ℂ) / (q : ℂ)) *
        quadraticCongruenceRootSumTotal q h a *
          ∏ p ∈ (Q / q).primeFactors,
            (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ)) := by
  have hq : q ≠ 0 := ne_zero_of_dvd_ne_zero hQ.ne_zero hqQ
  have hN : Squarefree (Q / q) := hQ.squarefree_of_dvd (Nat.div_dvd_of_dvd hqQ)
  have hqN : q.Coprime (Q / q) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [Nat.mul_div_cancel' hqQ]
  exact quadraticCongruence_reducedFrequencyAliasCollapse hq hN hqN h a

/-- Inserting an entire pairwise-coprime complementary packet in the modulus and frequency leaves
only the product of its root counts. -/
theorem quadraticCongruenceRootSumTotal_mul_prod_alias
    {q : ℕ} (hq : q ≠ 0) (s : Finset ℕ)
    (hpair : (s : Set ℕ).Pairwise Nat.Coprime)
    (hnz : ∀ n ∈ s, n ≠ 0) (hqcop : ∀ n ∈ s, q.Coprime n)
    (h a : ℤ) :
    quadraticCongruenceRootSumTotal (q * ∏ n ∈ s, n) h (a * ∏ n ∈ s, n) =
      (∏ n ∈ s, quadraticCongruenceRootCountTotal n h) *
        quadraticCongruenceRootSumTotal q h a := by
  have hprod : (∏ n ∈ s, n) ≠ 0 := Finset.prod_ne_zero_iff.mpr hnz
  have hcop : q.Coprime (∏ n ∈ s, n) := by
    rw [Nat.coprime_prod_right_iff]
    exact hqcop
  rw [quadraticCongruenceRootSumTotal_mul_alias hq hprod hcop h a,
    quadraticCongruenceRootCountTotal_prod s hpair hnz h]

/-- Boolean inclusion-exclusion factors exactly as a product of local survival terms. -/
theorem sum_powerset_signed_prod_eq_prod_one_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (ν : ι → ℂ) :
    (∑ t ∈ s.powerset, (-1 : ℂ) ^ t.card * ∏ p ∈ t, ν p) =
      ∏ p ∈ s, (1 - ν p) := by
  simpa using (Finset.prod_sub (fun _ : ι => (1 : ℂ)) ν s).symm

/-- A fixed active response can be pulled through Boolean inclusion-exclusion. -/
theorem futureDressedAliasSum_eq_active_mul_survival
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (ν : ι → ℂ) (active : ℂ) :
    (∑ t ∈ s.powerset, active * ((-1 : ℂ) ^ t.card * ∏ p ∈ t, ν p)) =
      active * ∏ p ∈ s, (1 - ν p) := by
  rw [← Finset.mul_sum, sum_powerset_signed_prod_eq_prod_one_sub]

/-- **Finite reduced-frequency Möbius alias collapse.** For any pairwise-coprime family of
inactive moduli, the signed sum of all complementary aliases is exactly the primitive response
times a product of local root-density survival factors.  Primality and squarefreeness are not
needed: they enter only when this Boolean identity is reindexed as a classical Möbius divisor
sum.  The frequency `a` is arbitrary. -/
theorem quadraticRootFiniteMobiusAliasCollapse
    {q : ℕ} (hq : q ≠ 0) (s : Finset ℕ)
    (hpair : (s : Set ℕ).Pairwise Nat.Coprime)
    (hnz : ∀ n ∈ s, n ≠ 0) (hqcop : ∀ n ∈ s, q.Coprime n)
    (h a : ℤ) :
    (∑ t ∈ s.powerset,
      (-1 : ℂ) ^ t.card *
        (quadraticCongruenceRootSumTotal (q * ∏ n ∈ t, n) h
            (a * ∏ n ∈ t, n) /
          (q * ∏ n ∈ t, n : ℕ))) =
      quadraticCongruenceRootSumTotal q h a / (q : ℂ) *
        ∏ n ∈ s,
          (1 - (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ)) := by
  rw [← futureDressedAliasSum_eq_active_mul_survival s
    (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ))
    (quadraticCongruenceRootSumTotal q h a / (q : ℂ))]
  apply Finset.sum_congr rfl
  intro t ht
  have hts : t ⊆ s := Finset.mem_powerset.mp ht
  have hpair_t : (t : Set ℕ).Pairwise Nat.Coprime := hpair.mono (by simpa)
  have hnz_t : ∀ n ∈ t, n ≠ 0 := fun n hn => hnz n (hts hn)
  have hqcop_t : ∀ n ∈ t, q.Coprime n := fun n hn => hqcop n (hts hn)
  rw [quadraticCongruenceRootSumTotal_mul_prod_alias hq t hpair_t hnz_t hqcop_t h a]
  rw [show ((q * ∏ n ∈ t, n : ℕ) : ℂ) = (q : ℂ) * ∏ n ∈ t, (n : ℂ) by
    push_cast
    simp]
  rw [show ((∏ n ∈ t, quadraticCongruenceRootCountTotal n h : ℕ) : ℂ) =
      ∏ n ∈ t, (quadraticCongruenceRootCountTotal n h : ℂ) by
    push_cast
    simp]
  rw [Finset.prod_div_distrib]
  ring

end RHTower
