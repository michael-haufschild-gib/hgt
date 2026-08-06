import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import GaloisForLFunctions.HTGeometry.PrimeSieveEulerTrace
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Coefficient decimation, inflation, and the off-multiple prime sieve

Decimation `(D_q a)(N) = a(qN)` and inflation `(S_q a)(M) = a(M/q)` on multiples
of `q` are exact finite-coefficient operations: decimation inverts inflation, the
composite `S_q D_q` is the coordinate projection onto the multiples of `q`, and
its complement `E_q = 1 - S_q D_q` is the coordinate projection onto the
non-multiples.  Composing the complements over a finite set of primes gives the
coordinate projection onto the integers coprime to the primorial, so the
off-multiple sieve of this file is the same operator as the commuting prime sieve
carried by the sieved diagonal.

Inflation acts on the ordinary Dirichlet series by the exact character `q^{-s}`,
with no convergence hypothesis: the series of the inflated sequence is a
reindexing of the original along multiplication by `q`.

The scale law of the sieve follows.  If a linear functional on coefficient
sequences carries the inflation character `q^{-s}`, and a family of sources
carries the decimation character `q^{s-1}`, then the off-multiple sieve of that
family scales by the Euler product of the sieve — the same density that governs
the sieved trace.
-/

open ArithmeticFunction Complex Filter Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient decimation: `(D_q a)(N) = a(qN)`. -/
def decimate (q : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun N => b (q * N)

/-- Coefficient inflation: `(S_q a)(M) = a(M/q)` on multiples of `q`, zero
elsewhere. -/
def inflate (q : ℕ) (b : ℕ → ℂ) : ℕ → ℂ :=
  fun M => if q ∣ M then b (M / q) else 0

theorem inflate_mul {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (N : ℕ) :
    inflate q b (q * N) = b N := by
  rw [inflate, if_pos (Dvd.intro N rfl), Nat.mul_div_cancel_left N hq]

theorem inflate_of_not_dvd {q M : ℕ} (h : ¬ q ∣ M) (b : ℕ → ℂ) :
    inflate q b M = 0 := by
  rw [inflate, if_neg h]

/-- **Decimation inverts inflation.** -/
theorem decimate_inflate {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) :
    decimate q (inflate q b) = b := by
  funext N
  rw [decimate, inflate_mul hq]

/-- The coordinate projection onto the multiples of `q`. -/
def multipleProjection (q : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := inflate q (decimate q b)

theorem multipleProjection_apply {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (M : ℕ) :
    multipleProjection q b M = if q ∣ M then b M else 0 := by
  rw [multipleProjection]
  by_cases h : q ∣ M
  · obtain ⟨N, rfl⟩ := h
    rw [inflate_mul hq, decimate, if_pos (Dvd.intro N rfl)]
  · rw [inflate_of_not_dvd h, if_neg h]

/-- The coordinate projection onto the non-multiples of `q`. -/
def offMultiple (q : ℕ) (b : ℕ → ℂ) : ℕ → ℂ :=
  fun M => b M - multipleProjection q b M

theorem offMultiple_eq (q : ℕ) (b : ℕ → ℂ) :
    offMultiple q b = fun M => b M - multipleProjection q b M := rfl

theorem offMultiple_apply {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (M : ℕ) :
    offMultiple q b M = if q ∣ M then 0 else b M := by
  rw [offMultiple, multipleProjection_apply hq]
  by_cases h : q ∣ M
  · rw [if_pos h, if_pos h, sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- The off-multiple sieve of a finite set of primes: the coordinate projection
onto the integers coprime to the primorial. -/
def sieveOffMultiple (P : Finset Nat.Primes) (b : ℕ → ℂ) : ℕ → ℂ :=
  fun M => if Nat.Coprime M (sievePrimorial P) then b M else 0

@[simp] theorem sieveOffMultiple_empty (b : ℕ → ℂ) : sieveOffMultiple ∅ b = b := by
  funext M
  rw [sieveOffMultiple, sievePrimorial_empty, if_pos (Nat.coprime_one_right M)]

/-- **The off-multiple sieve is the composite of the one-prime complements.** -/
theorem sieveOffMultiple_insert {p : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) (b : ℕ → ℂ) :
    sieveOffMultiple (insert p P) b = offMultiple (p : ℕ) (sieveOffMultiple P b) := by
  funext M
  rw [offMultiple_apply p.2.pos, sieveOffMultiple, sieveOffMultiple]
  by_cases hdvd : (p : ℕ) ∣ M
  · rw [if_pos hdvd,
      if_neg fun h => ((coprime_sievePrimorial_insert_iff hp M).mp h).2 hdvd]
  · rw [if_neg hdvd]
    by_cases hcop : Nat.Coprime M (sievePrimorial P)
    · rw [if_pos ((coprime_sievePrimorial_insert_iff hp M).mpr ⟨hcop, hdvd⟩),
        if_pos hcop]
    · rw [if_neg fun h => hcop ((coprime_sievePrimorial_insert_iff hp M).mp h).1,
        if_neg hcop]

/-- **Decimation at a prime outside the sieve commutes with the sieve.** -/
theorem decimate_sieveOffMultiple {p : Nat.Primes} {P : Finset Nat.Primes}
    (hp : p ∉ P) (b : ℕ → ℂ) :
    decimate (p : ℕ) (sieveOffMultiple P b)
      = sieveOffMultiple P (decimate (p : ℕ) b) := by
  funext N
  have hcopP : Nat.Coprime (p : ℕ) (sievePrimorial P) := coprime_sievePrimorial hp
  rw [decimate, sieveOffMultiple, sieveOffMultiple, decimate]
  by_cases hcop : Nat.Coprime N (sievePrimorial P)
  · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hcopP, hcop⟩), if_pos hcop]
  · rw [if_neg (fun h => hcop (Nat.coprime_mul_iff_left.mp h).2), if_neg hcop]

section Moebius

/-- The Möbius divisor sum, in complex form. -/
theorem sum_divisors_moebius_complex (n : ℕ) :
    ∑ d ∈ n.divisors, ((μ d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h : ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ)) (x := n),
      moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  calc ∑ d ∈ n.divisors, ((μ d : ℤ) : ℂ)
      = ((∑ d ∈ n.divisors, (μ d : ℤ) : ℤ) : ℂ) := by push_cast; ring
    _ = _ := by rw [h]; split <;> norm_num

/-- **Möbius expansion of the off-multiple sieve.**  The coordinate projection
onto the integers coprime to the primorial is the finite alternating sum of the
multiple-projections at the divisors of the primorial. -/
theorem sieveOffMultiple_eq_sum_divisors (P : Finset Nat.Primes) (b : ℕ → ℂ) (M : ℕ) :
    sieveOffMultiple P b M
      = ∑ d ∈ (sievePrimorial P).divisors,
          ((μ d : ℤ) : ℂ) * multipleProjection d b M := by
  classical
  have hM : sievePrimorial P ≠ 0 := sievePrimorial_ne_zero P
  have hterm : ∀ d ∈ (sievePrimorial P).divisors,
      ((μ d : ℤ) : ℂ) * multipleProjection d b M
        = (if d ∣ M then ((μ d : ℤ) : ℂ) else 0) * b M := by
    intro d hd
    rw [multipleProjection_apply (Nat.pos_of_mem_divisors hd)]
    split <;> ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.sum_filter,
    ← divisors_gcd_eq_filter M hM, sum_divisors_moebius_complex, sieveOffMultiple]
  by_cases h : Nat.gcd M (sievePrimorial P) = 1
  · rw [if_pos h, if_pos (show Nat.Coprime M (sievePrimorial P) from h), one_mul]
  · rw [if_neg h, if_neg (show ¬ Nat.Coprime M (sievePrimorial P) from h), zero_mul]

/-- The Möbius divisor sum of the primorial is the sieve density, in complex
form. -/
theorem sum_divisors_moebiusDiv_complex (P : Finset Nat.Primes) :
    ∑ d ∈ (sievePrimorial P).divisors, ((μ d : ℤ) : ℂ) / (d : ℂ)
      = ((sieveDensity P : ℝ) : ℂ) := by
  rw [← sum_divisors_moebiusDiv_sievePrimorial P, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  push_cast
  ring

end Moebius

section Dirichlet

/-- **The Dirichlet character of inflation.**  Inflation by `q` multiplies the
ordinary Dirichlet series by `q^{-s}`, exactly and without any convergence
hypothesis. -/
theorem LSeries_inflate {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (s : ℂ) :
    LSeries (inflate q b) s = ((q : ℂ)) ^ (-s) * LSeries b s := by
  have hqC : ((q : ℂ)) ≠ 0 := by exact_mod_cast hq.ne'
  have hinj : Function.Injective fun N : ℕ => q * N :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hq hab
  have hsupp : Function.support (fun M : ℕ => LSeries.term (inflate q b) s M)
      ⊆ Set.range fun N : ℕ => q * N := by
    intro M hM
    by_cases h : q ∣ M
    · obtain ⟨N, rfl⟩ := h
      exact ⟨N, rfl⟩
    · refine absurd ?_ hM
      show LSeries.term (inflate q b) s M = 0
      rcases Nat.eq_zero_or_pos M with rfl | hM0
      · exact LSeries.term_zero _ _
      · rw [LSeries.term_of_ne_zero hM0.ne' , inflate_of_not_dvd h, zero_div]
  have hterm : ∀ N : ℕ, LSeries.term (inflate q b) s (q * N)
      = ((q : ℂ)) ^ (-s) * LSeries.term b s N := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.mul_zero, LSeries.term_zero, LSeries.term_zero, mul_zero]
    · have hqN : q * N ≠ 0 := Nat.mul_ne_zero hq.ne' hN.ne'
      rw [LSeries.term_of_ne_zero hqN, LSeries.term_of_ne_zero hN.ne',
        inflate_mul hq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        Complex.cpow_neg]
      field_simp
  rw [LSeries, LSeries, ← tsum_mul_left, ← hinj.tsum_eq hsupp]
  exact tsum_congr hterm

/-- **The off-multiple Dirichlet split.**  The Dirichlet series of the
multiple-projection is the decimated series scaled by `q^{-s}`. -/
theorem LSeries_multipleProjection {q : ℕ} (hq : 0 < q) (b : ℕ → ℂ) (s : ℂ) :
    LSeries (multipleProjection q b) s
      = ((q : ℂ)) ^ (-s) * LSeries (decimate q b) s := by
  rw [multipleProjection, LSeries_inflate hq]

/-- Summability transfers to the multiple-projection: its terms are a subfamily
of the original terms. -/
theorem LSeriesSummable_multipleProjection {q : ℕ} (hq : 0 < q) {b : ℕ → ℂ} {s : ℂ}
    (hb : LSeriesSummable b s) : LSeriesSummable (multipleProjection q b) s := by
  refine Summable.of_norm_bounded hb.norm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero, norm_zero]
    positivity
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
      multipleProjection_apply hq]
    by_cases h : q ∣ n
    · rw [if_pos h]
    · rw [if_neg h, zero_div, norm_zero]
      positivity

/-- **The exact off-multiple Dirichlet split.**  The Dirichlet series of the
sequence supported off the multiples of `q` is the original series minus the
decimated series scaled by `q^{-s}`. -/
theorem LSeries_offMultiple {q : ℕ} (hq : 0 < q) {b : ℕ → ℂ} {s : ℂ}
    (hb : LSeriesSummable b s) :
    LSeries (offMultiple q b) s
      = LSeries b s - ((q : ℂ)) ^ (-s) * LSeries (decimate q b) s := by
  have hsplit : offMultiple q b = b - multipleProjection q b := rfl
  rw [hsplit, LSeries_sub hb (LSeriesSummable_multipleProjection hq hb),
    LSeries_multipleProjection hq]

end Dirichlet

section ScaleLaw

/-- **The prime-sieve scale law of a source with the decimation character.**

Let `J` be an additive functional on coefficient sequences carrying the
inflation character `q^{-s}`, and let `pol` be a family of sources on which
decimation by `q` is reindexing of the scale parameter and which carries the
decimation character `q^{s-1}`.  Then the off-multiple sieve of a finite prime
set scales every member of the family by the sieve density. -/
theorem J_sieveOffMultiple
    {J : (ℕ → ℂ) → ℂ} {s : ℂ} {pol : ℕ → ℕ → ℂ}
    (hsub : ∀ b c : ℕ → ℂ, J (fun M => b M - c M) = J b - J c)
    (hdec : ∀ a q : ℕ, decimate q (pol a) = pol (a * q))
    (hchar : ∀ a q : ℕ, 0 < q → J (pol (a * q)) = ((q : ℂ)) ^ (s - 1) * J (pol a))
    (hinf : ∀ (q : ℕ) (b : ℕ → ℂ), 0 < q → J (inflate q b) = ((q : ℂ)) ^ (-s) * J b)
    (P : Finset Nat.Primes) :
    ∀ a : ℕ, J (sieveOffMultiple P (pol a))
      = ((sieveDensity P : ℝ) : ℂ) * J (pol a) := by
  classical
  induction P using Finset.induction with
  | empty =>
      intro a
      rw [sieveOffMultiple_empty, sieveDensity_empty, Complex.ofReal_one, one_mul]
  | insert p P hp ih =>
      intro a
      have hppos : 0 < (p : ℕ) := p.2.pos
      have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hppos.ne'
      have hcomm := decimate_sieveOffMultiple hp (pol a)
      rw [hdec a (p : ℕ)] at hcomm
      have hJdec : J (decimate (p : ℕ) (sieveOffMultiple P (pol a)))
          = ((sieveDensity P : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (s - 1) * J (pol a) := by
        rw [hcomm, ih (a * (p : ℕ)), hchar a (p : ℕ) hppos, mul_assoc]
      have hchars : (((p : ℕ) : ℂ)) ^ (-s) * (((p : ℕ) : ℂ)) ^ (s - 1)
          = (((p : ℕ) : ℂ))⁻¹ := by
        rw [← Complex.cpow_add _ _ hpC, show -s + (s - 1) = -1 by ring,
          Complex.cpow_neg_one]
      rw [sieveOffMultiple_insert hp, offMultiple_eq, hsub, multipleProjection,
        hinf (p : ℕ) _ hppos, hJdec, ih a, sieveDensity_insert hp]
      push_cast
      rw [show (((p : ℕ) : ℂ)) ^ (-s)
          * (((sieveDensity P : ℝ) : ℂ) * (((p : ℕ) : ℂ)) ^ (s - 1) * J (pol a))
        = ((((p : ℕ) : ℂ)) ^ (-s) * (((p : ℕ) : ℂ)) ^ (s - 1))
          * (((sieveDensity P : ℝ) : ℂ) * J (pol a)) by ring, hchars]
      ring

end ScaleLaw

end GaloisForLFunctions.HTGeometry
