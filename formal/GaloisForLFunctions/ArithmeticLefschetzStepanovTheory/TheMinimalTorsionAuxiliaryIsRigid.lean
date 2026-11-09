import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionQuotientDetection
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheStepanovCountOfTheClosedPoints

/-!
# The minimal torsion auxiliary is rigid

For a finite prime set with least prime `p`, full multiplicity `r` on the
order-`q` torsion locus costs length `p^(qr)`. At equality there is only one
auxiliary up to an integer scalar: `(u_p^q - 1)^r`. Subtracting its top
coefficient leaves quotient support strictly below `r`, which Fourier–Euler
extraction detects.
-/

open MvPolynomial Finset

noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Prime weights uniquely determine their exponent vectors. -/
theorem weight_injective : Function.Injective (weight (P := P)) := by
  have hlog (a : P →₀ ℕ) : Real.log (weight a) = frequency a := by
    rw [weight, frequency, Nat.cast_prod, Real.log_prod (fun p _ => by
      have := (p : Nat.Primes).2.pos; positivity)]
    apply sum_congr rfl
    intro p _
    rw [Nat.cast_pow, Real.log_pow]
  intro a b h
  apply frequency_injective
  rw [← hlog, ← hlog, h]

/-- Quotient order is bounded by the arithmetic weight of an exponent. -/
theorem two_pow_quotientOrder_le_weight (q : ℕ) (a : P →₀ ℕ) :
    2 ^ (q * torsionQuotientOrder q a) ≤ weight a := by
  calc
    _ = ∏ p : P, 2 ^ (q * (a p / q)) := by
      rw [torsionQuotientOrder, mul_sum, ← prod_pow_eq_pow_sum]
    _ ≤ ∏ p : P, 2 ^ a p := prod_le_prod' fun p _ =>
      Nat.pow_le_pow_right (by omega) (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (a p) q)
    _ ≤ weight a := prod_le_prod' fun p _ => Nat.pow_le_pow_left (p : Nat.Primes).2.two_le _

/-- Strictly subcritical arithmetic support cannot have full torsion multiplicity. -/
theorem eq_zero_of_length_lt_torsionMultiplicity (q r : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) (hlen : length F < 2 ^ (q * r))
    (hmult : ∀ t : P → ZMod q,
      MvPolynomial.map (Int.castRingHom ℂ) F ∈
        vanishingIdeal ℂ {fun p => ZMod.stdAddChar (t p)} ^ r) : F = 0 := by
  have hz := eq_zero_of_torsionMultiplicity_of_quotientOrder_lt q r
    (MvPolynomial.map (Int.castRingHom ℂ) F) ?_ hmult
  · exact (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)
      (by simpa only [map_zero] using hz)
  · intro a ha
    have haF : a ∈ F.support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at ha
      exact MvPolynomial.mem_support_iff.mpr fun h => ha (by rw [h, map_zero])
    have hlt := (two_pow_quotientOrder_le_weight q a).trans_lt
      ((le_sup (f := weight) haF).trans_lt hlen)
    have hqr := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
    exact (Nat.mul_lt_mul_left (NeZero.pos q)).mp hqr

/-- Restricting the allowed primes raises the support threshold to the least prime. -/
theorem minPrime_pow_quotientOrder_le_weight (q : ℕ) (p : P)
    (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ)) (a : P →₀ ℕ) :
    ((p : Nat.Primes) : ℕ) ^ (q * torsionQuotientOrder q a) ≤ weight a := by
  calc
    _ = ∏ s : P, ((p : Nat.Primes) : ℕ) ^ (q * (a s / q)) := by
      rw [torsionQuotientOrder, mul_sum, ← prod_pow_eq_pow_sum]
    _ ≤ ∏ s : P, ((p : Nat.Primes) : ℕ) ^ a s := prod_le_prod' fun s _ =>
      Nat.pow_le_pow_right (p : Nat.Primes).2.pos
        (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (a s) q)
    _ ≤ weight a := prod_le_prod' fun s _ => Nat.pow_le_pow_left (hmin s) _

theorem eq_zero_of_length_lt_minPrime_torsionMultiplicity (q r : ℕ) [NeZero q]
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) (hlen : length F < ((p : Nat.Primes) : ℕ) ^ (q * r))
    (hmult : ∀ t : P → ZMod q,
      MvPolynomial.map (Int.castRingHom ℂ) F ∈
        vanishingIdeal ℂ {fun j => ZMod.stdAddChar (t j)} ^ r) : F = 0 := by
  have hz := eq_zero_of_torsionMultiplicity_of_quotientOrder_lt q r
    (MvPolynomial.map (Int.castRingHom ℂ) F) ?_ hmult
  · exact (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)
      (by simpa only [map_zero] using hz)
  · intro a ha
    have haF : a ∈ F.support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] at ha
      exact MvPolynomial.mem_support_iff.mpr fun h => ha (by rw [h, map_zero])
    have hlt := (minPrime_pow_quotientOrder_le_weight q p hmin a).trans_lt
      ((le_sup (f := weight) haF).trans_lt hlen)
    have hqr := (Nat.pow_lt_pow_iff_right (p : Nat.Primes).2.one_lt).mp hlt
    exact (Nat.mul_lt_mul_left (NeZero.pos q)).mp hqr

private theorem coeff_circlePoly_single (h : Polynomial ℤ) (p : P) (k : ℕ)
    (hk : k ≤ h.natDegree) :
    (circlePoly h p).coeff (Finsupp.single p k) = h.coeff k := by
  classical
  rw [circlePoly_eq_sum, MvPolynomial.coeff_sum, sum_eq_single k]
  · simp only [MvPolynomial.coeff_monomial, if_true]
  · intro j _ hjk
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro he
    exact hjk (by simpa using congrArg (fun a : P →₀ ℕ => a p) he)
  · intro hknot
    exact (hknot (mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim

/-- Equality in the torsion support bound has a single generator over the integers. -/
theorem minimal_torsion_auxiliary_eq (q r : ℕ) [NeZero q]
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) (hlen : length F ≤ ((p : Nat.Primes) : ℕ) ^ (q * r))
    (hmult : ∀ t : P → ZMod q,
      MvPolynomial.map (Int.castRingHom ℂ) F ∈
        vanishingIdeal ℂ {fun j => ZMod.stdAddChar (t j)} ^ r) :
    F = C (F.coeff (Finsupp.single p (q * r))) * (X p ^ q - 1) ^ r := by
  classical
  let h : Polynomial ℤ := (Polynomial.X ^ q - Polynomial.C 1) ^ r
  have hmon : h.Monic := (Polynomial.monic_X_pow_sub_C (1 : ℤ) (NeZero.ne q)).pow r
  have hdeg : h.natDegree = q * r := by
    dsimp only [h]
    rw [(Polynomial.monic_X_pow_sub_C (1 : ℤ) (NeZero.ne q)).natDegree_pow,
      Polynomial.natDegree_X_pow_sub_C, Nat.mul_comm]
  have hcircle : circlePoly h p = (X p ^ q - 1) ^ r := by
    simp only [circlePoly, h, map_pow, map_sub, Polynomial.aeval_X,
      map_one]
  have htop : (circlePoly h p).coeff (Finsupp.single p (q * r)) = 1 := by
    rw [← hdeg, coeff_circlePoly_single h p h.natDegree le_rfl]
    exact hmon.coeff_natDegree
  let c := F.coeff (Finsupp.single p (q * r))
  let G := F - C c * circlePoly h p
  have hGlen : length G < ((p : Nat.Primes) : ℕ) ^ (q * r) := by
    have hp0 := (p : Nat.Primes).2.pos
    apply (Finset.sup_lt_iff (by positivity)).mpr
    intro a ha
    have haG : G.coeff a ≠ 0 := MvPolynomial.mem_support_iff.mp ha
    have haUnion := MvPolynomial.support_sub P F (C c * circlePoly h p) ha
    have hale : weight a ≤ ((p : Nat.Primes) : ℕ) ^ (q * r) := by
      rcases mem_union.mp haUnion with haF | haB
      · exact (le_sup (f := weight) haF).trans hlen
      · have haB' : a ∈ (circlePoly h p).support := by
          rw [MvPolynomial.mem_support_iff, coeff_C_mul] at haB
          exact MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp haB).2)
        have hB := le_sup (f := weight) haB'
        change weight a ≤ length (circlePoly h p) at hB
        rwa [length_circlePoly hmon.ne_zero, hdeg] at hB
    apply lt_of_le_of_ne hale
    intro heq
    have hae : a = Finsupp.single p (q * r) := by
      apply weight_injective
      rw [weight_single, heq]
    apply haG
    simp only [G, MvPolynomial.coeff_sub, coeff_C_mul, hae, htop, mul_one, c, sub_self]
  have hGmult : ∀ t : P → ZMod q,
      MvPolynomial.map (Int.castRingHom ℂ) G ∈
        vanishingIdeal ℂ {fun j => ZMod.stdAddChar (t j)} ^ r := by
    intro t
    dsimp only [G]
    rw [map_sub, map_mul]
    apply Ideal.sub_mem _ (hmult t)
    apply Ideal.mul_mem_left
    rw [hcircle, map_pow, map_sub, map_pow, MvPolynomial.map_X, map_one]
    apply Ideal.pow_mem_pow
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
    simp only [map_sub, map_pow, eval_X, map_one]
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self,
      zero_mul, AddChar.map_zero_eq_one, sub_self]
  have hz := eq_zero_of_length_lt_minPrime_torsionMultiplicity q r p hmin G hGlen hGmult
  have heq := sub_eq_zero.mp hz
  rwa [hcircle] at heq

/-- The entire minimal-length torsion kernel is generated by one prime binomial. -/
theorem minimal_torsion_auxiliary_iff (q r : ℕ) [NeZero q]
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) :
    (length F ≤ ((p : Nat.Primes) : ℕ) ^ (q * r) ∧
      ∀ t : P → ZMod q, MvPolynomial.map (Int.castRingHom ℂ) F ∈
        vanishingIdeal ℂ {fun j => ZMod.stdAddChar (t j)} ^ r) ↔
      ∃ c : ℤ, F = C c * (X p ^ q - 1) ^ r := by
  classical
  constructor
  · rintro ⟨hlen, hmult⟩
    exact ⟨_, minimal_torsion_auxiliary_eq q r p hmin F hlen hmult⟩
  · rintro ⟨c, rfl⟩
    let h : Polynomial ℤ := (Polynomial.X ^ q - Polynomial.C 1) ^ r
    have hmon : h.Monic := (Polynomial.monic_X_pow_sub_C (1 : ℤ) (NeZero.ne q)).pow r
    have hdeg : h.natDegree = q * r := by
      dsimp only [h]
      rw [(Polynomial.monic_X_pow_sub_C (1 : ℤ) (NeZero.ne q)).natDegree_pow,
        Polynomial.natDegree_X_pow_sub_C, Nat.mul_comm]
    have hcircle : circlePoly h p = (X p ^ q - 1) ^ r := by
      simp only [circlePoly, h, map_pow, map_sub, Polynomial.aeval_X, map_one]
    constructor
    · apply Finset.sup_le
      intro a ha
      rw [MvPolynomial.mem_support_iff, coeff_C_mul, ← hcircle] at ha
      have haB := MvPolynomial.mem_support_iff.mpr ((mul_ne_zero_iff.mp ha).2)
      have hB := le_sup (f := weight) haB
      change weight a ≤ length (circlePoly h p) at hB
      rwa [length_circlePoly hmon.ne_zero, hdeg] at hB
    · intro t
      rw [map_mul]
      apply Ideal.mul_mem_left
      rw [map_pow, map_sub, map_pow, MvPolynomial.map_X, map_one]
      apply Ideal.pow_mem_pow
      rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
      simp only [map_sub, map_pow, eval_X, map_one]
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul, AddChar.map_zero_eq_one, sub_self]

#print axioms minimal_torsion_auxiliary_eq
#print axioms minimal_torsion_auxiliary_iff

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
