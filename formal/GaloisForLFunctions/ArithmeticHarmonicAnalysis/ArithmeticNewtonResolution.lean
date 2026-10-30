import GaloisForLFunctions.ArithmeticHarmonicAnalysis.ResidueNewtonDetection
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionArithmeticResolution

/-!
# Arithmetic length bounds residue Newton degree

Writing each prime valuation as its residue modulo `q` plus `q` times its
quotient gives an injective encoding of every positive support integer.
Unique factorization bounds the sum of quotient exponents by arithmetic
length: support below `2^(qr)` has quotient degree below `r`. Hence the
residue Newton coefficients of order below `r` determine every coefficient.
These algebraic coordinates are explicit; identification with analytic
torus jets is a separate assertion.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable (q r : ℕ) [NeZero q] [NeZero r]

/-- Quotient exponents after removing the residue modulo the torsion order. -/
def valuationQuotient (P : Finset ℕ) (n : ℕ) : P → ℕ :=
  fun p => n.factorization p / q

omit [NeZero q] [NeZero r] in
private theorem primeFactors_subset_shortPrimes {n : ℕ}
    (hn : n ∈ Ioo 0 (2 ^ (q * r))) : n.primeFactors ⊆ shortPrimes (q * r) := by
  intro p hp
  exact Nat.mem_primesBelow.mpr ⟨
    (Nat.le_of_dvd (mem_Ioo.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans_lt
      (mem_Ioo.mp hn).2,
    Nat.prime_of_mem_primeFactors hp⟩

omit [NeZero q] [NeZero r] in
/-- Residues together with quotient exponents retain every integer in the support interval. -/
def arithmeticNewtonEmbedding : Ioo 0 (2 ^ (q * r)) ↪
    ((shortPrimes (q * r) → ZMod q) × (shortPrimes (q * r) → ℕ)) where
  toFun n := (valuationResidue q (shortPrimes (q * r)) n,
    valuationQuotient q (shortPrimes (q * r)) n)
  inj' := by
    intro m n h
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (mem_Ioo.mp m.property).1.ne'
      (mem_Ioo.mp n.property).1.ne'
    intro p
    by_cases hp : p.Prime
    · by_cases hplt : p < 2 ^ (q * r)
      · have hpP : p ∈ shortPrimes (q * r) := Nat.mem_primesBelow.mpr ⟨hplt, hp⟩
        have hres := congrArg (fun v => v.1 ⟨p, hpP⟩) h
        have hquo := congrArg (fun v => v.2 ⟨p, hpP⟩) h
        change (m.val.factorization p : ZMod q) = (n.val.factorization p : ZMod q) at hres
        change m.val.factorization p / q = n.val.factorization p / q at hquo
        have hmod := (ZMod.natCast_eq_natCast_iff' _ _ q).mp hres
        calc
          m.val.factorization p = m.val.factorization p % q + q * (m.val.factorization p / q) :=
            (Nat.mod_add_div _ _).symm
          _ = n.val.factorization p % q + q * (n.val.factorization p / q) := by rw [hmod, hquo]
          _ = n.val.factorization p := Nat.mod_add_div _ _
      · rw [Nat.factorization_eq_zero_of_lt
          ((mem_Ioo.mp m.property).2.trans_le (le_of_not_gt hplt)),
          Nat.factorization_eq_zero_of_lt
          ((mem_Ioo.mp n.property).2.trans_le (le_of_not_gt hplt))]
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
        Nat.factorization_eq_zero_of_not_prime _ hp]

omit [NeZero r] in
/-- Every quotient multiindex below integer length `2^(qr)` has total order below `r`. -/
theorem valuationQuotient_order_lt (n : Ioo 0 (2 ^ (q * r))) :
    newtonOrder (valuationQuotient q (shortPrimes (q * r)) n) < r := by
  have hfac : (∏ p ∈ shortPrimes (q * r), p ^ n.val.factorization p) = n := by
    calc
      _ = ∏ p ∈ n.val.primeFactors, p ^ n.val.factorization p := by
        symm
        apply Finset.prod_subset (primeFactors_subset_shortPrimes q r n.property)
        intro p _ hp
        have hz : n.val.factorization p = 0 := by
          by_contra h
          exact hp (by simpa only [Nat.support_factorization] using
            (Finsupp.mem_support_iff.mpr h))
        rw [hz, pow_zero]
      _ = n := (Nat.prod_primeFactors_pow_factorization (mem_Ioo.mp n.property).1.ne').symm
  have hpow : 2 ^ (q * newtonOrder (valuationQuotient q (shortPrimes (q * r)) n)) ≤ n.val := by
    calc
      _ = ∏ p : shortPrimes (q * r), 2 ^ (q * (n.val.factorization p / q)) := by
        rw [newtonOrder, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
        rfl
      _ ≤ ∏ p : shortPrimes (q * r), p.val ^ n.val.factorization p := by
        apply Finset.prod_le_prod'
        intro p _
        have hp := (Nat.mem_primesBelow.mp p.property).2
        have he : q * (n.val.factorization p / q) ≤ n.val.factorization p := by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (n.val.factorization p) q
        exact (pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) he).trans
          (Nat.pow_le_pow_left hp.two_le _)
      _ = n.val := by
        rw [Finset.prod_coe_sort (shortPrimes (q * r)) (fun p => p ^ n.val.factorization p)]
        exact hfac
  have hlt := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    (hpow.trans_lt (mem_Ioo.mp n.property).2)
  exact (Nat.mul_lt_mul_left (NeZero.pos q)).mp hlt

/-- The original coefficient array in exact residue and quotient coordinates. -/
def arithmeticNewtonArray (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    ((shortPrimes (q * r) → ZMod q) × (shortPrimes (q * r) → ℕ)) →₀ ℂ :=
  Finsupp.embDomain (arithmeticNewtonEmbedding q r) (Finsupp.equivFunOnFinite.symm c)

omit [NeZero q] [NeZero r] in
/-- Reindexing preserves every arithmetic coefficient exactly. -/
theorem arithmeticNewtonArray_apply (c : Ioo 0 (2 ^ (q * r)) → ℂ)
    (n : Ioo 0 (2 ^ (q * r))) :
    arithmeticNewtonArray q r c (arithmeticNewtonEmbedding q r n) = c n := by
  rw [arithmeticNewtonArray, Finsupp.embDomain_apply_self]
  rfl

/-- Integer support bounds the degree of the residue Newton array. -/
theorem arithmeticNewtonArray_degree_lt (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    newtonDegree (arithmeticNewtonArray q r c) < r := by
  apply (Finset.sup_lt_iff (NeZero.pos r)).mpr
  intro v hv
  rw [arithmeticNewtonArray, Finsupp.support_embDomain] at hv
  obtain ⟨n, _, rfl⟩ := Finset.mem_map.mp hv
  exact valuationQuotient_order_lt q r n

/-- Newton coefficients of order below `r` determine every auxiliary supported below `2^(qr)`. -/
theorem arithmeticNewton_vanishing_iff (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ b a, newtonOrder a < r →
      residueNewtonCoefficient (arithmeticNewtonArray q r c) b a = 0) ↔
      ∀ n, c n = 0 := by
  constructor
  · intro h
    have hz : arithmeticNewtonArray q r c = 0 :=
      (residueNewton_vanishing_iff _).mp fun b a ha =>
        h b a (ha.trans_lt (arithmeticNewtonArray_degree_lt q r c))
    intro n
    rw [← arithmeticNewtonArray_apply q r c n, hz, Finsupp.zero_apply]
  · intro h b a _
    have hc : c = 0 := funext h
    subst c
    have hz : Finsupp.equivFunOnFinite.symm (0 : Ioo 0 (2 ^ (q * r)) → ℂ) = 0 :=
      Finsupp.ext fun _ => rfl
    simp only [arithmeticNewtonArray, hz, Finsupp.embDomain_zero,
      residueNewtonCoefficient, Finsupp.support_zero, filter_empty, sum_empty]

omit [NeZero q] [NeZero r] in
/-- Newton coefficients are explicit weighted sums of the original arithmetic coefficients. -/
theorem arithmeticNewtonCoefficient_eq (c : Ioo 0 (2 ^ (q * r)) → ℂ)
    (b : shortPrimes (q * r) → ZMod q) (a : shortPrimes (q * r) → ℕ) :
    residueNewtonCoefficient (arithmeticNewtonArray q r c) b a =
      ∑ n : Ioo 0 (2 ^ (q * r)),
        if valuationResidue q (shortPrimes (q * r)) n = b then
          c n * ∏ p, ((valuationQuotient q (shortPrimes (q * r)) n p).choose (a p) : ℂ)
        else 0 := by
  unfold residueNewtonCoefficient
  rw [Finset.sum_filter]
  change (Finsupp.embDomain (arithmeticNewtonEmbedding q r)
    (Finsupp.equivFunOnFinite.symm c)).sum
      (fun v z => if v.1 = b then z * ∏ i, ((v.2 i).choose (a i) : ℂ) else 0) = _
  rw [Finsupp.sum_embDomain, Finsupp.sum_fintype]
  · rfl
  · intro n
    split_ifs <;> simp only [zero_mul]

/-- Torsion samples with the exact quotient-binomial weight of one Newton order. -/
def arithmeticNewtonSample (c : Ioo 0 (2 ^ (q * r)) → ℂ)
    (a : shortPrimes (q * r) → ℕ) (t : shortPrimes (q * r) → ZMod q) : ℂ :=
  torsionPolynomial q univ (fun n : Ioo 0 (2 ^ (q * r)) =>
    valuationResidue q (shortPrimes (q * r)) n)
    (fun n => c n * ∏ p,
      ((valuationQuotient q (shortPrimes (q * r)) n p).choose (a p) : ℂ)) t

omit [NeZero r] in
/-- Fourier inversion separates every residue Newton coefficient from its weighted torsion samples. -/
theorem arithmeticNewton_sample_recovery (c : Ioo 0 (2 ^ (q * r)) → ℂ)
    (b : shortPrimes (q * r) → ZMod q) (a : shortPrimes (q * r) → ℕ) :
    (∑ t, arithmeticNewtonSample q r c a t * conj (torsionPhase q b t)) =
      (q : ℂ) ^ Fintype.card (shortPrimes (q * r)) *
        residueNewtonCoefficient (arithmeticNewtonArray q r c) b a := by
  have h := torsion_coefficient_recovery q univ
    (fun n : Ioo 0 (2 ^ (q * r)) => valuationResidue q (shortPrimes (q * r)) n)
    (fun n => c n * ∏ p,
      ((valuationQuotient q (shortPrimes (q * r)) n p).choose (a p) : ℂ)) b
  rw [residueCoefficient, Finset.sum_filter, ← arithmeticNewtonCoefficient_eq q r c b a] at h
  exact h

/-- Orders below `r` on the whole torsion grid detect every coefficient below length `2^(qr)`. -/
theorem arithmeticNewton_samples_vanish_iff (c : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ a, newtonOrder a < r → ∀ t, arithmeticNewtonSample q r c a t = 0) ↔
      ∀ n, c n = 0 := by
  constructor
  · intro h
    apply (arithmeticNewton_vanishing_iff q r c).mp
    intro b a ha
    have hr := arithmeticNewton_sample_recovery q r c b a
    simp only [h a ha, zero_mul, Finset.sum_const_zero] at hr
    exact (mul_eq_zero.mp hr.symm).resolve_left
      (pow_ne_zero _ (by exact_mod_cast NeZero.ne q))
  · intro h a _ t
    unfold arithmeticNewtonSample torsionPolynomial
    apply Finset.sum_eq_zero
    intro n _
    dsimp only
    rw [h n, zero_mul, zero_mul]

omit [NeZero r] in
theorem arithmeticNewtonSample_sub (c d : Ioo 0 (2 ^ (q * r)) → ℂ)
    (a : shortPrimes (q * r) → ℕ) (t : shortPrimes (q * r) → ZMod q) :
    arithmeticNewtonSample q r (c - d) a t =
      arithmeticNewtonSample q r c a t - arithmeticNewtonSample q r d a t := by
  simp only [arithmeticNewtonSample, torsionPolynomial, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib]

/-- Equality of all low-order samples is equality of the original coefficient arrays. -/
theorem arithmeticNewton_samples_eq_iff (c d : Ioo 0 (2 ^ (q * r)) → ℂ) :
    (∀ a, newtonOrder a < r → ∀ t,
      arithmeticNewtonSample q r c a t = arithmeticNewtonSample q r d a t) ↔ c = d := by
  constructor
  · intro h
    have hz : ∀ n, (c - d) n = 0 :=
      (arithmeticNewton_samples_vanish_iff q r (c - d)).mp fun a ha t => by
        rw [arithmeticNewtonSample_sub, h a ha t, sub_self]
    exact funext fun n => sub_eq_zero.mp (hz n)
  · intro h
    subst d
    exact fun _ _ _ => rfl

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
