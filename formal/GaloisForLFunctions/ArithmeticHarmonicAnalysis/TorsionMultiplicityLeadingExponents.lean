import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionQuotientDetection

/-!
# Leading exponents of full torsion multiplicity

Every coordinatewise maximal exponent of a polynomial vanishing to order
`r` on the full order-`q` torsion grid contains at least `r` complete
`q`-blocks. The shifted Euler word for that exponent, followed by Fourier
projection to its residue, reads its coefficient alone. This localizes the
multiplicity obstruction at each maximal monomial, without a degree bound.
-/

open MvPolynomial Finset
open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Full torsion multiplicity annihilates every lower-order residue Newton coefficient. -/
theorem residueNewton_eq_zero_of_torsionMultiplicity
    (q r : ℕ) [NeZero q] (F : MvPolynomial ι ℂ)
    (hmult : ∀ t : ι → ZMod q,
      F ∈ vanishingIdeal ℂ {fun i => ZMod.stdAddChar (t i)} ^ r)
    (b : ι → ZMod q) (k : ι → ℕ) (hk : (∑ i, k i) < r) :
    residueCoefficient q F.support (fun a i => (a i : ZMod q))
      (fun a => F.coeff a * ∏ i, ((a i / q).choose (k i) : ℂ)) b = 0 := by
  have hexp : finiteMonomialPolynomial F.support (fun a i => a i) F.coeff = F := by
    conv_rhs => rw [MvPolynomial.as_sum F]
    rw [finiteMonomialPolynomial]
    apply sum_congr rfl
    intro a _
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    intro i
    exact pow_zero _
  have hjet (t : ι → ZMod q) :
      eval (fun i => ZMod.stdAddChar (t i))
        (shiftedEulerWord (newtonEulerWord q b k) F) = 0 := by
    have hlen : 1 + (newtonEulerWord q b k).length ≤ r := by
      rw [newtonEulerWord_length]
      omega
    have hm := shiftedEulerWord_mem_ideal_pow (newtonEulerWord q b k)
      (vanishingIdeal ℂ {fun i => ZMod.stdAddChar (t i)}) 1
      (Ideal.pow_le_pow_right hlen (hmult t))
    simpa only [pow_one, mem_vanishingIdeal_singleton_iff, aeval_eq_eval] using hm
  have hrec := newtonEuler_fourier_extraction q F.support (fun a i => a i) F.coeff b k
  rw [hexp] at hrec
  simp only [hjet, zero_mul, sum_const_zero] at hrec
  have hnorm : (q : ℂ) ^ Fintype.card ι *
      ((q : ℂ) ^ (∑ i, k i) * ∏ i, ((k i).factorial : ℂ)) ≠ 0 := by
    have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    exact mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero (pow_ne_zero _ hq)
      (prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast Nat.factorial_ne_zero (k i)))
  exact (mul_eq_zero.mp hrec.symm).resolve_left hnorm

/-- Every coordinatewise maximal support exponent carries the required quotient order. -/
theorem le_torsionQuotientOrder_of_maximal
    (q r : ℕ) [NeZero q] (F : MvPolynomial ι ℂ) (a : ι →₀ ℕ)
    (ha : a ∈ F.support) (hmax : ∀ d ∈ F.support, a ≤ d → d = a)
    (hmult : ∀ t : ι → ZMod q,
      F ∈ vanishingIdeal ℂ {fun i => ZMod.stdAddChar (t i)} ^ r) :
    r ≤ torsionQuotientOrder q a := by
  classical
  by_contra hnot
  have hk : (∑ i, a i / q) < r := lt_of_not_ge hnot
  have hz := residueNewton_eq_zero_of_torsionMultiplicity q r F hmult
    (fun i => (a i : ZMod q)) (fun i => a i / q) hk
  have htop : residueCoefficient q F.support (fun d i => (d i : ZMod q))
      (fun d => F.coeff d * ∏ i, ((d i / q).choose (a i / q) : ℂ))
      (fun i => (a i : ZMod q)) = F.coeff a := by
    rw [residueCoefficient, sum_eq_single a]
    · simp only [Nat.choose_self, Nat.cast_one, prod_const_one, mul_one]
    · intro d hd hda
      obtain ⟨hd, hres⟩ := mem_filter.mp hd
      have hnot : ¬ ∀ i, a i / q ≤ d i / q := by
        intro hle
        apply hda (hmax d hd ?_)
        intro i
        have hr := (ZMod.natCast_eq_natCast_iff' (d i) (a i) q).mp (congrFun hres i)
        have hm := Nat.mul_le_mul_left q (hle i)
        have h1 := Nat.mod_add_div (a i) q
        have h2 := Nat.mod_add_div (d i) q
        omega
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      have hp : (∏ j, ((d j / q).choose (a j / q) : ℂ)) = 0 :=
        prod_eq_zero (mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero])
      rw [hp, mul_zero]
    · intro hnot
      exact (hnot (mem_filter.mpr ⟨ha, rfl⟩)).elim
  rw [htop] at hz
  exact (MvPolynomial.mem_support_iff.mp ha) hz

#print axioms le_torsionQuotientOrder_of_maximal

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
