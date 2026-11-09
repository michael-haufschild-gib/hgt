import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialOrbitPreserversAreAdams

/-!
# Integral orbit preservers are exactly Adams operations

The complex classification leaves a common time translation. Integral
coefficients make every translation factor real and unimodular, hence a
sign. Two prime coordinates have no nonzero common torsion return, so the
translation vanishes.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
open InfiniteRankWeilTheory

variable {P : Finset Nat.Primes}

/-- Orbit preservation for polynomial maps defined over the integers. -/
def IntegerPreservesPrimeOrbit (F : P → MvPolynomial P ℤ) : Prop :=
  ∀ t : ℝ, ∃ u : ℝ, ∀ p : P, orbitValue (F p) t = orbitPoint P u p

/-- Extension of coefficients preserves evaluation on the prime orbit. -/
theorem complexOrbitValue_map_int (F : MvPolynomial P ℤ) (t : ℝ) :
    complexOrbitValue (MvPolynomial.map (Int.castRingHom ℂ) F) t = orbitValue F t := by
  rw [complexOrbitValue, MvPolynomial.eval_map, orbitValue, MvPolynomial.aeval_def]
  rfl

/-- Integer coefficients remove the time translation from the complex classification. -/
theorem integerPreservesPrimeOrbit_monomial (p q : P) (hpq : p ≠ q)
    (F : P → MvPolynomial P ℤ) (hF : IntegerPreservesPrimeOrbit F) :
    ∃ n : ℕ, ∀ r, F r = MvPolynomial.monomial (Finsupp.single r n) 1 := by
  classical
  let G : P → MvPolynomial P ℂ := fun r => MvPolynomial.map (Int.castRingHom ℂ) (F r)
  have hG : PreservesPrimeOrbit G := by
    intro t
    obtain ⟨u, hu⟩ := hF t
    refine ⟨u, fun r => ?_⟩
    change complexOrbitValue (MvPolynomial.map (Int.castRingHom ℂ) (F r)) t = _
    rw [complexOrbitValue_map_int]
    exact hu r
  obtain ⟨n, b, hGb⟩ := preservesPrimeOrbit_eq_translatedAdams p q hpq G hG
  have hcoeff (r : P) : (((F r).coeff (Finsupp.single r n) : ℤ) : ℂ) = orbitPoint P b r := by
    have hr := congrArg (MvPolynomial.coeff (Finsupp.single r n)) (congrFun hGb r)
    simpa [G, translatedAdams, MvPolynomial.coeff_map] using hr
  have hconj (r : P) : (starRingEnd ℂ) (orbitPoint P b r) = orbitPoint P b r := by
    rw [← hcoeff r]
    simp
  have hpow (r : P) : phase ((r : Nat.Primes) : ℕ) b ^ 2 = 1 := by
    change (orbitPoint P b r) ^ 2 = 1
    calc
      _ = orbitPoint P b r * (starRingEnd ℂ) (orbitPoint P b r) := by
        rw [hconj r, pow_two]
      _ = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        change ((‖phase ((r : Nat.Primes) : ℕ) b‖ ^ 2 : ℝ) : ℂ) = 1
        rw [norm_phase]
        simp
  have hb : b = 0 := eq_zero_of_torsion_return p.val.property q.val.property
    (fun he => hpq (Subtype.ext (Subtype.ext he))) (Nat.succ_pos 1) (hpow p) (hpow q)
  refine ⟨n, fun r => ?_⟩
  apply MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective
  have hr := congrFun hGb r
  simpa [G, translatedAdams, hb, orbitPoint, phase] using hr

/-- An integer polynomial map preserves the prime orbit exactly when it is an Adams operation. -/
theorem integerPreservesPrimeOrbit_iff (p q : P) (hpq : p ≠ q)
    (F : P → MvPolynomial P ℤ) :
    IntegerPreservesPrimeOrbit F ↔ ∃ n : ℕ, ∀ r, F r = MvPolynomial.X r ^ n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := integerPreservesPrimeOrbit_monomial p q hpq F h
    exact ⟨n, fun r => by rw [hn r, MvPolynomial.X_pow_eq_monomial]⟩
  · rintro ⟨n, hn⟩ t
    refine ⟨(n : ℝ) * t, fun r => ?_⟩
    rw [hn r]
    simp only [orbitValue, map_pow, MvPolynomial.aeval_X]
    exact (phase_nat_mul ((r : Nat.Primes) : ℕ) n t).symm

/-- Every integral algebra endomorphism preserving the prime orbit is an Adams operation. -/
theorem integer_endomorphism_is_adams (p q : P) (hpq : p ≠ q)
    (Φ : MvPolynomial P ℤ →ₐ[ℤ] MvPolynomial P ℤ)
    (hΦ : IntegerPreservesPrimeOrbit (fun r => Φ (MvPolynomial.X r))) :
    ∃ n : ℕ, Φ = adams n := by
  obtain ⟨n, hn⟩ := (integerPreservesPrimeOrbit_iff p q hpq _).mp hΦ
  refine ⟨n, ?_⟩
  apply MvPolynomial.algHom_ext
  intro r
  rw [hn r]
  simp only [adams, MvPolynomial.aeval_X]

#print axioms integerPreservesPrimeOrbit_iff
#print axioms integer_endomorphism_is_adams

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
