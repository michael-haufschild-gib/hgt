import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.ThePolynomialImageOfStepanovSyzygies
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.UniformMonicGridPowers

/-!
# The sharp arithmetic cost of polynomial Stepanov syzygies

The full affine Adams equations have degree `q`, whereas their torus
restrictions have degree `q-1`. The integral Newton filtration prices the
polynomial syzygy construction on its actual affine fixed locus.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

open ArithmeticHarmonicAnalysis

/-- The affine fixed-point equation has arithmetic degree `q`, including its zero root. -/
theorem arithmeticMonicAt_adamsFixed (q : ℕ) (hq : 2 ≤ q) (p : P) :
    ArithmeticMonicAt ((X p : MvPolynomial P ℤ) ^ q - X p) (Finsupp.single p q) := by
  classical
  have hsingle : Finsupp.single p q ≠ Finsupp.single p 1 := by
    intro h
    have he := congrArg (fun a : P →₀ ℕ => a p) h
    simp only [Finsupp.single_eq_same] at he
    omega
  suffices h : ArithmeticMonicAt ((X p : MvPolynomial P ℤ) ^ q - X p ^ 1)
      (Finsupp.single p q) by simpa only [pow_one] using h
  constructor
  · simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_X_pow, if_true,
      if_neg hsingle.symm, sub_zero]
  · intro b hb
    have hm := MvPolynomial.support_sub P (X p ^ q) (X p ^ 1) hb
    rw [MvPolynomial.support_X_pow, MvPolynomial.support_X_pow] at hm
    rcases mem_union.mp hm with hb | hb
    · rw [mem_singleton.mp hb]
    · rw [mem_singleton.mp hb, weight_single, weight_single]
      exact Nat.pow_le_pow_right (p : Nat.Primes).2.pos (by omega)

/-- Newton polynomials for the full affine Adams fixed-point equations. -/
def adamsNewtonPolynomial (q : ℕ) (a : P →₀ ℕ) : MvPolynomial P ℤ :=
  monicGridNewtonPolynomial q (fun p => X p ^ q - X p) a

theorem arithmeticMonicAt_adamsFixed_pow (q : ℕ) (hq : 2 ≤ q) (r : ℕ) (p : P) :
    ArithmeticMonicAt (((X p : MvPolynomial P ℤ) ^ q - X p) ^ r)
      (Finsupp.single p (q * r)) := by
  letI : NeZero q := ⟨by omega⟩
  have h := monicGridNewtonPolynomial_monic q (fun p => X p ^ q - X p)
    (arithmeticMonicAt_adamsFixed q hq) (Finsupp.single p (q * r))
  rwa [monicGridNewtonPolynomial_single_mul] at h

/-- Integral coordinates adapted to the full affine fixed locus. -/
def adamsNewtonBasis (q : ℕ) (hq : 2 ≤ q) :
    Module.Basis (P →₀ ℕ) ℤ (MvPolynomial P ℤ) := by
  letI : NeZero q := ⟨by omega⟩
  exact monicGridBasis q (fun p => X p ^ q - X p) (arithmeticMonicAt_adamsFixed q hq)

/-- The complete integral filtration of polynomial Stepanov constructions. -/
theorem stepanov_syzygies_iff_adamsNewton_support (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (F : MvPolynomial P ℤ) :
    (∃ m, ∃ f g : Fin m → MvPolynomial P ℤ,
      (∀ L : List P, L.length < r → stepanovWordMoment L f g = 0) ∧
        stepanovAux q f g = F) ↔
      ∀ a ∈ ((adamsNewtonBasis q hq).repr F).support, r ≤ torsionQuotientOrder q a := by
  letI : NeZero q := ⟨by omega⟩
  rw [← mem_adamsFixedIdeal_pow_iff_stepanov_syzygies]
  exact mem_monicGridIdeal_pow_iff_repr q _ (arithmeticMonicAt_adamsFixed q hq) r F

/-- Global polynomial syzygies cost the degree of the full affine Adams equation. -/
theorem minPrime_pow_le_length_stepanov_syzygies (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    {m : ℕ} (f g : Fin m → MvPolynomial P ℤ)
    (hsy : ∀ L : List P, L.length < r → stepanovWordMoment L f g = 0)
    (hne : stepanovAux q f g ≠ 0) :
    ((p : Nat.Primes) : ℕ) ^ (q * r) ≤ length (stepanovAux q f g) := by
  letI : NeZero q := ⟨by omega⟩
  apply minPrime_pow_le_length_of_mem_monicGridIdeal_pow q
    (fun p => X p ^ q - X p) (arithmeticMonicAt_adamsFixed q hq) r p hmin _ hne
  exact (mem_adamsFixedIdeal_pow_iff_stepanov_syzygies q r _).mpr ⟨m, f, g, hsy, rfl⟩

/-- At minimal arithmetic length every polynomial syzygy construction uses one least-prime equation. -/
theorem minimal_stepanov_syzygies_eq (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    {m : ℕ} (f g : Fin m → MvPolynomial P ℤ)
    (hsy : ∀ L : List P, L.length < r → stepanovWordMoment L f g = 0)
    (hlen : length (stepanovAux q f g) ≤ ((p : Nat.Primes) : ℕ) ^ (q * r)) :
    ∃ c : ℤ, stepanovAux q f g = C c * (X p ^ q - X p) ^ r := by
  letI : NeZero q := ⟨by omega⟩
  apply minimal_monicGridIdeal_pow_eq q (fun p => X p ^ q - X p)
    (arithmeticMonicAt_adamsFixed q hq) r p hmin _ _ hlen
  exact (mem_adamsFixedIdeal_pow_iff_stepanov_syzygies q r _).mpr ⟨m, f, g, hsy, rfl⟩

#print axioms stepanov_syzygies_iff_adamsNewton_support
#print axioms minPrime_pow_le_length_stepanov_syzygies
#print axioms minimal_stepanov_syzygies_eq

/-- The entire first nonzero filtered piece consists of integer multiples of one equation power. -/
theorem minimal_stepanov_image_iff (q : ℕ) (hq : 2 ≤ q) (r : ℕ)
    (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) :
    ((∃ m, ∃ f g : Fin m → MvPolynomial P ℤ,
      (∀ L : List P, L.length < r → stepanovWordMoment L f g = 0) ∧
        stepanovAux q f g = F) ∧ length F ≤ ((p : Nat.Primes) : ℕ) ^ (q * r)) ↔
      ∃ c : ℤ, F = C c * (X p ^ q - X p) ^ r := by
  constructor
  · rintro ⟨⟨m, f, g, hsy, rfl⟩, hlen⟩
    exact minimal_stepanov_syzygies_eq q hq r p hmin f g hsy hlen
  · rintro ⟨c, rfl⟩
    constructor
    · apply (mem_adamsFixedIdeal_pow_iff_stepanov_syzygies q r _).mp
      apply Ideal.mul_mem_left
      have hg : ((X p : MvPolynomial P ℤ) ^ q - X p) ∈ adamsFixedIdeal q :=
        Ideal.subset_span ⟨p, rfl⟩
      exact Ideal.pow_mem_pow hg r
    · apply Finset.sup_le
      intro a ha
      have ha' : a ∈ (((X p : MvPolynomial P ℤ) ^ q - X p) ^ r).support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at ha
        exact MvPolynomial.mem_support_iff.mpr (mul_ne_zero_iff.mp ha).2
      have h := (arithmeticMonicAt_adamsFixed_pow q hq r p).2 a ha'
      rwa [weight_single] at h

/-- The lower bound is attained by an actual polynomial syzygy construction. -/
theorem exists_stepanov_syzygies_at_sharp_length (q : ℕ) (hq : 2 ≤ q) (r : ℕ) (p : P) :
    ∃ m, ∃ f g : Fin m → MvPolynomial P ℤ,
      (∀ L : List P, L.length < r → stepanovWordMoment L f g = 0) ∧
        stepanovAux q f g = (X p ^ q - X p) ^ r ∧
        stepanovAux q f g ≠ 0 ∧
        length (stepanovAux q f g) = ((p : Nat.Primes) : ℕ) ^ (q * r) := by
  letI : NeZero q := ⟨by omega⟩
  have hm := arithmeticMonicAt_adamsFixed_pow q hq r p
  have hg : ((X p : MvPolynomial P ℤ) ^ q - X p) ∈ adamsFixedIdeal q :=
    Ideal.subset_span ⟨p, rfl⟩
  have hi : ((X p : MvPolynomial P ℤ) ^ q - X p) ^ r ∈ adamsFixedIdeal q ^ r :=
    Ideal.pow_mem_pow hg r
  obtain ⟨m, f, g, hsy, he⟩ :=
    (mem_adamsFixedIdeal_pow_iff_stepanov_syzygies q r _).mp hi
  refine ⟨m, f, g, hsy, he, ?_, ?_⟩
  · rw [he]; exact hm.ne_zero
  · rw [he, hm.length, weight_single]

#print axioms exists_stepanov_syzygies_at_sharp_length
#print axioms minimal_stepanov_image_iff

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
