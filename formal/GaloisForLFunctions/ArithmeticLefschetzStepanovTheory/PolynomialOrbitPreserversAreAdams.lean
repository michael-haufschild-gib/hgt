import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialUnitOrbit
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PrimeOrbitClockRigidity
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.FinitePrimeClockMultipliers

/-!
# Polynomial self-maps preserving the prime orbit

Orbit preservation forces translated Adams operations. The argument imposes
no regularity on the induced clock: finite spectra, divisibility, and the
finite prime-logarithm lattice determine it.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- A polynomial map sends every prime-orbit point to another point of that orbit. -/
def PreservesPrimeOrbit (F : P → MvPolynomial P ℂ) : Prop :=
  ∀ t : ℝ, ∃ u : ℝ, ∀ p : P, complexOrbitValue (F p) t = orbitPoint P u p

/-- An Adams operation followed by a real translation of the prime orbit. -/
def translatedAdams (n : ℕ) (b : ℝ) (p : P) : MvPolynomial P ℂ :=
  MvPolynomial.monomial (Finsupp.single p n) (orbitPoint P b p)

/-- The unit Adams exponent with zero translation is the identity map. -/
theorem translatedAdams_one_zero :
    translatedAdams (P := P) 1 0 = fun r => MvPolynomial.X r := by
  funext r
  simp only [translatedAdams, orbitPoint, InfiniteRankWeilTheory.phase,
    zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero,
    ← MvPolynomial.X_pow_eq_monomial, pow_one]

/-- Every polynomial orbit preserver is a translated Adams operation. -/
theorem preservesPrimeOrbit_eq_translatedAdams (p q : P) (hpq : p ≠ q)
    (F : P → MvPolynomial P ℂ) (hF : PreservesPrimeOrbit F) :
    ∃ n : ℕ, ∃ b : ℝ, F = translatedAdams n b := by
  classical
  have hunit (r : P) (t : ℝ) : ‖complexOrbitValue (F r) t‖ = 1 := by
    obtain ⟨u, hu⟩ := hF t
    rw [hu r]
    exact InfiniteRankWeilTheory.norm_phase _ _
  choose A c hc hmon using fun r => complexOrbitValue_unit_monomial (F r) (hunit r)
  obtain ⟨b, hb⟩ := hF 0
  have hcb (r : P) : c r = orbitPoint P b r := by
    have hr := hb r
    rw [hmon r, complexOrbitValue_monomial] at hr
    simpa only [expChar, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one] using hr
  choose u hu using hF
  have hnorm (t : ℝ) (r : P) :
      orbitPoint P (u t - b) r = expChar (-frequency (A r)) t := by
    rw [orbitPoint, phase_sub]
    change orbitPoint P (u t) r / orbitPoint P b r = _
    rw [← hu t r, hmon r, complexOrbitValue_monomial, ← hcb r]
    have hc0 : c r ≠ 0 := by intro hz; have := hc r; simp [hz] at this
    field_simp
  obtain ⟨a, hclock, hfreq⟩ := prime_character_clock_linear p q hpq
    (fun t => u t - b) (fun r => -frequency (A r)) hnorm
  have hA (r : P) : frequency (A r) = a * Real.log ((r : Nat.Primes) : ℕ) := by
    have hr := hfreq r
    linarith only [hr]
  obtain ⟨n, hn, hAn⟩ := prime_frequency_dilation_is_nat p a A hA
  refine ⟨n, b, funext fun r => ?_⟩
  rw [hmon r, hAn r, hcb r]
  rfl

/-- Translated Adams operations induce exactly the affine clock `t ↦ nt+b`. -/
theorem complexOrbitValue_translatedAdams (n : ℕ) (b t : ℝ) (r : P) :
    complexOrbitValue (translatedAdams n b r) t =
      orbitPoint P ((n : ℝ) * t + b) r := by
  rw [translatedAdams, complexOrbitValue_monomial, frequency_single]
  unfold orbitPoint
  rw [phase_add, mul_comm]
  congr 1
  rw [phase_eq_expChar]
  unfold expChar
  congr 1
  push_cast
  ring

/-- The classification includes every polynomial self-map, with no assumed clock regularity. -/
theorem preservesPrimeOrbit_iff (p q : P) (hpq : p ≠ q)
    (F : P → MvPolynomial P ℂ) :
    PreservesPrimeOrbit F ↔ ∃ n : ℕ, ∃ b : ℝ, F = translatedAdams n b := by
  refine ⟨preservesPrimeOrbit_eq_translatedAdams p q hpq F, ?_⟩
  rintro ⟨n, b, rfl⟩ t
  exact ⟨(n : ℝ) * t + b, fun r => complexOrbitValue_translatedAdams n b t r⟩

/-- The Adams exponent and time translation are uniquely determined. -/
theorem translatedAdams_eq_iff (p q : P) (hpq : p ≠ q)
    (n m : ℕ) (b d : ℝ) :
    translatedAdams (P := P) n b = translatedAdams m d ↔ n = m ∧ b = d := by
  constructor
  · intro h
    have he (t : ℝ) : (n : ℝ) * t + b = (m : ℝ) * t + d := by
      apply orbitPoint_injective p q hpq
      funext r
      rw [← complexOrbitValue_translatedAdams, ← complexOrbitValue_translatedAdams, h]
    have hb : b = d := by simpa only [mul_zero, zero_add] using he 0
    have hn : (n : ℝ) = m := by
      have h1 := he 1
      simp only [mul_one, hb] at h1
      exact add_right_cancel h1
    exact ⟨by exact_mod_cast hn, hb⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Fixed prime-orbit points are exactly the fixed times of the affine clock. -/
theorem translatedAdams_fixed_iff (p q : P) (hpq : p ≠ q)
    (n : ℕ) (b t : ℝ) :
    (∀ r, complexOrbitValue (translatedAdams (P := P) n b r) t = orbitPoint P t r) ↔
      ((n : ℝ) - 1) * t + b = 0 := by
  simp only [complexOrbitValue_translatedAdams]
  constructor
  · intro h
    have he := orbitPoint_injective p q hpq (funext h)
    linarith only [he]
  · intro h r
    have he : (n : ℝ) * t + b = t := by linarith only [h]
    rw [he]

/-- A nontranslation has exactly one fixed orbit point. -/
theorem translatedAdams_fixed_iff_of_ne_one (p q : P) (hpq : p ≠ q)
    (n : ℕ) (hn : n ≠ 1) (b t : ℝ) :
    (∀ r, complexOrbitValue (translatedAdams (P := P) n b r) t = orbitPoint P t r) ↔
      t = -b / ((n : ℝ) - 1) := by
  rw [translatedAdams_fixed_iff p q hpq]
  have hn0 : (n : ℝ) - 1 ≠ 0 := by
    intro he
    apply hn
    exact_mod_cast sub_eq_zero.mp he
  rw [eq_div_iff hn0]
  constructor <;> intro h <;> linarith only [h]

/-- A time translation has a fixed orbit point exactly when it is the identity. -/
theorem translatedAdams_translation_fixed_iff (p q : P) (hpq : p ≠ q) (b t : ℝ) :
    (∀ r, complexOrbitValue (translatedAdams (P := P) 1 b r) t = orbitPoint P t r) ↔ b = 0 := by
  rw [translatedAdams_fixed_iff p q hpq]
  simp only [Nat.cast_one, sub_self, zero_mul, zero_add]

/-- A polynomial orbit preserver fixing two distinct orbit points is the identity. -/
theorem preservesPrimeOrbit_two_fixed_points (p q : P) (hpq : p ≠ q)
    (F : P → MvPolynomial P ℂ) (hF : PreservesPrimeOrbit F)
    (s t : ℝ) (hst : s ≠ t)
    (hs : ∀ r, complexOrbitValue (F r) s = orbitPoint P s r)
    (ht : ∀ r, complexOrbitValue (F r) t = orbitPoint P t r) :
    F = translatedAdams 1 0 := by
  obtain ⟨n, b, rfl⟩ := preservesPrimeOrbit_eq_translatedAdams p q hpq F hF
  have hse := (translatedAdams_fixed_iff p q hpq n b s).mp hs
  have hte := (translatedAdams_fixed_iff p q hpq n b t).mp ht
  have hprod : ((n : ℝ) - 1) * (s - t) = 0 := by
    calc
      _ = (((n : ℝ) - 1) * s + b) - (((n : ℝ) - 1) * t + b) := by ring
      _ = 0 := by rw [hse, hte, sub_self]
  have hn : (n : ℝ) = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hst))
  have hn' : n = 1 := by exact_mod_cast hn
  have hb : b = 0 := by simpa only [hn, sub_self, zero_mul, zero_add] using hse
  rw [hn', hb]

#print axioms preservesPrimeOrbit_iff
#print axioms preservesPrimeOrbit_two_fixed_points

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
