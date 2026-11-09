import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialQuotientFrequencies
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PolynomialOrbitPreserversAreAdams
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.EntireQuotientCharacters
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.SignedPrimeClockMultipliers

/-!
# Rational prime-orbit preservers are Laurent Adams maps

Every rational self-map defined on and preserving a finite prime orbit with
two distinct primes is an integer power map followed by a time translation.
Logarithmic residues remove genuine poles; order-one rigidity forces
characters; the finite prime-logarithm lattice forces an integer slope.
Polynomial cross-multiplication records the exact rational identities,
including common factors, negative exponents, uniqueness, and fixed points.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
variable {P : Finset Nat.Primes}

/-- A polynomial identity expressing the rational coordinate `p^(−ib)X_p^n`.
Positive and negative parts of the integer exponent clear all denominators. -/
def LaurentAdamsRelation (N D : P → MvPolynomial P ℂ) (n : ℤ) (b : ℝ) : Prop :=
  ∀ r : P, N r * translatedAdams (-n).toNat 0 r =
    D r * translatedAdams n.toNat b r

private theorem laurentAdams_phase_split (n : ℤ) (b t : ℝ) (r : P) :
    orbitPoint P ((n.toNat : ℝ) * t + b) r =
      orbitPoint P (((-n).toNat : ℝ) * t) r * orbitPoint P ((n : ℝ) * t + b) r := by
  have hn : (n.toNat : ℝ) - ((-n).toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast int_toNat_sub_neg_toNat n
  unfold orbitPoint
  rw [← phase_add]
  congr 1
  have hn' : (n.toNat : ℝ) = ((-n).toNat : ℝ) + (n : ℝ) := by linarith only [hn]
  rw [hn']
  ring

/-- The Laurent Adams identity is equivalent to its integer affine orbit clock. -/
theorem laurentAdamsRelation_iff_clock (N D : P → MvPolynomial P ℂ)
    (hD : ∀ t : ℝ, ∀ r : P, complexOrbitValue (D r) t ≠ 0) (n : ℤ) (b : ℝ) :
    LaurentAdamsRelation N D n b ↔ ∀ t : ℝ, ∀ r : P,
      complexOrbitValue (N r) t / complexOrbitValue (D r) t =
        orbitPoint P ((n : ℝ) * t + b) r := by
  constructor
  · intro h t r
    have he := congrArg (fun F => complexOrbitValue F t) (h r)
    rw [complexOrbitValue_mul, complexOrbitValue_mul,
      complexOrbitValue_translatedAdams, complexOrbitValue_translatedAdams, add_zero,
      laurentAdams_phase_split n b t r] at he
    apply (div_eq_iff (hD t r)).mpr
    have hne : orbitPoint P (((-n).toNat : ℝ) * t) r ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hne
    calc complexOrbitValue (N r) t * orbitPoint P (((-n).toNat : ℝ) * t) r =
        complexOrbitValue (D r) t *
          (orbitPoint P (((-n).toNat : ℝ) * t) r * orbitPoint P ((n : ℝ) * t + b) r) := he
      _ = _ := by ring
  · intro h r
    apply complexOrbitValue_injective
    funext t
    rw [complexOrbitValue_mul, complexOrbitValue_mul,
      complexOrbitValue_translatedAdams, complexOrbitValue_translatedAdams, add_zero,
      laurentAdams_phase_split n b t r]
    rw [(div_eq_iff (hD t r)).mp (h t r)]
    ring

/-- A defined Laurent Adams rational map has unique exponent and translation. -/
theorem laurentAdamsRelation_parameters_unique (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ)
    (hD : ∀ t : ℝ, ∀ r : P, complexOrbitValue (D r) t ≠ 0)
    {n m : ℤ} {b d : ℝ} (hn : LaurentAdamsRelation N D n b)
    (hm : LaurentAdamsRelation N D m d) : n = m ∧ b = d := by
  have hn' := (laurentAdamsRelation_iff_clock N D hD n b).mp hn
  have hm' := (laurentAdamsRelation_iff_clock N D hD m d).mp hm
  have he (t : ℝ) : (n : ℝ) * t + b = (m : ℝ) * t + d := by
    apply orbitPoint_injective p q hpq
    funext r
    exact (hn' t r).symm.trans (hm' t r)
  have hb : b = d := by simpa only [mul_zero, zero_add] using he 0
  have hn : (n : ℝ) = m := by
    have hh := he 1
    simp only [mul_one, hb] at hh
    exact add_right_cancel hh
  exact ⟨by exact_mod_cast hn, hb⟩

/-- Fixed points satisfy the exact affine clock equation. -/
theorem laurentAdamsRelation_fixed_iff (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ)
    (hD : ∀ t : ℝ, ∀ r : P, complexOrbitValue (D r) t ≠ 0)
    {n : ℤ} {b : ℝ} (h : LaurentAdamsRelation N D n b) (t : ℝ) :
    (∀ r : P, complexOrbitValue (N r) t / complexOrbitValue (D r) t = orbitPoint P t r) ↔
      ((n : ℝ) - 1) * t + b = 0 := by
  have hc := (laurentAdamsRelation_iff_clock N D hD n b).mp h
  simp only [hc]
  constructor
  · intro he
    have hh := orbitPoint_injective p q hpq (funext he)
    linarith only [hh]
  · intro he r
    have ht : (n : ℝ) * t + b = t := by linarith only [he]
    rw [ht]

/-- Polynomial quotients defined on the whole prime orbit and carrying it into itself. -/
def RationalPreservesPrimeOrbit (N D : P → MvPolynomial P ℂ) : Prop :=
  (∀ t : ℝ, ∀ r : P, complexOrbitValue (D r) t ≠ 0) ∧
    ∀ t : ℝ, ∃ u : ℝ, ∀ r : P,
      complexOrbitValue (N r) t / complexOrbitValue (D r) t = orbitPoint P u r

/-- Integer residues and order-one rigidity turn every rational orbit coordinate into a character. -/
theorem rational_preserver_coordinates_are_characters (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ) (hR : RationalPreservesPrimeOrbit N D) (r : P) :
    ∃ γ : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ t : ℝ,
      complexOrbitValue (N r) t = c * expChar γ t * complexOrbitValue (D r) t := by
  classical
  obtain ⟨s, hrs⟩ : ∃ s : P, r ≠ s := by
    by_cases hr : r = p
    · exact ⟨q, hr ▸ hpq⟩
    · exact ⟨p, hr⟩
  have hDr (t : ℝ) : entirePrimeOrbitValue (D r) t ≠ 0 := by
    rw [entirePrimeOrbitValue_ofReal]
    exact hR.1 t r
  have hDs (t : ℝ) : entirePrimeOrbitValue (D s) t ≠ 0 := by
    rw [entirePrimeOrbitValue_ofReal]
    exact hR.1 t s
  have hclock (t : ℝ) : ∃ u : ℂ,
      entirePrimeOrbitValue (N r) t / entirePrimeOrbitValue (D r) t =
        Complex.exp ((Real.log ((r : Nat.Primes) : ℕ) : ℂ) * u) ∧
      entirePrimeOrbitValue (N s) t / entirePrimeOrbitValue (D s) t =
        Complex.exp ((Real.log ((s : Nat.Primes) : ℕ) : ℂ) * u) := by
    obtain ⟨u, hu⟩ := hR.2 t
    refine ⟨-(u : ℂ) * Complex.I, ?_, ?_⟩
    · rw [entirePrimeOrbitValue_ofReal, entirePrimeOrbitValue_ofReal, hu r]
      unfold orbitPoint InfiniteRankWeilTheory.phase
      congr 1
      push_cast
      ring
    · rw [entirePrimeOrbitValue_ofReal, entirePrimeOrbitValue_ofReal, hu s]
      unfold orbitPoint InfiniteRankWeilTheory.phase
      congr 1
      push_cast
      ring
  have horder (z : ℂ) : analyticOrderAt (entirePrimeOrbitValue (N r)) z =
      analyticOrderAt (entirePrimeOrbitValue (D r)) z :=
    (equal_divisors_of_common_exponential_clock
      (analyticOnNhd_entirePrimeOrbitValue (N r))
      (analyticOnNhd_entirePrimeOrbitValue (D r))
      (analyticOnNhd_entirePrimeOrbitValue (N s))
      (analyticOnNhd_entirePrimeOrbitValue (D s)) hDr hDs hclock
      (primeLog_int_relation r s hrs) z).1
  have hunit (t : ℝ) :
      ‖entirePrimeOrbitValue (N r) t / entirePrimeOrbitValue (D r) t‖ = 1 := by
    obtain ⟨u, hu⟩ := hR.2 t
    rw [entirePrimeOrbitValue_ofReal, entirePrimeOrbitValue_ofReal, hu r]
    exact InfiniteRankWeilTheory.norm_phase _ _
  obtain ⟨γ, c, hc, hfac⟩ := entire_quotient_eq_character
    (analyticOnNhd_entirePrimeOrbitValue (N r))
    (analyticOnNhd_entirePrimeOrbitValue (D r)) hDr horder
    (entirePrimeOrbitValue_proximity (N r)) (entirePrimeOrbitValue_proximity (D r)) hunit
  exact ⟨γ, c, hc, fun t => by simpa only [entirePrimeOrbitValue_ofReal] using hfac t⟩

/-- The clock of every rational prime-orbit preserver is an integer affine map. -/
theorem rational_preserver_integer_affine_clock (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ) (hR : RationalPreservesPrimeOrbit N D) :
    ∃ n : ℤ, ∃ b : ℝ, ∀ t : ℝ, ∀ r : P,
      complexOrbitValue (N r) t / complexOrbitValue (D r) t =
        orbitPoint P ((n : ℝ) * t + b) r := by
  classical
  choose γ c hc hfac using rational_preserver_coordinates_are_characters p q hpq N D hR
  have hc0 (r : P) : c r ≠ 0 := by
    intro hz
    have hh := hc r
    simp only [hz, norm_zero] at hh
    exact zero_ne_one hh
  have hD0 (r : P) : D r ≠ 0 := by
    intro hz
    have hh := hR.1 0 r
    simp only [hz, complexOrbitValue, map_zero, ne_eq, not_true_eq_false] at hh
  choose A B hAB using fun r => polynomial_quotient_character_frequency
    (N r) (D r) (c r) (γ r) (hc0 r) (hD0 r) (hfac r)
  obtain ⟨b, hb⟩ := hR.2 0
  have hcb (r : P) : c r = orbitPoint P b r := by
    have he : complexOrbitValue (N r) 0 / complexOrbitValue (D r) 0 = c r := by
      apply (div_eq_iff (hR.1 0 r)).mpr
      simpa only [expChar, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, mul_one] using hfac r 0
    exact he.symm.trans (hb r)
  choose u hu using hR.2
  have hnorm (t : ℝ) (r : P) : orbitPoint P (u t - b) r = expChar (γ r) t := by
    rw [orbitPoint, phase_sub]
    change orbitPoint P (u t) r / orbitPoint P b r = _
    rw [← hu t r, ← hcb r, hfac r t]
    field_simp [hR.1 t r, hc0 r]
  obtain ⟨a, hclock, hfreq⟩ := prime_character_clock_linear p q hpq
    (fun t => u t - b) γ hnorm
  let M : P → P → ℤ := fun r k => (B r k : ℤ) - A r k
  have hM (r : P) : ∑ k, (M r k : ℝ) * Real.log ((k : Nat.Primes) : ℕ) =
      a * Real.log ((r : Nat.Primes) : ℕ) := by
    simp only [M, Int.cast_sub, Int.cast_natCast, sub_mul, sum_sub_distrib]
    change frequency (B r) - frequency (A r) = _
    linarith only [hAB r, hfreq r]
  obtain ⟨n, hn, _⟩ := prime_log_lattice_dilation_is_int p a M hM
  refine ⟨n, b, fun t r => ?_⟩
  have ht : u t = (n : ℝ) * t + b := by
    have hh := hclock t
    rw [hn] at hh
    linarith only [hh]
  rw [hu t r, ht]

/-- Rational prime-orbit preservers are exactly the translated Laurent Adams maps. -/
theorem rationalPreservesPrimeOrbit_iff (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ) :
    RationalPreservesPrimeOrbit N D ↔
      (∀ t : ℝ, ∀ r : P, complexOrbitValue (D r) t ≠ 0) ∧
        ∃ n : ℤ, ∃ b : ℝ, LaurentAdamsRelation N D n b := by
  constructor
  · intro hR
    obtain ⟨n, b, hc⟩ := rational_preserver_integer_affine_clock p q hpq N D hR
    exact ⟨hR.1, n, b, (laurentAdamsRelation_iff_clock N D hR.1 n b).mpr hc⟩
  · rintro ⟨hD, n, b, h⟩
    refine ⟨hD, fun t => ⟨(n : ℝ) * t + b, ?_⟩⟩
    exact (laurentAdamsRelation_iff_clock N D hD n b).mp h t

/-- Every integer exponent, including time reversal, occurs in the rational category. -/
theorem rationalPreservesPrimeOrbit_laurentAdams (n : ℤ) (b : ℝ) :
    RationalPreservesPrimeOrbit (translatedAdams (P := P) n.toNat b)
      (translatedAdams (-n).toNat 0) := by
  have hD (t : ℝ) (r : P) :
      complexOrbitValue (translatedAdams (-n).toNat 0 r) t ≠ 0 := by
    rw [complexOrbitValue_translatedAdams]
    exact Complex.exp_ne_zero _
  have hrel : LaurentAdamsRelation (translatedAdams n.toNat b)
      (translatedAdams (-n).toNat 0) n b := fun r => mul_comm _ _
  exact ⟨hD, fun t => ⟨(n : ℝ) * t + b,
    (laurentAdamsRelation_iff_clock _ _ hD n b).mp hrel t⟩⟩

/-- A rational orbit preserver fixing two distinct orbit points is the identity rational map. -/
theorem rational_preserver_two_fixed_points (p q : P) (hpq : p ≠ q)
    (N D : P → MvPolynomial P ℂ) (hR : RationalPreservesPrimeOrbit N D)
    {t u : ℝ} (htu : t ≠ u)
    (ht : ∀ r : P, complexOrbitValue (N r) t / complexOrbitValue (D r) t = orbitPoint P t r)
    (hu : ∀ r : P, complexOrbitValue (N r) u / complexOrbitValue (D r) u = orbitPoint P u r) :
    ∀ r : P, N r = D r * MvPolynomial.X r := by
  obtain ⟨_, n, b, hrel⟩ := (rationalPreservesPrimeOrbit_iff p q hpq N D).mp hR
  have hte := (laurentAdamsRelation_fixed_iff p q hpq N D hR.1 hrel t).mp ht
  have hue := (laurentAdamsRelation_fixed_iff p q hpq N D hR.1 hrel u).mp hu
  have hm : ((n : ℝ) - 1) * (t - u) = 0 := by linear_combination hte - hue
  have hn : (n : ℝ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr htu))
  have hb : b = 0 := by simpa only [hn, sub_self, zero_mul, zero_add] using hte
  have hc := (laurentAdamsRelation_iff_clock N D hR.1 n b).mp hrel
  intro r
  apply complexOrbitValue_injective
  funext v
  rw [complexOrbitValue_mul]
  have he := hc v r
  rw [hn, hb, one_mul, add_zero] at he
  have hN := (div_eq_iff (hR.1 v r)).mp he
  simpa only [complexOrbitValue, MvPolynomial.eval_X, mul_comm] using hN

#print axioms laurentAdamsRelation_iff_clock
#print axioms laurentAdamsRelation_parameters_unique
#print axioms rational_preserver_integer_affine_clock
#print axioms rationalPreservesPrimeOrbit_iff
#print axioms rational_preserver_two_fixed_points

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
