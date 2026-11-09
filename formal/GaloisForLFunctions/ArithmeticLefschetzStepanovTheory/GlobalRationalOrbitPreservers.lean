import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.GlobalPrimeClockMultipliers
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.EntireQuotientCharacters

/-!
# Rational preservers of the full prime orbit

Every rational coordinate may use its own finite set of input primes.
Preservation of the full orbit nevertheless forces one translated integer
power map. Six exponentials supplies the missing algebraicity of the clock;
no common finite invariant prime set is assumed.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- A nonnegative integer power followed by translation of the full orbit. -/
def globalTranslatedAdams (n : ℕ) (b : ℝ) (p : Nat.Primes) :
    MvPolynomial Nat.Primes ℂ :=
  MvPolynomial.C (globalOrbitPoint b p) * MvPolynomial.X p ^ n

/-- The explicit polynomial family induces its affine clock. -/
theorem globalOrbitValue_globalTranslatedAdams (n : ℕ) (b t : ℝ) (p : Nat.Primes) :
    globalOrbitValue (globalTranslatedAdams n b p) t =
      globalOrbitPoint ((n : ℝ) * t + b) p := by
  simp only [globalOrbitValue, globalTranslatedAdams, map_mul, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  unfold globalOrbitPoint
  rw [phase_add, mul_comm]
  congr 1
  unfold InfiniteRankWeilTheory.phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A polynomial identity expressing the rational coordinate `p^(−ib)X_p^n`.
Positive and negative parts of the integer exponent clear all denominators. -/
def GlobalLaurentAdamsRelation (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) (n : ℤ) (b : ℝ) : Prop :=
  ∀ r : Nat.Primes, N r * globalTranslatedAdams (-n).toNat 0 r =
    D r * globalTranslatedAdams n.toNat b r

private theorem globalLaurentAdams_phase_split (n : ℤ) (b t : ℝ) (r : Nat.Primes) :
    globalOrbitPoint ((n.toNat : ℝ) * t + b) r =
      globalOrbitPoint (((-n).toNat : ℝ) * t) r * globalOrbitPoint ((n : ℝ) * t + b) r := by
  have hn : (n.toNat : ℝ) - ((-n).toNat : ℝ) = (n : ℝ) := by
    exact_mod_cast int_toNat_sub_neg_toNat n
  unfold globalOrbitPoint
  rw [← phase_add]
  congr 1
  have hn' : (n.toNat : ℝ) = ((-n).toNat : ℝ) + (n : ℝ) := by linarith only [hn]
  rw [hn']
  ring

/-- The Laurent Adams identity is equivalent to its integer affine orbit clock. -/
theorem globalLaurentAdamsRelation_iff_clock (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ)
    (hD : ∀ t : ℝ, ∀ r : Nat.Primes, globalOrbitValue (D r) t ≠ 0) (n : ℤ) (b : ℝ) :
    GlobalLaurentAdamsRelation N D n b ↔ ∀ t : ℝ, ∀ r : Nat.Primes,
      globalOrbitValue (N r) t / globalOrbitValue (D r) t =
        globalOrbitPoint ((n : ℝ) * t + b) r := by
  constructor
  · intro h t r
    have he := congrArg (fun F => globalOrbitValue F t) (h r)
    rw [globalOrbitValue_mul, globalOrbitValue_mul,
      globalOrbitValue_globalTranslatedAdams, globalOrbitValue_globalTranslatedAdams, add_zero,
      globalLaurentAdams_phase_split n b t r] at he
    apply (div_eq_iff (hD t r)).mpr
    have hne : globalOrbitPoint (((-n).toNat : ℝ) * t) r ≠ 0 := Complex.exp_ne_zero _
    apply mul_right_cancel₀ hne
    calc globalOrbitValue (N r) t * globalOrbitPoint (((-n).toNat : ℝ) * t) r =
        globalOrbitValue (D r) t *
          (globalOrbitPoint (((-n).toNat : ℝ) * t) r * globalOrbitPoint ((n : ℝ) * t + b) r) := he
      _ = _ := by ring
  · intro h r
    apply globalOrbitValue_injective
    funext t
    rw [globalOrbitValue_mul, globalOrbitValue_mul,
      globalOrbitValue_globalTranslatedAdams, globalOrbitValue_globalTranslatedAdams, add_zero,
      globalLaurentAdams_phase_split n b t r]
    rw [(div_eq_iff (hD t r)).mp (h t r)]
    ring

/-- A defined Laurent Adams rational map has unique exponent and translation. -/
theorem globalLaurentAdamsRelation_parameters_unique
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ)
    (hD : ∀ t : ℝ, ∀ r : Nat.Primes, globalOrbitValue (D r) t ≠ 0)
    {n m : ℤ} {b d : ℝ} (hn : GlobalLaurentAdamsRelation N D n b)
    (hm : GlobalLaurentAdamsRelation N D m d) : n = m ∧ b = d := by
  have hn' := (globalLaurentAdamsRelation_iff_clock N D hD n b).mp hn
  have hm' := (globalLaurentAdamsRelation_iff_clock N D hD m d).mp hm
  have he (t : ℝ) : (n : ℝ) * t + b = (m : ℝ) * t + d := by
    apply globalOrbitPoint_injective
    funext r
    exact (hn' t r).symm.trans (hm' t r)
  have hb : b = d := by simpa only [mul_zero, zero_add] using he 0
  have hn : (n : ℝ) = m := by
    have hh := he 1
    simp only [mul_one, hb] at hh
    exact add_right_cancel hh
  exact ⟨by exact_mod_cast hn, hb⟩

/-- Fixed points satisfy the exact affine clock equation. -/
theorem globalLaurentAdamsRelation_fixed_iff
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ)
    (hD : ∀ t : ℝ, ∀ r : Nat.Primes, globalOrbitValue (D r) t ≠ 0)
    {n : ℤ} {b : ℝ} (h : GlobalLaurentAdamsRelation N D n b) (t : ℝ) :
    (∀ r : Nat.Primes, globalOrbitValue (N r) t / globalOrbitValue (D r) t = globalOrbitPoint t r) ↔
      ((n : ℝ) - 1) * t + b = 0 := by
  have hc := (globalLaurentAdamsRelation_iff_clock N D hD n b).mp h
  simp only [hc]
  constructor
  · intro he
    have hh := globalOrbitPoint_injective (funext he)
    linarith only [hh]
  · intro he r
    have ht : (n : ℝ) * t + b = t := by linarith only [he]
    rw [ht]

/-- Polynomial quotients defined on the whole prime orbit and carrying it into itself. -/
def GlobalRationalPreservesPrimeOrbit (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) : Prop :=
  (∀ t : ℝ, ∀ r : Nat.Primes, globalOrbitValue (D r) t ≠ 0) ∧
    ∀ t : ℝ, ∃ u : ℝ, ∀ r : Nat.Primes,
      globalOrbitValue (N r) t / globalOrbitValue (D r) t = globalOrbitPoint u r

/-- Integer residues and order-one rigidity turn every rational orbit coordinate into a character. -/
theorem global_rational_preserver_coordinates_are_characters (p q : Nat.Primes) (hpq : p ≠ q)
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) (hR : GlobalRationalPreservesPrimeOrbit N D) (r : Nat.Primes) :
    ∃ γ : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ t : ℝ,
      globalOrbitValue (N r) t = c * expChar γ t * globalOrbitValue (D r) t := by
  classical
  obtain ⟨s, hrs⟩ : ∃ s : Nat.Primes, r ≠ s := by
    by_cases hr : r = p
    · exact ⟨q, hr ▸ hpq⟩
    · exact ⟨p, hr⟩
  have hDr (t : ℝ) : entireGlobalOrbitValue (D r) t ≠ 0 := by
    rw [entireGlobalOrbitValue_ofReal]
    exact hR.1 t r
  have hDs (t : ℝ) : entireGlobalOrbitValue (D s) t ≠ 0 := by
    rw [entireGlobalOrbitValue_ofReal]
    exact hR.1 t s
  have hclock (t : ℝ) : ∃ u : ℂ,
      entireGlobalOrbitValue (N r) t / entireGlobalOrbitValue (D r) t =
        Complex.exp ((Real.log (r : ℕ) : ℂ) * u) ∧
      entireGlobalOrbitValue (N s) t / entireGlobalOrbitValue (D s) t =
        Complex.exp ((Real.log (s : ℕ) : ℂ) * u) := by
    obtain ⟨u, hu⟩ := hR.2 t
    refine ⟨-(u : ℂ) * Complex.I, ?_, ?_⟩
    · rw [entireGlobalOrbitValue_ofReal, entireGlobalOrbitValue_ofReal, hu r]
      unfold globalOrbitPoint InfiniteRankWeilTheory.phase
      congr 1
      push_cast
      ring
    · rw [entireGlobalOrbitValue_ofReal, entireGlobalOrbitValue_ofReal, hu s]
      unfold globalOrbitPoint InfiniteRankWeilTheory.phase
      congr 1
      push_cast
      ring
  have horder (z : ℂ) : analyticOrderAt (entireGlobalOrbitValue (N r)) z =
      analyticOrderAt (entireGlobalOrbitValue (D r)) z :=
    (equal_divisors_of_common_exponential_clock
      (analyticOnNhd_entireGlobalOrbitValue (N r))
      (analyticOnNhd_entireGlobalOrbitValue (D r))
      (analyticOnNhd_entireGlobalOrbitValue (N s))
      (analyticOnNhd_entireGlobalOrbitValue (D s)) hDr hDs hclock
      (global_primeLog_int_relation r s hrs) z).1
  have hunit (t : ℝ) :
      ‖entireGlobalOrbitValue (N r) t / entireGlobalOrbitValue (D r) t‖ = 1 := by
    obtain ⟨u, hu⟩ := hR.2 t
    rw [entireGlobalOrbitValue_ofReal, entireGlobalOrbitValue_ofReal, hu r]
    exact InfiniteRankWeilTheory.norm_phase _ _
  obtain ⟨γ, c, hc, hfac⟩ := entire_quotient_eq_character
    (analyticOnNhd_entireGlobalOrbitValue (N r))
    (analyticOnNhd_entireGlobalOrbitValue (D r)) hDr horder
    (entireGlobalOrbitValue_proximity (N r)) (entireGlobalOrbitValue_proximity (D r)) hunit
  exact ⟨γ, c, hc, fun t => by simpa only [entireGlobalOrbitValue_ofReal] using hfac t⟩

/-- The clock of every rational prime-orbit preserver is an integer affine map. -/
theorem global_rational_preserver_integer_affine_clock
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) (hR : GlobalRationalPreservesPrimeOrbit N D) :
    ∃ n : ℤ, ∃ b : ℝ, ∀ t : ℝ, ∀ r : Nat.Primes,
      globalOrbitValue (N r) t / globalOrbitValue (D r) t =
        globalOrbitPoint ((n : ℝ) * t + b) r := by
  classical
  have h23 : (⟨2, Nat.prime_two⟩ : Nat.Primes) ≠ ⟨3, Nat.prime_three⟩ := by
    intro he
    have hn := congrArg Subtype.val he
    norm_num at hn
  choose γ c hc hfac using global_rational_preserver_coordinates_are_characters
    ⟨2, Nat.prime_two⟩ ⟨3, Nat.prime_three⟩ h23 N D hR
  have hc0 (r : Nat.Primes) : c r ≠ 0 := by
    intro hz
    have hh := hc r
    simp only [hz, norm_zero] at hh
    exact zero_ne_one hh
  have hD0 (r : Nat.Primes) : D r ≠ 0 := by
    intro hz
    have hh := hR.1 0 r
    simp only [hz, globalOrbitValue, map_zero, ne_eq, not_true_eq_false] at hh
  choose A B hAB using fun r => global_polynomial_quotient_character_frequency
    (N r) (D r) (c r) (γ r) (hc0 r) (hD0 r) (hfac r)
  obtain ⟨b, hb⟩ := hR.2 0
  have hcb (r : Nat.Primes) : c r = globalOrbitPoint b r := by
    have he : globalOrbitValue (N r) 0 / globalOrbitValue (D r) 0 = c r := by
      apply (div_eq_iff (hR.1 0 r)).mpr
      simpa only [expChar, Complex.ofReal_zero, mul_zero, zero_mul,
        Complex.exp_zero, mul_one] using hfac r 0
    exact he.symm.trans (hb r)
  choose u hu using hR.2
  have hnorm (t : ℝ) (r : Nat.Primes) : globalOrbitPoint (u t - b) r = expChar (γ r) t := by
    rw [globalOrbitPoint, phase_sub]
    change globalOrbitPoint (u t) r / globalOrbitPoint b r = _
    rw [← hu t r, ← hcb r, hfac r t]
    field_simp [hR.1 t r, hc0 r]
  obtain ⟨a, hclock, hfreq⟩ := global_prime_character_clock_linear
    (fun t => u t - b) γ hnorm
  have hfrequency (r : Nat.Primes) :
      a * Real.log (r : ℕ) = globalFrequency (B r) - globalFrequency (A r) := by
    linarith only [hAB r, hfreq r]
  obtain ⟨n, hn⟩ := global_prime_frequency_dilation_is_int a
    (fun r => ⟨B r, A r, hfrequency r⟩)
  refine ⟨n, b, fun t r => ?_⟩
  have ht : u t = (n : ℝ) * t + b := by
    have hh := hclock t
    rw [hn] at hh
    linarith only [hh]
  rw [hu t r, ht]

/-- Rational prime-orbit preservers are exactly the translated Laurent Adams maps. -/
theorem globalRationalPreservesPrimeOrbit_iff
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) :
    GlobalRationalPreservesPrimeOrbit N D ↔
      (∀ t : ℝ, ∀ r : Nat.Primes, globalOrbitValue (D r) t ≠ 0) ∧
        ∃ n : ℤ, ∃ b : ℝ, GlobalLaurentAdamsRelation N D n b := by
  constructor
  · intro hR
    obtain ⟨n, b, hc⟩ := global_rational_preserver_integer_affine_clock N D hR
    exact ⟨hR.1, n, b, (globalLaurentAdamsRelation_iff_clock N D hR.1 n b).mpr hc⟩
  · rintro ⟨hD, n, b, h⟩
    refine ⟨hD, fun t => ⟨(n : ℝ) * t + b, ?_⟩⟩
    exact (globalLaurentAdamsRelation_iff_clock N D hD n b).mp h t

/-- Every integer exponent, including time reversal, occurs in the rational category. -/
theorem globalRationalPreservesPrimeOrbit_laurentAdams (n : ℤ) (b : ℝ) :
    GlobalRationalPreservesPrimeOrbit (globalTranslatedAdams n.toNat b)
      (globalTranslatedAdams (-n).toNat 0) := by
  have hD (t : ℝ) (r : Nat.Primes) :
      globalOrbitValue (globalTranslatedAdams (-n).toNat 0 r) t ≠ 0 := by
    rw [globalOrbitValue_globalTranslatedAdams]
    exact Complex.exp_ne_zero _
  have hrel : GlobalLaurentAdamsRelation (globalTranslatedAdams n.toNat b)
      (globalTranslatedAdams (-n).toNat 0) n b := fun r => mul_comm _ _
  exact ⟨hD, fun t => ⟨(n : ℝ) * t + b,
    (globalLaurentAdamsRelation_iff_clock _ _ hD n b).mp hrel t⟩⟩

/-- A rational orbit preserver fixing two distinct orbit points is the identity rational map. -/
theorem global_rational_preserver_two_fixed_points
    (N D : Nat.Primes → MvPolynomial Nat.Primes ℂ) (hR : GlobalRationalPreservesPrimeOrbit N D)
    {t u : ℝ} (htu : t ≠ u)
    (ht : ∀ r : Nat.Primes, globalOrbitValue (N r) t / globalOrbitValue (D r) t = globalOrbitPoint t r)
    (hu : ∀ r : Nat.Primes, globalOrbitValue (N r) u / globalOrbitValue (D r) u = globalOrbitPoint u r) :
    ∀ r : Nat.Primes, N r = D r * MvPolynomial.X r := by
  obtain ⟨_, n, b, hrel⟩ := (globalRationalPreservesPrimeOrbit_iff N D).mp hR
  have hte := (globalLaurentAdamsRelation_fixed_iff N D hR.1 hrel t).mp ht
  have hue := (globalLaurentAdamsRelation_fixed_iff N D hR.1 hrel u).mp hu
  have hm : ((n : ℝ) - 1) * (t - u) = 0 := by linear_combination hte - hue
  have hn : (n : ℝ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr htu))
  have hb : b = 0 := by simpa only [hn, sub_self, zero_mul, zero_add] using hte
  have hc := (globalLaurentAdamsRelation_iff_clock N D hR.1 n b).mp hrel
  intro r
  apply globalOrbitValue_injective
  funext v
  rw [globalOrbitValue_mul]
  have he := hc v r
  rw [hn, hb, one_mul, add_zero] at he
  have hN := (div_eq_iff (hR.1 v r)).mp he
  simpa only [globalOrbitValue, MvPolynomial.eval_X, mul_comm] using hN

#print axioms globalLaurentAdamsRelation_iff_clock
#print axioms globalLaurentAdamsRelation_parameters_unique
#print axioms global_rational_preserver_integer_affine_clock
#print axioms globalRationalPreservesPrimeOrbit_iff
#print axioms globalRationalPreservesPrimeOrbit_laurentAdams
#print axioms global_rational_preserver_two_fixed_points

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
