import GaloisForLFunctions.HTGeometry.PrimeCompletionHypertranscendenceCollapse
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaSchemeChange
import GaloisForLFunctions.HTGeometry.GammaWeierstrass
import GaloisForLFunctions.HTGeometry.GammaReflectionRatioClock
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA

/-!
# Prime-occupation polarized Gamma-phase survival

The inverse-prime nome family enumerates the reciprocal positive integers.  Genus one removes its
divergent first occupation moment.  The resulting all-prime product is exactly a reciprocal-Gamma
Weierstrass factor.  Multiplying the two reflected orientations collapses to Euler's sine product,
whereas their quotient retains a hypertranscendental Gamma phase.

For a finite prime source, the genus-zero to genus-one scheme change is exactly the exponential of
the first occupation moment.  Thus the linear counterterm is not auxiliary normalization: it is the
finite-source reflection-odd anomaly whose all-prime unrenormalized limit diverges.

These are carrier and anomaly statements, not a zero-location theorem.
-/

open Complex Set Filter Topology
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher
open HTGeometry

noncomputable section

open scoped UnivMeroFieldInstances

/-! ## Reciprocal-integer occupation spectrum -/

/-- Prime nome at inverse-linear temperature. -/
def primeLinearNome (p : Nat.Primes) : ℂ :=
  (((p : ℕ) : ℂ)⁻¹)

theorem primeLinearNome_ne_zero (p : Nat.Primes) :
    primeLinearNome p ≠ 0 := by
  exact inv_ne_zero (by exact_mod_cast p.2.ne_zero)

theorem norm_primeLinearNome_lt_one (p : Nat.Primes) :
    ‖primeLinearNome p‖ < 1 := by
  rw [primeLinearNome, norm_inv, Complex.norm_natCast]
  exact (inv_lt_one₀ (by exact_mod_cast p.2.pos)).2
    (by exact_mod_cast p.2.one_lt)

/-- A prime-linear occupation monomial is the reciprocal of its represented positive integer. -/
theorem nomeMonomial_primeLinearNome (ν : Nat.Primes →₀ ℕ) :
    HTGeometry.nomeMonomial primeLinearNome ν =
      (((primeProduct ν : ℕ) : ℂ)⁻¹) := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
      simp [HTGeometry.nomeMonomial, primeLinearNome, primeProduct]
  | single_add a b f haf hb ih =>
      have hleft :
          HTGeometry.nomeMonomial primeLinearNome (Finsupp.single a b + f) =
            primeLinearNome a ^ b * HTGeometry.nomeMonomial primeLinearNome f := by
        unfold HTGeometry.nomeMonomial
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      have hprod :
          primeProduct (Finsupp.single a b + f) =
            (a : ℕ) ^ b * primeProduct f := by
        unfold primeProduct
        rw [Finsupp.prod_add_index']
        · rw [Finsupp.prod_single_index]
          simp
        · intro p
          simp
        · intro p k l
          rw [pow_add]
      rw [hleft, ih, hprod, Nat.cast_mul, Nat.cast_pow]
      simp only [primeLinearNome]
      field_simp
      ring

theorem primaryFactor_one_genus (z : ℂ) :
    HTGeometry.primaryFactor 1 z = (1 - z) * Complex.exp z := by
  simp [HTGeometry.primaryFactor, HTGeometry.primaryExponent]

/-- Genus-one all-prime occupation product. -/
def primeLinearCompletion (t : ℂ) : ℂ :=
  HTGeometry.infiniteMultipleEllipticGamma 1 primeLinearNome t

/-- Unique factorization turns the prime-occupation completion into the classical genus-one
Weierstrass product over the positive integers. -/
theorem primeLinearCompletion_eq_weierstrass (t : ℂ) :
    primeLinearCompletion t =
      ∏' n : ℕ,
        (1 - t / ((n : ℂ) + 1)) *
          Complex.exp (t / ((n : ℂ) + 1)) := by
  rw [primeLinearCompletion, HTGeometry.infiniteMultipleEllipticGamma,
    HTGeometry.canonicalWeightProduct]
  calc
    (∏' ν : Nat.Primes →₀ ℕ,
        HTGeometry.primaryFactor 1
          (t * HTGeometry.nomeMonomial primeLinearNome ν)) =
        ∏' n : ℕ+,
          HTGeometry.primaryFactor 1
            (t * HTGeometry.nomeMonomial primeLinearNome
              (primeOccupationEquivPNat.symm n)) := by
            exact (primeOccupationEquivPNat.symm.tprod_eq
              (fun ν : Nat.Primes →₀ ℕ =>
                HTGeometry.primaryFactor 1
                  (t * HTGeometry.nomeMonomial primeLinearNome ν))).symm
    _ = ∏' n : ℕ+,
        (1 - t / ((n : ℕ) : ℂ)) *
          Complex.exp (t / ((n : ℕ) : ℂ)) := by
          apply tprod_congr
          intro n
          rw [primaryFactor_one_genus, nomeMonomial_primeLinearNome]
          have hn :
              primeProduct (primeOccupationEquivPNat.symm n) = (n : ℕ) := by
            exact congrArg Subtype.val
              (primeOccupationEquivPNat.apply_symm_apply n)
          rw [hn]
          simp [div_eq_mul_inv]
    _ = ∏' n : ℕ,
        (1 - t / ((n : ℂ) + 1)) *
          Complex.exp (t / ((n : ℂ) + 1)) := by
          rw [tprod_pnat_eq_tprod_succ
            (f := fun n : ℕ =>
              (1 - t / (n : ℂ)) * Complex.exp (t / (n : ℂ)))]
          apply tprod_congr
          intro n
          norm_num

/-! ## Archimedean completion -/

/-- The all-prime genus-one completion is exactly the reciprocal-Gamma Weierstrass factor.
The identity is global, including positive integers where both sides vanish. -/
theorem primeLinearCompletion_eq_gamma (t : ℂ) :
    primeLinearCompletion t =
      Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
        (Complex.Gamma (1 - t))⁻¹ := by
  rw [primeLinearCompletion_eq_weierstrass]
  let W : ℂ :=
    ∏' n : ℕ,
      (1 - t / ((n : ℂ) + 1)) *
        Complex.exp (t / ((n : ℂ) + 1))
  change W = _
  by_cases hpole : ∃ m : ℕ, -t = -(m : ℂ)
  · obtain ⟨m, hm⟩ := hpole
    have ht : t = (m : ℂ) := neg_inj.mp hm
    cases m with
    | zero =>
        simp [W, ht]
    | succ m =>
        have hfactor :
            (1 - ((m + 1 : ℕ) : ℂ) / ((m : ℂ) + 1)) *
                Complex.exp (((m + 1 : ℕ) : ℂ) / ((m : ℂ) + 1)) = 0 := by
          have hm1 : (m : ℂ) + 1 ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero m
          field_simp
          push_cast
          ring
        have hW : W = 0 := by
          change
            (∏' n : ℕ,
              (1 - t / ((n : ℂ) + 1)) *
                Complex.exp (t / ((n : ℂ) + 1))) = 0
          rw [tprod_of_exists_eq_zero]
          exact ⟨m, by simpa [ht] using hfactor⟩
        rw [hW, ht]
        have harg :
            (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by
          push_cast
          ring
        rw [harg, Complex.Gamma_neg_nat_eq_zero]
        simp
  · have ht0 : t ≠ 0 := by
      intro ht
      apply hpole
      exact ⟨0, by simp [ht]⟩
    have hpole' : ∀ m : ℕ, -t ≠ -(m : ℂ) := by
      intro m hm
      exact hpole ⟨m, hm⟩
    have hW :=
      HilbertSchmidt.Gamma_inv_weierstrass (-t) hpole'
    have hW' :
        (Complex.Gamma (-t))⁻¹ =
          (-t) *
            Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * t)) * W := by
      simpa [W, neg_div] using! hW
    have hrec :
        (Complex.Gamma (-t))⁻¹ =
          (-t) * (Complex.Gamma (1 - t))⁻¹ := by
      simpa [sub_eq_add_neg, add_comm] using
        (Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (-t))
    have hcancel :
        Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * t)) * W =
          (Complex.Gamma (1 - t))⁻¹ := by
      apply mul_left_cancel₀ (neg_ne_zero.mpr ht0)
      calc
        (-t) *
              (Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * t)) * W) =
            (Complex.Gamma (-t))⁻¹ := by
              rw [hW']
              ring
        _ = (-t) * (Complex.Gamma (1 - t))⁻¹ := hrec
    calc
      W =
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
            (Complex.exp (-((Real.eulerMascheroniConstant : ℂ) * t)) * W) := by
              rw [← mul_assoc, ← Complex.exp_add]
              simp
      _ = Complex.exp ((Real.eulerMascheroniConstant : ℂ) * t) *
          (Complex.Gamma (1 - t))⁻¹ := by rw [hcancel]

/-! ## Exact reflected intensity collapse -/

/-- Reflection multiplication cancels every genus-one exponential counterterm factorwise and
leaves Euler's sine product. -/
theorem primeLinearCompletion_mul_reflection_mul_eq_sin (t : ℂ) :
    (Real.pi : ℂ) * t *
        (primeLinearCompletion t * primeLinearCompletion (-t)) =
      Complex.sin ((Real.pi : ℂ) * t) := by
  rw [primeLinearCompletion_eq_weierstrass,
    primeLinearCompletion_eq_weierstrass]
  let f : ℕ → ℂ := fun n =>
    (1 - t / ((n : ℂ) + 1)) *
      Complex.exp (t / ((n : ℂ) + 1))
  let g : ℕ → ℂ := fun n =>
    (1 - (-t) / ((n : ℂ) + 1)) *
      Complex.exp ((-t) / ((n : ℂ) + 1))
  have hf : Multipliable f := by
    simpa [f, neg_div] using!
      (HilbertSchmidt.multipliable_weierstrassFactor (-t))
  have hg : Multipliable g := by
    simpa [g, neg_div] using
      (HilbertSchmidt.multipliable_weierstrassFactor t)
  have hterm : (fun n => f n * g n) =
      (fun n : ℕ => (1 : ℂ) + sineTerm t n) := by
    funext n
    have hn : (n : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    calc
      f n * g n =
          ((1 - t / ((n : ℂ) + 1)) *
            (1 + t / ((n : ℂ) + 1))) *
          (Complex.exp (t / ((n : ℂ) + 1)) *
            Complex.exp (-(t / ((n : ℂ) + 1)))) := by
              simp only [f, g, neg_div, sub_neg_eq_add]
              ring
      _ = ((1 - t / ((n : ℂ) + 1)) *
            (1 + t / ((n : ℂ) + 1))) := by
              rw [← Complex.exp_add]
              simp
      _ = (1 : ℂ) + sineTerm t n := by
              simp only [sineTerm]
              field_simp
              ring
  change (Real.pi : ℂ) * t * ((∏' n, f n) * ∏' n, g n) = _
  rw [← hf.tprod_mul hg, hterm]
  by_cases ht : t = 0
  · subst t
    simp
  · have hmul : Multipliable
        (fun n : ℕ => (1 : ℂ) + sineTerm t n) :=
      multipliable_sineTerm t
    have hprod :
        (∏' n : ℕ, ((1 : ℂ) + sineTerm t n)) =
          Complex.sin ((Real.pi : ℂ) * t) /
            ((Real.pi : ℂ) * t) := by
      rw [← Multipliable.hasProd_iff hmul,
        Multipliable.hasProd_iff_tendsto_nat hmul]
      exact tendsto_euler_sin_prod' ht
    rw [hprod]
    field_simp [Real.pi_ne_zero, ht]

/-! ## Exact finite-source anomaly -/

/-- First occupation moment of a finite prime source. -/
def finitePrimeOccupationFirstMoment (S : Finset Nat.Primes) : ℂ :=
  ∑' ν : S →₀ ℕ,
    HTGeometry.nomeMonomial (fun p : S => primeLinearNome p) ν

/-- Raising the finite-source product from genus zero to genus one adds exactly the linear first
occupation moment and no higher counterterm. -/
theorem finitePrime_infiniteGenusCounterterm_zero_one
    (S : Finset Nat.Primes) (t : ℂ) :
    HTGeometry.infiniteGenusCounterterm
        0 1 (fun p : S => primeLinearNome p) t =
      t * finitePrimeOccupationFirstMoment S := by
  have hsum :
      Summable (fun p : S => ‖primeLinearNome p‖ ^ (0 + 1)) :=
    Summable.of_finite
  rw [HTGeometry.infiniteGenusCounterterm_eq_moment_sum
    (g := 0) (h := 1) (fun p : S => primeLinearNome p)
    (fun p => norm_primeLinearNome_lt_one p) hsum t]
  simp [finitePrimeOccupationFirstMoment]

/-- Exact finite-source renormalization law.  The exponential counterterm is the source's first
occupation moment. -/
theorem finitePrime_genusOne_eq_genusZero_mul_firstMomentGauge
    (S : Finset Nat.Primes) (t : ℂ) :
    HTGeometry.infiniteMultipleEllipticGamma
        1 (fun p : S => primeLinearNome p) t =
      HTGeometry.infiniteMultipleEllipticGamma
          0 (fun p : S => primeLinearNome p) t *
        Complex.exp (t * finitePrimeOccupationFirstMoment S) := by
  have hsum :
      Summable (fun p : S => ‖primeLinearNome p‖ ^ (0 + 1)) :=
    Summable.of_finite
  rw [HTGeometry.infiniteMultipleEllipticGamma_scheme_change
    (g := 0) (h := 1) (by omega)
    (fun p : S => primeLinearNome p)
    (fun p => primeLinearNome_ne_zero p)
    (fun p => norm_primeLinearNome_lt_one p) hsum t]
  rw [finitePrime_infiniteGenusCounterterm_zero_one]

/-- In the reflected quotient, finite-source genus renormalization is exactly twice the first
occupation moment.  This is the finite polarized anomaly before the all-prime limit. -/
theorem finitePrime_genusOne_polarized_eq_genusZero_polarized_mul_firstMomentGauge
    (S : Finset Nat.Primes) (t : ℂ) :
    HTGeometry.infiniteMultipleEllipticGamma
          1 (fun p : S => primeLinearNome p) t /
        HTGeometry.infiniteMultipleEllipticGamma
          1 (fun p : S => primeLinearNome p) (-t) =
      Complex.exp (2 * t * finitePrimeOccupationFirstMoment S) *
        (HTGeometry.infiniteMultipleEllipticGamma
            0 (fun p : S => primeLinearNome p) t /
          HTGeometry.infiniteMultipleEllipticGamma
            0 (fun p : S => primeLinearNome p) (-t)) := by
  rw [finitePrime_genusOne_eq_genusZero_mul_firstMomentGauge,
    finitePrime_genusOne_eq_genusZero_mul_firstMomentGauge]
  rw [show (-t) * finitePrimeOccupationFirstMoment S =
      -(t * finitePrimeOccupationFirstMoment S) by ring]
  rw [show 2 * t * finitePrimeOccupationFirstMoment S =
      2 * (t * finitePrimeOccupationFirstMoment S) by ring]
  let A : ℂ :=
    HTGeometry.infiniteMultipleEllipticGamma
      0 (fun p : S => primeLinearNome p) t
  let B : ℂ :=
    HTGeometry.infiniteMultipleEllipticGamma
      0 (fun p : S => primeLinearNome p) (-t)
  let x : ℂ := t * finitePrimeOccupationFirstMoment S
  change (A * Complex.exp x) / (B * Complex.exp (-x)) =
    Complex.exp (2 * x) * (A / B)
  calc
    (A * Complex.exp x) / (B * Complex.exp (-x)) =
        (Complex.exp x / Complex.exp (-x)) * (A / B) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
          ring
    _ = Complex.exp (2 * x) * (A / B) := by
      congr 1
      rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring

/-! ## Completed intensity and phase -/

/-- The polarized quotient of the two reflected genus-one occupation completions. -/
def primeOccupationPolarizedPhase (t : ℂ) : ℂ :=
  primeLinearCompletion t / primeLinearCompletion (-t)

/-- The reflected Gamma factors cannot both hit their non-positive-integer junk-zero sets. -/
theorem gamma_one_sub_one_add_ne_zero_or_ne_zero (t : ℂ) :
    Complex.Gamma (1 - t) ≠ 0 ∨ Complex.Gamma (1 + t) ≠ 0 := by
  by_cases hminus : Complex.Gamma (1 - t) = 0
  · right
    intro hplus
    obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff (1 - t)).mp hminus
    obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff (1 + t)).mp hplus
    have hsum : (2 : ℂ) = -((m : ℂ) + (n : ℂ)) := by
      linear_combination hm + hn
    have hre : (2 : ℝ) = -((m : ℝ) + (n : ℝ)) := by
      simpa using congrArg Complex.re hsum
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · exact Or.inl hminus

theorem inv_div_inv_eq_div_of_ne_zero_or_ne_zero
    (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) :
    a⁻¹ / b⁻¹ = b / a := by
  rcases h with ha | hb
  · by_cases hb0 : b = 0
    · simp [hb0]
    · field_simp
  · by_cases ha0 : a = 0
    · simp [ha0]
    · field_simp

/-- Exact value identity for the completed polarized quotient.  The even occupation sector has
collapsed to sine, but the odd sector is the Euler-Gamma reflection ratio with its unique linear
gauge restored. -/
theorem primeOccupationPolarizedPhase_eq_gammaRatio (t : ℂ) :
    primeOccupationPolarizedPhase t =
      Complex.exp
          (2 * (Real.eulerMascheroniConstant : ℂ) * t) *
        (Complex.Gamma (1 + t) / Complex.Gamma (1 - t)) := by
  rw [primeOccupationPolarizedPhase,
    primeLinearCompletion_eq_gamma,
    primeLinearCompletion_eq_gamma]
  simp only [sub_neg_eq_add]
  rw [show (Real.eulerMascheroniConstant : ℂ) * -t =
      -((Real.eulerMascheroniConstant : ℂ) * t) by ring]
  rw [show 2 * (Real.eulerMascheroniConstant : ℂ) * t =
      2 * ((Real.eulerMascheroniConstant : ℂ) * t) by ring]
  let x : ℂ := (Real.eulerMascheroniConstant : ℂ) * t
  let A : ℂ := Complex.Gamma (1 - t)
  let B : ℂ := Complex.Gamma (1 + t)
  change (Complex.exp x * A⁻¹) / (Complex.exp (-x) * B⁻¹) =
    Complex.exp (2 * x) * (B / A)
  calc
    (Complex.exp x * A⁻¹) / (Complex.exp (-x) * B⁻¹) =
        (Complex.exp x / Complex.exp (-x)) * (A⁻¹ / B⁻¹) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
          ring
    _ = Complex.exp (2 * x) * (B / A) := by
      rw [inv_div_inv_eq_div_of_ne_zero_or_ne_zero A B
        (by simpa [A, B] using gamma_one_sub_one_add_ne_zero_or_ne_zero t)]
      congr 1
      rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring

/-- Meromorphic Gamma-phase representative of the completed polarized quotient. -/
def primeOccupationPolarizedGammaPhaseMero : meroField Set.univ :=
  physicalExponentialMero
      (2 * (Real.eulerMascheroniConstant : ℂ)) *
    (gammaReflectionRatioMero 1)⁻¹

/-- The completed polarized Gamma phase remains hypertranscendental after the first-moment
counterterm is removed. -/
theorem hypertranscendentalOver_primeOccupationPolarizedGammaPhaseMero :
    HypertranscendentalOver (RatFunc ℂ)
      primeOccupationPolarizedGammaPhaseMero := by
  rw [primeOccupationPolarizedGammaPhaseMero, mul_comm]
  exact
    (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero
        (2 * (Real.eulerMascheroniConstant : ℂ)))
      (physicalExponentialMero_ne_zero
        (2 * (Real.eulerMascheroniConstant : ℂ)))).2
      (HTGeometry.hypertranscendentalOver_inv_iff.mpr
        (hypertranscendentalOver_gammaReflectionRatioMero 1))

end

end GaloisForLFunctions
