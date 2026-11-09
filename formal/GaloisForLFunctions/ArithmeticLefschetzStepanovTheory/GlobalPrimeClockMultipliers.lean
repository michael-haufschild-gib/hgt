import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.SignedPrimeClockMultipliers
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PrimeOrbitClockRigidity
import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.GlobalPrimeOrbitPolynomials
import GaloisForLFunctions.RHTower.SixExponentials.PrimePowers

/-!
# Clocks on the full prime-frequency lattice

Three prime outputs and six exponentials force an algebraic clock slope.
Baker independence on one finite frequency support makes that slope an
integer, without any finite invariant prime set. Two output characters
determine the same linear clock on every prime coordinate.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- Algebraic powers at three distinct primes force an algebraic real exponent. -/
theorem algebraic_of_three_prime_exp {a : ℝ} {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hap : IsAlgebraic ℚ (Complex.exp ((a : ℂ) * (Real.log p : ℂ))))
    (haq : IsAlgebraic ℚ (Complex.exp ((a : ℂ) * (Real.log q : ℂ))))
    (har : IsAlgebraic ℚ (Complex.exp ((a : ℂ) * (Real.log r : ℂ)))) :
    IsAlgebraic ℤ a := by
  by_contra ha
  have hx : ∀ n m : ℤ, (n : ℂ) * 1 + (m : ℂ) * (a : ℂ) = 0 → n = 0 ∧ m = 0 := by
    intro n m h
    have hre : (n : ℝ) + (m : ℝ) * a = 0 := by
      simpa only [mul_one, Complex.add_re, Complex.mul_re, Complex.intCast_re,
        Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, Complex.zero_re] using congrArg Complex.re h
    have hm : m = 0 := by
      by_contra hm
      apply ha
      refine ⟨Polynomial.C m * Polynomial.X + Polynomial.C n, ?_, ?_⟩
      · intro hz
        apply hm
        have hcoeff := congrArg (fun f : Polynomial ℤ => f.coeff 1) hz
        simpa only [Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_C,
          Polynomial.coeff_zero, Nat.sub_self, Nat.one_ne_zero, ite_true, ite_false,
          add_zero] using hcoeff
      · simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        change (m : ℝ) * a + (n : ℝ) = 0
        linarith only [hre]
    refine ⟨?_, hm⟩
    have hn : (n : ℝ) = 0 := by
      simpa only [hm, Int.cast_zero, zero_mul, add_zero] using hre
    exact_mod_cast hn
  apply RHTower.SixExponentials.six_exponentials hx
    (RHTower.SixExponentials.prime_logs_independent hp hq hr hpq hpr hqr)
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, one_mul, Fin.mk_one,
    Fin.isValue, Fin.reduceFinMk]
  · rw [RHTower.SixExponentials.exp_log_nat hp.pos]; exact isAlgebraic_nat p
  · rw [RHTower.SixExponentials.exp_log_nat hq.pos]; exact isAlgebraic_nat q
  · rw [RHTower.SixExponentials.exp_log_nat hr.pos]; exact isAlgebraic_nat r
  · exact hap
  · exact haq
  · exact har

#print axioms algebraic_of_three_prime_exp

/-- A finite set containing the monomial support computes the same frequency. -/
theorem globalFrequency_eq_sum (α : Nat.Primes →₀ ℕ) (P : Finset Nat.Primes)
    (hα : α.support ⊆ P) :
    globalFrequency α = ∑ p : P, (α p : ℝ) * Real.log ((p : Nat.Primes) : ℕ) := by
  classical
  calc
    globalFrequency α = ∑ p ∈ P, (α p : ℝ) * Real.log (p : ℕ) :=
      Finsupp.sum_of_support_subset α hα
        (fun p n => (n : ℝ) * Real.log (p : ℕ)) (by intro p hp; simp)
    _ = ∑ p : P, (α p : ℝ) * Real.log ((p : Nat.Primes) : ℕ) :=
      (Finset.sum_coe_sort P (fun p : Nat.Primes =>
        (α p : ℝ) * Real.log (p : ℕ))).symm

/-- One algebraic multiple of a prime logarithm in the signed prime-frequency
lattice already has an integer multiplier. -/
theorem global_frequency_algebraic_multiple (p : Nat.Primes) (a : ℝ)
    (ha : IsAlgebraic ℤ a) (α β : Nat.Primes →₀ ℕ)
    (h : globalFrequency α - globalFrequency β = a * Real.log (p : ℕ)) :
    ∃ n : ℤ, a = n := by
  classical
  let P : Finset Nat.Primes := insert p (α.support ∪ β.support)
  let pP : P := ⟨p, mem_insert_self _ _⟩
  have hα : α.support ⊆ P := fun q hq => mem_insert_of_mem (mem_union_left _ hq)
  have hβ : β.support ⊆ P := fun q hq => mem_insert_of_mem (mem_union_right _ hq)
  let c : P → ℝ := fun q => (α q : ℝ) - (β q : ℝ) - if q = pP then a else 0
  have hc (q : P) : IsAlgebraic ℤ (c q) := by
    apply ((isAlgebraic_nat (α q)).sub (isAlgebraic_nat (β q))).sub
    split_ifs
    · exact ha
    · exact isAlgebraic_zero
  have hrel : ∑ q, c q * Real.log ((q : Nat.Primes) : ℕ) = 0 := by
    simp only [c, sub_mul, sum_sub_distrib, ite_mul, zero_mul,
      sum_ite_eq', mem_univ, if_true]
    rw [← globalFrequency_eq_sum α P hα, ← globalFrequency_eq_sum β P hβ]
    exact sub_eq_zero.mpr h
  have hp := primeLog_algebraic_relation c hc hrel pP
  have he : a = (α p : ℝ) - (β p : ℝ) := by
    have hpeq : (α p : ℝ) - (β p : ℝ) - a = 0 := by
      simpa only [c, pP, if_true] using hp
    linarith only [hpeq]
  refine ⟨(α p : ℤ) - (β p : ℤ), ?_⟩
  simpa only [Int.cast_sub, Int.cast_natCast] using he

/-- Preserving the full signed prime-frequency lattice forces an integer scalar,
even when no finite invariant prime set exists. -/
theorem global_prime_frequency_dilation_is_int (a : ℝ)
    (h : ∀ p : Nat.Primes, ∃ α β : Nat.Primes →₀ ℕ,
      a * Real.log (p : ℕ) = globalFrequency α - globalFrequency β) :
    ∃ n : ℤ, a = n := by
  have halg (p : Nat.Primes) :
      IsAlgebraic ℚ (Complex.exp ((a : ℂ) * (Real.log (p : ℕ) : ℂ))) := by
    obtain ⟨α, β, hαβ⟩ := h p
    let q : ℚ := (primeProduct α : ℚ) / (primeProduct β : ℚ)
    have he : Complex.exp ((a : ℂ) * (Real.log (p : ℕ) : ℂ)) = (q : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, hαβ,
        Real.exp_sub, exp_globalFrequency, exp_globalFrequency]
      simp only [q, Complex.ofReal_div, Complex.ofReal_natCast,
        Rat.cast_div, Rat.cast_natCast]
    rw [he]
    exact isAlgebraic_rat ℚ q
  have ha : IsAlgebraic ℤ a := algebraic_of_three_prime_exp
    Nat.prime_two Nat.prime_three Nat.prime_five
    (by norm_num) (by norm_num) (by norm_num)
    (halg ⟨2, Nat.prime_two⟩) (halg ⟨3, Nat.prime_three⟩) (halg ⟨5, Nat.prime_five⟩)
  obtain ⟨α, β, hαβ⟩ := h ⟨2, Nat.prime_two⟩
  exact global_frequency_algebraic_multiple ⟨2, Nat.prime_two⟩ a ha α β hαβ.symm

#print axioms global_frequency_algebraic_multiple
#print axioms global_prime_frequency_dilation_is_int

/-- The full prime orbit identifies its real parameter. -/
theorem globalOrbitPoint_injective : Function.Injective globalOrbitPoint := by
  intro s t h
  apply sub_eq_zero.mp
  apply InfiniteRankWeilTheory.eq_zero_of_exact_return Nat.prime_two Nat.prime_three (by norm_num)
  · rw [phase_sub, show InfiniteRankWeilTheory.phase 2 s =
      InfiniteRankWeilTheory.phase 2 t from congrFun h ⟨2, Nat.prime_two⟩]
    exact div_self (Complex.exp_ne_zero _)
  · rw [phase_sub, show InfiniteRankWeilTheory.phase 3 s =
      InfiniteRankWeilTheory.phase 3 t from congrFun h ⟨3, Nat.prime_three⟩]
    exact div_self (Complex.exp_ne_zero _)

/-- Integer residues at any two distinct output primes are independent. -/
theorem global_primeLog_int_relation (p q : Nat.Primes) (hpq : p ≠ q) (n m : ℤ)
    (h : (Real.log (q : ℕ) : ℂ) * (n : ℂ) =
      (Real.log (p : ℕ) : ℂ) * (m : ℂ)) : n = 0 ∧ m = 0 := by
  classical
  let P : Finset Nat.Primes := {p, q}
  let pP : P := ⟨p, by simp [P]⟩
  let qP : P := ⟨q, by simp [P]⟩
  exact primeLog_int_relation pP qP
    (fun he => hpq (congrArg Subtype.val he)) n m h

/-- Two output characters determine the clock; the same slope governs every prime. -/
theorem global_prime_character_clock_linear (τ : ℝ → ℝ) (γ : Nat.Primes → ℝ)
    (h : ∀ t p, globalOrbitPoint (τ t) p = expChar (γ p) t) :
    ∃ a : ℝ, (∀ t, τ t = a * t) ∧ ∀ p, γ p = -Real.log (p : ℕ) * a := by
  classical
  let P : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩}
  let pP : P := ⟨⟨2, Nat.prime_two⟩, by simp [P]⟩
  let qP : P := ⟨⟨3, Nat.prime_three⟩, by simp [P]⟩
  have hpq : pP ≠ qP := by
    intro he
    have hn := congrArg (fun r : P => ((r : Nat.Primes) : ℕ)) he
    norm_num [pP, qP] at hn
  obtain ⟨a, ha, _⟩ := prime_character_clock_linear pP qP hpq τ
    (fun r => γ r.val) (fun t r => h t r.val)
  let f : ℝ →+ ℝ :=
    { toFun := fun t => a * t
      map_zero' := mul_zero a
      map_add' := fun s t => mul_add a s t }
  refine ⟨a, ha, fun p => ?_⟩
  have hp := additive_character_clock f (-Real.log (p : ℕ)) (γ p)
    (fun t => by
      rw [← phase_eq_expChar]
      change globalOrbitPoint (a * t) p = _
      rw [← ha t]
      exact h t p) 1
  change -Real.log (p : ℕ) * (a * 1) = γ p * 1 at hp
  simpa only [mul_one] using hp.symm

#print axioms global_prime_character_clock_linear

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
