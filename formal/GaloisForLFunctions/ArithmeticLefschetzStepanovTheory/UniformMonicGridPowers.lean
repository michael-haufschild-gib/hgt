import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.ArithmeticMonicBases
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionMultiplicityLeadingExponents
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Integral powers of arithmetic monic grid ideals

Generators with arithmetic leading monomials `X_p^q` give integral Newton
coordinates. Multiplication by a generator shifts one quotient index;
ideal powers therefore correspond to total quotient order.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Newton polynomials for a family of monic grid equations of common degree. -/
def monicGridNewtonPolynomial (q : ℕ) (G : P → MvPolynomial P ℤ) (a : P →₀ ℕ) :
    MvPolynomial P ℤ := ∏ p : P, X p ^ (a p % q) * G p ^ (a p / q)

def monicGridIdeal (G : P → MvPolynomial P ℤ) : Ideal (MvPolynomial P ℤ) :=
  Ideal.span (Set.range G)

/-- The grid Newton family has exactly the prescribed arithmetic leading monomials. -/
theorem monicGridNewtonPolynomial_monic (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) (a : P →₀ ℕ) :
    ArithmeticMonicAt (monicGridNewtonPolynomial q G a) a := by
  have hp (p : P) : ArithmeticMonicAt (X p ^ (a p % q) * G p ^ (a p / q))
      (Finsupp.single p (a p)) := by
    have hm := (arithmeticMonicAt_monomial (Finsupp.single p (a p % q))).mul
      ((hG p).pow (a p / q))
    rw [← MvPolynomial.X_pow_eq_monomial] at hm
    have he : Finsupp.single p (a p % q) + (a p / q) • Finsupp.single p q =
        Finsupp.single p (a p) := by
      ext s
      by_cases hs : s = p
      · subst s
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.smul_apply, smul_eq_mul]
        simpa only [Nat.mul_comm] using Nat.mod_add_div (a p) q
      · simp [Finsupp.single_eq_of_ne hs]
    rwa [he] at hm
  have h := arithmeticMonicAt_prod univ _ _ (fun p _ => hp p)
  have he : (∑ p : P, Finsupp.single p (a p)) = a := by
    have hh := Finsupp.sum_fintype a (fun p n => Finsupp.single p n)
      (fun p => by simp only [Finsupp.single_zero])
    rw [Finsupp.sum_single] at hh
    exact hh.symm
  simpa only [monicGridNewtonPolynomial, he] using h

/-- Integral Newton coordinates for arithmetic monic grid equations. -/
def monicGridBasis (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) :
    Module.Basis (P →₀ ℕ) ℤ (MvPolynomial P ℤ) :=
  arithmeticMonicBasis (monicGridNewtonPolynomial q G) (monicGridNewtonPolynomial_monic q G hG)

theorem monicGridBasis_apply (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) (a : P →₀ ℕ) :
    monicGridBasis q G hG a = monicGridNewtonPolynomial q G a :=
  arithmeticMonicBasis_apply _ _

/-- The Newton span at quotient order at least `r`. -/
def monicGridSpan (q : ℕ) (G : P → MvPolynomial P ℤ) (r : ℕ) :
    Submodule ℤ (MvPolynomial P ℤ) :=
  Submodule.span ℤ (monicGridNewtonPolynomial q G '' {a | r ≤ torsionQuotientOrder q a})

/-- Every complete quotient block supplies a factor of the grid ideal. -/
theorem monicGridNewtonPolynomial_mem_ideal_pow (q r : ℕ) (G : P → MvPolynomial P ℤ)
    (a : P →₀ ℕ) (hr : r ≤ torsionQuotientOrder q a) :
    monicGridNewtonPolynomial q G a ∈ monicGridIdeal G ^ r := by
  classical
  have hfactor (p : P) : X p ^ (a p % q) * G p ^ (a p / q) ∈
      monicGridIdeal G ^ (a p / q) := by
    apply Ideal.mul_mem_left
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self p)) _
  have hprod (S : Finset P) :
      (∏ p ∈ S, X p ^ (a p % q) * G p ^ (a p / q)) ∈
        monicGridIdeal G ^ (∑ p ∈ S, a p / q) := by
    induction S using Finset.induction_on with
    | empty => simp only [prod_empty, sum_empty, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | @insert p S hp ih =>
      rw [prod_insert hp, sum_insert hp, pow_add]
      exact Ideal.mul_mem_mul (hfactor p) ih
  apply Ideal.pow_le_pow_right hr
  exact hprod univ

theorem monicGridNewtonPolynomial_shift (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (a : P →₀ ℕ) (p : P) :
    monicGridNewtonPolynomial q G (a + Finsupp.single p q) =
      monicGridNewtonPolynomial q G a * G p := by
  classical
  have hdiv : (a p + q) / q = a p / q + 1 := by
    simpa only [mul_one] using Nat.add_mul_div_left (a p) 1 (NeZero.pos q)
  have hmod : (a p + q) % q = a p % q := by
    simpa only [mul_one] using Nat.add_mul_mod_self_left (a p) q 1
  have hterm (s : P) : X s ^ ((a + Finsupp.single p q) s % q) *
      G s ^ ((a + Finsupp.single p q) s / q) =
      (X s ^ (a s % q) * G s ^ (a s / q)) * (if s = p then G p else 1) := by
    by_cases hs : s = p
    · subst s
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, hdiv, hmod, if_pos rfl,
        pow_succ, mul_assoc]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hs, add_zero, if_neg hs, mul_one]
  unfold monicGridNewtonPolynomial
  simp_rw [hterm]
  rw [prod_mul_distrib]
  simp

theorem torsionQuotientOrder_shift (q : ℕ) [NeZero q] (a : P →₀ ℕ) (p : P) :
    torsionQuotientOrder q (a + Finsupp.single p q) = torsionQuotientOrder q a + 1 := by
  classical
  have hdiv : (a p + q) / q = a p / q + 1 := by
    simpa only [mul_one] using Nat.add_mul_div_left (a p) 1 (NeZero.pos q)
  have hterm (s : P) : (a + Finsupp.single p q) s / q =
      a s / q + if s = p then 1 else 0 := by
    by_cases hs : s = p
    · subst s; simp only [Finsupp.add_apply, Finsupp.single_eq_same, hdiv, if_pos rfl]
    · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne hs, add_zero, if_neg hs]
  unfold torsionQuotientOrder
  simp_rw [hterm]
  rw [sum_add_distrib]
  simp

/-- Multiplication by one grid equation raises the Newton order by one. -/
theorem mul_generator_mem_monicGridSpan (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (r : ℕ) (F : MvPolynomial P ℤ) (hF : F ∈ monicGridSpan q G r) (p : P) :
    F * G p ∈ monicGridSpan q G (r + 1) := by
  classical
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨a, ha, rfl⟩ := hF
    rw [← monicGridNewtonPolynomial_shift]
    apply Submodule.subset_span
    exact ⟨a + Finsupp.single p q, by
      simpa only [Set.mem_setOf_eq, torsionQuotientOrder_shift, Nat.add_le_add_iff_right] using ha,
      rfl⟩
  | zero => simpa only [zero_mul] using (monicGridSpan q G (r + 1)).zero_mem
  | add F H hF hH ihF ihH =>
    simpa only [add_mul] using (monicGridSpan q G (r + 1)).add_mem ihF ihH
  | smul c F hF ih =>
    simpa only [smul_mul_assoc] using (monicGridSpan q G (r + 1)).smul_mem c ih

theorem mem_ideal_pow_of_mem_monicGridSpan (q r : ℕ) (G : P → MvPolynomial P ℤ)
    (F : MvPolynomial P ℤ) (hF : F ∈ monicGridSpan q G r) :
    F ∈ monicGridIdeal G ^ r := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨a, ha, rfl⟩ := hF
    exact monicGridNewtonPolynomial_mem_ideal_pow q r G a ha
  | zero => exact (monicGridIdeal G ^ r).zero_mem
  | add F H hF hH ihF ihH => exact (monicGridIdeal G ^ r).add_mem ihF ihH
  | smul c F hF ih => exact (monicGridIdeal G ^ r).smul_mem c ih

/-- Ideal powers retain precisely the Newton indices of sufficient quotient order. -/
theorem mem_monicGridIdeal_pow_iff (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) (r : ℕ)
    (F : MvPolynomial P ℤ) :
    F ∈ monicGridIdeal G ^ r ↔ F ∈ monicGridSpan q G r := by
  classical
  refine ⟨?_, mem_ideal_pow_of_mem_monicGridSpan q r G F⟩
  induction r generalizing F with
  | zero =>
    intro _
    obtain ⟨c, hc⟩ := arithmeticMonicSynthesis_surjective
      (monicGridNewtonPolynomial_monic q G hG) F
    rw [← hc, arithmeticMonicSynthesis_apply]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨a, Nat.zero_le _, rfl⟩
  | succ r ih =>
    intro hF
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF ?_ ?_
    · intro A hA B hB
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hB
      rw [Finset.mul_sum]
      apply Submodule.sum_mem
      intro p _
      rw [← mul_assoc]
      exact mul_generator_mem_monicGridSpan q G r (A * c p)
        (ih (A * c p) (Ideal.mul_mem_right (c p) _ hA)) p
    · intro A B hA hB
      exact (monicGridSpan q G (r + 1)).add_mem hA hB

theorem mem_monicGridIdeal_pow_iff_repr (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) (r : ℕ)
    (F : MvPolynomial P ℤ) :
    F ∈ monicGridIdeal G ^ r ↔
      ∀ a ∈ ((monicGridBasis q G hG).repr F).support, r ≤ torsionQuotientOrder q a := by
  rw [mem_monicGridIdeal_pow_iff q G hG]
  have he : monicGridNewtonPolynomial q G = monicGridBasis q G hG :=
    funext fun a => (monicGridBasis_apply q G hG a).symm
  rw [monicGridSpan, he, Module.Basis.mem_span_image]
  rfl

theorem monicGridBasis_repr_length (q : ℕ) [NeZero q] (G : P → MvPolynomial P ℤ)
    (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q)) (F : MvPolynomial P ℤ) :
    ((monicGridBasis q G hG).repr F).support.sup weight = length F :=
  arithmeticMonicBasis_repr_length _ F

#print axioms mem_monicGridIdeal_pow_iff_repr
#print axioms monicGridBasis_repr_length

theorem monicGridNewtonPolynomial_zero (q : ℕ) (G : P → MvPolynomial P ℤ) :
    monicGridNewtonPolynomial q G 0 = 1 := by simp [monicGridNewtonPolynomial]

theorem monicGridNewtonPolynomial_single_mul (q r : ℕ) [NeZero q]
    (G : P → MvPolynomial P ℤ) (p : P) :
    monicGridNewtonPolynomial q G (Finsupp.single p (q * r)) = G p ^ r := by
  induction r with
  | zero => simp only [mul_zero, Finsupp.single_zero, monicGridNewtonPolynomial_zero, pow_zero]
  | succ r ih =>
    have he : Finsupp.single p (q * (r + 1)) = Finsupp.single p (q * r) + Finsupp.single p q := by
      ext s
      by_cases hs : s = p
      · subst s; simp only [Finsupp.single_eq_same, Finsupp.add_apply, Nat.mul_succ]
      · simp [Finsupp.single_eq_of_ne hs]
    rw [he, monicGridNewtonPolynomial_shift, ih, pow_succ]

/-- The least allowed prime gives the exact first possible length in an ideal power. -/
theorem minPrime_pow_le_length_of_mem_monicGridIdeal_pow (q : ℕ) [NeZero q]
    (G : P → MvPolynomial P ℤ) (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q))
    (r : ℕ) (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) (hF : F ≠ 0) (hmem : F ∈ monicGridIdeal G ^ r) :
    ((p : Nat.Primes) : ℕ) ^ (q * r) ≤ length F := by
  classical
  let b := monicGridBasis q G hG
  have hc : b.repr F ≠ 0 := by
    intro hz
    apply hF
    apply b.repr.injective
    simpa only [map_zero] using hz
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hc
  have hr := (mem_monicGridIdeal_pow_iff_repr q G hG r F).mp hmem a ha
  calc
    _ ≤ ((p : Nat.Primes) : ℕ) ^ (q * torsionQuotientOrder q a) :=
      Nat.pow_le_pow_right (p : Nat.Primes).2.pos (Nat.mul_le_mul_left q hr)
    _ ≤ weight a := minPrime_pow_quotientOrder_le_weight q p hmin a
    _ ≤ (b.repr F).support.sup weight := le_sup ha
    _ = length F := monicGridBasis_repr_length q G hG F

/-- At the first possible length, a grid-ideal power is generated by the least-prime equation. -/
theorem minimal_monicGridIdeal_pow_eq (q : ℕ) [NeZero q]
    (G : P → MvPolynomial P ℤ) (hG : ∀ p, ArithmeticMonicAt (G p) (Finsupp.single p q))
    (r : ℕ) (p : P) (hmin : ∀ s : P, ((p : Nat.Primes) : ℕ) ≤ ((s : Nat.Primes) : ℕ))
    (F : MvPolynomial P ℤ) (hmem : F ∈ monicGridIdeal G ^ r)
    (hlen : length F ≤ ((p : Nat.Primes) : ℕ) ^ (q * r)) :
    ∃ c : ℤ, F = C c * G p ^ r := by
  classical
  let b := monicGridBasis q G hG
  let a₀ : P →₀ ℕ := Finsupp.single p (q * r)
  have hs : ∀ a ∈ (b.repr F).support, a = a₀ := by
    intro a ha
    have hr := (mem_monicGridIdeal_pow_iff_repr q G hG r F).mp hmem a ha
    have hlow : ((p : Nat.Primes) : ℕ) ^ (q * r) ≤ weight a :=
      (Nat.pow_le_pow_right (p : Nat.Primes).2.pos (Nat.mul_le_mul_left q hr)).trans
        (minPrime_pow_quotientOrder_le_weight q p hmin a)
    have hu : weight a ≤ length F := by
      rw [← monicGridBasis_repr_length q G hG F]
      exact le_sup ha
    apply weight_injective
    rw [weight_single]
    exact le_antisymm (hu.trans hlen) hlow
  have hc : b.repr F = Finsupp.single a₀ (b.repr F a₀) := by
    ext a
    by_cases ha : a = a₀
    · subst a; rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne ha]
      exact Finsupp.notMem_support_iff.mp (fun hm => ha (hs a hm))
  refine ⟨b.repr F a₀, ?_⟩
  have he := arithmeticMonicSynthesis_repr (monicGridNewtonPolynomial_monic q G hG) F
  change arithmeticMonicSynthesis (monicGridNewtonPolynomial q G) (b.repr F) = F at he
  rw [hc, arithmeticMonicSynthesis_single] at he
  rw [← he]
  change (b.repr F a₀) • monicGridNewtonPolynomial q G (Finsupp.single p (q * r)) = _
  rw [monicGridNewtonPolynomial_single_mul, MvPolynomial.smul_eq_C_mul]

#print axioms minimal_monicGridIdeal_pow_eq

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
