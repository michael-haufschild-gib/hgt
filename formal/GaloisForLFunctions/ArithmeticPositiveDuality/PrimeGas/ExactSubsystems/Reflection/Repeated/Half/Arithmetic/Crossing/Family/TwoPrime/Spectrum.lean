import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime.Blocks
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime.Signed
import GaloisForLFunctions.RHTower.MollifiedDeviationHeadFourthMoment

/-! # Realization of matched blocks by simple two-prime occupation spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime

open Finset Real

/-- Energy of the prime-gas shell with the two indicated occupations. -/
def mode (p q : Nat.Primes) (u : ℕ × ℕ) : ℝ :=
  energy ⟨p.val^u.1*q.val^u.2,mul_pos (pow_pos p.property.pos _) (pow_pos q.property.pos _)⟩

theorem mode_eq (p q : Nat.Primes) (u : ℕ × ℕ) :
    mode p q u=(u.1 : ℝ)*log (p.val : ℝ)+(u.2 : ℝ)*log (q.val : ℝ) := by
  change log (((p.val^u.1*q.val^u.2 : ℕ) : ℝ))=_
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,log_mul (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.property.ne_zero))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr q.property.ne_zero)),log_pow,log_pow]

theorem mode_injective (p q : Nat.Primes) (diff : p≠q) : Function.Injective (mode p q) := by
  intro x y eq
  change log (((p.val^x.1*q.val^x.2 : ℕ) : ℝ))=log (((p.val^y.1*q.val^y.2 : ℕ) : ℝ)) at eq
  have pos (z : ℕ × ℕ) : (0 : ℝ)< ((p.val^z.1*q.val^z.2 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (mul_pos (pow_pos p.property.pos _) (pow_pos q.property.pos _))
  have same : p.val^x.1*q.val^x.2=p.val^y.1*q.val^y.2 :=
    Nat.cast_injective (R := ℝ) (log_injOn_pos (pos x) (pos y) eq)
  obtain ⟨left,right⟩ := RHTower.exponents_eq_of_primePow_mul_eq p.property q.property
    (fun h => diff (Subtype.ext h)) same
  exact Prod.ext left right

def source (p q : Nat.Primes) {n : ℕ} (x : Cell n) := mode p q (first x,second x)

theorem source_pos (p q : Nat.Primes) {n : ℕ} (x : Cell n) : 0<source p q x := by
  have pp := log_pos (Nat.one_lt_cast.mpr p.property.one_lt)
  have qp := log_pos (Nat.one_lt_cast.mpr q.property.one_lt)
  rw [source,mode_eq]
  exact add_pos (mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ _)) pp)
    (mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ _)) qp)

theorem source_injective (p q : Nat.Primes) (diff : p≠q) {n : ℕ} : Function.Injective (@source p q n) := by
  intro x y eq
  have same := mode_injective p q diff eq
  exact Prod.ext (Fin.ext (Nat.add_right_cancel (congrArg Prod.fst same)))
    (Fin.ext (Nat.add_right_cancel (congrArg Prod.snd same)))

private theorem exp_source (p q : Nat.Primes) {n : ℕ} (x : Cell n) :
    exp (source p q x)=(direct p.val q.val x : ℝ) := by
  change exp (log (direct p.val q.val x : ℝ))=_
  exact exp_log (Nat.cast_pos.mpr (mul_pos (pow_pos p.property.pos _) (pow_pos q.property.pos _)))

/-- The complementary natural labels clear the denominators of all reciprocal moments. -/
theorem reciprocal_moment (p q : Nat.Primes) {n : ℕ} (x : Cell n) (h : ℕ) :
    exp (-(h : ℝ)*source p q x)=(reverse p.val q.val x : ℝ)^h / (((p.val*q.val)^n : ℕ) : ℝ)^h := by
  let a := direct p.val q.val x
  let b := reverse p.val q.val x
  let c := (p.val*q.val)^n
  have eq : (a : ℝ)*(b : ℝ)=(c : ℝ) := by exact_mod_cast complementary_product p.val q.val x
  have ap : 0 < (a : ℝ) := Nat.cast_pos.mpr (mul_pos (pow_pos p.property.pos _) (pow_pos q.property.pos _))
  have cp : 0 < (c : ℝ) := Nat.cast_pos.mpr (pow_pos (Nat.mul_pos p.property.pos q.property.pos) _)
  rw [neg_mul,exp_neg,exp_nat_mul,exp_source]
  change ((a : ℝ)^h)⁻¹=(b : ℝ)^h/(c : ℝ)^h
  have id := congrArg (fun u : ℝ => u^h) eq
  rw [mul_pow] at id
  field_simp
  linarith only [id]

theorem balanced_mean (p q : Nat.Primes) {n : ℕ} {A B : Finset (Cell n)}
    (h₁ : (∑ x ∈ A, first x)=∑ x ∈ B, first x) (h₂ : (∑ x ∈ A, second x)=∑ x ∈ B, second x) :
    (∑ x ∈ A, source p q x)=∑ x ∈ B, source p q x := by
  simp only [source,mode_eq,sum_add_distrib,← sum_mul,← Nat.cast_sum,h₁,h₂]

theorem balanced_reading (p q : Nat.Primes) {n : ℕ} {A B : Finset (Cell n)}
    (mean : (∑ x ∈ A, source p q x)=∑ x ∈ B, source p q x) (h : ℕ)
    (f : (∑ x ∈ A, (direct p.val q.val x)^h)=∑ x ∈ B, (direct p.val q.val x)^h)
    (g : (∑ x ∈ A, (reverse p.val q.val x)^h)=∑ x ∈ B, (reverse p.val q.val x)^h) :
    agrees (signedEnergy A B (source p q)) (h : ℝ) := by
  apply signed_agrees A B _ mean
  · simp only [exp_nat_mul,exp_source,← Nat.cast_pow,← Nat.cast_sum,f]
  · simp only [reciprocal_moment,← sum_div,← Nat.cast_pow,← Nat.cast_sum,g]

/-- Dilation clears rational probe orders. Translation places both reflected blocks
in the nonnegative occupation quadrant. -/
def occupations (D : ℕ) {n : ℕ} (A B : Finset (Cell n)) : States A B → ℕ × ℕ :=
  Sum.elim (fun x => (D*(n+first x.val),D*(n+second x.val)))
    (fun y => (D*(n-first y.val),D*(n-second y.val)))

theorem realized (p q : Nat.Primes) {n : ℕ} (A B : Finset (Cell n)) (D : ℕ) :
    mode p q ∘ occupations D A B = fun i =>
      (D : ℝ)*signedEnergy A B (source p q) i+(D : ℝ)*((n : ℝ)*log (p.val : ℝ)+(n : ℝ)*log (q.val : ℝ)) := by
  funext i
  cases i with
  | inl x =>
    simp only [Function.comp_apply,occupations,Sum.elim_inl,mode_eq,signedEnergy,source,Nat.cast_add,Nat.cast_mul]
    ring
  | inr y =>
    simp only [Function.comp_apply,occupations,Sum.elim_inr,mode_eq,signedEnergy,source,Nat.cast_sub (first_le y.val),
      Nat.cast_sub (second_le y.val),Nat.cast_mul]
    ring

#print axioms mode_injective
#print axioms reciprocal_moment
#print axioms balanced_reading
#print axioms realized

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.TwoPrime
