import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Substitution

/-! # Finite height bounds for integer dilations of evaluated shell rings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open MvPolynomial

/-- An integer-scaled inclusion iterates without ever taking roots of a shell. -/
theorem iterate_step {t : ℝ} {p q : ℕ} (h : kernel (t*p) ≤ kernel (t*q)) (n k : ℕ) :
    kernel (t*↑(p^n*k)) ≤ kernel (t*↑(q^n*k)) := by
  induction n generalizing k with
  | zero => simp only [pow_zero,one_mul,le_refl]
  | succ n ih =>
    have first := kernel_dilate h (p^n*k)
    have next := ih (q*k)
    have mid : t*q*↑(p^n*k)=t*↑(p^n*(q*k)) := by push_cast; ring
    rw [mid] at first
    simpa only [pow_succ,Nat.cast_mul,Nat.cast_pow,mul_assoc,mul_left_comm,mul_comm] using first.trans next

private theorem climb {R : Type*} [CommRing R] (J : ℕ → Ideal R)
    (prime : ∀ k, (J k).IsPrime) {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (step : ∀ k : ℕ, 0<k → J (p*k)<J (q*k)) (n k : ℕ) (hk : 0<k) :
    (J (p^n*k)).height+n ≤ (J (q^n*k)).height := by
  induction n generalizing k with
  | zero => simp only [Nat.cast_zero,add_zero,pow_zero,one_mul,le_refl]
  | succ n ih =>
    let j := p^n*k
    letI := prime (p*j)
    letI := prime (q*j)
    have one := Ideal.height_add_one_le_of_lt_of_isPrime (step j (mul_pos (pow_pos hp _) hk))
    have rest := ih (q*k) (mul_pos hq hk)
    rw [show p^n*(q*k)=q*j by dsimp only [j]; ring] at rest
    have full := (add_le_add_left one (n : ℕ∞)).trans (by simpa only [add_comm] using rest)
    simpa only [j,pow_succ,Nat.cast_succ,mul_assoc,mul_comm,mul_left_comm,add_assoc,add_comm,add_left_comm] using full

/-- In a polynomial ring on a finite set of labels there is no strict
specialization from p*k to q*k for every common dilation k. -/
theorem no_strict_dilations {ι : Type*} [Finite ι] (a : ι → ℕ+) (t : ℝ)
    {p q : ℕ} (hp : 0<p) (hq : 0<q) :
    ¬∀ k : ℕ, 0<k → sampledKernel a (t*↑(p*k)) < sampledKernel a (t*↑(q*k)) := by
  intro strict
  let J (k : ℕ) := sampledKernel a (t*k)
  have pr (k : ℕ) : (J k).IsPrime := RingHom.ker_isPrime _
  let D := 1+Nat.card ι
  let N := D+1
  have length := climb J pr hp hq strict N 1 zero_lt_one
  let I := J (q^N*1)
  letI : I.IsPrime := pr _
  have lower : (N : ℕ∞) ≤ I.height := le_trans le_add_self length
  have dimZ : ringKrullDim ℤ ≤ (1 : ℕ) := Ring.krullDimLE_iff.mp inferInstance
  have upper : ringKrullDim (MvPolynomial ι ℤ) ≤ (D : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
    simpa only [D,Nat.cast_add,Nat.cast_one] using add_le_add_left dimZ (Nat.card ι)
  have bound := (WithBot.coe_le_coe.mpr lower).trans (I.height_le_ringKrullDim_of_isPrime.trans upper)
  have impossible : N≤D := by exact_mod_cast bound
  exact (Nat.not_succ_le_self D) impossible

#print axioms iterate_step
#print axioms no_strict_dilations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
