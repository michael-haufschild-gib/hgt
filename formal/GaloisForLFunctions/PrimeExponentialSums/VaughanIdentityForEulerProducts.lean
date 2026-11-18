import GaloisForLFunctions.HTGeometry.OperatorTailDirichletMatroid
import GaloisForLFunctions.RHTower.Sieve.HeathBrownFinitePacket
import GaloisForLFunctions.RHTower.SelbergPairingPrimeSquare

/-!
# Coefficients and signs in the automorphic Vaughan identity

Section 1.1 of arXiv:2610.18928 splits a logarithmic derivative at two
independent cutoffs. The Dirichlet-series identity gives a positive log-weighted
term and the residual factor `1 − F B`. Reversing both signs, as in its
coefficient formula (1.1), negates every coefficient when the first cutoff is one.
-/

noncomputable section
open ArithmeticFunction GaloisForLFunctions.HTGeometry RHTower.Sieve

namespace GaloisForLFunctions.PrimeExponentialSums.Vaughan

abbrev Coeff := ArithmeticFunction ℂ

/-- Dirichlet coefficients of the negative logarithmic derivative. -/
def mangoldt (F : Coeffˣ) : Coeff := logWeight (F : Coeff) * ↑F⁻¹

theorem recover_logWeight (F : Coeffˣ) :
    mangoldt F * (F : Coeff) = logWeight (F : Coeff) := by
  rw [mangoldt, mul_assoc, F.inv_mul, mul_one]

/-- The logarithmic coefficient at a prime is the normalized prime coefficient times log p. -/
theorem prime_value (F : Coeffˣ) (p : Nat.Primes) :
    mangoldt F p = (Real.log (p : ℕ) : ℂ) * (F : Coeff) p * (↑F⁻¹ : Coeff) 1 := by
  rw [mangoldt, RHTower.arithmeticFunction_mul_apply_prime' _ _ p.property]
  simp [logWeight_apply]

/-- Inversion of the Euler product reverses all logarithmic coefficients. -/
theorem inverse (F : Coeffˣ) : mangoldt F⁻¹ = -mangoldt F := by
  have h := logWeight_leibniz (F : Coeff) (↑F⁻¹ : Coeff)
  rw [F.mul_inv] at h
  have h1 : logWeight (1 : Coeff) = 0 := by
    ext n
    by_cases hn : n = 1 <;> simp [hn]
  rw [h1] at h
  unfold mangoldt
  simp only [inv_inv]
  linear_combination -h

/-- Multiplication of Euler products adds their logarithmic coefficients. -/
theorem product (F G : Coeffˣ) : mangoldt (F * G) = mangoldt F + mangoldt G := by
  simp only [mangoldt, Units.val_mul, mul_inv_rev, logWeight_leibniz]
  calc
    _ = logWeight (F : Coeff) * ↑F⁻¹ * ((G : Coeff) * ↑G⁻¹) +
        logWeight (G : Coeff) * ↑G⁻¹ * ((F : Coeff) * ↑F⁻¹) := by ring
    _ = _ := by rw [F.mul_inv, G.mul_inv, mul_one, mul_one]

/-- The short inverse leaves a residual supported strictly beyond its cutoff. -/
def remainder (F : Coeffˣ) (V : ℕ) : Coeff := 1 - (F : Coeff) * coeffTrunc ↑F⁻¹ V

theorem remainder_head (F : Coeffˣ) (V : ℕ) :
    AgreeUpTo (remainder F V) 0 V := by
  have h := (agreeUpTo_refl (F : Coeff) V).mul (coeffTrunc_agreeUpTo (↑F⁻¹ : Coeff) V)
  rw [F.mul_inv] at h
  intro n hn
  change (1 : Coeff) n - _ = 0
  rw [h n hn, sub_self]

/-- The two short pieces and the bilinear remainder recover the whole logarithmic derivative. -/
theorem decomposition (F : Coeffˣ) (U V : ℕ) :
    mangoldt F = coeffTrunc (mangoldt F) U
      + logWeight (F : Coeff) * coeffTrunc ↑F⁻¹ V
      - (F : Coeff) * coeffTrunc (mangoldt F) U * coeffTrunc ↑F⁻¹ V
      + (mangoldt F - coeffTrunc (mangoldt F) U) * remainder F V := by
  rw [← recover_logWeight F, remainder]
  ring

/-- The bilinear remainder first occurs at or above the product of the first omitted indices. -/
theorem bilinear_support (F : Coeffˣ) (U V n : ℕ) :
    n < (U + 1) * (V + 1) →
    ((mangoldt F - coeffTrunc (mangoldt F) U) * remainder F V) n = 0 := by
  intro hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ij hij
  obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hij
  by_cases hi : ij.1 ≤ U
  · change (mangoldt F ij.1 - coeffTrunc (mangoldt F) U ij.1) * _ = 0
    rw [coeffTrunc_apply_of_le _ hi, sub_self, zero_mul]
  · have hj : ij.2 ≤ V := by
      by_contra! h
      exact hn.not_ge (hprod ▸ Nat.mul_le_mul (Nat.lt_of_not_ge hi) h)
    rw [remainder_head F V _ hj]
    exact mul_zero _

private theorem mangoldt_one (F : Coeffˣ) : mangoldt F 1 = 0 := by
  simp [mangoldt]

private theorem first_head (F : Coeffˣ) : coeffTrunc (mangoldt F) 1 = 0 := by
  ext n
  by_cases h : n ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> simp [mangoldt_one]
  · simp [h]

/-- The prime-square logarithmic coefficient subtracts the square of the normalized
prime coefficient from twice the normalized prime-square coefficient (Remark 1). -/
theorem prime_square (F : Coeffˣ) (p : Nat.Primes) :
    mangoldt F ((p : ℕ)^2) = (Real.log (p : ℕ) : ℂ) *
      (2 * (F : Coeff) ((p : ℕ)^2) * (↑F⁻¹ : Coeff) 1 -
        ((F : Coeff) p * (↑F⁻¹ : Coeff) 1)^2) := by
  have h := congrArg (fun f : Coeff => f ((p : ℕ)^2)) (recover_logWeight F)
  change (mangoldt F * (F : Coeff)) _ = logWeight (F : Coeff) _ at h
  rw [RHTower.arithmeticFunction_mul_apply_prime_sq _ _ p.property,
    mangoldt_one, prime_value, logWeight_apply] at h
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, Complex.ofReal_mul,
    Complex.ofReal_ofNat, zero_mul, zero_add] at h
  have h₁ : (F : Coeff) 1 * (↑F⁻¹ : Coeff) 1 = 1 := by
    rw [← ArithmeticFunction.mul_apply_one, F.mul_inv]
    simp
  linear_combination (↑F⁻¹ : Coeff) 1 * h - mangoldt F ((p : ℕ)^2) * h₁

/-- The two reversed signs in (1.1) give exactly the opposite answer at cutoff one.
The residual is written with the same lower support as the paper whenever V ≥ 1. -/
theorem reversed_at_one (F : Coeffˣ) (V : ℕ) :
    coeffTrunc (mangoldt F) 1
      - logWeight (F : Coeff) * coeffTrunc ↑F⁻¹ V
      - (F : Coeff) * coeffTrunc (mangoldt F) 1 * coeffTrunc ↑F⁻¹ V
      + (mangoldt F - coeffTrunc (mangoldt F) 1) *
          ((F : Coeff) * coeffTrunc ↑F⁻¹ V - 1) = -mangoldt F := by
  rw [first_head, ← recover_logWeight F]
  ring

/-- A coefficient system has zero logarithmic derivative precisely when it is supported at one. -/
theorem vanishing_iff (F : Coeffˣ) :
    mangoldt F = 0 ↔ ∀ n : ℕ, 1 < n → (F : Coeff) n = 0 := by
  constructor
  · intro h n hn
    have hd := recover_logWeight F
    rw [h, zero_mul] at hd
    have hc := congrArg (fun a : Coeff => a n) hd.symm
    change (Real.log n : ℂ) * (F : Coeff) n = 0 at hc
    have hp : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    exact (mul_eq_zero.mp hc).resolve_left (by exact_mod_cast hp.ne')
  · intro h
    have hd : logWeight (F : Coeff) = 0 := by
      ext n
      rcases n with _ | n
      · simp
      cases n with
      | zero => simp
      | succ n => simp [h _ (by omega : 1 < n + 1 + 1)]
    rw [mangoldt, hd, zero_mul]

/-- The classical zeta Euler product gives a concrete counterexample at every prime. -/
def zetaUnit : Coeffˣ :=
  ⟨(zeta : Coeff), (moebius : Coeff), coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

theorem zeta_prime_sign (p : Nat.Primes) :
    (-mangoldt zetaUnit) p ≠ mangoldt zetaUnit p := by
  have hv : mangoldt zetaUnit p = (Real.log (p : ℕ) : ℂ) := by
    rw [prime_value]
    simp [zetaUnit, p.property.ne_zero]
  rw [ArithmeticFunction.neg_apply, hv]
  have hp : 0 < Real.log (p : ℕ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  intro he
  have hre := congrArg Complex.re he
  change -Real.log (p : ℕ) = Real.log (p : ℕ) at hre
  linarith

end GaloisForLFunctions.PrimeExponentialSums.Vaughan

#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.recover_logWeight
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.prime_value
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.inverse
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.product
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.remainder_head
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.decomposition
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.bilinear_support
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.prime_square
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.reversed_at_one
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.vanishing_iff
#print axioms GaloisForLFunctions.PrimeExponentialSums.Vaughan.zeta_prime_sign
