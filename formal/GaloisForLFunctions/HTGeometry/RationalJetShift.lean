import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# Iterated derivatives of a rational function

Every iterated derivative of `p/q` is a polynomial over `q^{k+1}`, with numerators produced by the
quotient rule recursion

`N_0 = p`,  `N_{k+1} = q N_k' - (k+1) q' N_k`.

This is the denominator bookkeeping needed to shift a differential relation by a rational function.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Numerators of the iterated derivatives of `p / q`. -/
def ratDerivNum (p q : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => p
  | k + 1 => q * (ratDerivNum p q k).derivative - (k + 1 : ℕ) • (q.derivative * ratDerivNum p q k)

@[simp]
theorem ratDerivNum_zero (p q : Polynomial ℂ) : ratDerivNum p q 0 = p := rfl

theorem ratDerivNum_succ (p q : Polynomial ℂ) (k : ℕ) :
    ratDerivNum p q (k + 1) =
      q * (ratDerivNum p q k).derivative - (k + 1 : ℕ) • (q.derivative * ratDerivNum p q k) := rfl

/-- **The iterated derivatives of a rational function.** -/
theorem iteratedDeriv_ratFunc (p q : Polynomial ℂ) (k : ℕ) {z : ℂ}
    (hq : ∀ w : ℂ, Polynomial.eval w q ≠ 0) :
    iteratedDeriv k (fun w : ℂ => Polynomial.eval w p / Polynomial.eval w q) z
      = Polynomial.eval z (ratDerivNum p q k) / Polynomial.eval z q ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (fun w : ℂ => Polynomial.eval w p / Polynomial.eval w q)
        = fun w : ℂ => Polynomial.eval w (ratDerivNum p q k) / Polynomial.eval w q ^ (k + 1) := by
      funext w
      exact ih (z := w)
    rw [iteratedDeriv_succ, hfun]
    have hpow : (fun w : ℂ => Polynomial.eval w q ^ (k + 1))
        = fun w : ℂ => Polynomial.eval w (q ^ (k + 1)) := by
      funext w
      rw [Polynomial.eval_pow]
    have hne : Polynomial.eval z q ^ (k + 1) ≠ 0 := pow_ne_zero _ (hq z)
    have hnum' : HasDerivAt (fun w : ℂ => Polynomial.eval w (ratDerivNum p q k))
        (Polynomial.eval z (ratDerivNum p q k).derivative) z := (ratDerivNum p q k).hasDerivAt z
    have hden' : HasDerivAt (fun w : ℂ => Polynomial.eval w q ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * Polynomial.eval z q ^ k * Polynomial.eval z q.derivative) z :=
      (q.hasDerivAt z).pow (k + 1)
    have hdiv := hnum'.div hden' hne
    have hd : deriv (fun w : ℂ => Polynomial.eval w (ratDerivNum p q k)
        / Polynomial.eval w q ^ (k + 1)) z
        = (Polynomial.eval z (ratDerivNum p q k).derivative * Polynomial.eval z q ^ (k + 1)
            - Polynomial.eval z (ratDerivNum p q k) *
              (((k + 1 : ℕ) : ℂ) * Polynomial.eval z q ^ k * Polynomial.eval z q.derivative))
          / (Polynomial.eval z q ^ (k + 1)) ^ (2 : ℕ) := hdiv.deriv
    rw [hd, ratDerivNum_succ]
    have hqz : Polynomial.eval z q ≠ 0 := hq z
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_smul, nsmul_eq_mul,
      Polynomial.eval_natCast]
    push_cast
    field_simp
    ring

end

end GaloisForLFunctions.HTGeometry
