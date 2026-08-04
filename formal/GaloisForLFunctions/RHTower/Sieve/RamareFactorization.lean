import GaloisForLFunctions.RHTower.Sieve.RamareSquarePart

/-!
# Factorizing the Ramaré bilinear sum

Away from the square-divisible integers the designated prime splits off multiplicatively: if `p` is
prime, `p ∣ n` and `p² ∤ n`, then `p` and `n/p` are coprime, so a multiplicative `f` satisfies

`f(n) = f(p)·f(n/p)`.

For a weight depending only on the cofactor the inner sum therefore factors, and the bilinear sum
becomes `∑_p f(p) · (cofactor sum)` — the shape the mean-value theorems act on.
-/

namespace RHTower.Sieve

open Finset

/-- A prime dividing `n` exactly once is coprime to the cofactor. -/
theorem coprime_div_of_not_sq_dvd {p n : ℕ} (hp : p.Prime) (hdvd : p ∣ n)
    (hsq : ¬ (p * p) ∣ n) : Nat.Coprime p (n / p) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hcon
  exact hsq (by
    obtain ⟨c, hc⟩ := hcon
    refine ⟨c, ?_⟩
    have hn : p * (n / p) = n := Nat.mul_div_cancel' hdvd
    rw [← hn, hc]
    ring)

/-- **Pointwise factorization off the square-divisible integers.** -/
theorem map_eq_mul_of_dvd_not_sq {f : ℕ → ℝ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    {p n : ℕ} (hp : p.Prime) (hdvd : p ∣ n) (hsq : ¬ (p * p) ∣ n) :
    f n = f p * f (n / p) := by
  have hn : p * (n / p) = n := Nat.mul_div_cancel' hdvd
  calc f n = f (p * (n / p)) := by rw [hn]
    _ = f p * f (n / p) := hf p (n / p) (coprime_div_of_not_sq_dvd hp hdvd hsq)

/-- **The inner sum factorizes.**  For a weight depending only on the cofactor, the designated
prime's contribution is `f p` times a sum over cofactors. -/
theorem sum_eq_mul_sum_image {f g : ℕ → ℝ}
    (hf : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b)
    {p : ℕ} (hp : p.Prime) (T : Finset ℕ)
    (hdvd : ∀ n ∈ T, p ∣ n) (hsq : ∀ n ∈ T, ¬ (p * p) ∣ n) :
    ∑ n ∈ T, f n * g (n / p) = f p * ∑ m ∈ T.image (fun n => n / p), f m * g m := by
  classical
  have hinj : Set.InjOn (fun n => n / p) ↑T := by
    intro x hx y hy hxy
    have hx' : p * (x / p) = x := Nat.mul_div_cancel' (hdvd x hx)
    have hy' : p * (y / p) = y := Nat.mul_div_cancel' (hdvd y hy)
    dsimp only at hxy
    rw [← hx', ← hy', hxy]
  rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h), Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [map_eq_mul_of_dvd_not_sq hf hp (hdvd n hn) (hsq n hn)]
  ring

end RHTower.Sieve
