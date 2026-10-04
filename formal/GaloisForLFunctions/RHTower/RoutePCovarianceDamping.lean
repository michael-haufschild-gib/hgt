import GaloisForLFunctions.RHTower.RoutePNativeCovarianceSource

/-! # Exact damping conjugation of the finite native covariance -/

open Finset

namespace RHTower.RoutePWindow

variable {ι : Type*} [DecidableEq ι]

theorem head_damping (P : Finset ι) (a b : ι → ℝ) (f : ℝ → ℝ) (ε t : ℝ) :
    head P a (fun p => damping ε (a p)*b p) (fun x => damping ε x*f x) t =
      damping ε t*head P a b f t := by
  induction P using Finset.induction_on generalizing t with
  | empty => simp
  | @insert p P hp ih =>
    rw [head_insert P _ _ _ hp, head_insert P a b f hp, ih, ih]
    calc
      _ = damping ε t*head P a b f t-
          (damping ε (a p)*damping ε (t-a p))*(b p*head P a b f (t-a p)) := by ring
      _ = _ := by rw [damping_delay]; ring

omit [DecidableEq ι] in
theorem prod_damping (P : Finset ι) (a : ι → ℝ) (ε : ℝ) :
    (∏ p ∈ P, damping ε (a p)) = damping ε (∑ p ∈ P, a p) := by
  unfold damping
  rw [← Real.exp_sum]
  congr 1
  rw [mul_sum, sum_div]

theorem covariance_damping (P : Finset ι) (a b w : ι → ℝ) (f : ℝ → ℝ) (ε t : ℝ) :
    covariance P a (fun p => damping ε (a p)*b p)
      (fun p => (damping ε (a p))^2*w p) (fun x => damping ε x*f x) t =
        (damping ε t)^2*covariance P a b w f t := by
  unfold covariance
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  rw [head_damping, prod_mul_distrib, prod_pow, prod_damping]
  calc
    _ = (damping ε (∑ p ∈ R, a p)*damping ε (t-∑ p ∈ R, a p))^2*
        ((∏ p ∈ R, w p)*(head (P \ R) a b f (t-∑ p ∈ R, a p))^2) := by ring
    _ = _ := by rw [damping_delay]

theorem damping_sq (ε t : ℝ) : (damping ε t)^2 = Real.exp (-ε*t) := by
  unfold damping
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem primeGain_eq_damping (ε : ℝ) (p : Nat.Primes) :
    primeGain ε p = damping ε (Real.log (p : ℝ))*primeGain 0 p := by
  simp [primeGain, damping, div_eq_mul_inv]

/-- All damping is exactly the physical weight at the original clock. -/
theorem prime_covariance_damping (P : Finset Nat.Primes) (ε t : ℝ) :
    covariance P (fun p => Real.log (p : ℝ)) (meanGain (primeGain ε))
      (noiseGain (primeGain ε)) (unitClockSource ε) t =
        Real.exp (-ε*t)*covariance P (fun p => Real.log (p : ℝ))
          (meanGain (primeGain 0)) (noiseGain (primeGain 0)) (unitClockSource 0) t := by
  have hb : meanGain (primeGain ε) = fun p : Nat.Primes =>
      damping ε (Real.log (p : ℝ))*meanGain (primeGain 0) p := by
    funext p
    unfold meanGain
    rw [primeGain_eq_damping]
    ring
  have hw : noiseGain (primeGain ε) = fun p : Nat.Primes =>
      (damping ε (Real.log (p : ℝ)))^2*noiseGain (primeGain 0) p := by
    funext p
    unfold noiseGain
    rw [primeGain_eq_damping]
    ring
  have hf : unitClockSource ε = fun t => damping ε t*unitClockSource 0 t := by
    funext t
    simp [unitClockSource, damping]
  rw [hb, hw, hf, covariance_damping, damping_sq]

end RHTower.RoutePWindow
