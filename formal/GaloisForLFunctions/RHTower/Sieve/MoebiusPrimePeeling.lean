import GaloisForLFunctions.RHTower.Sieve.CoprimePeeledReindex

/-!
# The Möbius prime-peeling recursion

Specialising the peeling identity to a Möbius-weighted sum makes the peeled part re-enter with the
opposite sign: for a prime `p` not dividing the modulus,

`S_e(y) = S_{pe}(y) − ∑_{j ≤ y/p, (pe,j)=1} μ(j) g(p j)`.

The corrections therefore alternate and telescope across the primes of the modulus, which is the
cancellation the two retired routes lacked.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The Möbius prime-peeling recursion.** -/
theorem sum_moebius_peel {p e y : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) (g : ℕ → ℝ) :
    ∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime e j), ((μ j : ℤ) : ℝ) * g j
      = (∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime (p * e) j),
            ((μ j : ℤ) : ℝ) * g j)
        - ∑ j ∈ (Finset.Icc 1 (y / p)).filter (fun j => Nat.Coprime (p * e) j),
            ((μ j : ℤ) : ℝ) * g (p * j) := by
  classical
  have hstep := sum_filter_coprime_split (p := p) (e := e) (y := y) hp
    (fun j => ((μ j : ℤ) : ℝ) * g j)
  have hre := sum_filter_coprime_dvd_reindex (p := p) (e := e) (y := y) hp hpe
    (fun j => ((μ j : ℤ) : ℝ) * g j)
  rw [hstep, hre]
  have hsplit2 := sum_filter_coprime_split (p := p) (e := e) (y := y / p) hp
    (fun j => ((μ (p * j) : ℤ) : ℝ) * g (p * j))
  have hzero : ∑ j ∈ (Finset.Icc 1 (y / p)).filter (fun j => Nat.Coprime e j ∧ p ∣ j),
      ((μ (p * j) : ℤ) : ℝ) * g (p * j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    obtain ⟨-, -, hdvd⟩ := Finset.mem_filter.mp hj
    have hnc : ¬ Nat.Coprime p j := fun hc => (hp.coprime_iff_not_dvd.mp hc) hdvd
    have h0 : (μ (p * j) : ℤ) = 0 := moebius_mul_eq_zero_of_not_coprime hnc
    have h0R : ((μ (p * j) : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    rw [h0R, zero_mul]
  have hflip : ∑ j ∈ (Finset.Icc 1 (y / p)).filter (fun j => Nat.Coprime (p * e) j),
      ((μ (p * j) : ℤ) : ℝ) * g (p * j)
      = - ∑ j ∈ (Finset.Icc 1 (y / p)).filter (fun j => Nat.Coprime (p * e) j),
          ((μ j : ℤ) : ℝ) * g (p * j) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨-, hc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hcp, -⟩ := Nat.coprime_mul_iff_left.mp hc
    have hfac : (μ (p * j) : ℤ) = (μ p : ℤ) * (μ j : ℤ) := moebius_mul_of_coprime hcp
    have hmp : (μ p : ℤ) = -1 := moebius_apply_prime hp
    rw [hfac, hmp] at *
    push_cast
    ring
  rw [hsplit2, hzero, hflip]
  ring

end RHTower.Sieve
