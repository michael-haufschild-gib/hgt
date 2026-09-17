import GaloisForLFunctions.RHTower.PrimeLogThetaPrecompletionAllJetBoundary
import GaloisForLFunctions.HTGeometry.CofinitePacketVandermonde

/-!
# Prime-log theta precompletion all-jet finite-core faithfulness

The non-Bessel all-jet boundary from the preceding module would be useless if prime-labelled
finite sources could cancel through every retained degree.  They cannot.  On a packet of `N`
distinct primes, its degrees `0` through `N - 1` are a diagonally weighted Vandermonde system in
the distinct nodes `log p`.  The diagonal factors consist of the degree-zero literal boundary
coefficient and never vanish.  Thus the finite jet prefix is already injective on every labelled
finite source packet.

This is a source-faithfulness statement, not a source-to-divisor or escape theorem.  Combined with
the all-jet non-Bessel theorem, it isolates the required next arena precisely: an unbounded or
projective jet object that retains finite packet coordinates without collapsing its degree axis to
a Hilbert direct sum.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal InnerProduct LinearPMap

namespace RHTower

noncomputable section

/-- The literal all-degree boundary jet of one finite labelled prime packet. -/
def primeLogThetaPrecompletionWeightedFinitePacketJet {N : ℕ}
    (x : ℝ) (p : Fin N → Nat.Primes) (a : Fin N → ℂ) : ℕ → ℂ :=
  fun n => ∑ i : Fin N,
    a i * primeLogThetaPrecompletionWeightedBoundaryCoefficient n x (p i)

/-- Every degree is the degree-zero boundary coefficient times its literal prime-log monomial. -/
theorem primeLogThetaPrecompletionWeightedBoundaryCoefficient_eq_zero_mul_log_pow
    (n : ℕ) (x : ℝ) (p : Nat.Primes) :
    primeLogThetaPrecompletionWeightedBoundaryCoefficient n x p =
      primeLogThetaPrecompletionWeightedBoundaryCoefficient 0 x p *
        (Real.log (p : ℝ) : ℂ) ^ n := by
  unfold primeLogThetaPrecompletionWeightedBoundaryCoefficient
  rw [show n + 2 = 2 + n by omega, pow_add]
  norm_num
  ring

/-- The degree-zero literal boundary coefficient is nonzero at every prime and every real clock. -/
theorem primeLogThetaPrecompletionWeightedBoundaryCoefficient_zero_ne_zero
    (x : ℝ) (p : Nat.Primes) :
    primeLogThetaPrecompletionWeightedBoundaryCoefficient 0 x p ≠ 0 := by
  unfold primeLogThetaPrecompletionWeightedBoundaryCoefficient
  apply mul_ne_zero
  · norm_cast
    apply div_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact pow_ne_zero _
          (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
    · exact_mod_cast p.2.ne_zero
  · exact Complex.exp_ne_zero _

/-- **Finite-core all-jet faithfulness.**  On a packet of `N` distinct prime labels, vanishing of
the first `N` literal boundary degrees is equivalent to vanishing of every packet coefficient. -/
theorem primeLogThetaPrecompletionWeightedFinitePacketJet_prefix_zero_iff
    {N : ℕ} (x : ℝ) (p : Fin N → Nat.Primes) (hp : Function.Injective p)
    (a : Fin N → ℂ) :
    (∀ n : Fin N, primeLogThetaPrecompletionWeightedFinitePacketJet x p a n = 0) ↔
      a = 0 := by
  constructor
  · intro hzero
    let f : Fin N → ℂ := fun i => (Real.log (p i : ℝ) : ℂ)
    let v : Fin N → ℂ := fun i =>
      a i * primeLogThetaPrecompletionWeightedBoundaryCoefficient 0 x (p i)
    have hf : Function.Injective f := by
      intro i j hij
      change (Real.log (p i : ℝ) : ℂ) = Real.log (p j : ℝ) at hij
      have hlog : Real.log (p i : ℝ) = Real.log (p j : ℝ) := by
        exact Complex.ofReal_injective hij
      exact hp (GaloisForLFunctions.HTGeometry.log_prime_injective hlog)
    have hmom : ∀ n : Fin N, ∑ i : Fin N, v i * f i ^ (n : ℕ) = 0 := by
      intro n
      have hn := hzero n
      unfold primeLogThetaPrecompletionWeightedFinitePacketJet at hn
      have hrewrite :
          (fun i : Fin N =>
            a i * primeLogThetaPrecompletionWeightedBoundaryCoefficient n x (p i)) =
          fun i => a i *
            (primeLogThetaPrecompletionWeightedBoundaryCoefficient 0 x (p i) *
              (Real.log (p i : ℝ) : ℂ) ^ (n : ℕ)) := by
        funext i
        rw [primeLogThetaPrecompletionWeightedBoundaryCoefficient_eq_zero_mul_log_pow]
      rw [hrewrite] at hn
      simpa [v, f, mul_assoc] using hn
    have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hmom
    funext i
    have hvi := congrFun hv i
    dsimp [v] at hvi
    exact (mul_eq_zero.mp hvi).resolve_right
      (primeLogThetaPrecompletionWeightedBoundaryCoefficient_zero_ne_zero x (p i))
  · rintro rfl n
    simp [primeLogThetaPrecompletionWeightedFinitePacketJet]

end

end RHTower
