import GaloisForLFunctions.ArithmeticGaugeTheory.TheAdditivelyInvariantPoint
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant

/-!
# The finite gauge points sample Haar measure

Haar measure on the gauge torus gives every twisted sum the mean square `Σ |c_n|²`
(`ArithmeticCorrelationGeometry.integral_twistSum_mul_conj`). The gauge points of the primitive
Dirichlet characters of conductor at most `R` (`dirichletGauge`) form a finite, arithmetically special
sample of the torus. The multiplicative large sieve says that this sample overcounts the Haar mean
square by at most the factor `(N + R² − 1)/1`, uniformly in the coefficients.

* **Rough sources** (`RoughSource`). A coefficient system supported on positive integers whose prime
  factors all exceed `R`. On such integers every Dirichlet gauge point of conductor at most `R` is its
  character (`twist_dirichletGauge_of_rough`).
* **The large sieve on the gauge torus** (`dirichletGauge_largeSieve`). For a rough source of length
  `N`,
  `Σ_{q ≤ R} (q/φ(q)) Σ_{χ primitive mod q} |Σ_n c_n χ_χ(n)|² ≤ (N + R² − 1) Σ |c_n|²`.
* **Comparison with Haar** (`dirichletGauge_largeSieve_haar`). The right-hand side is
  `(N + R² − 1)` times the Haar mean square of the same twisted sum.

So for statistics of length `N` the finite gauge points up to conductor `√N` reproduce the typical
(Haar) mean square up to a factor `2`. This is the gauge form of the engine behind
Bombieri–Vinogradov: level of distribution says that the special points of conductor up to `√N` are,
in mean square, as typical as Haar-random points. It controls gauge charge at the special points on
average over conductors, never at the single point `0`.
-/

open MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-- A source supported on positive integers all of whose prime factors exceed `R`. -/
def RoughSource (R : ℕ) (c : ℕ → ℂ) : Prop :=
  ∀ n, c n ≠ 0 → n ≠ 0 ∧ ∀ p, p.Prime → p ∣ n → R < p

/-- A rough integer is prime to every modulus `q ≤ R`. -/
theorem coprime_of_rough {R n q : ℕ} (hn : ∀ p, p.Prime → p ∣ n → R < p) (hq0 : 0 < q)
    (hq : q ≤ R) : Nat.Coprime n q := by
  refine Nat.coprime_of_dvd fun p hp hpn hpq => ?_
  have h1 := hn p hp hpn
  have h2 : p ≤ q := Nat.le_of_dvd hq0 hpq
  omega

/-- On rough integers a Dirichlet gauge point of small conductor is its character. -/
theorem twist_dirichletGauge_of_rough {R q : ℕ} [NeZero q] (hq : q ≤ R)
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn0 : n ≠ 0) (hn : ∀ p, p.Prime → p ∣ n → R < p) :
    twist (dirichletGauge χ) n = χ n :=
  twist_dirichletGauge χ hn0 (coprime_of_rough hn (Nat.pos_of_ne_zero (NeZero.ne q)) hq)

open Classical in
/-- **The large sieve on the gauge torus.** For a rough source of length `N` and `R ≥ 2`, the
Dirichlet gauge points of primitive characters of conductor at most `R`, weighted by `q/φ(q)`, carry
at most `(N + R² − 1) Σ |c_n|²` of mean square. -/
theorem dirichletGauge_largeSieve (N R : ℕ) (hR : 2 ≤ R) {c : ℕ → ℂ} (hc : RoughSource R c) :
    ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * twist (dirichletGauge ψ) n‖ ^ 2 ≤
      ((N : ℝ) + (R : ℝ) ^ 2 - 1) * ∑ n ∈ range N, ‖c n‖ ^ 2 := by
  have hsieve := BezoutValuationIncidence.multiplicative_largeSieve_sharp N R hR
    (fun n => conj (c n))
  have hnorm : ∑ n ∈ range N, ‖conj (c n)‖ ^ 2 = ∑ n ∈ range N, ‖c n‖ ^ 2 :=
    sum_congr rfl fun n _ => by rw [Complex.norm_conj]
  rw [hnorm] at hsieve
  refine le_of_eq_of_le ?_ hsieve
  refine sum_congr rfl fun r hr => ?_
  congr 1
  refine sum_congr rfl fun ψ _ => ?_
  -- On the support of `c` the twist is the character.
  have hterm : ∑ n ∈ range N, c n * twist (dirichletGauge ψ) n =
      conj (∑ n ∈ range N, conj (c n) * conj (ψ n)) := by
    rw [map_sum]
    refine sum_congr rfl fun n _ => ?_
    by_cases h0 : c n = 0
    · simp [h0]
    · obtain ⟨hn0, hrough⟩ := hc n h0
      rw [twist_dirichletGauge_of_rough (by have := mem_range.mp hr; omega) ψ hn0 hrough,
        map_mul, Complex.conj_conj, Complex.conj_conj]
  rw [hterm, Complex.norm_conj]

/-- The twisted sums of the source over `range N` have Haar mean square `Σ |c_n|²`. -/
theorem integral_twistSum_range_mul_conj {N : ℕ} {c : ℕ → ℂ} (hc0 : c 0 = 0) :
    ∫ x, (∑ n ∈ range N, c n * twist x n) * conj (∑ n ∈ range N, c n * twist x n) ∂gaugeHaar =
      ((∑ n ∈ range N, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
  -- Remove the index `0`, where the coefficient vanishes.
  have hdrop : ∀ x : GaugeTorus, ∑ n ∈ range N, c n * twist x n =
      twistSum ((range N).filter (fun n => n ≠ 0)) c x := by
    intro x
    rw [twistSum, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rfl
    · rw [not_ne_iff.mp h, hc0, zero_mul]
  simp_rw [hdrop]
  rw [integral_twistSum_mul_conj (fun n hn => (mem_filter.mp hn).2), Complex.ofReal_sum,
    sum_filter]
  refine sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · rw [not_ne_iff.mp h, hc0]
    simp

open Classical in
/-- **Comparison with Haar.** The finite gauge sample overcounts the Haar mean square of a rough
source by at most the factor `N + R² − 1`. -/
theorem dirichletGauge_largeSieve_haar (N R : ℕ) (hR : 2 ≤ R) {c : ℕ → ℂ} (hc : RoughSource R c) :
    ∑ r ∈ range R, ((r + 1 : ℕ) : ℝ) / (r + 1).totient *
        ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ (r + 1))).filter (fun ψ => ψ.IsPrimitive),
          ‖∑ n ∈ range N, c n * twist (dirichletGauge ψ) n‖ ^ 2 ≤
      ((N : ℝ) + (R : ℝ) ^ 2 - 1) *
        (∫ x, (∑ n ∈ range N, c n * twist x n) *
          conj (∑ n ∈ range N, c n * twist x n) ∂gaugeHaar).re := by
  have hc0 : c 0 = 0 := by
    by_contra h
    exact (hc 0 h).1 rfl
  rw [integral_twistSum_range_mul_conj hc0, Complex.ofReal_re]
  exact dirichletGauge_largeSieve N R hR hc

end GaloisForLFunctions.ArithmeticGaugeTheory
