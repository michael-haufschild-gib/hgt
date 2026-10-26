import GaloisForLFunctions.ArithmeticCorrelationGeometry.ChargedBoundariesAreCriticalAtAQuarter
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# The prime source is typical except for its pole

Twist the von Mangoldt source by the gauge torus: `ψ_x(N) = Σ_{n ≤ N} Λ(n) χ_x(n)`.

* **Almost every twist has no pole** (`ae_norm_twistedPsi_le`). The normalized source
  `Λ(n)/log(n+1)` is bounded by one, so its twisted partial sums obey the almost-sure square-root
  law; an Abel step with the increasing weight `log(n+1)` gives
  `|ψ_x(N)| ≤ C_x √(N+1) (1 + log(N+1))³` for Haar-almost every `x`.
* **The gauge point `0` has a pole** (`tendsto_twistedPsi_zero_div`). `ψ_0(N)/N → 1`: the prime
  number theorem says that the actual prime source is atypical in its orbit, by exactly a linear
  term — the pole of `ζ` at `s = 1`, the archimedean place (`TheBoundaryOfADilationIsTheArchimedeanPlace`).
* **RH is typicality modulo the pole** (`riemannHypothesis_iff_twistedPsi_zero_sub`). The Riemann
  hypothesis is the statement that after subtracting its pole the point `0` cancels at the
  square-root scale (von Koch).

Gauge status: for the Möbius source RH asks whether `0` is typical; for the prime source `0` is
provably atypical, and RH asks that the archimedean pole be its only atypicality.
-/

open MeasureTheory Finset Filter Topology Asymptotics
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

/-- The twisted Chebyshev function `ψ_x(N) = Σ_{1 ≤ n ≤ N} Λ(n) χ_x(n)`. -/
def twistedPsi (N : ℕ) (x : GaugeTorus) : ℂ := ∑ n ∈ Ioc 0 N, ((Λ n : ℝ) : ℂ) * twist x n

/-- The normalized prime source `Λ(n)/log(n+1)`, bounded by one. -/
def normalizedPrimeSource (n : ℕ) : ℂ := (((Λ n : ℝ) / Real.log (n + 1) : ℝ) : ℂ)

theorem norm_normalizedPrimeSource_le (n : ℕ) : ‖normalizedPrimeSource n‖ ≤ 1 := by
  rw [normalizedPrimeSource, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hlog : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by norm_cast; omega)
  rw [abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlog.le),
    div_le_one hlog]
  calc (Λ n : ℝ) ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    _ ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by positivity) (by linarith)

/-- **Abel step with an increasing weight.** If `c 0 = 0` and every partial sum up to `N` is at most
`B`, the `w`-weighted sum is at most `2 B w(N+1)`. -/
theorem norm_sum_Ioc_mul_le_of_monotone {c : ℕ → ℂ} (hc0 : c 0 = 0) {w : ℕ → ℝ} (hw : Monotone w)
    (hw0 : 0 ≤ w 0) {N : ℕ} {B : ℝ} (hB : ∀ n ≤ N, ‖∑ i ∈ range (n + 1), c i‖ ≤ B) :
    ‖∑ n ∈ Ioc 0 N, c n * (w n : ℂ)‖ ≤ 2 * B * w (N + 1) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le N))
  rw [sum_Ioc_mul_eq_abel c (fun n => (w n : ℂ)) (Nat.zero_le N)]
  have hS0 : ∑ i ∈ range (0 + 1), c i = 0 := by simp [hc0]
  rw [hS0, zero_mul, sub_zero]
  have hsum : ‖∑ j ∈ Ioc 0 N, (∑ i ∈ range (j + 1), c i) * ((w j : ℂ) - (w (j + 1) : ℂ))‖ ≤
      B * (w (N + 1) - w 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Ioc 0 N, ‖(∑ i ∈ range (j + 1), c i) * ((w j : ℂ) - (w (j + 1) : ℂ))‖
        ≤ ∑ j ∈ Ioc 0 N, B * (w (j + 1) - w j) := by
          refine sum_le_sum fun j hj => ?_
          rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (by linarith [hw (Nat.le_succ j)])]
          exact (mul_le_mul_of_nonneg_right (hB j (mem_Ioc.mp hj).2)
            (by linarith [hw (Nat.le_succ j)])).trans_eq (by ring)
      _ = B * (w (N + 1) - w 1) := by
          rw [← mul_sum]
          congr 1
          have := sum_Ioc_sub_succ w (Nat.zero_le N)
          rw [← neg_sub, ← this, ← sum_neg_distrib]
          exact sum_congr rfl fun j _ => by ring
  have hw1 : 0 ≤ w 1 := hw0.trans (hw (Nat.zero_le 1))
  have hwN : 0 ≤ w (N + 1) := hw0.trans (hw (Nat.zero_le _))
  calc ‖(∑ i ∈ range (N + 1), c i) * (w (N + 1) : ℂ) +
        ∑ j ∈ Ioc 0 N, (∑ i ∈ range (j + 1), c i) * ((w j : ℂ) - (w (j + 1) : ℂ))‖
      ≤ B * w (N + 1) + B * (w (N + 1) - w 1) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ hsum)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwN]
        exact mul_le_mul_of_nonneg_right (hB N le_rfl) hwN
    _ ≤ 2 * B * w (N + 1) := by nlinarith

/-- **Almost every twist of the prime source has no pole.** -/
theorem ae_norm_twistedPsi_le :
    ∀ᵐ x ∂gaugeHaar, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖twistedPsi N x‖ ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
  filter_upwards [ae_exists_norm_gaugePartialSum_le normalizedPrimeSource
    norm_normalizedPrimeSource_le] with x ⟨C, hC, hb⟩
  refine ⟨4 * C, by positivity, fun N => ?_⟩
  set c : ℕ → ℂ := fun n => normalizedPrimeSource n * twist x n
  have hc0 : c 0 = 0 := by simp [c, normalizedPrimeSource]
  set B := C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 2
  have hB : ∀ n ≤ N, ‖∑ i ∈ range (n + 1), c i‖ ≤ B := by
    intro n hn
    have hsplit : ∑ i ∈ range (n + 1), c i = gaugePartialSum normalizedPrimeSource n x := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), hc0, zero_add,
        gaugePartialSum, twistSum]
      rfl
    rw [hsplit]
    refine (hb n).trans ?_
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have h1 : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)])
    have h4 : (1 + Real.log ((n : ℝ) + 1)) ^ 2 ≤ (1 + Real.log ((N : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h4 (by positivity) (by positivity)
  have hw : Monotone (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact Real.log_le_log (by positivity) (by linarith)
  have habel := norm_sum_Ioc_mul_le_of_monotone hc0 hw (by simp) hB
  have heq : twistedPsi N x = ∑ n ∈ Ioc 0 N, c n * ((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) := by
    refine sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) < (n : ℝ) + 1 := by
      have h1 := (mem_Ioc.mp hn).1
      have : (1 : ℝ) ≤ n := by exact_mod_cast h1
      linarith
    have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := (Real.log_pos hn1).ne'
    have hlogC : ((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
    simp only [c, normalizedPrimeSource]
    push_cast
    field_simp
  rw [heq]
  refine habel.trans ?_
  have hlogN : Real.log (((N + 1 : ℕ) : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 2) / ((N : ℝ) + 1) by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at this
    push_cast
    have hfrac : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 ≤ 1 := by
      rw [div_sub_one hpos.ne', div_le_one hpos]; linarith
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
    linarith
  have hB0 : 0 ≤ B := by positivity
  have hl : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (N : ℝ) + 1 by linarith [N.cast_nonneg (α := ℝ)])]
  calc 2 * B * Real.log (((N + 1 : ℕ) : ℝ) + 1) ≤ 2 * B * (1 + Real.log ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlogN (by positivity)
    _ ≤ 4 * C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by
        simp only [B]
        have : 0 ≤ C * Real.sqrt ((N : ℝ) + 1) * (1 + Real.log ((N : ℝ) + 1)) ^ 3 := by positivity
        nlinarith

/-- At the gauge point `0` the twisted Chebyshev function is `ψ`. -/
theorem twistedPsi_zero (N : ℕ) : twistedPsi N 0 = ((Chebyshev.psi N : ℝ) : ℂ) := by
  rw [twistedPsi, Chebyshev.psi, Nat.floor_natCast]
  push_cast
  exact sum_congr rfl fun n _ => by rw [twist_zero, mul_one]

/-- **The gauge point `0` has a pole**: `ψ_0(N)/N → 1` (the prime number theorem). -/
theorem tendsto_twistedPsi_zero_div :
    Tendsto (fun N : ℕ => twistedPsi N 0 / (N : ℂ)) atTop (𝓝 1) := by
  have h := RHTower.tendsto_chebyshevPsiReal_div.comp tendsto_natCast_atTop_atTop
  have h' := (Complex.continuous_ofReal.tendsto _).comp h
  refine (h'.congr fun N => ?_).trans_eq (by simp)
  simp only [Function.comp_apply, twistedPsi_zero]
  rw [RHTower.chebyshevPsiReal_eq_sum_range, Nat.floor_natCast,
    RHTower.sum_range_succ_vonMangoldt_eq_sum_Icc, Chebyshev.psi, Nat.floor_natCast]
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI]
  push_cast
  norm_cast

/-- **RH is the typicality of the point `0` modulo its pole** (von Koch). -/
theorem riemannHypothesis_iff_twistedPsi_zero_sub :
    RiemannHypothesis ↔ (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => Real.sqrt x * Real.log x ^ 2) :=
  RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO

end GaloisForLFunctions.ArithmeticCorrelationGeometry
