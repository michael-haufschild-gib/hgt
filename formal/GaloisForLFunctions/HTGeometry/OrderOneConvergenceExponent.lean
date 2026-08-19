/-
# Order-one divisors have convergence exponent below two

A divisor `a : ι → ℂ` presented over an arbitrary index type, locally finite and with the counting
bound `n(r) ≤ K (1 + r) log (2 + r)`, has summable inverse squares.  This is the input a genus-one
canonical product consumes, and the counting bound is exactly what Jensen's inequality extracts
from an order-one growth envelope.

The proof is the logarithmic bucket decomposition already used for exponent zero: bucket `i` by
`⌊log ‖a i‖⌋`, so that bucket `n` lies in the disc of radius `e^{n+1}` and every element of it
contributes at most `e^{-2n}`.  The bucket mass is at most `K (1 + e^{n+1}) log (2 + e^{n+1})`,
which is `O(n · e^{n})`, so the bucket total is `O(n · e^{-n})` and the series converges.
-/
import GaloisForLFunctions.HTGeometry.CountableDivisorConvergenceExponent

noncomputable section

open Filter Topology Set Asymptotics Metric

namespace GaloisForLFunctions.CountableDivisor

variable {ι : Type*}

/-- The divisor has order-one density, `n(r) ≤ K (1 + r) log (2 + r)` for `r ≥ 1`. -/
def OrderOneDensityIdx (a : ι → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r →
    (divisorIdxCount a r : ℝ) ≤ K * (1 + r) * Real.log (2 + r)

/-- The bucket majorant of an order-one divisor is summable. -/
theorem summable_orderOneBucketMajorant {K : ℝ} (hK : 0 ≤ K) :
    Summable (fun n : ℕ =>
      (K * (1 + Real.exp ((n : ℝ) + 1)) * Real.log (2 + Real.exp ((n : ℝ) + 1))) *
        Real.exp (-2 * (n : ℝ))) := by
  have hmaj : Summable (fun n : ℕ =>
      (2 * K * Real.exp 1) * (((n : ℝ) + 1) * Real.exp (-1 * (n : ℝ)))
        + (2 * K * Real.exp 1 * Real.log 2) * Real.exp (-1 * (n : ℝ))) := by
    refine Summable.add ((summable_linear_expNeg (α := 1) one_pos).mul_left _) ?_
    refine Summable.mul_left _ ?_
    have hbase : ‖Real.exp (-1)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    refine (summable_geometric_of_norm_lt_one hbase).congr (fun n => ?_)
    rw [← Real.exp_nat_mul]
    ring_nf
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have h1 : (0 : ℝ) ≤ Real.log (2 + Real.exp ((n : ℝ) + 1)) :=
      Real.log_nonneg (by have := (Real.exp_pos ((n : ℝ) + 1)).le; linarith)
    have h2 : (0 : ℝ) ≤ 1 + Real.exp ((n : ℝ) + 1) := by
      have := (Real.exp_pos ((n : ℝ) + 1)).le; linarith
    have := Real.exp_nonneg (-2 * (n : ℝ))
    positivity
  · set E : ℝ := Real.exp ((n : ℝ) + 1) with hE
    have hE1 : (1 : ℝ) ≤ E := Real.one_le_exp (by positivity)
    have hE2 : (2 : ℝ) ≤ E := by
      rw [hE]
      calc (2 : ℝ) ≤ Real.exp 1 := by
            have := Real.add_one_le_exp (1 : ℝ); linarith
        _ ≤ Real.exp ((n : ℝ) + 1) := Real.exp_le_exp.mpr
            (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hlog : Real.log (2 + E) ≤ Real.log 2 + ((n : ℝ) + 1) := by
      have hle : 2 + E ≤ 2 * E := by linarith
      calc Real.log (2 + E) ≤ Real.log (2 * E) :=
            Real.log_le_log (by linarith) hle
        _ = Real.log 2 + ((n : ℝ) + 1) := by
            rw [Real.log_mul (by norm_num) (by linarith), hE, Real.log_exp]
    have hlin : 1 + E ≤ 2 * E := by linarith
    have hlognn : (0 : ℝ) ≤ Real.log (2 + E) := Real.log_nonneg (by linarith)
    have hexpsplit : Real.exp (-2 * (n : ℝ)) = Real.exp (-1 * (n : ℝ)) * Real.exp (-1 * (n : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    have hEbound : E * Real.exp (-1 * (n : ℝ)) ≤ Real.exp 1 := by
      rw [hE, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by ring_nf; exact le_rfl)
    have hexpnn : (0 : ℝ) ≤ Real.exp (-1 * (n : ℝ)) := Real.exp_nonneg _
    have hstep1 : (K * (1 + E) * Real.log (2 + E)) * Real.exp (-2 * (n : ℝ))
        ≤ (K * (2 * E) * (Real.log 2 + ((n : ℝ) + 1))) * Real.exp (-2 * (n : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
      have h1 : K * (1 + E) * Real.log (2 + E) ≤ K * (2 * E) * Real.log (2 + E) := by
        refine mul_le_mul_of_nonneg_right ?_ hlognn
        exact mul_le_mul_of_nonneg_left hlin hK
      have h2 : K * (2 * E) * Real.log (2 + E) ≤ K * (2 * E) * (Real.log 2 + ((n : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left hlog ?_
        have : (0 : ℝ) ≤ 2 * E := by linarith
        positivity
      linarith
    refine le_trans hstep1 ?_
    rw [hexpsplit]
    have hkey : (K * (2 * E) * (Real.log 2 + ((n : ℝ) + 1))) *
        (Real.exp (-1 * (n : ℝ)) * Real.exp (-1 * (n : ℝ)))
        = (2 * K * (Real.log 2 + ((n : ℝ) + 1)) * Real.exp (-1 * (n : ℝ))) *
            (E * Real.exp (-1 * (n : ℝ))) := by ring
    rw [hkey]
    have hcoef : (0 : ℝ) ≤ 2 * K * (Real.log 2 + ((n : ℝ) + 1)) * Real.exp (-1 * (n : ℝ)) := by
      have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have : (0 : ℝ) ≤ Real.log 2 + ((n : ℝ) + 1) := by positivity
      positivity
    have := mul_le_mul_of_nonneg_left hEbound hcoef
    refine le_trans this ?_
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hexp1 : (0 : ℝ) ≤ Real.exp 1 := Real.exp_nonneg _
    nlinarith [Real.exp_nonneg (-1 * (n : ℝ)), Real.exp_nonneg 1]

/-- **Convergence exponent below two.**  An order-one divisor has summable inverse squares. -/
theorem summable_rpow_neg_two_of_orderOneDensity {a : ι → ℂ}
    (hloc : LocallyFiniteDivisor a) (hden : OrderOneDensityIdx a) :
    Summable (fun i : ι => ‖a i‖ ^ (-2 : ℝ)) := by
  classical
  obtain ⟨K, hK, hcount⟩ := hden
  set S : Set ι := {i : ι | ‖a i‖ ≤ 1} with hS
  rw [← summable_subtype_and_compl (s := S)]
  constructor
  · haveI : Finite ↑S := Set.Finite.to_subtype (hloc 1)
    exact Summable.of_finite
  · have hgt : ∀ p : ↑(Sᶜ), 1 < ‖a p.1‖ := by
      intro p
      have hp := p.2
      simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
      exact hp
    have hle : ∀ n : ℕ, ({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard
        ≤ {i : ι | logBucket a i = n}.ncard := by
      intro n
      exact Set.ncard_le_ncard_of_injOn (fun p : ↑(Sᶜ) => (p : ι))
        (fun p hp => hp) (fun p _ q _ h => Subtype.ext h)
        (finite_logBucket_fiber hloc n)
    have hfib : ∀ n : ℕ, {p : ↑(Sᶜ) | logBucket a p.1 = n}.Finite := by
      intro n
      refine Set.Finite.ofFinset ((finite_logBucket_fiber hloc n).toFinset.preimage
        (fun p : ↑(Sᶜ) => (p : ι)) (fun p _ q _ h => Subtype.ext h)) ?_
      intro p
      simp [Set.Finite.mem_toFinset]
    refine summable_of_bucket _ (fun p => Real.rpow_nonneg (norm_nonneg _) _)
      (fun p => logBucket a p.1) hfib (fun n => Real.exp (-2 * (n : ℝ)))
      (fun p => norm_rpow_le_expBucket (hgt p) (by norm_num)) ?_
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_orderOneBucketMajorant hK)
    have hexp1 : (1 : ℝ) ≤ Real.exp ((n : ℝ) + 1) := Real.one_le_exp (by positivity)
    have h3 : (({p : ↑(Sᶜ) | logBucket a p.1 = n}).ncard : ℝ)
        ≤ ({i : ι | logBucket a i = n}.ncard : ℝ) := by exact_mod_cast hle n
    have h4 := le_trans h3 (ncard_logBucket_fiber_le hloc n)
    have h5 := hcount (Real.exp ((n : ℝ) + 1)) hexp1
    exact mul_le_mul_of_nonneg_right (le_trans h4 h5) (Real.exp_nonneg _)

/-- The inverse-square summability in the form the genus-one canonical product consumes. -/
theorem summable_inv_norm_sq_idx {a : ι → ℂ} (hane : ∀ i, a i ≠ 0)
    (hloc : LocallyFiniteDivisor a) (hden : OrderOneDensityIdx a) :
    Summable (fun i : ι => 1 / ‖a i‖ ^ 2) := by
  refine (summable_rpow_neg_two_of_orderOneDensity hloc hden).congr (fun i => ?_)
  have hpos : (0 : ℝ) < ‖a i‖ := norm_pos_iff.mpr (hane i)
  rw [Real.rpow_neg hpos.le, one_div]
  congr 1
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end GaloisForLFunctions.CountableDivisor
