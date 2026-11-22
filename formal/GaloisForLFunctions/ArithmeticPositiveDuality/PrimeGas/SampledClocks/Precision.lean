import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ClockBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.FiniteResolution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LogarithmicPhaseContinuity

/-!
# Exact and positive-radius observations in one clock network

A zero radius requires equality of the phases. A positive radius accepts
a metric neighborhood of equality. Only nonzero times measured exactly
connect components for purposes of the heat trace threshold.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open scoped Classical NNReal
variable {I E : Type*}

namespace Network

variable (G : Network I E)

theorem phase_distance (e : E) (x : I → ℕ+) :
    dist (G.phase e x) 1 = dist (clockPhase (G.time e) (x (G.src e))) (clockPhase (G.time e) (x (G.dst e))) := by
  let a := G.phase e x
  let b := clockPhase (G.time e) (x (G.dst e))
  have hp : a*b = clockPhase (G.time e) (x (G.src e)) := by
    change Circle.exp (G.time e * (energy (x (G.src e)) - energy (x (G.dst e)))) *
      Circle.exp (G.time e * energy (x (G.dst e))) = Circle.exp (G.time e * energy (x (G.src e)))
    rw [← Circle.exp_add]
    congr 1
    ring
  rw [← hp]
  change dist (a : ℂ) 1 = dist ((a : ℂ)*(b : ℂ)) (b : ℂ)
  rw [dist_eq_norm,dist_eq_norm,← sub_one_mul,norm_mul,Circle.norm_coe,mul_one]

def Gate (r : E → ℝ≥0) (x : I → ℕ+) : Prop := ∀ e,
  if r e = 0 then G.phase e x = 1 else dist (G.phase e x) 1 < (r e : ℝ)

def exactAt (r : E → ℝ≥0) : Network I E :=
  ⟨G.src,G.dst,fun e => if r e = 0 then G.time e else 0⟩

private def softAt (r : E → ℝ≥0) : Readout I {e : E // r e ≠ 0} (fun _ => Circle) where
  left e := G.src e.val
  right e := G.dst e.val
  value e := clockPhase (G.time e.val)
  radius e := ⟨r e.val, by exact_mod_cast (pos_iff_ne_zero.mpr e.property : 0 < r e.val)⟩

theorem gate_accepted (r : E → ℝ≥0) : G.Gate r = Accepted (G.exactAt r) (G.softAt r) := by
  funext x
  apply propext
  constructor
  · intro h
    constructor
    · intro e
      by_cases he : r e = 0
      · simpa only [exactAt,phase,if_pos he] using (show G.phase e x = 1 by simpa only [if_pos he] using h e)
      · simp [exactAt,phase,he]
    · intro e
      change dist (clockPhase (G.time e.val) (x (G.src e.val)))
        (clockPhase (G.time e.val) (x (G.dst e.val))) < (r e.val : ℝ)
      rw [← G.phase_distance]
      simpa only [if_neg e.property] using h e.val
  · rintro ⟨hh,hs⟩ e
    by_cases he : r e = 0
    · rw [if_pos he]
      simpa only [exactAt,phase,if_pos he] using hh e
    · rw [if_neg he,G.phase_distance]
      exact hs ⟨e,he⟩

theorem gate_traceClass_iff [Fintype I] [Fintype E] (r : E → ℝ≥0) (s : ℂ) :
    HasSectorHeat (G.Gate r) s ↔ (G.exactAt r).Domain s := by
  rw [G.gate_accepted,accepted_heat_iff]

end Network

/-- For two copies the boundary is one half exactly with a nonzero time and exact phase resolution. -/
theorem binary_precision_threshold (t : ℝ) (r : ℝ≥0) (s : ℂ) :
    HasSectorHeat ((binary t).Gate (fun _ => r)) s ↔
      (if r = 0 ∧ t ≠ 0 then (1/2 : ℝ) else 1) < s.re := by
  rw [Network.gate_traceClass_iff]
  by_cases hr : r = 0
  · have he : (binary t).exactAt (fun _ => r) = binary t := by simp [Network.exactAt,binary,hr]
    rw [he,← Network.traceClass_iff,binary_threshold]
    by_cases ht : t = 0 <;> simp [hr,ht]
  · have he : (binary t).exactAt (fun _ => r) = binary 0 := by simp [Network.exactAt,binary,hr]
    rw [he,← Network.traceClass_iff,binary_threshold]
    simp [hr]

#print axioms Network.phase_distance
#print axioms Network.gate_traceClass_iff
#print axioms binary_precision_threshold

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
