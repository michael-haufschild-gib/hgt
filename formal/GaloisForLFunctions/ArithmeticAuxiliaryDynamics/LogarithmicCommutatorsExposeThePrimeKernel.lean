import GaloisForLFunctions.RHTower.LogarithmicMobiusReconstruction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Logarithmic commutators expose the prime convolution

Let `S` be finite summation over logarithmic integer delays, `M` its Möbius inverse,
and `X f(t) = t f(t)`. The exact conjugation `M X S = X + Λ` exposes the von Mangoldt
convolution. Every iterate is `M X^k S`; no limit or estimate is used.
-/

open RHTower ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

/-- Multiplication by logarithmic time. -/
def timeMultiply (f : ℝ → ℝ) (t : ℝ) : ℝ := t * f t

/-- Time multiplication plus convolution with the von Mangoldt weights. -/
def primeRaise (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * f t + logarithmicWeightedDilation (fun n => vonMangoldt n) f t

/-- The commutator inserts one logarithm in the arithmetic coefficient. -/
theorem timeMultiply_commutator (a : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    timeMultiply (logarithmicWeightedDilation a f) t -
        logarithmicWeightedDilation a (timeMultiply f) t =
      logarithmicWeightedDilation (fun n => a n * Real.log n) f t := by
  simp only [timeMultiply, logarithmicWeightedDilation, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The logarithmically weighted Möbius kernel followed by `S` is `−Λ`. -/
theorem logMobius_dilationSum (f : ℝ → ℝ) (t : ℝ) :
    logarithmicWeightedDilation (fun n => (moebius n : ℝ) * Real.log n)
        (logarithmicDilationSum f) t =
      -logarithmicWeightedDilation (fun n => vonMangoldt n) f t := by
  change logarithmicWeightedDilation (fun n => (moebius n : ℝ) * Real.log n)
    (logarithmicWeightedDilation (fun _ => 1) f) t = _
  rw [logarithmicWeightedDilation_comp]
  have hc : (fun k => ∑ p ∈ k.divisorsAntidiagonal,
      ((moebius p.1 : ℝ) * Real.log p.1) * (1 : ℝ)) = fun k => -vonMangoldt k := by
    funext k
    simp only [mul_one]
    rw [Nat.sum_divisorsAntidiagonal (fun d _ => (moebius d : ℝ) * Real.log d)]
    exact ArithmeticFunction.sum_moebius_mul_log_eq
  rw [hc]
  simp only [logarithmicWeightedDilation, neg_mul, Finset.sum_neg_distrib]

/-- Exact conjugation of time multiplication by integer summation. -/
theorem mobius_timeMultiply_dilationSum (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    logarithmicMobiusInverse (timeMultiply (logarithmicDilationSum f)) t = primeRaise f t := by
  have h := timeMultiply_commutator (fun n => (moebius n : ℝ)) (logarithmicDilationSum f) t
  change t * logarithmicMobiusInverse (logarithmicDilationSum f) t -
      logarithmicMobiusInverse (timeMultiply (logarithmicDilationSum f)) t = _ at h
  rw [logarithmicMobiusInverse_dilationSum f ht, logMobius_dilationSum] at h
  unfold primeRaise
  linarith

/-- A finite delay sum only reads nonnegative times. -/
private theorem logarithmicWeightedDilation_congr_nonneg {f g : ℝ → ℝ}
    (h : ∀ t, 0 ≤ t → f t = g t) (a : ℕ → ℝ) (t : ℝ) :
    logarithmicWeightedDilation a f t = logarithmicWeightedDilation a g t := by
  unfold logarithmicWeightedDilation
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hnexp : (n : ℝ) ≤ Real.exp t :=
    (Nat.le_floor_iff (Real.exp_pos t).le).mp (Finset.mem_Icc.mp hn).2
  have hlog : Real.log n ≤ t := (Real.log_le_iff_le_exp hn0).mpr hnexp
  rw [h _ (sub_nonneg.mpr hlog)]

/-- The raising operator becomes multiplication by time after floor summation. -/
theorem dilationSum_primeRaise (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    logarithmicDilationSum (primeRaise f) t = t * logarithmicDilationSum f t := by
  have h : logarithmicDilationSum (primeRaise f) t =
      logarithmicDilationSum
        (logarithmicMobiusInverse (timeMultiply (logarithmicDilationSum f))) t :=
    logarithmicWeightedDilation_congr_nonneg
      (fun u hu => (mobius_timeMultiply_dilationSum f hu).symm) (fun _ => 1) t
  rw [h, logarithmicDilationSum_mobiusInverse _ ht]
  rfl

/-- Every number of raising steps has the same exact arithmetic conjugation. -/
theorem dilationSum_iterate_primeRaise (k : ℕ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    logarithmicDilationSum (primeRaise^[k] f) t = t ^ k * logarithmicDilationSum f t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', dilationSum_primeRaise _ ht, ih, pow_succ]
      ring

/-- Iterated amplification reconstructs the time-weighted arithmetic source exactly. -/
theorem iterate_primeRaise_eq_mobius (k : ℕ) (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    primeRaise^[k] f t =
      logarithmicMobiusInverse (fun u => u ^ k * logarithmicDilationSum f u) t := by
  rw [← logarithmicMobiusInverse_dilationSum (primeRaise^[k] f) ht]
  exact logarithmicWeightedDilation_congr_nonneg
    (fun u hu => dilationSum_iterate_primeRaise k f hu) (fun n => (moebius n : ℝ)) t


end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
