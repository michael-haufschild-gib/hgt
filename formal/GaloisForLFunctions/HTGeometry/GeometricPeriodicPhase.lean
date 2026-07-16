import GaloisForLFunctions.HTGeometry.ExactGeometricLevelCascade
import GaloisForLFunctions.HTGeometry.TorsionLanguageUniversalPhase

/-!
# Eventual periodic phases on translated geometric windows

An eventually periodic Taylor phase is literally constant on every fixed translated atom window
along a sufficiently late arithmetic progression.  The grouped ADE weight polynomial is pulled
back along the same progression by polynomial composition.
-/

namespace GaloisForLFunctions

open Filter Finset Polynomial PowerSeries Topology

noncomputable section

/-- A concrete tail-periodicity predicate with an explicit starting index. -/
def PeriodicFrom (u : ℕ → ℂ) (p T : ℕ) : Prop :=
  ∀ n, T ≤ n → u (n + p) = u n

/-- Tail periodicity iterates through every natural multiple of the period. -/
theorem PeriodicFrom.add_mul
    {u : ℕ → ℂ} {p T : ℕ} (hu : PeriodicFrom u p T)
    {n : ℕ} (hn : T ≤ n) (k : ℕ) :
    u (n + p * k) = u n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hu (n + p * k) (hn.trans (Nat.le_add_right _ _)), ih]

/-- Arithmetic progressions of positive step are strictly increasing. -/
theorem strictMono_add_mul_right {q₀ p : ℕ} (hp : 0 < p) :
    StrictMono (fun k : ℕ => q₀ + p * k) := by
  intro i j hij
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hij hp) q₀

/-- Every fixed translated window has a constant phase state along a late period progression. -/
theorem PeriodicFrom.windowShift_add_mul
    {u : ℕ → ℂ} {p T q₀ K : ℕ} (hu : PeriodicFrom u p T)
    (hK : K ≤ q₀) (hT : T ≤ q₀ - K) (k r : ℕ) :
    u (windowShift (q₀ + p * k) K r) = u (windowShift q₀ K r) := by
  have hidx : windowShift (q₀ + p * k) K r = (q₀ - K + r) + p * k := by
    dsimp [windowShift]
    omega
  rw [hidx]
  exact hu.add_mul (hT.trans (Nat.le_add_right _ r)) k

/-- The multiplicative phase of a bounded atom pattern is constant on a late period progression. -/
theorem PeriodicFrom.patternPhase_add_mul
    {u : ℕ → ℂ} {p T q₀ K M D : ℕ} (hu : PeriodicFrom u p T)
    (hK : K ≤ q₀) (hT : T ≤ q₀ - K)
    (pattern : Fin M → Fin (D + 1)) (k : ℕ) :
    (∏ r : Fin M,
      u (windowShift (q₀ + p * k) K (r : ℕ)) ^ (pattern r : ℕ)) =
      ∏ r : Fin M, u (windowShift q₀ K (r : ℕ)) ^ (pattern r : ℕ) := by
  apply Finset.prod_congr rfl
  intro r hr
  rw [hu.windowShift_add_mul hK hT]

/-- Pull a complex polynomial back along `k ↦ q₀ + p*k`. -/
def arithmeticProgressionPolynomial (q₀ p : ℕ) (W : ℂ[X]) : ℂ[X] :=
  W.comp (C (q₀ : ℂ) + C (p : ℂ) * X)

@[simp] theorem arithmeticProgressionPolynomial_eval
    (q₀ p k : ℕ) (W : ℂ[X]) :
    (arithmeticProgressionPolynomial q₀ p W).eval (k : ℂ) =
      W.eval (q₀ + p * k : ℕ) := by
  rw [arithmeticProgressionPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  norm_cast

/-- Along a late period progression, the intrinsic phase of every translated bounded atom is the
fixed phase character read at the initial window. -/
theorem PeriodicFrom.normalizedAtomPhase_shifted_add_mul
    {F : PowerSeries ℂ} {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-b i) : ℝ) : ℂ) * u i)
    {p T q₀ K M D : ℕ} (hu : PeriodicFrom u p T)
    (hK : K ≤ q₀) (hT : T ≤ q₀ - K)
    (pattern : Fin M → Fin (D + 1)) (k : ℕ) :
    normalizedAtomPhase F b
        (shiftedAtomPatternKey (q₀ + p * k) K pattern) =
      ∏ r : Fin M, u (windowShift q₀ K (r : ℕ)) ^ (pattern r : ℕ) := by
  rw [normalizedAtomPhase_shiftedAtomPatternKey_eq F b u hcoeff]
  exact hu.patternPhase_add_mul hK hT pattern k

end

end GaloisForLFunctions
