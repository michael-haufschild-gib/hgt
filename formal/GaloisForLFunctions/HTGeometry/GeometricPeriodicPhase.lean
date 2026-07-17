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

/-- A geometric exponential in the progression parameter beats polynomial growth in the
corresponding arithmetic progression. -/
theorem tendsto_add_mul_pow_mul_exp_neg_geometric
    {lam gamma : ℝ} (hlam : 1 < lam) (hgamma : 0 < gamma)
    (q₀ p P : ℕ) :
    Tendsto (fun k : ℕ =>
      (((q₀ + p * k : ℕ) : ℝ) ^ P) * Real.exp (-gamma * lam ^ k))
      atTop (nhds 0) := by
  let C : ℝ := q₀ + p
  have hC : 0 ≤ C := by positivity
  have hcore := tendsto_natAdd_pow_mul_exp_neg_geometric hlam hgamma 1 P
  have hupper : Tendsto (fun k : ℕ =>
      C ^ P * ((((k + 1 : ℕ) : ℝ) ^ P) * Real.exp (-gamma * lam ^ k)))
      atTop (nhds 0) := by
    simpa using hcore.const_mul (C ^ P)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun k =>
      mul_nonneg (pow_nonneg (by positivity) P) (Real.exp_nonneg _)
  · filter_upwards with k
    have hq : ((q₀ + p * k : ℕ) : ℝ) ≤ C * ((k + 1 : ℕ) : ℝ) := by
      dsimp [C]
      norm_cast
      nlinarith
    have hpow : (((q₀ + p * k : ℕ) : ℝ) ^ P) ≤
        (C * ((k + 1 : ℕ) : ℝ)) ^ P := pow_le_pow_left₀ (by positivity) hq P
    calc
      (((q₀ + p * k : ℕ) : ℝ) ^ P) * Real.exp (-gamma * lam ^ k) ≤
          (C * ((k + 1 : ℕ) : ℝ)) ^ P * Real.exp (-gamma * lam ^ k) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = C ^ P * ((((k + 1 : ℕ) : ℝ) ^ P) *
          Real.exp (-gamma * lam ^ k)) := by rw [mul_pow]; ring
  · exact hupper

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
  W.comp (Polynomial.C (q₀ : ℂ) + Polynomial.C (p : ℂ) * Polynomial.X)

@[simp] theorem arithmeticProgressionPolynomial_eval
    (q₀ p k : ℕ) (W : ℂ[X]) :
    (arithmeticProgressionPolynomial q₀ p W).eval (k : ℂ) =
      W.eval (((q₀ + p * k : ℕ) : ℕ) : ℂ) := by
  rw [arithmeticProgressionPolynomial, Polynomial.eval_comp]
  congr 1
  simp

/-- Pullback along a positive-step arithmetic progression preserves nonzero polynomials. -/
theorem arithmeticProgressionPolynomial_ne_zero
    {q₀ p : ℕ} (hp : 0 < p) {W : ℂ[X]} (hW : W ≠ 0) :
    arithmeticProgressionPolynomial q₀ p W ≠ 0 := by
  intro hzero
  rcases Polynomial.comp_eq_zero_iff.mp hzero with h | h
  · exact hW h
  · have hcoeff := congrArg (fun Q : ℂ[X] => Q.coeff 1) h.2
    simp [arithmeticProgressionPolynomial] at hcoeff
    exact_mod_cast (show p ≠ 0 by omega) hcoeff

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
