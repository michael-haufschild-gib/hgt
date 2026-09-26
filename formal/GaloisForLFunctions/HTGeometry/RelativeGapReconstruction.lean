import GaloisForLFunctions.HTGeometry.RelativeGapCurvature

/-!
# Realizing arbitrary relative-gap curvature

Every real curvature sequence has a canonical positive path after choosing its
first two logarithmic coordinates. Recovering a path from its own curvature is
exact. Thus a positional sign hierarchy requires information beyond positivity
and the relative-gap definition.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Discrete integration of a prescribed logarithmic curvature. -/
def logCurvaturePath (a b : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => a
  | 1 => b
  | n + 2 => 2 * logCurvaturePath a b c (n + 1) - logCurvaturePath a b c n + c n

theorem logCurvaturePath_curvature (a b : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    logStepCurvature (logCurvaturePath a b c n) (logCurvaturePath a b c (n + 1))
      (logCurvaturePath a b c (n + 2)) = c n := by
  rw [logCurvaturePath]
  unfold logStepCurvature
  ring

/-- Curvature together with two initial values recovers every real sequence. -/
theorem logCurvaturePath_reconstruct (u : ℕ → ℝ) (n : ℕ) :
    logCurvaturePath (u 0) (u 1)
      (fun k => logStepCurvature (u k) (u (k + 1)) (u (k + 2))) n = u n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h0 h1 =>
    rw [logCurvaturePath, h0, h1]
    unfold logStepCurvature
    ring

/-- Changes of initial data are exactly affine gauge changes. -/
theorem logCurvaturePath_change_initial (a b a' b' : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    logCurvaturePath a' b' c n - logCurvaturePath a b c n =
      (a' - a) + (n : ℝ) * ((b' - b) - (a' - a)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [logCurvaturePath]
  | one => simp [logCurvaturePath]
  | more n h0 h1 =>
    rw [logCurvaturePath, logCurvaturePath]
    push_cast
    push_cast at h1
    linarith

theorem logCurvaturePath_add (a b a' b' : ℝ) (c d : ℕ → ℝ) (n : ℕ) :
    logCurvaturePath (a + a') (b + b') (fun k => c k + d k) n =
      logCurvaturePath a b c n + logCurvaturePath a' b' d n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n h0 h1 =>
    rw [logCurvaturePath, logCurvaturePath, logCurvaturePath, h0, h1]
    ring

/-- Positive path with exactly the specified logarithmic acceleration. -/
def positiveCurvaturePath (a b : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (logCurvaturePath a b c n)

theorem positiveCurvaturePath_pos (a b : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    0 < positiveCurvaturePath a b c n := Real.exp_pos _

theorem positiveCurvaturePath_expansion_iff (a b : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    relativeStep (positiveCurvaturePath a b c n) (positiveCurvaturePath a b c (n + 1)) <
      relativeStep (positiveCurvaturePath a b c (n + 1)) (positiveCurvaturePath a b c (n + 2)) ↔
        0 < c n := by
  simp only [positiveCurvaturePath, relativeStep_exp, logRelativeStep_lt_iff,
    logCurvaturePath_curvature]

theorem positiveCurvaturePath_neutral_iff (a b : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    relativeStep (positiveCurvaturePath a b c n) (positiveCurvaturePath a b c (n + 1)) =
      relativeStep (positiveCurvaturePath a b c (n + 1)) (positiveCurvaturePath a b c (n + 2)) ↔
        c n = 0 := by
  simp only [positiveCurvaturePath, relativeStep_exp, logRelativeStep_eq_iff,
    logCurvaturePath_curvature]

/-- Every prescribed binary signal is realized by a positive sequence. -/
theorem positiveCurvaturePath_binary_signal (signal : ℕ → Bool) (n : ℕ) :
    let p := positiveCurvaturePath 0 0 (fun k => if signal k then 1 else -1)
    relativeStep (p n) (p (n + 1)) < relativeStep (p (n + 1)) (p (n + 2)) ↔
      signal n = true := by
  dsimp only
  rw [positiveCurvaturePath_expansion_iff]
  cases signal n <;> simp

end
end GaloisForLFunctions.HTGeometry
