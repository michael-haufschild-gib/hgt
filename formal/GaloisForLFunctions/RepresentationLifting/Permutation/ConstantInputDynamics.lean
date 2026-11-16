import GaloisForLFunctions.RepresentationLifting.Permutation.HistogramDynamics

/-!
# Exact synchronized dynamics on constant encoded histories

For a nonempty constant input, every attention average is its single value
state. The trajectory is therefore an explicit recurrence independent of
all attention and pooling scores, and of the history length. In particular
the pooled classifier cannot recover that length from constant tokens.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.SharedAttention
open HTGeometry

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

omit [AddCommGroup V] [Module ℝ V] in
private theorem countPool_unit (score : V → ℝ) (value : V → W) (x : V) :
    countPool (fun _ : Unit => 1) score value (fun _ => x) = value x := by
  have he : Real.exp (score x) ≠ 0 := by positivity
  simp only [countPool, Fintype.sum_unique, Nat.cast_one, one_mul, smul_smul,
    inv_mul_cancel₀ he, one_smul]

/-- The common latent state of a constant encoded history. -/
def synchronousRefine (value post : V → V) (token : V) : ℕ → V → V
  | 0, y => y
  | n + 1, y =>
      let z := synchronousRefine value post token n y + token
      post (z + value z)

private theorem countRefine_unit (score : V → V → ℝ) (value post : V → V)
    (token initial : V) (depth : ℕ) :
    countRefine (fun _ : Unit => 1) score value post (fun _ => token) depth (fun _ => initial) =
      fun _ => synchronousRefine value post token depth initial := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [countRefine, ih]
    funext u
    simp only [countBlock, countPool_unit, synchronousRefine]

/-- On every positive constant length, the readout is the same explicit score-free recurrence. -/
theorem readout_constant (n : ℕ) (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → W) (depth : ℕ) (initial token : V) :
    readout score value post poolScore output depth initial (fun _ : Fin (n + 1) => token) =
      output (synchronousRefine value post token depth initial) := by
  have hm : historyMultiplicity (fun _ : Fin (n + 1) => ()) = fun _ : Unit => n + 1 := by
    funext u
    cases u
    simp [historyMultiplicity]
  have h := readout_eq_countReadout (fun _ : Fin (n + 1) => ()) score value post
    poolScore output depth initial (fun _ : Unit => token)
  simp only [hm, Function.comp_def] at h
  rw [h]
  have hs := countReadout_scale n (fun _ : Unit => 1) score value post
    poolScore output depth initial (fun _ : Unit => token)
  simp only [mul_one] at hs
  rw [hs, countReadout, countRefine_unit, countPool_unit]

/-- No choice of scores, shared maps or depth makes the scalar readout count constant tokens. -/
theorem readout_cannot_count_constant_tokens (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → ℝ) (depth : ℕ) (initial token : V) :
    ¬ ∀ n : ℕ, readout score value post poolScore output depth initial
      (fun _ : Fin (n + 1) => token) = ((n + 1 : ℕ) : ℝ) := by
  intro h
  have h₀ := h 0
  have h₁ := h 1
  rw [readout_constant] at h₀ h₁
  have he := h₀.symm.trans h₁
  norm_num at he

#print axioms readout_constant
#print axioms readout_cannot_count_constant_tokens

end GaloisForLFunctions.RepresentationLifting.SharedAttention
