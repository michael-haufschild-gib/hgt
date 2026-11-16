import GaloisForLFunctions.RepresentationLifting.Permutation.SharedAttention
import GaloisForLFunctions.HTGeometry.ReplicaHistoryFactorizationLaw

/-!
# Exact shared-attention dynamics on finite histograms

The position-independent refinement and softmax readout of arXiv:2610.23353,
§§3.2--3.3, evolve identical input tokens identically. Grouping each attention
sum by the corpus's history multiplicities gives an exact recurrence with one
state per symbol. Multiplicities weight both the softmax numerator and its
denominator; no approximation or choice of orbit representatives is needed.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.SharedAttention
open HTGeometry

variable {ι A V W : Type*} [Fintype ι] [Fintype A] [DecidableEq A]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

private theorem sum_value_eq_histogram (label : ι → A) (v : A → W) :
    (∑ i, v (label i)) = ∑ a, (historyMultiplicity label a : ℝ) • v a := by
  symm
  simp only [Nat.cast_smul_eq_nsmul, historyMultiplicity, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- Softmax pooling of symbol states with their exact natural multiplicities. -/
def countPool (count : A → ℕ) (score : V → ℝ) (value : V → W) (x : A → V) : W :=
  (∑ a, (count a : ℝ) * Real.exp (score (x a)))⁻¹ •
    ∑ a, ((count a : ℝ) * Real.exp (score (x a))) • value (x a)

omit [AddCommGroup V] [Module ℝ V] in
/-- Grouping repeated tokens preserves the normalized weighted sum exactly. -/
theorem pool_eq_countPool (label : ι → A) (score : V → ℝ)
    (value : V → W) (x : A → V) :
    pool score value (x ∘ label) = countPool (historyMultiplicity label) score value x := by
  unfold pool countPool
  simp only [Function.comp_apply]
  rw [sum_history_energy_eq_histogram (fun a => Real.exp (score (x a))) label,
    sum_value_eq_histogram label (fun a => Real.exp (score (x a)) • value (x a))]
  simp only [smul_smul]

/-- One shared attention block on the symbol states. -/
def countBlock (count : A → ℕ) (score : V → V → ℝ) (value post : V → V)
    (x : A → V) (a : A) : V :=
  post (x a + countPool count (score (x a)) value x)

/-- The latent token states are the pullback of the compressed block states. -/
theorem block_eq_countBlock (label : ι → A) (score : V → V → ℝ)
    (value post : V → V) (x : A → V) :
    block score value post (x ∘ label) =
      countBlock (historyMultiplicity label) score value post x ∘ label := by
  funext i
  simp only [block, attention, countBlock, Function.comp_apply, pool_eq_countPool]

/-- Input reinjection and shared refinement on one state per symbol. -/
def countRefine (count : A → ℕ) (score : V → V → ℝ) (value post : V → V)
    (input : A → V) : ℕ → (A → V) → (A → V)
  | 0, y => y
  | n + 1, y => countBlock count score value post
      (fun a => countRefine count score value post input n y a + input a)

/-- Every intermediate state, at every depth, is determined by the same histogram recurrence. -/
theorem refine_eq_countRefine (label : ι → A) (score : V → V → ℝ)
    (value post : V → V) (input y : A → V) (n : ℕ) :
    refine score value post (input ∘ label) n (y ∘ label) =
      countRefine (historyMultiplicity label) score value post input n y ∘ label := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [refine, countRefine, ih, Function.comp_apply]
    exact block_eq_countBlock label score value post
      (fun a => countRefine (historyMultiplicity label) score value post input n y a + input a)

/-- Explicit histogram readout with broadcast initialization. -/
def countReadout (count : A → ℕ) (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → W) (depth : ℕ) (initial : V) (input : A → V) : W :=
  countPool count poolScore output
    (countRefine count score value post input depth (fun _ => initial))

/-- The whole classifier is computed exactly from symbol values and their multiplicities. -/
theorem readout_eq_countReadout (label : ι → A) (score : V → V → ℝ)
    (value post : V → V) (poolScore : V → ℝ) (output : V → W)
    (depth : ℕ) (initial : V) (input : A → V) :
    readout score value post poolScore output depth initial (input ∘ label) =
      countReadout (historyMultiplicity label) score value post poolScore output depth initial input := by
  unfold readout countReadout
  rw [show (fun _ : ι => initial) = (fun _ : A => initial) ∘ label from rfl,
    refine_eq_countRefine, pool_eq_countPool]

omit [DecidableEq A] [AddCommGroup V] [Module ℝ V] in
/-- A common positive integer factor cancels from both softmax sums, including the empty case. -/
theorem countPool_scale (k : ℕ) (count : A → ℕ) (score : V → ℝ)
    (value : V → W) (x : A → V) :
    countPool (fun a => (k + 1) * count a) score value x = countPool count score value x := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  unfold countPool
  simp only [Nat.cast_mul, mul_assoc, ← Finset.mul_sum, ← smul_smul, ← Finset.smul_sum]
  rw [mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hk, mul_one]

omit [DecidableEq A] in
/-- Repeating every symbol equally leaves every compressed block unchanged. -/
theorem countBlock_scale (k : ℕ) (count : A → ℕ) (score : V → V → ℝ)
    (value post : V → V) (x : A → V) :
    countBlock (fun a => (k + 1) * count a) score value post x =
      countBlock count score value post x := by
  funext a
  rw [countBlock, countBlock, countPool_scale]

omit [DecidableEq A] in
/-- Uniform replication leaves the full compressed trajectory unchanged. -/
theorem countRefine_scale (k : ℕ) (count : A → ℕ) (score : V → V → ℝ)
    (value post : V → V) (input y : A → V) (depth : ℕ) :
    countRefine (fun a => (k + 1) * count a) score value post input depth y =
      countRefine count score value post input depth y := by
  induction depth with
  | zero => rfl
  | succ depth ih => rw [countRefine, countRefine, ih, countBlock_scale]

omit [DecidableEq A] in
/-- The readout depends on relative symbol counts, not their common positive integer scale. -/
theorem countReadout_scale (k : ℕ) (count : A → ℕ) (score : V → V → ℝ)
    (value post : V → V) (poolScore : V → ℝ) (output : V → W)
    (depth : ℕ) (initial : V) (input : A → V) :
    countReadout (fun a => (k + 1) * count a) score value post poolScore output depth initial input =
      countReadout count score value post poolScore output depth initial input := by
  unfold countReadout
  rw [countRefine_scale, countPool_scale]

#print axioms pool_eq_countPool
#print axioms refine_eq_countRefine
#print axioms readout_eq_countReadout
#print axioms countReadout_scale

end GaloisForLFunctions.RepresentationLifting.SharedAttention
