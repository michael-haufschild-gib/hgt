import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Module

/-!
# Permutation symmetry of shared attention and recursive readout

Attention sums over tokens, shared pointwise maps commute with reindexing, and
softmax pooling removes the remaining token index. Consequently a broadcast initial
state gives a permutation-invariant classifier at every recursion depth. This proves
the architectural invariance stated in §3.3 of arXiv:2610.23353, independently of training.
-/

noncomputable section
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.SharedAttention

variable {ι V W : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Softmax pooling, allowing any shared score and value maps. -/
def pool (score : V → ℝ) (value : V → W) (x : ι → V) : W :=
  (∑ i, Real.exp (score (x i)))⁻¹ • ∑ i, Real.exp (score (x i)) • value (x i)

/-- Attention with a token-dependent query and shared key/value rules. -/
def attention (score : V → V → ℝ) (value : V → V) (x : ι → V) (i : ι) : V :=
  pool (score (x i)) value x

/-- Shared residual attention followed by a shared pointwise map. -/
def block (score : V → V → ℝ) (value post : V → V) (x : ι → V) (i : ι) : V :=
  post (x i + attention score value x i)

/-- Each recursive cycle reinjects the encoded input before shared refinement. -/
def refine (score : V → V → ℝ) (value post : V → V) (input : ι → V) :
    ℕ → (ι → V) → (ι → V)
  | 0, y => y
  | n + 1, y => block score value post (fun i => refine score value post input n y i + input i)

/-- Sequence-level output after any number of shared cycles. -/
def readout (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → W) (depth : ℕ) (initial : V) (input : ι → V) : W :=
  pool poolScore output (refine score value post input depth (fun _ => initial))

/-- Normalized exponential pooling is independent of the token enumeration. -/
theorem pool_perm (score : V → ℝ) (value : V → W) (x : ι → V) (e : Equiv.Perm ι) :
    pool score value (x ∘ e) = pool score value x := by
  unfold pool
  congr 1
  · exact congrArg Inv.inv (e.sum_comp (fun i => Real.exp (score (x i))))
  · exact e.sum_comp (fun i => Real.exp (score (x i)) • value (x i))

/-- Queries reindex with tokens while each attention average remains unchanged. -/
theorem attention_perm (score : V → V → ℝ) (value : V → V) (x : ι → V)
    (e : Equiv.Perm ι) : attention score value (x ∘ e) = attention score value x ∘ e := by
  funext i
  exact pool_perm (score (x (e i))) value x e

theorem block_perm (score : V → V → ℝ) (value post : V → V) (x : ι → V)
    (e : Equiv.Perm ι) : block score value post (x ∘ e) = block score value post x ∘ e := by
  funext i
  simp only [block, attention_perm, Function.comp_apply]

/-- Equivariance survives arbitrary recursion depth and repeated input injection. -/
theorem refine_perm (score : V → V → ℝ) (value post : V → V) (input y : ι → V)
    (n : ℕ) (e : Equiv.Perm ι) :
    refine score value post (input ∘ e) n (y ∘ e) =
      refine score value post input n y ∘ e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [refine, ih, Function.comp_apply]
    exact block_perm score value post (fun i => refine score value post input n y i + input i) e

/-- Broadcast initialization and pooling make the complete recursive classifier invariant. -/
theorem readout_perm (score : V → V → ℝ) (value post : V → V)
    (poolScore : V → ℝ) (output : V → W) (depth : ℕ) (initial : V) (input : ι → V)
    (e : Equiv.Perm ι) :
    readout score value post poolScore output depth initial (input ∘ e) =
      readout score value post poolScore output depth initial input := by
  unfold readout
  rw [show (fun _ : ι => initial) = (fun _ : ι => initial) ∘ e from rfl,
    refine_perm, pool_perm]

#print axioms pool_perm
#print axioms refine_perm
#print axioms readout_perm

end GaloisForLFunctions.RepresentationLifting.SharedAttention
