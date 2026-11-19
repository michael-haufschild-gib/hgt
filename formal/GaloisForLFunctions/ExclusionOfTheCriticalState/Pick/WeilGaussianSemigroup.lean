import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianLimitOfProbeDephasing
import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardyBoundarySaturation
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Joint Gaussian jump evolution of arithmetic probe forms

The weak-step limit produces a positive Schur multiplier for any finite
bank of jumps, including simultaneous linear, quadratic and quartic jumps.
Its generator is a sum of diagonal double commutators. Its fixed algebra
preserves joint eigenspaces, and the two reflection-sector bounds on the
signed Weil form persist at every nonnegative time.
-/

noncomputable section
open Matrix Finset Filter
open scoped Topology ComplexOrder NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open HilbertMetric.CauchyDephasing

private theorem ones_symbol (n : ℕ) :
    (Matrix.of fun _ _ : Fin n => (1 : ℂ)).PosSemidef := by
  have h := symbol_posSemidef (fun _ : Fin n => (0:ℝ))
  change (Matrix.of fun _ _ : Fin n => (coherence 0 0 : ℂ)).PosSemidef at h
  simpa only [coherence_self,Complex.ofReal_one] using h

private theorem cauchy_power_symbol {n : ℕ} (r : Fin n → ℝ) (k : ℕ) :
    (Matrix.of fun i j => (coherence (r i) (r j) : ℂ)^k).PosSemidef := by
  induction k with
  | zero =>
    simpa only [pow_zero] using ones_symbol n
  | succ k ih =>
    simpa only [pow_succ,Matrix.hadamard,HilbertMetric.CauchyDephasing.symbol,Matrix.of_apply] using ih.hadamard (symbol_posSemidef r)

private theorem gaussian_symbol {n : ℕ} (r : Fin n → ℝ) :
    (Matrix.of fun i j => (Real.exp (-gapCost (r i) (r j)) : ℂ)).PosSemidef := by
  let A := fun k : ℕ => Matrix.of fun i j => (weakCoherence k (r i) (r j) : ℂ)
  apply _root_.RHTower.posSemidef_of_entrywise_tendsto A
  · intro k
    simpa only [A,weakCoherence,Complex.ofReal_pow] using
      cauchy_power_symbol (fun i => r i / Real.sqrt (k+1:ℝ)) (k+1)
  · intro i j
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (weakCoherence_tendsto _ _)

variable {d n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- The commuting channels add squared differences across all jumps. -/
def jointCost (r : Fin d → Fin n → ℝ) (i j : Fin n) : ℝ := ∑ l, gapCost (r l i) (r l j)

/-- Arithmetic matrices evolve by the Gaussian of their joint jump distance. -/
def jumpEvolution (t : ℝ) (r : Fin d → Fin n → ℝ) (A : Mat) : Mat :=
  Matrix.of fun i j => (Real.exp (-t*jointCost r i j) : ℂ)*A i j

private theorem partial_symbol (t : ℝ≥0) (r : Fin d → Fin n → ℝ) (s : Finset (Fin d)) :
    (Matrix.of fun i j => (Real.exp (-t.val*∑ l ∈ s, gapCost (r l i) (r l j)) : ℂ)).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [sum_empty,mul_zero,Real.exp_zero,Complex.ofReal_one] using ones_symbol n
  | insert l s hl ih =>
    have hs (i j : Fin n) : gapCost (Real.sqrt t.val*r l i) (Real.sqrt t.val*r l j) =
        t.val*gapCost (r l i) (r l j) := by
      simp only [gapCost,← mul_sub,mul_pow,Real.sq_sqrt t.property]
      ring
    have h := (gaussian_symbol (fun i => Real.sqrt t.val*r l i)).hadamard ih
    simpa only [sum_insert hl,mul_add,Real.exp_add,Complex.ofReal_mul,Matrix.hadamard,
      Matrix.of_apply,hs,neg_mul] using h

/-- Every amplified finite Gaussian Schur symbol is positive. Auxiliary
indices may carry repeated jump vectors. -/
theorem jointGaussian_symbol_positive (t : ℝ≥0) (r : Fin d → Fin n → ℝ) :
    (Matrix.of fun i j => (Real.exp (-t.val*jointCost r i j) : ℂ)).PosSemidef :=
  partial_symbol t r univ

private theorem evolution_psd (t : ℝ≥0) (r : Fin d → Fin n → ℝ) {A : Mat} (hA : A.PosSemidef) :
    (jumpEvolution t r A).PosSemidef := (jointGaussian_symbol_positive t r).hadamard hA

/-- Sector positivity and both signed Weil bounds survive simultaneous jumps. -/
theorem gaussian_probe_sector_bounds (t : ℝ≥0) (r : Fin d → Fin n → ℝ) (p : Fin n → {x : ℝ // 1 ≤ x}) :
    let W := probeGram (fun i => (p i).val)
    let H := hilbertProbeGram p
    (jumpEvolution t r (positiveProbeGram p)).PosSemidef ∧
    (jumpEvolution t r (negativeProbeGram p)).PosSemidef ∧
    (jumpEvolution t r H + jumpEvolution t r W).PosSemidef ∧
    (jumpEvolution t r H - jumpEvolution t r W).PosSemidef := by
  refine ⟨evolution_psd t r (positiveProbeGram_posSemidef p),
    evolution_psd t r (negativeProbeGram_posSemidef p),?_,?_⟩
  · convert evolution_psd t r (hilbertProbeGram_add_probeGram_posSemidef p) using 1
    ext i j
    exact (mul_add _ _ _).symm
  · convert evolution_psd t r (hilbertProbeGram_sub_probeGram_posSemidef p) using 1
    ext i j
    exact (mul_sub _ _ _).symm

theorem jumpEvolution_add (s t : ℝ) (r : Fin d → Fin n → ℝ) (A : Mat) :
    jumpEvolution (s+t) r A = jumpEvolution s r (jumpEvolution t r A) := by
  ext i j
  simp only [jumpEvolution,Matrix.of_apply,neg_add,add_mul,Real.exp_add,Complex.ofReal_mul,mul_assoc]

private theorem joint_zero (r : Fin d → Fin n → ℝ) (i j : Fin n) :
    jointCost r i j = 0 ↔ ∀ l, r l i = r l j := by
  have h (l : Fin d) (_ : l ∈ (univ : Finset (Fin d))) : 0 ≤ gapCost (r l i) (r l j) := by
    unfold gapCost
    positivity
  rw [jointCost,Finset.sum_eq_zero_iff_of_nonneg h]
  simp only [mem_univ,forall_true_left]
  have eq0 (x y : ℝ) : gapCost x y = 0 ↔ x=y := by
    simp [gapCost,sub_eq_zero]
  simp only [eq0]

/-- Positive-time fixed operators have support exactly inside joint eigenspaces. -/
theorem jointGaussian_fixed_iff (t : ℝ) (r : Fin d → Fin n → ℝ) (A : Mat) :
    jumpEvolution t r A = A ↔ t = 0 ∨ ∀ i j, A i j ≠ 0 → ∀ l, r l i = r l j := by
  have he (i j) : (Real.exp (-t*jointCost r i j) : ℂ) = 1 ↔ t = 0 ∨ ∀ l, r l i = r l j := by
    rw [← Complex.ofReal_one,Complex.ofReal_inj,Real.exp_eq_one_iff,mul_eq_zero,neg_eq_zero,joint_zero]
  constructor
  · intro h
    by_cases ht : t = 0
    · exact Or.inl ht
    · right
      intro i j hij
      have h' := Matrix.ext_iff.mpr h i j
      change _ * A i j = A i j at h'
      exact ((he i j).mp (mul_right_cancel₀ hij (h'.trans (one_mul _).symm))).resolve_left ht
  · rintro (rfl|h)
    · ext i j; simp [jumpEvolution]
    · ext i j
      by_cases h0 : A i j = 0
      · simp [jumpEvolution,h0]
      · exact (congrArg (fun z : ℂ => z*A i j) ((he i j).mpr (Or.inr (h i j h0)))).trans (one_mul _)

/-- A jump acts by taking the commutator with its diagonal momentum observable. -/
def momentumBracket (u : Fin n → ℝ) (A : Mat) : Mat :=
  let D := diagonal fun i => (u i : ℂ)
  D*A-A*D

private theorem bracket_entry (u : Fin n → ℝ) (A : Mat) (i j : Fin n) :
    momentumBracket u A i j = ((u i-u j : ℝ) : ℂ)*A i j := by
  simp only [momentumBracket,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Complex.ofReal_sub]
  ring

/-- The exact joint evolution solves the sum-of-double-commutators master
equation in every matrix entry, with the normalization from the Cauchy limit. -/
theorem jumpEvolution_master_equation (t : ℝ) (r : Fin d → Fin n → ℝ) (A : Mat) (i j : Fin n) :
    let B := jumpEvolution t r A
    HasDerivAt (fun s : ℝ => jumpEvolution s r A i j)
      ((-1/8:ℂ)*∑ l, momentumBracket (r l) (momentumBracket (r l) B) i j) t := by
  let c := jointCost r i j
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-s*c)) (Real.exp (-t*c)*(-c)) t := by
    simpa only [Pi.neg_apply,id_eq,neg_one_mul] using (((hasDerivAt_id t).neg.mul_const c).exp)
  let B := jumpEvolution t r A
  let g := fun l => ((r l i-r l j:ℝ):ℂ)^2
  have hc : (c:ℂ)=(∑ l, g l)/8 := by
    simp only [c,jointCost,g,gapCost,Complex.ofReal_sum,Complex.ofReal_div,
      Complex.ofReal_pow,Complex.ofReal_ofNat,Finset.sum_div]
  have hs : (∑ l, momentumBracket (r l) (momentumBracket (r l) B) i j) =
      (∑ l, g l)*B i j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp only [bracket_entry,g,pow_two,mul_assoc]
  change HasDerivAt (fun s : ℝ => (Real.exp (-s*c):ℂ)*A i j) _ t
  rw [show (-1/8:ℂ)*(∑ l, momentumBracket (r l) (momentumBracket (r l) B) i j) =
      ((Real.exp (-t*c)*(-c):ℝ):ℂ)*A i j by
    rw [hs,Complex.ofReal_mul,Complex.ofReal_neg,hc]
    change _*((∑ l, g l)*((Real.exp (-t*c):ℂ)*A i j))=_
    ring]
  exact hd.ofReal_comp.mul_const (A i j)

#print axioms jointGaussian_symbol_positive
#print axioms gaussian_probe_sector_bounds
#print axioms jumpEvolution_add
#print axioms jointGaussian_fixed_iff
#print axioms jumpEvolution_master_equation
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
