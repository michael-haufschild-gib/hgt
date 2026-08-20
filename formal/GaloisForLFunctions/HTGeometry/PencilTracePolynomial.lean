/-
# The power traces of a linear operator pencil are homogeneous forms

Expanding a power of a linear combination of operators over ordered words shows that the `k`-th
power trace of a linear pencil is a finite combination of products of `k` coordinate forms, hence --
by polarization -- a combination of `k`-th powers of linear forms.  That is the residual-target
hypothesis the several-variable micro-spectrum construction consumes.

Main results:
* `opWord`, `pow_sum_smul_eq_sum_word` — **the ordered-word expansion of a pencil power**.
* `opTrace_finsetSum` — the trace is additive on finite families of trace-class operators.
* `opTrace_pow_sum_smul` — **the power trace as a coefficient sum over words**.
* `pencilTraceForm_mem_span` — **the power trace of a pencil lies in the span of `k`-th powers**.
-/
import GaloisForLFunctions.HTGeometry.PencilMomentRealization
import GaloisForLFunctions.HTGeometry.OperatorDeterminantSufficiency
import GaloisForLFunctions.HTGeometry.OperatorDeterminantScaling

open Finset ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ordered operator word attached to a multi-index. -/
def opWord {d k : ℕ} (B : Fin d → (H →L[ℂ] H)) (f : Fin k → Fin d) : H →L[ℂ] H :=
  (List.ofFn fun r => B (f r)).prod

omit [CompleteSpace H] in
theorem opWord_zero {d : ℕ} (B : Fin d → (H →L[ℂ] H)) (f : Fin 0 → Fin d) :
    opWord B f = 1 := by
  rw [opWord]
  simp

omit [CompleteSpace H] in
theorem opWord_succ {d k : ℕ} (B : Fin d → (H →L[ℂ] H)) (f : Fin (k + 1) → Fin d) :
    opWord B f = B (f 0) * opWord B (Fin.tail f) := by
  rw [opWord, opWord, List.ofFn_succ, List.prod_cons]
  rfl

omit [CompleteSpace H] in
/-- **The ordered-word expansion of a pencil power.** -/
theorem pow_pencilOperator_eq_sum_word {d : ℕ} (B : Fin d → (H →L[ℂ] H)) (c : Fin d → ℂ) :
    ∀ k : ℕ, (pencilOperator B c) ^ k
      = ∑ f : Fin k → Fin d, (∏ r, c (f r)) • opWord B f := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, Fintype.sum_unique]
      simp [opWord_zero]
  | succ k ih =>
      have hstep : (pencilOperator B c) ^ (k + 1)
          = ∑ j, ∑ g : Fin k → Fin d, (c j * ∏ r, c (g r)) • (B j * opWord B g) := by
        rw [pow_succ', ih, pencilOperator, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [smul_mul_smul_comm]
      have hequiv : (∑ f : Fin (k + 1) → Fin d, (∏ r, c (f r)) • opWord B f)
          = ∑ q : Fin d × (Fin k → Fin d),
              (c q.1 * ∏ r, c (q.2 r)) • (B q.1 * opWord B q.2) := by
        refine Fintype.sum_equiv
          ({ toFun := fun f : Fin (k + 1) → Fin d => (f 0, Fin.tail f)
             invFun := fun q => Fin.cons q.1 q.2
             left_inv := fun f => by simp
             right_inv := fun q => by simp } :
              (Fin (k + 1) → Fin d) ≃ Fin d × (Fin k → Fin d)) _ _ fun f => ?_
        show (∏ r, c (f r)) • opWord B f
          = (c (f 0) * ∏ r, c (Fin.tail f r)) • (B (f 0) * opWord B (Fin.tail f))
        rw [← opWord_succ, Fin.prod_univ_succ]
        rfl
      rw [Fintype.sum_prod_type] at hequiv
      rw [hstep]
      exact hequiv.symm

/-! ## Finite additivity of the trace -/

omit [CompleteSpace H] in
theorem memSchattenClass_one_finsetSum {ι : Type*} (s : Finset ι) (X : ι → (H →L[ℂ] H))
    (hX : ∀ i ∈ s, MemSchattenClass 1 (X i)) : MemSchattenClass 1 (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using memSchattenClass_of_hasRankLE one_pos (hasRankLE_zero (H := H) 0)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine memSchattenClass_add one_pos (hX a (Finset.mem_insert_self a s)) ?_
      exact ih fun i hi => hX i (Finset.mem_insert_of_mem hi)

theorem opTrace_finsetSum {ι : Type*} (s : Finset ι) (X : ι → (H →L[ℂ] H))
    (hX : ∀ i ∈ s, MemSchattenClass 1 (X i)) :
    opTrace (∑ i ∈ s, X i) = ∑ i ∈ s, opTrace (X i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [opTrace]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        opTrace_add_of_memSchattenClass_one (hX a (Finset.mem_insert_self a s))
          (memSchattenClass_one_finsetSum s X fun i hi => hX i (Finset.mem_insert_of_mem hi))]
      rw [ih fun i hi => hX i (Finset.mem_insert_of_mem hi)]

/-! ## Rank of a word -/

omit [CompleteSpace H] in
theorem hasRankLE_opWord {d k N : ℕ} {B : Fin d → (H →L[ℂ] H)}
    (hB : ∀ j, HasRankLE (B j) N) (f : Fin (k + 1) → Fin d) :
    HasRankLE (opWord B f) N := by
  obtain ⟨W, hW, hle, hmem⟩ := hB (f 0)
  refine ⟨W, hW, hle, fun x => ?_⟩
  rw [opWord_succ]
  exact hmem _

omit [CompleteSpace H] in
theorem HasRankLE.smul {X : H →L[ℂ] H} {N : ℕ} (hX : HasRankLE X N) (a : ℂ) :
    HasRankLE (a • X) N := by
  obtain ⟨W, hW, hle, hmem⟩ := hX
  exact ⟨W, hW, hle, fun x => by
    rw [smul_apply]
    exact Submodule.smul_mem _ _ (hmem x)⟩

/-- **The power trace of a pencil as a coefficient sum over ordered words.** -/
theorem opTrace_pow_pencilOperator {d k N : ℕ} {B : Fin d → (H →L[ℂ] H)}
    (hB : ∀ j, HasRankLE (B j) N) (c : Fin d → ℂ) :
    opTrace ((pencilOperator B c) ^ (k + 1))
      = ∑ f : Fin (k + 1) → Fin d, (∏ r, c (f r)) * opTrace (opWord B f) := by
  rw [pow_pencilOperator_eq_sum_word]
  rw [opTrace_finsetSum _ _ (fun f _ =>
    memSchattenClass_one_of_hasRankLE ((hasRankLE_opWord hB f).smul (∏ r, c (f r))))]
  exact Finset.sum_congr rfl fun f _ => opTrace_smul _ _

/-- **The power trace of a linear pencil lies in the span of `k`-th powers of linear forms.**
This is the residual-target hypothesis the several-variable micro-spectrum construction consumes. -/
theorem pencilTraceForm_mem_span {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {d k N : ℕ} {B : Fin d → (H →L[ℂ] H)} (hB : ∀ j, HasRankLE (B j) N)
    (coord : Fin d → (V →L[ℂ] ℂ)) :
    (fun v => opTrace ((pencilOperator B (fun j => coord j v)) ^ (k + 1)))
      ∈ Submodule.span ℂ (clmPowSet V (k + 1)) := by
  have hfun : (fun v => opTrace ((pencilOperator B (fun j => coord j v)) ^ (k + 1)))
      = ∑ f : Fin (k + 1) → Fin d,
          opTrace (opWord B f) • (fun v : V => ∏ r, coord (f r) v) := by
    funext v
    rw [opTrace_pow_pencilOperator hB, Finset.sum_apply]
    refine Finset.sum_congr rfl fun f _ => ?_
    show (∏ r, coord (f r) v) * opTrace (opWord B f)
      = opTrace (opWord B f) • ∏ r, coord (f r) v
    rw [smul_eq_mul, mul_comm]
  rw [hfun]
  refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
  exact prod_clm_mem_span_clmPow (fun r => coord (f r))

end

end GaloisForLFunctions.HTGeometry
