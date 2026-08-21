import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.GroupTheory.Perm.Fin
import GaloisForLFunctions.HTGeometry.IteratedFDerivSymmetric

/-!
# A symmetric multilinear map is determined by its diagonal

If a continuous multilinear map `M` on `Fin k` slots is invariant under permutations of its
arguments and vanishes on the diagonal, then it vanishes identically.

The proof is an induction on `k`.  The diagonal restriction `u ↦ M (u, …, u)` is the composition
of `M` with the diagonal embedding, so its derivative at `v` sends `w` to
`∑ i, M (update (v, …, v) i w)`; by symmetry all `k` summands agree, so the vanishing of the
diagonal forces `M (w, v, …, v) = 0`.  Currying the first slot then produces a symmetric
`(k-1)`-linear map with vanishing diagonal.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The diagonal embedding as a continuous linear map. -/
noncomputable def diagCLM (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    E →L[ℝ] (Fin k → E) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ E

@[simp] theorem diagCLM_apply (k : ℕ) (u : E) : diagCLM E k u = fun _ => u := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem update_diag_comp_swap (k : ℕ) (v w : E) (i : Fin (k + 1)) :
    Function.update (fun _ : Fin (k + 1) => v) i w
      = (Function.update (fun _ : Fin (k + 1) => v) 0 w) ∘ (Equiv.swap 0 i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Equiv.swap_apply_right]
  · have h1 : Equiv.swap (0 : Fin (k + 1)) i j ≠ 0 := by
      intro h
      have := congrArg (Equiv.swap (0 : Fin (k + 1)) i) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact hj this
    simp [hj, h1]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cons_eq_update_diag (k : ℕ) (v w : E) :
    (Fin.cons w (fun _ : Fin k => v) : Fin (k + 1) → E)
      = Function.update (fun _ : Fin (k + 1) => v) 0 w := by
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ i => simp [Fin.succ_ne_zero i]

/-- **A symmetric continuous multilinear map with vanishing diagonal is zero.** -/
theorem continuousMultilinearMap_eq_zero_of_diagonal :
    ∀ (k : ℕ) (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F),
      (∀ (σ : Equiv.Perm (Fin k)) (m : Fin k → E), M (m ∘ σ) = M m) →
      (∀ u : E, M (fun _ => u) = 0) → M = 0 := by
  intro k
  induction k with
  | zero =>
      intro M _ hdiag
      ext m
      have hm : m = fun _ : Fin 0 => (0 : E) := by
        funext i
        exact i.elim0
      rw [hm, hdiag 0]
      simp
  | succ k ih =>
      intro M hsym hdiag
      -- the derivative of the diagonal restriction vanishes
      have hstep : ∀ v w : E, M (Function.update (fun _ : Fin (k + 1) => v) 0 w) = 0 := by
        intro v w
        have hΦ : (fun u : E => M (fun _ : Fin (k + 1) => u)) = fun _ : E => (0 : F) := by
          funext u
          exact hdiag u
        have hd1 : HasFDerivAt (fun u : E => M (fun _ : Fin (k + 1) => u)) (0 : E →L[ℝ] F) v := by
          rw [hΦ]
          exact hasFDerivAt_const _ _
        have hd2 : HasFDerivAt (fun u : E => M (fun _ : Fin (k + 1) => u))
            ((M.linearDeriv (fun _ : Fin (k + 1) => v)).comp (diagCLM E (k + 1))) v :=
          (M.hasFDerivAt (fun _ : Fin (k + 1) => v)).comp v
            ((diagCLM E (k + 1)).hasFDerivAt)
        have heq := hd1.unique hd2
        have hsum : ∑ i : Fin (k + 1), M (Function.update (fun _ : Fin (k + 1) => v) i w) = 0 := by
          have h := congrArg (fun L : E →L[ℝ] F => L w) heq
          simp only [zero_apply, ContinuousLinearMap.coe_comp,
            Function.comp_apply, diagCLM_apply,
            ContinuousMultilinearMap.linearDeriv_apply] at h
          exact h.symm
        have hall : ∀ i : Fin (k + 1),
            M (Function.update (fun _ : Fin (k + 1) => v) i w)
              = M (Function.update (fun _ : Fin (k + 1) => v) 0 w) := by
          intro i
          rw [update_diag_comp_swap k v w i]
          exact hsym (Equiv.swap 0 i) _
        rw [Finset.sum_congr rfl fun i _ => hall i, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin] at hsum
        have hcast : (((k + 1 : ℕ) : ℝ)) • M (Function.update (fun _ : Fin (k + 1) => v) 0 w)
            = (k + 1) • M (Function.update (fun _ : Fin (k + 1) => v) 0 w) :=
          Nat.cast_smul_eq_nsmul ℝ _ _
        rw [← hcast] at hsum
        have hne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
        exact (smul_eq_zero.mp hsum).resolve_left hne
      -- curry off the first slot
      have hcurry : ∀ w : E, M.curryLeft w = 0 := by
        intro w
        refine ih (M.curryLeft w) ?_ ?_
        · intro σ u
          set τ : Equiv.Perm (Fin (k + 1)) := Equiv.Perm.decomposeFin.symm (0, σ) with hτ
          have hcons : (Fin.cons w (u ∘ σ) : Fin (k + 1) → E)
              = (Fin.cons w u : Fin (k + 1) → E) ∘ τ := by
            funext j
            induction j using Fin.cases with
            | zero => simp [hτ, Equiv.Perm.decomposeFin_symm_apply_zero]
            | succ i =>
                simp [hτ, Equiv.Perm.decomposeFin_symm_apply_succ]
          simp only [ContinuousMultilinearMap.curryLeft_apply]
          rw [hcons]
          exact hsym τ _
        · intro v
          simp only [ContinuousMultilinearMap.curryLeft_apply]
          rw [cons_eq_update_diag k v w]
          exact hstep v w
      ext m
      have h1 := hcurry (m 0)
      have h2 : M (Fin.cons (m 0) (Fin.tail m)) = 0 := by
        have := congrArg (fun L => L (Fin.tail m)) h1
        simpa [ContinuousMultilinearMap.curryLeft_apply] using this
      rw [Fin.cons_self_tail] at h2
      simpa using h2


/-! ### Consequence for iterated derivatives -/

/-- **Some directional derivative of order `k` detects a nonzero `k`-th derivative.**  For a `C^k`
map the `k`-th derivative is symmetric, so it is determined by its diagonal; hence if it does not
vanish, then neither does `t ↦ f (x + t v)` differentiated `k` times, for some direction `v`. -/
theorem exists_diagonal_ne_zero_of_iteratedFDeriv_ne_zero {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {f : E → F}
    {x : E} (hf : ContDiffAt ℝ ((k : ℕ)) f x) (h : iteratedFDeriv ℝ k f x ≠ 0) :
    ∃ v : E, iteratedFDeriv ℝ k f x (fun _ => v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (continuousMultilinearMap_eq_zero_of_diagonal k (iteratedFDeriv ℝ k f x)
    (fun σ m => iteratedFDeriv_comp_perm hf σ m) hcon)

end GaloisForLFunctions.HTGeometry
