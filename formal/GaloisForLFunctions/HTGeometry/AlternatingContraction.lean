import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.RCLike.Basic

/-!
# Contraction of alternating forms and the Cartan formula

Contracting a continuous alternating form against a fixed vector and antisymmetrizing the derivative
splits the derivative into the directional derivative in that vector and the contraction of the
exterior derivative.  This is the Cartan formula for a constant vector field, in the form used to
compare a form with its average along the flow of that field.  A form all of whose contractions
against the coordinate vectors vanish is zero.

* `contractCLM` : contraction of an alternating form against a vector.
* `cartan_contract` : the Cartan formula for a constant direction.
* `extDeriv_contract` : the exterior derivative of a contracted form.
* `form_eq_zero_of_contract` : a form with vanishing coordinate contractions is zero.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousAlternatingMap

section Contraction

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Removing a later entry of a tuple with a prepended entry. -/
theorem removeNth_succ_cons {α : Type*} (x : α) (v : Fin (n + 1) → α) (j : Fin (n + 1)) :
    Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → α) = Fin.cons x (Fin.removeNth j v) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      show (Fin.cons x v : Fin (n + 2) → α) (j.succ.succAbove 0) = x
      rw [Fin.succ_succAbove_zero]
      exact Fin.cons_zero _ _
  | succ k =>
      show (Fin.cons x v : Fin (n + 2) → α) (j.succ.succAbove k.succ) = v (j.succAbove k)
      rw [Fin.succ_succAbove_succ]
      exact Fin.cons_succ _ _ _

/-- **Contraction of an alternating form against a vector**, as a continuous linear map in the
form. -/
noncomputable def contractCLM (x : E) :
    (E [⋀^Fin (n + 1)]→L[𝕜] 𝕜) →L[𝕜] (E [⋀^Fin n]→L[𝕜] 𝕜) :=
  (ContinuousLinearMap.apply 𝕜 (E [⋀^Fin n]→L[𝕜] 𝕜) x).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := 𝕜) (E := E) (F := 𝕜)
      (n := n)).toContinuousLinearMap

@[simp]
theorem contractCLM_apply (x : E) (A : E [⋀^Fin (n + 1)]→L[𝕜] 𝕜) (v : Fin n → E) :
    contractCLM (𝕜 := 𝕜) x A v = A (Fin.cons x v) := rfl

theorem contractCLM_add (x y : E) (A : E [⋀^Fin (n + 1)]→L[𝕜] 𝕜) :
    contractCLM (𝕜 := 𝕜) (x + y) A = contractCLM x A + contractCLM y A :=
  map_add (ContinuousAlternatingMap.curryLeft A) x y

theorem contractCLM_smul (c : 𝕜) (x : E) (A : E [⋀^Fin (n + 1)]→L[𝕜] 𝕜) :
    contractCLM (𝕜 := 𝕜) (c • x) A = c • contractCLM x A :=
  map_smul (ContinuousAlternatingMap.curryLeft A) c x

/-- **The Cartan formula for a constant direction**: antisymmetrizing the contraction of a
derivative is the derivative in that direction minus the contraction of the antisymmetrization.  For
a closed form the last term vanishes, which is what lets a period average remove the derivative
term. -/
theorem cartan_contract (B : E →L[𝕜] (E [⋀^Fin (n + 1)]→L[𝕜] 𝕜)) (x : E) :
    alternatizeUncurryFin ((contractCLM (𝕜 := 𝕜) x).comp B) =
      B x - contractCLM x (alternatizeUncurryFin B) := by
  ext v
  have hsplit : alternatizeUncurryFin B (Fin.cons x v) =
      B x v - alternatizeUncurryFin ((contractCLM (𝕜 := 𝕜) x).comp B) v := by
    rw [alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    have hfirst : (-1 : ℤ) ^ ((0 : Fin (n + 2)) : ℕ) •
        (B ((Fin.cons x v : Fin (n + 2) → E) 0))
          (Fin.removeNth 0 (Fin.cons x v : Fin (n + 2) → E)) = B x v := by
      rw [Fin.removeNth_zero]
      simp
    have hrest : ∀ j : Fin (n + 1),
        (-1 : ℤ) ^ ((j.succ : Fin (n + 2)) : ℕ) •
          (B ((Fin.cons x v : Fin (n + 2) → E) j.succ))
            (Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → E)) =
          -((-1 : ℤ) ^ (j : ℕ) • ((contractCLM (𝕜 := 𝕜) x).comp B) (v j) (Fin.removeNth j v)) := by
      intro j
      rw [removeNth_succ_cons, Fin.cons_succ]
      show (-1 : ℤ) ^ ((j : ℕ) + 1) • (B (v j)) (Fin.cons x (Fin.removeNth j v)) =
        -((-1 : ℤ) ^ (j : ℕ) • (B (v j)) (Fin.cons x (Fin.removeNth j v)))
      rw [pow_succ, mul_comm, neg_mul, one_mul, neg_smul]
    rw [hfirst, Finset.sum_congr rfl fun j _ => hrest j, Finset.sum_neg_distrib,
      alternatizeUncurryFin_apply]
    ring
  show alternatizeUncurryFin ((contractCLM (𝕜 := 𝕜) x).comp B) v =
    B x v - (alternatizeUncurryFin B) (Fin.cons x v)
  rw [hsplit]
  ring

/-- **The exterior derivative of a contracted form** is the antisymmetrized contraction of the
derivative. -/
theorem extDeriv_contract {β : E → E [⋀^Fin (n + 1)]→L[𝕜] 𝕜} {w : E}
    (hdiff : DifferentiableAt 𝕜 β w) (x : E) :
    extDeriv (fun y => contractCLM (𝕜 := 𝕜) x (β y)) w =
      alternatizeUncurryFin ((contractCLM (𝕜 := 𝕜) x).comp (fderiv 𝕜 β w)) := by
  have hfd : fderiv 𝕜 (fun y => contractCLM (𝕜 := 𝕜) x (β y)) w =
      (contractCLM (𝕜 := 𝕜) x).comp (fderiv 𝕜 β w) := by
    have h := ((contractCLM (𝕜 := 𝕜) (n := n) x).hasFDerivAt).comp w hdiff.hasFDerivAt
    exact h.fderiv
  rw [extDeriv, hfd]

end Contraction

section CoordinateContraction

variable {𝕜 : Type*} [RCLike 𝕜] {n r : ℕ}

/-- **A form whose contractions against the coordinate vectors vanish is zero.** -/
theorem form_eq_zero_of_contract {α : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜}
    (h : ∀ j : Fin r, contractCLM (𝕜 := 𝕜) (Pi.single j (1 : 𝕜) : Fin r → 𝕜) α = 0) : α = 0 := by
  classical
  ext v
  have hbasis : ∀ j : Fin r,
      (fun l => if j = l then (1 : 𝕜) else 0) = (Pi.single j (1 : 𝕜) : Fin r → 𝕜) := by
    intro j
    funext l
    rw [Pi.single_apply]
    by_cases hl : j = l
    · rw [if_pos hl, if_pos hl.symm]
    · rw [if_neg hl, if_neg (Ne.symm hl)]
  have hcontract : contractCLM (𝕜 := 𝕜) (n := n) (v 0) α = 0 := by
    conv_lhs =>
      rw [show v 0 = ∑ j, (v 0) j • (fun l => if j = l then (1 : 𝕜) else 0) from
        pi_eq_sum_univ (v 0)]
    have hsum : ∀ (t : Finset (Fin r)),
        contractCLM (𝕜 := 𝕜) (n := n)
            (∑ j ∈ t, (v 0) j • (fun l => if j = l then (1 : 𝕜) else 0)) α = 0 := by
      intro t
      induction t using Finset.induction with
      | empty =>
          rw [Finset.sum_empty]
          ext u
          show α (Fin.cons (0 : Fin r → 𝕜) u) = (0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) u
          rw [show ((0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) u) = (0 : 𝕜) from rfl]
          exact ContinuousAlternatingMap.map_coord_zero α 0 (Fin.cons_zero _ _)
      | insert a t ha ih =>
          rw [Finset.sum_insert ha, contractCLM_add, ih, add_zero, contractCLM_smul, hbasis a, h a]
          ext u
          show (v 0 a) • ((0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) u) =
            (0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) u
          rw [show ((0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) u) = (0 : 𝕜) from rfl, smul_eq_mul,
            mul_zero]
    exact hsum Finset.univ
  have hval : α v = contractCLM (𝕜 := 𝕜) (v 0) α (Fin.tail v) := by
    show α v = α (Fin.cons (v 0) (Fin.tail v))
    rw [Fin.cons_self_tail]
  rw [hval, hcontract]
  rfl

end CoordinateContraction

end GaloisForLFunctions.HTGeometry
