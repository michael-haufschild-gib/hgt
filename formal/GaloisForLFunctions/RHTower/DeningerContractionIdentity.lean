import GaloisForLFunctions.RHTower.DeningerStageDeRham
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import GaloisForLFunctions.HTGeometry.AlternatingContraction

/-!
# Contraction against a closed form

Contracting a differential form against the base point and antisymmetrizing recovers the derivative
of the form, as soon as the form is closed.  This is the algebraic identity behind the homotopy
operator of the Poincaré lemma in every degree: the closedness of a form says that the alternating
sum of its derivative over an insertion of the base point telescopes.

* `deningerContractCLM` : contraction of an alternating form against a vector.
* `deningerRemoveNth_succ_cons` : removing a later entry of a tuple with a prepended entry.
* `deningerAlternatize_contract` : the antisymmetrized contraction of a closed derivative.
-/

namespace RHTower

open ContinuousAlternatingMap

section Contraction

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Removing a later entry of a tuple with a prepended entry. -/
theorem deningerRemoveNth_succ_cons {α : Type*} (x : α) (v : Fin (n + 1) → α)
    (j : Fin (n + 1)) :
    Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → α) = Fin.cons x (Fin.removeNth j v) :=
  GaloisForLFunctions.HTGeometry.removeNth_succ_cons x v j

/-- **Contraction of an alternating form against a vector**, as a continuous linear map in the
form. -/
noncomputable def deningerContractCLM (x : E) :
    (E [⋀^Fin (n + 1)]→L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) :=
  (ContinuousLinearMap.apply ℂ (E [⋀^Fin n]→L[ℂ] ℂ) x).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
      (n := n)).toContinuousLinearMap

@[simp]
theorem deningerContractCLM_apply (x : E) (A : E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (v : Fin n → E) :
    deningerContractCLM x A v = A (Fin.cons x v) := rfl

/-- **The antisymmetrized contraction of the derivative of a closed form is the derivative at the
base point.**  This is the identity that makes the homotopy operator invert the exterior derivative:
the closedness of the form, applied to the tuple with the base point prepended, splits into the term
at the base point and the antisymmetrized contraction. -/
theorem deningerAlternatize_contract (B : E →L[ℂ] (E [⋀^Fin (n + 1)]→L[ℂ] ℂ))
    (hB : alternatizeUncurryFin B = 0) (x : E) :
    alternatizeUncurryFin ((deningerContractCLM x).comp B) = B x := by
  ext v
  have hzero : alternatizeUncurryFin B (Fin.cons x v) = 0 := by
    rw [hB]
    rfl
  rw [alternatizeUncurryFin_apply] at hzero
  rw [Fin.sum_univ_succ] at hzero
  have hfirst : (-1 : ℤ) ^ ((0 : Fin (n + 2)) : ℕ) •
      (B ((Fin.cons x v : Fin (n + 2) → E) 0))
        (Fin.removeNth 0 (Fin.cons x v : Fin (n + 2) → E)) = B x v := by
    rw [Fin.removeNth_zero]
    simp
  have hrest : ∀ j : Fin (n + 1),
      (-1 : ℤ) ^ ((j.succ : Fin (n + 2)) : ℕ) •
        (B ((Fin.cons x v : Fin (n + 2) → E) j.succ))
          (Fin.removeNth j.succ (Fin.cons x v : Fin (n + 2) → E)) =
        -((-1 : ℤ) ^ (j : ℕ) • ((deningerContractCLM x).comp B) (v j) (Fin.removeNth j v)) := by
    intro j
    rw [deningerRemoveNth_succ_cons, Fin.cons_succ]
    show (-1 : ℤ) ^ ((j : ℕ) + 1) • (B (v j)) (Fin.cons x (Fin.removeNth j v)) =
      -((-1 : ℤ) ^ (j : ℕ) • (B (v j)) (Fin.cons x (Fin.removeNth j v)))
    rw [pow_succ, mul_comm, neg_mul, one_mul, neg_smul]
  rw [hfirst, Finset.sum_congr rfl fun j _ => hrest j, Finset.sum_neg_distrib] at hzero
  rw [alternatizeUncurryFin_apply]
  rw [add_neg_eq_zero] at hzero
  exact hzero.symm

end Contraction

end RHTower

namespace RHTower

section CartanFormula

open ContinuousAlternatingMap

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The Cartan formula for a constant direction**: antisymmetrizing the contraction of a
derivative is the derivative in that direction minus the contraction of the antisymmetrization.  For
a closed form the last term vanishes, which is the contraction identity used by the homotopy
operator; in general it is the identity that lets a period average remove the derivative term. -/
theorem deningerCartan_contract (B : E →L[ℂ] (E [⋀^Fin (n + 1)]→L[ℂ] ℂ)) (x : E) :
    alternatizeUncurryFin ((deningerContractCLM x).comp B) =
      B x - deningerContractCLM x (alternatizeUncurryFin B) := by
  ext v
  have hsplit : alternatizeUncurryFin B (Fin.cons x v) =
      B x v - alternatizeUncurryFin ((deningerContractCLM x).comp B) v := by
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
          -((-1 : ℤ) ^ (j : ℕ) • ((deningerContractCLM x).comp B) (v j) (Fin.removeNth j v)) := by
      intro j
      rw [deningerRemoveNth_succ_cons, Fin.cons_succ]
      show (-1 : ℤ) ^ ((j : ℕ) + 1) • (B (v j)) (Fin.cons x (Fin.removeNth j v)) =
        -((-1 : ℤ) ^ (j : ℕ) • (B (v j)) (Fin.cons x (Fin.removeNth j v)))
      rw [pow_succ, mul_comm, neg_mul, one_mul, neg_smul]
    rw [hfirst, Finset.sum_congr rfl fun j _ => hrest j, Finset.sum_neg_distrib,
      alternatizeUncurryFin_apply]
    ring
  show alternatizeUncurryFin ((deningerContractCLM x).comp B) v =
    B x v - (alternatizeUncurryFin B) (Fin.cons x v)
  rw [hsplit]
  ring

end CartanFormula

end RHTower
