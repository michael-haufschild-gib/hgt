import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginLocalParameters
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalGraphParameterIdeal

/-! The transverse coordinate differences generate the origin ideal
in the local ring. -/

noncomputable section

open GlobalTheory.WH
open scoped Matrix

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B" => rB k E x {0}
variable (e : OriginFibrePoint k E x)
local notation "R" => loc B (Subtype.val e)
local notation "ε" => locEval B (Subtype.val e)
local notation "t" => localOriginCoordinate e

/-- Cleared equations for a function give its local coordinate row,
with the prescribed residue after dividing the denominator. -/
theorem exists_localRows_of_cleared (z : Fin d → E) (M : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : B) (g : Fin d → B), e.1 c ≠ 0 ∧
      (c : E) * z m = ∑ l, (g l : E) * (t l : E) ∧
      ∀ l, e.1 (g l) = e.1 c * M m l) :
    ∃ A : Matrix (Fin d) (Fin d) R, A.map ε = M ∧
      ∀ m, ((A *ᵥ t) m : E) = z m := by
  let i : B →ₐ[k] R := Subalgebra.inclusion (le_loc B e.1)
  have hi (a : B) : ε (i a) = e.1 a := locEval_inclusion B e.1 a
  choose c g hc he hM using hrow
  have hu (m : Fin d) : IsUnit (i (c m)) :=
    isUnit_loc_of_eval_ne_zero B e.1 _ ((locEval_inclusion B e.1 (c m)).symm ▸ hc m)
  let u (m : Fin d) := (hu m).unit
  let A : Matrix (Fin d) (Fin d) R := fun m l => (↑(u m)⁻¹ : R) * i (g m l)
  have hmul (m l : Fin d) : i (c m) * A m l = i (g m l) := by
    calc
      i (c m) * A m l = (↑(u m) : R) * A m l :=
        congrArg (fun b => b * A m l) (hu m).unit_spec.symm
      _ = i (g m l) := by
        change (↑(u m) : R) * ((↑(u m)⁻¹ : R) * i (g m l)) = _
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  refine ⟨A, ?_, ?_⟩
  · ext m l
    change ε (A m l) = M m l
    apply mul_left_cancel₀ (hc m)
    have hh := congrArg ε (hmul m l)
    rw [map_mul, hi, hi, hM] at hh
    exact hh
  · intro m
    have hc₀ : (c m : E) ≠ 0 := by
      intro hz
      exact hc m (by rw [show c m = 0 from Subtype.ext hz, map_zero])
    apply mul_left_cancel₀ hc₀
    change (c m : E) * (R).val ((A *ᵥ t) m) = _
    rw [he, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← mul_assoc]
    exact congrArg (fun y : R => (y : E) * (t l : E)) (hmul m l)

/-- If the difference matrix is invertible on the residue field,
the local coordinate differences generate the evaluation kernel. -/
theorem IsFinCover.span_localDifferenceCoordinates (h : IsFinCover k E x)
    [IsReduced (B ⧸ originIdeal k E x)]
    {M : Matrix (Fin d) (Fin d) k} (A : Matrix (Fin d) (Fin d) R)
    (hA : A.map ε = M) (hM : (1 - M).det ≠ 0)
    (r : Fin d → R) (hr : ∀ j, (r j : E) = (t j : E) - ((A *ᵥ t) j : E)) :
    Ideal.span (Set.range r) = RingHom.ker (ε).toRingHom := by
  have he : ε ((1 - A).det) = (1 - M).det := by
    calc
      _ = ((1 - A).map ε).det := RingHom.map_det (ε).toRingHom _
      _ = _ := by
        rw [← hA]
        congr 1
        ext i j
        simp [Matrix.one_apply, apply_ite]
  have hu : IsUnit (1 - A).det := isUnit_loc_of_eval_ne_zero B e.1 _ (he.symm ▸ hM)
  have hm : r = (1 - A) *ᵥ t := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    funext j
    apply Subtype.ext
    exact hr j
  rw [hm, span_range_mulVec_eq _ hu, h.span_localOriginCoordinates e]

end GlobalTheory.PD
