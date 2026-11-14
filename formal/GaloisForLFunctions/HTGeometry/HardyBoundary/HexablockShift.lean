import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.HTGeometry.SingularGaugeToeplitzHorizon

/-!
# Hexablock coordinates of the unilateral shift

The sum and difference channels of the unilateral shift recover exactly the
usual operator-valued Toeplitz fixed space. Compactness forces every such
operator to vanish. Arbitrary powers of the shift also satisfy the energy
and cross-coordinate identities of the hexablock parametrization.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open ContinuousLinearMap Hexablock
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The unilateral shift's sum/difference tuple satisfies exactly the block Toeplitz condition. -/
theorem hexablock_shift_brownHalmos_iff (T : VecSeq E →L[ℂ] VecSeq E) :
    BrownHalmos (halfDiff vecForward 1) (halfSum vecForward 1)
      (halfSum vecForward 1) vecForward T ↔
    ∀ n m (x y : E),
      ⟪lp.single 2 (n + 1) x, T (lp.single 2 (m + 1) y)⟫_ℂ =
        ⟪lp.single 2 n x, T (lp.single 2 m y)⟫_ℂ := by
  rw [slice_brownHalmos_iff, star_eq_adjoint, adjoint_vecForward]
  exact fixed_iff_toeplitz T

/-- There are no nonzero compact operators satisfying these Brown–Halmos relations. -/
theorem hexablock_shift_compact_iff (T : VecSeq E →L[ℂ] VecSeq E) :
    (BrownHalmos (halfDiff vecForward 1) (halfSum vecForward 1)
      (halfSum vecForward 1) vecForward T ∧ IsCompactOperator T) ↔ T = 0 := by
  rw [slice_brownHalmos_iff, star_eq_adjoint, adjoint_vecForward]
  constructor
  · intro h
    exact eq_zero_of_compact_fixed h.2 h.1
  · rintro rfl
    exact ⟨by simp only [mul_zero, zero_mul], isCompactOperator_zero⟩

private theorem shift_isometry :
    star (vecForward : VecSeq E →L[ℂ] VecSeq E) * vecForward = 1 := by
  rw [star_eq_adjoint, adjoint_vecForward]
  exact vecBack_comp_vecForward

/-- Four independently chosen shift powers give both energy partitions and the cross identity. -/
theorem hexablock_shift_powers_relations (m n r s : ℕ) :
    let u : VecSeq E →L[ℂ] VecSeq E := vecForward ^ m
    let v : VecSeq E →L[ℂ] VecSeq E := vecForward ^ n
    let w : VecSeq E →L[ℂ] VecSeq E := vecForward ^ r
    let z : VecSeq E →L[ℂ] VecSeq E := vecForward ^ s
    (star (a u w) * a u w + star (x₁ u v) * x₁ u v = 1) ∧
    (star (a u w) * a u w + star (x₂ u w z) * x₂ u w z = 1) ∧
    star (x₃ u v w z) * x₃ u v w z = 1 ∧
    star (x₁ u v) * x₃ u v w z = x₂ u w z := by
  dsimp only
  have h (k : ℕ) := isometry_pow (vecForward : VecSeq E →L[ℂ] VecSeq E) shift_isometry k
  obtain ⟨h₁, h₂, h₃⟩ := energy _ _ _ _ (h m) (h n) (h r) (h s)
  exact ⟨h₁, h₂, h₃, cross _ _ _ _ (h m) (h n)
    ((Commute.refl _).pow_pow m n) ((Commute.refl _).pow_pow m r)
    ((Commute.refl _).pow_pow m s)⟩

end GaloisForLFunctions.HTGeometry
