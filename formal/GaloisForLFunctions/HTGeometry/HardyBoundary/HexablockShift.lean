import GaloisForLFunctions.HTGeometry.OperatorTheory.TetrablockAlgebra
import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.HTGeometry.SingularGaugeToeplitzHorizon

/-!
# Hexablock coordinates of the unilateral shift

The sum and difference channels of the unilateral shift recover exactly the
usual operator-valued Toeplitz fixed space. Compactness forces every such
operator to vanish. Arbitrary powers of the shift also satisfy the energy
and cross-coordinate identities of the hexablock parametrization. In the
scalar case, the coordinate channels and their adjoints have only scalar
common commutants.
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
  rw [slice_brownHalmos_iff, _root_.ContinuousLinearMap.star_eq_adjoint, adjoint_vecForward]
  exact fixed_iff_toeplitz T

/-- There are no nonzero compact operators satisfying these Brown–Halmos relations. -/
theorem hexablock_shift_compact_iff (T : VecSeq E →L[ℂ] VecSeq E) :
    (BrownHalmos (halfDiff vecForward 1) (halfSum vecForward 1)
      (halfSum vecForward 1) vecForward T ∧ IsCompactOperator T) ↔ T = 0 := by
  rw [slice_brownHalmos_iff, _root_.ContinuousLinearMap.star_eq_adjoint, adjoint_vecForward]
  constructor
  · intro h
    exact eq_zero_of_compact_fixed h.2 h.1
  · rintro rfl
    exact ⟨by simp only [mul_zero, zero_mul], isCompactOperator_zero⟩

private theorem shift_isometry :
    star (vecForward : VecSeq E →L[ℂ] VecSeq E) * vecForward = 1 := by
  rw [_root_.ContinuousLinearMap.star_eq_adjoint, adjoint_vecForward]
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

/-- The tetrablock parametrization also applies to any three shift powers. -/
theorem tetrablock_shift_powers_relations (m n r : ℕ) :
    let u : VecSeq E →L[ℂ] VecSeq E := vecForward ^ m
    let v : VecSeq E →L[ℂ] VecSeq E := vecForward ^ n
    let z : VecSeq E →L[ℂ] VecSeq E := vecForward ^ r
    (star (halfDiff u v) * halfDiff u v +
      star (Tetrablock.x₂ u v) * Tetrablock.x₂ u v = 1) ∧
    (star (Tetrablock.x₂ u v) * Tetrablock.x₃ u v z = Tetrablock.x₁ u v z) ∧
    star (Tetrablock.x₃ u v z) * Tetrablock.x₃ u v z = 1 := by
  dsimp only
  have h (k : ℕ) := isometry_pow (vecForward : VecSeq E →L[ℂ] VecSeq E) shift_isometry k
  exact ⟨Tetrablock.energy _ _ (h m) (h n),
    Tetrablock.cross _ _ _ (h m) (h n) ((Commute.refl _).pow_pow m n)
      ((Commute.refl _).pow_pow m r) ((Commute.refl _).pow_pow n r),
    Tetrablock.last_isometry _ _ _ (h m) (h n) (h r)⟩

/-- The scalar unilateral shift and its adjoint have only scalar common commutants. -/
theorem scalar_shift_adjoint_commutant_iff (T : VecSeq ℂ →L[ℂ] VecSeq ℂ) :
    (Commute T vecForward ∧ Commute T vecBack) ↔ ∃ c : ℂ, T = c • 1 := by
  constructor
  · rintro ⟨hS, hB⟩
    let e : ℕ → VecSeq ℂ := fun n => lp.single 2 n 1
    have hSe (n : ℕ) : vecForward (e n) = e (n + 1) := by
      apply lp.ext
      funext m
      cases m with
      | zero => simp [e, lp.single_apply, Pi.single_apply]
      | succ m => simp [e, lp.single_apply, Pi.single_apply]
    have hBe : vecBack (e 0) = 0 := by
      apply lp.ext
      funext m
      simp [e, lp.single_apply, Pi.single_apply]
    have hBT : vecBack (T (e 0)) = 0 := by
      calc
        vecBack (T (e 0)) = T (vecBack (e 0)) :=
          (congrArg (fun R : VecSeq ℂ →L[ℂ] VecSeq ℂ => R (e 0)) hB.eq).symm
        _ = 0 := by rw [hBe, map_zero]
    let c : ℂ := T (e 0) 0
    have hTe : T (e 0) = c • e 0 := by
      apply lp.ext
      funext m
      cases m with
      | zero => simp [c, e, lp.single_apply]
      | succ m =>
        have hm := congrArg (fun x : VecSeq ℂ => x m) hBT
        simpa [e, lp.single_apply, Pi.single_apply] using hm
    have hTen (n : ℕ) : T (e n) = c • e n := by
      induction n with
      | zero => exact hTe
      | succ n ih =>
        rw [← hSe]
        calc
          T (vecForward (e n)) = vecForward (T (e n)) :=
            congrArg (fun R : VecSeq ℂ →L[ℂ] VecSeq ℂ => R (e n)) hS.eq
          _ = c • vecForward (e n) := by rw [ih, map_smul]
    have hsingle (n : ℕ) (a : ℂ) : T (lp.single 2 n a) = c • lp.single 2 n a := by
      have he : (lp.single 2 n a : VecSeq ℂ) = a • e n := by
        apply lp.ext
        funext m
        simp [e, lp.single_apply, Pi.single_apply]
      rw [he, map_smul, hTen, smul_comm]
    refine ⟨c, ?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hs := lp.hasSum_single (p := 2) (by norm_num) x
    have h₁ := hs.map T T.continuous
    have h₂ := hs.map (c • (1 : VecSeq ℂ →L[ℂ] VecSeq ℂ))
      (c • (1 : VecSeq ℂ →L[ℂ] VecSeq ℂ)).continuous
    apply h₁.unique
    convert h₂ using 1
    funext n
    exact hsingle n (x n)
  · rintro ⟨c, rfl⟩
    exact ⟨(Commute.one_left _).smul_left c, (Commute.one_left _).smul_left c⟩

/-- The scalar hexablock slice and its adjoints act irreducibly. -/
theorem hexablock_scalar_shift_commutant_iff (T : VecSeq ℂ →L[ℂ] VecSeq ℂ) :
    ((Commute T (halfDiff vecForward 1) ∧ Commute T (halfSum vecForward 1)) ∧
      (Commute T (star (halfDiff vecForward 1)) ∧
        Commute T (star (halfSum vecForward 1)))) ↔ ∃ c : ℂ, T = c • 1 := by
  rw [slice_commutant_iff, slice_adjoint_commutant_iff,
    _root_.ContinuousLinearMap.star_eq_adjoint, adjoint_vecForward]
  exact scalar_shift_adjoint_commutant_iff T


end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.hexablock_shift_brownHalmos_iff
#print axioms GaloisForLFunctions.HTGeometry.hexablock_shift_compact_iff
#print axioms GaloisForLFunctions.HTGeometry.hexablock_shift_powers_relations

#print axioms GaloisForLFunctions.HTGeometry.tetrablock_shift_powers_relations

#print axioms GaloisForLFunctions.HTGeometry.hexablock_scalar_shift_commutant_iff
