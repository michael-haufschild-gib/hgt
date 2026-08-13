import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Generalized Laplace containment for determinantal ideals

For a matrix over an arbitrary commutative ring, every `(r+s)`-minor is a signed sum of
products of an `r`-minor and an `s`-minor.  Consequently the ideal of `(r+s)`-minors is
contained in the product of the two smaller determinantal ideals, and the ideal of
`n*k`-minors is contained in the `k`-th power of the ideal of `n`-minors.

The proof uses the exterior product `AlternatingMap.domCoprod`.  It does not divide by a
factorial and therefore remains valid with torsion and nilpotents.
-/

namespace RHTower

noncomputable section

open scoped TensorProduct

open AlternatingMap

variable {R : Type*} [CommRing R]

/-- Restriction of a row vector on a sum to its left coordinates. -/
def deningerLaplaceLeftProj (r s : ℕ) :
    (Fin r ⊕ Fin s → R) →ₗ[R] (Fin r → R) where
  toFun v i := v (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of a row vector on a sum to its right coordinates. -/
def deningerLaplaceRightProj (r s : ℕ) :
    (Fin r ⊕ Fin s → R) →ₗ[R] (Fin s → R) where
  toFun v i := v (Sum.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The determinant formed from the left block of columns. -/
def deningerLaplaceLeftMinor (r s : ℕ) :
    (Fin r ⊕ Fin s → R) [⋀^Fin r]→ₗ[R] R :=
  Matrix.detRowAlternating.compLinearMap (deningerLaplaceLeftProj r s)

/-- The determinant formed from the right block of columns. -/
def deningerLaplaceRightMinor (r s : ℕ) :
    (Fin r ⊕ Fin s → R) [⋀^Fin s]→ₗ[R] R :=
  Matrix.detRowAlternating.compLinearMap (deningerLaplaceRightProj r s)

/-- Exterior product of the left and right minor maps, followed by multiplication. -/
def deningerBlockLaplace (r s : ℕ) :
    (Fin r ⊕ Fin s → R) [⋀^Fin r ⊕ Fin s]→ₗ[R] R :=
  (LinearMap.mul' R R).compAlternatingMap
    ((deningerLaplaceLeftMinor r s).domCoprod (deningerLaplaceRightMinor r s))

/-- Generalized Laplace expansion as an equality of alternating maps. -/
theorem deningerBlockLaplace_eq_det (r s : ℕ) :
    deningerBlockLaplace (R := R) r s = Matrix.detRowAlternating := by
  rw [(deningerBlockLaplace (R := R) r s).eq_smul_basis_det
    (Pi.basisFun R (Fin r ⊕ Fin s))]
  rw [Pi.basisFun_det]
  suffices deningerBlockLaplace (R := R) r s
      (Pi.basisFun R (Fin r ⊕ Fin s)) = 1 by
    rw [this, one_smul]
  change (LinearMap.mul' R R)
      (((deningerLaplaceLeftMinor (R := R) r s).domCoprod
        (deningerLaplaceRightMinor (R := R) r s)
        (Pi.basisFun R (Fin r ⊕ Fin s)))) = 1
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  let q0 : Equiv.Perm.ModSumCongr (Fin r) (Fin s) :=
    Quotient.mk'' (1 : Equiv.Perm (Fin r ⊕ Fin s))
  have hother : ∀ q, q ≠ q0 →
      (LinearMap.mul' R R)
          ((AlternatingMap.domCoprod.summand
            (deningerLaplaceLeftMinor (R := R) r s)
            (deningerLaplaceRightMinor (R := R) r s) q)
              (Pi.basisFun R (Fin r ⊕ Fin s))) = 0 := by
    intro q hq
    induction q using Quotient.inductionOn' with
    | h σ =>
      have hcross : ∃ i : Fin r, ∃ j : Fin s, σ (Sum.inl i) = Sum.inr j := by
        by_contra h
        push Not at h
        have hmaps : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
          rintro _ ⟨i, rfl⟩
          rcases hσ : σ (Sum.inl i) with j | j
          · exact ⟨j, rfl⟩
          · exact (h i j hσ).elim
        have hmem := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
        apply hq
        apply (QuotientGroup.eq).2
        simpa using
          (Equiv.Perm.sumCongrHom (Fin r) (Fin s)).range.inv_mem hmem
      obtain ⟨i, j, hij⟩ := hcross
      have hz : (deningerLaplaceLeftMinor (R := R) r s)
          (fun a => Pi.basisFun R (Fin r ⊕ Fin s) (σ (Sum.inl a))) = 0 := by
        rw [deningerLaplaceLeftMinor, AlternatingMap.compLinearMap_apply]
        apply AlternatingMap.map_coord_zero _ i
        funext x
        simp [deningerLaplaceLeftProj, Pi.basisFun_apply, hij]
      rw [AlternatingMap.domCoprod.summand_mk'']
      simp only [_root_.smul_apply, MultilinearMap.domDomCongr_apply,
        MultilinearMap.domCoprod_apply]
      let a := (deningerLaplaceLeftMinor (R := R) r s)
        (fun x => Pi.basisFun R (Fin r ⊕ Fin s) (σ (Sum.inl x)))
      let b := (deningerLaplaceRightMinor (R := R) r s)
        (fun x => Pi.basisFun R (Fin r ⊕ Fin s) (σ (Sum.inr x)))
      change (LinearMap.mul' R R) (Equiv.Perm.sign σ • (a ⊗ₜ[R] b)) = 0
      have ha : a = 0 := hz
      simp [ha]
  calc
    _ = (LinearMap.mul' R R)
        ((AlternatingMap.domCoprod.summand
          (deningerLaplaceLeftMinor (R := R) r s)
          (deningerLaplaceRightMinor (R := R) r s) q0)
            (Pi.basisFun R (Fin r ⊕ Fin s))) :=
      Fintype.sum_eq_single q0 hother
    _ = 1 := by
      rw [show q0 = Quotient.mk'' (1 : Equiv.Perm (Fin r ⊕ Fin s)) by rfl,
        AlternatingMap.domCoprod.summand_mk'']
      simp only [Equiv.Perm.sign_one, one_smul,
        MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
        LinearMap.mul'_apply]
      simp only [deningerLaplaceLeftMinor, deningerLaplaceRightMinor,
        deningerLaplaceLeftProj, deningerLaplaceRightProj, Pi.basisFun_apply]
      let ML : Matrix (Fin r) (Fin r) R := fun i j =>
        (Pi.single (Sum.inl i : Fin r ⊕ Fin s) (1 : R) :
          (Fin r ⊕ Fin s) → R) (Sum.inl j)
      let MR : Matrix (Fin s) (Fin s) R := fun i j =>
        (Pi.single (Sum.inr i : Fin r ⊕ Fin s) (1 : R) :
          (Fin r ⊕ Fin s) → R) (Sum.inr j)
      change ML.det * MR.det = 1
      have hl : ML = 1 := by
        ext i j
        simp [ML, Pi.single_apply, Matrix.one_apply, eq_comm]
      have hr : MR = 1 := by
        ext i j
        simp [MR, Pi.single_apply, Matrix.one_apply, eq_comm]
      simp [hl, hr]

/-- Set of all `d`-minors of a possibly infinite rectangular matrix. -/
def deningerMatrixMinorSet {ι κ : Type*} (d : ℕ) (M : Matrix ι κ R) : Set R :=
  {x | ∃ rows : Fin d → ι, ∃ cols : Fin d → κ,
    x = (M.submatrix rows cols).det}

/-- Ideal generated by all `d`-minors of a possibly infinite rectangular matrix. -/
def deningerMatrixMinorIdeal {ι κ : Type*} (d : ℕ) (M : Matrix ι κ R) : Ideal R :=
  Ideal.span (deningerMatrixMinorSet d M)

/-- Every selected minor belongs to its determinantal ideal. -/
theorem deningerMatrixMinorDet_mem {ι κ : Type*} (d : ℕ) (M : Matrix ι κ R)
    (rows : Fin d → ι) (cols : Fin d → κ) :
    (M.submatrix rows cols).det ∈ deningerMatrixMinorIdeal d M := by
  apply Ideal.subset_span
  exact ⟨rows, cols, rfl⟩

/-- A minor on a sum of index blocks belongs to the product of the two minor ideals. -/
theorem deningerMatrixMinorDet_sum_mem_mul {ι κ : Type*}
    (r s : ℕ) (M : Matrix ι κ R)
    (rows : Fin r ⊕ Fin s → ι) (cols : Fin r ⊕ Fin s → κ) :
    (M.submatrix rows cols).det ∈
      deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M := by
  change Matrix.detRowAlternating
      (fun i j => M (rows i) (cols j)) ∈
    deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M
  rw [← deningerBlockLaplace_eq_det]
  change (LinearMap.mul' R R)
      (((deningerLaplaceLeftMinor (R := R) r s).domCoprod
        (deningerLaplaceRightMinor (R := R) r s))
        (fun i j => M (rows i) (cols j))) ∈
    deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M
  rw [AlternatingMap.domCoprod_apply, _root_.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  induction q using Quotient.inductionOn' with
  | h σ =>
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [_root_.smul_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply]
    let a := (deningerLaplaceLeftMinor (R := R) r s)
      (fun x j => M (rows (σ (Sum.inl x))) (cols j))
    let b := (deningerLaplaceRightMinor (R := R) r s)
      (fun x j => M (rows (σ (Sum.inr x))) (cols j))
    change (LinearMap.mul' R R) (Equiv.Perm.sign σ • (a ⊗ₜ[R] b)) ∈
      deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M
    have ha : a ∈ deningerMatrixMinorIdeal r M := by
      change (M.submatrix (fun x => rows (σ (Sum.inl x)))
        (fun j => cols (Sum.inl j))).det ∈ deningerMatrixMinorIdeal r M
      exact deningerMatrixMinorDet_mem r M
        (fun x => rows (σ (Sum.inl x))) (fun j => cols (Sum.inl j))
    have hb : b ∈ deningerMatrixMinorIdeal s M := by
      change (M.submatrix (fun x => rows (σ (Sum.inr x)))
        (fun j => cols (Sum.inr j))).det ∈ deningerMatrixMinorIdeal s M
      exact deningerMatrixMinorDet_mem s M
        (fun x => rows (σ (Sum.inr x))) (fun j => cols (Sum.inr j))
    have hab : a * b ∈
        deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M :=
      Ideal.mul_mem_mul ha hb
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · simpa [hs] using hab
    · simpa [hs] using
        (deningerMatrixMinorIdeal r M *
          deningerMatrixMinorIdeal s M).neg_mem hab

/-- Generalized Laplace containment `I_(r+s) ≤ I_r I_s`. -/
theorem deningerMatrixMinorIdeal_add_le_mul {ι κ : Type*}
    (r s : ℕ) (M : Matrix ι κ R) :
    deningerMatrixMinorIdeal (r + s) M ≤
      deningerMatrixMinorIdeal r M * deningerMatrixMinorIdeal s M := by
  rw [deningerMatrixMinorIdeal, Ideal.span_le]
  rintro x ⟨rows, cols, rfl⟩
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have h := deningerMatrixMinorDet_sum_mem_mul r s M
    (rows ∘ e) (cols ∘ e)
  have heq : (M.submatrix (rows ∘ e) (cols ∘ e)).det =
      (M.submatrix rows cols).det := by
    change ((M.submatrix rows cols).submatrix e e).det = _
    exact Matrix.det_submatrix_equiv_self e _
  rw [← heq]
  exact h

/-- Iterated generalized Laplace containment `I_(n*k) ≤ I_n^k`. -/
theorem deningerMatrixMinorIdeal_mul_le_pow {ι κ : Type*}
    (n k : ℕ) (M : Matrix ι κ R) :
    deningerMatrixMinorIdeal (n * k) M ≤
      (deningerMatrixMinorIdeal n M) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        deningerMatrixMinorIdeal (n * (k + 1)) M =
            deningerMatrixMinorIdeal (n + n * k) M := by
          rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ deningerMatrixMinorIdeal n M *
            deningerMatrixMinorIdeal (n * k) M :=
          deningerMatrixMinorIdeal_add_le_mul n (n * k) M
        _ ≤ deningerMatrixMinorIdeal n M *
            (deningerMatrixMinorIdeal n M) ^ k :=
          Ideal.mul_mono_right ih
        _ = (deningerMatrixMinorIdeal n M) ^ (k + 1) := by
          rw [pow_succ']

end

end RHTower
