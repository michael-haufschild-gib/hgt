import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterPolynomialPowers
import GaloisForLFunctions.RHTower.Artin.ArtinInducedSpanIsAnIdeal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! Exterior powers and Newton identities realize matrix power traces as virtual characters. -/

open GaloisForLFunctions Polynomial Module

noncomputable section

namespace GlobalTheory.CuspGL

private def exteriorRep {G : Type} [Group G] {n : ℕ} (j : ℕ)
    (ρ : G →* GL (Fin n) ℂ) : Representation ℂ G (⋀[ℂ]^j (Fin n → ℂ)) where
  toFun g := exteriorPower.map j (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one, exteriorPower.map_id]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul, exteriorPower.map_comp]
    rfl

private theorem trace_exterior_eq_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) :
    LinearMap.trace ℂ (⋀[ℂ]^j (Fin n → ℂ)) (exteriorPower.map j (Matrix.toLin' M)) =
      ∑ S ∈ Finset.univ.powersetCard j, (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  classical
  let b := Pi.basisFun ℂ (Fin n)
  rw [LinearMap.trace_eq_matrix_trace ℂ (b.exteriorPower j)]
  unfold Matrix.trace
  rw [Finset.sum_subtype (p := fun S : Finset (Fin n) => S ∈ Set.powersetCard (Fin n) j) _
    (fun S => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti,
    exteriorPower.ιMultiDual_apply_ιMulti]
  let e := (S.1.orderIsoOfFin S.2).toEquiv
  let A : Matrix S.val S.val ℂ := M.submatrix Subtype.val Subtype.val
  let T : Matrix (Fin j) (Fin j) ℂ := A.submatrix e e
  calc
    _ = T.transpose.det := by
      apply congrArg (Matrix.det : Matrix (Fin j) (Fin j) ℂ → ℂ)
      ext i k
      simp only [T, A, Matrix.of_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
        Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
      simp [e, b, Basis.coord_apply, Finset.coe_orderIsoOfFin_apply, Matrix.toLin'_apply]
    _ = T.det := Matrix.det_transpose T
    _ = _ := Matrix.det_submatrix_equiv_self e A

private theorem esymm_roots_eq_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ S ∈ Finset.univ.powersetCard j,
      (M.submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rcases le_or_gt j n with hj | hj
  · have hcoef := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have hminors := M.charpoly_coeff_eq_sum_minors j (by simpa using hj)
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at hcoef
    rw [Fintype.card_fin, hcoef] at hminors
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) hminors
  · rw [Finset.powersetCard_eq_empty.mpr (by simpa using hj), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp

private theorem esymm_mem_virtual {G : Type} [Group G] {n : ℕ} (j : ℕ)
    (ρ : G →* GL (Fin n) ℂ) :
    (fun g => (ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.esymm j) ∈ virtualCharacterGroup G := by
  let b := (Pi.basisFun ℂ (Fin n)).exteriorPower j
  letI : FiniteDimensional ℂ (⋀[ℂ]^j (Fin n → ℂ)) := Module.Finite.of_basis b
  refine AddSubgroup.subset_closure ⟨FDRep.of (exteriorRep j ρ), ?_⟩
  funext g
  change LinearMap.trace ℂ _ (exteriorPower.map j (Matrix.toLin' (ρ g : Matrix (Fin n) (Fin n) ℂ))) = _
  rw [trace_exterior_eq_minors, esymm_roots_eq_minors]

private theorem sum_antidiagonal_filter_ioo_eq_sum_ioo (k : ℕ) (g : ℕ → ℕ → ℂ) :
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 ∈ Set.Ioo 0 k, g a.1 a.2
      = ∑ i ∈ Finset.Ioo 0 k, g i (k - i) := by
  rw [Finset.sum_filter,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => if i ∈ Set.Ioo 0 k then g i j else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ioo]
  omega

private theorem aeval_psum_eq_sum_map_pow (s : Multiset ℂ) (n : ℕ) :
    MvPolynomial.aeval (fun x : s => (x : ℂ)) (MvPolynomial.psum s ℂ n) = (s.map (· ^ n)).sum := by
  classical
  rw [MvPolynomial.psum, map_sum]
  simp only [map_pow, MvPolynomial.aeval_X]
  conv_rhs => rw [← Multiset.map_univ_coe s]
  rw [Multiset.map_map]
  rfl

private theorem multiset_newton_psum (s : Multiset ℂ) (r : ℕ) (hr : 0 < r) :
    (s.map (· ^ r)).sum = (-1) ^ (r + 1) * (r : ℂ) * s.esymm r
      - ∑ i ∈ Finset.Ioo 0 r, (-1) ^ i * s.esymm i * (s.map (· ^ (r - i))).sum := by
  classical
  have key := congrArg (MvPolynomial.aeval (fun x : s => (x : ℂ)))
    (MvPolynomial.psum_eq_mul_esymm_sub_sum s ℂ r hr)
  simp only [map_sub, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.map_univ_coe,
    aeval_psum_eq_sum_map_pow] at key
  rw [key, sum_antidiagonal_filter_ioo_eq_sum_ioo r (fun i j => (-1) ^ i * s.esymm i * (s.map (· ^ j)).sum)]


/-- The sum of the `r`-th powers of the characteristic roots is a virtual character. -/
theorem complex_root_power_sum_mem_virtual {G : Type} [Group G] {n : ℕ}
    (ρ : G →* GL (Fin n) ℂ) (r : ℕ) :
    (fun g => (((ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots).map (· ^ r)).sum) ∈
      virtualCharacterGroup G := by
  have hconst (c : ℤ) : (fun _ : G => (c : ℂ)) ∈ virtualCharacterGroup G := by
    have hone : (1 : G → ℂ) ∈ virtualCharacterGroup G :=
      AddSubgroup.subset_closure one_mem_fdCharacterSet
    convert zsmul_mem hone c using 1
    funext g
    simp [← Int.cast_smul_eq_zsmul ℂ]
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · convert hconst n using 1
      funext g
      simp [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]
    · let e (i : ℕ) (g : G) := (ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots.esymm i
      let p (i : ℕ) (g : G) := (((ρ g : Matrix (Fin n) (Fin n) ℂ).charpoly.roots).map (· ^ i)).sum
      have he : p r = (fun _ => (((-1) ^ (r + 1) * r : ℤ) : ℂ)) * e r -
          ∑ i ∈ Finset.Ioo 0 r, (fun _ => (((-1) ^ i : ℤ) : ℂ)) * e i * p (r - i) := by
        funext g
        simp only [e, p, Pi.sub_apply, Pi.mul_apply, Finset.sum_apply, Int.cast_mul, Int.cast_pow,
          Int.cast_neg, Int.cast_one, Int.cast_natCast]
        exact multiset_newton_psum _ _ hr
      change p r ∈ virtualCharacterGroup G
      rw [he]
      refine sub_mem (mul_mem_virtualCharacterGroup (hconst _) (esymm_mem_virtual r ρ))
        (AddSubgroup.sum_mem _ fun i hi => ?_)
      have := (Finset.mem_Ioo.mp hi).1
      exact mul_mem_virtualCharacterGroup
        (mul_mem_virtualCharacterGroup (hconst _) (esymm_mem_virtual i ρ)) (ih _ (by omega))

end GlobalTheory.CuspGL
