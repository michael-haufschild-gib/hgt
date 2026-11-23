import GaloisForLFunctions.HTGeometry.KroneckerIdentityIsometry
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization
import GaloisForLFunctions.HTGeometry.SiteSupportedReindex
import GaloisForLFunctions.HTGeometry.ObserverProfileStability
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget

/-!
# Circuit approximation on a disjoint tensor factor

Reading one diagonal block of a matrix is contractive in operator norm.
An operator confined to the other factor therefore cannot improve the best
scalar approximation to a tensor-local evolution.
-/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
private theorem slice_norm_le (a : κ) (w : EuclideanSpace ℂ (ι × κ)) :
    ‖(EuclideanSpace.equiv ι ℂ).symm (fun i => w.ofLp (i,a))‖ ≤ ‖w‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_euclideanOfFun,EuclideanSpace.norm_eq,Real.sq_sqrt (by positivity), Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (f := fun c : κ => ‖w.ofLp (i,c)‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- Each diagonal block, including the compression to one basis state of a
gate's support, has operator norm bounded by the full matrix norm. -/
theorem diagonal_ancilla_block_norm_le (a : κ) (X : Matrix (ι × κ) (ι × κ) ℂ) :
    ‖X.submatrix (fun i => (i,a)) (fun i => (i,a))‖ ≤ ‖X‖ := by
  let B := X.submatrix (fun i => (i,a)) (fun i => (i,a))
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) B).opNorm_le_bound (norm_nonneg X)
  intro v
  let v' := euclideanAncillaEmbed a v
  let w := Matrix.toEuclideanCLM (𝕜 := ℂ) X v'
  have he : Matrix.toEuclideanCLM (𝕜 := ℂ) B v =
      (EuclideanSpace.equiv ι ℂ).symm (fun i => w.ofLp (i,a)) := by
    ext i
    change (B *ᵥ v.ofLp) i = (X *ᵥ v'.ofLp) (i,a)
    simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,B,Matrix.submatrix_apply,
      v',euclideanAncillaEmbed_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [he]
  exact (slice_norm_le a w).trans ((Matrix.toEuclideanCLM (𝕜 := ℂ) X).le_opNorm v' |>.trans_eq
    (by rw [show ‖v'‖ = ‖v‖ from (euclideanAncillaEmbed a).norm_map _]; rfl))

/-- Every diagonal entry of an operator on the second factor supplies a
scalar approximation at least as accurate as the whole disjoint operator. -/
theorem disjoint_factor_scalar_bound (V : Matrix ι ι ℂ) (C : Matrix κ κ ℂ) (a : κ) :
    ‖V - (C a a) • (1 : Matrix ι ι ℂ)‖ ≤
      ‖V ⊗ₖ (1 : Matrix κ κ ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ C‖ := by
  have h := diagonal_ancilla_block_norm_le a (V ⊗ₖ (1 : Matrix κ κ ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ C)
  convert h using 2
  ext i j
  simp [Matrix.submatrix_apply,Matrix.kroneckerMap_apply,Matrix.smul_apply,mul_comm]

/-- At any error and in every finite nonempty spectator dimension,
approximability by a disjoint matrix is equivalent to approximability by a
single complex scalar, with identical error. -/
theorem disjoint_factor_approximation_iff_scalar [Nonempty κ] (V : Matrix ι ι ℂ) (ε : ℝ) :
    (∃ C : Matrix κ κ ℂ, ‖V ⊗ₖ (1 : Matrix κ κ ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ C‖ ≤ ε) ↔
      ∃ z : ℂ, ‖V-z • (1 : Matrix ι ι ℂ)‖ ≤ ε := by
  constructor
  · rintro ⟨C,h⟩
    exact ⟨_,(disjoint_factor_scalar_bound V C (Classical.arbitrary κ)).trans h⟩
  · rintro ⟨z,hz⟩
    refine ⟨z • (1 : Matrix κ κ ℂ),?_⟩
    have he : V ⊗ₖ (1 : Matrix κ κ ℂ) - (1 : Matrix ι ι ℂ) ⊗ₖ (z • (1 : Matrix κ κ ℂ)) =
        (V-z • (1 : Matrix ι ι ℂ)) ⊗ₖ (1 : Matrix κ κ ℂ) := by
      ext ⟨i,a⟩ ⟨j,b⟩
      change V i j * _ - _ * (z * _) = (V i j - z * _) * _
      ring
    rwa [he,l2_opNorm_kronecker_one]

#print axioms disjoint_factor_approximation_iff_scalar
section Site
variable {Q : Type*} [Fintype Q] [DecidableEq Q] {A : Q → Type*}
    [∀ q, Fintype (A q)] [∀ q, DecidableEq (A q)] [∀ q, Nonempty (A q)]

/-- Every individual diagonal entry of an operator on disjoint sites
gives a scalar approximation at least as accurate as the full operator. -/
theorem disjoint_site_diagonal_bound {S T : Finset Q} (hST : Disjoint S T)
    {X Y : Matrix (∀ q, A q) (∀ q, A q) ℂ} (hX : IsSiteSupported S X) (hY : IsSiteSupported T Y) (x : ∀ q, A q) :
    ‖X - (Y x x) • (1 : Matrix (∀ q, A q) (∀ q, A q) ℂ)‖ ≤ ‖X-Y‖ := by
  classical
  obtain ⟨B,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hX
  obtain ⟨C,rfl⟩ := exists_liftLocalMatrix_of_isSiteSupported hY
  let Z := liftLocalMatrixOutsideDisjoint hST C
  let e := configurationSplitEquiv A S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  have hB : Φ (liftLocalMatrix S B) = B ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) :=
    reindex_liftLocalMatrix_eq_kronecker_one S B
  have hC : Φ (liftLocalMatrix T C) = (1 : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) ⊗ₖ Z :=
    reindex_liftLocalMatrix_disjoint_eq_one_kronecker hST C
  let a := (e x).2
  let z := Z a a
  have hz : liftLocalMatrix T C x x = z := by
    have h := congrArg (fun M => M (e x) (e x)) hC
    simpa only [Φ,Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,Matrix.submatrix_apply,
      Equiv.symm_apply_apply,Matrix.kroneckerMap_apply,Matrix.one_apply_eq,one_mul,z,a] using h
  rw [hz]
  rw [← l2_opNorm_reindexAlgEquiv_eq e (liftLocalMatrix S B - z • 1),
    ← l2_opNorm_reindexAlgEquiv_eq e (liftLocalMatrix S B - liftLocalMatrix T C)]
  change ‖Φ _‖ ≤ ‖Φ _‖
  rw [map_sub,map_sub,map_smul,map_one,hB,hC]
  have he : B ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) - z • 1 =
      (B - z • 1) ⊗ₖ (1 : Matrix (OutsideConfiguration A S) (OutsideConfiguration A S) ℂ) := by
    ext ⟨i,a⟩ ⟨j,b⟩
    by_cases hij : i=j <;> by_cases hab : a=b <;>
      simp [Matrix.kroneckerMap_apply,hij,hab]
  rw [he,l2_opNorm_kronecker_one]
  exact disjoint_factor_scalar_bound B Z a

/-- A matrix on disjoint sites approximates an operator no better than a
complex scalar at the same error. -/
theorem disjoint_site_scalar_bound {S T : Finset Q} (hST : Disjoint S T)
    {X Y : Matrix (∀ q, A q) (∀ q, A q) ℂ} (hX : IsSiteSupported S X) (hY : IsSiteSupported T Y) :
    ∃ z : ℂ, ‖X - z • (1 : Matrix (∀ q, A q) (∀ q, A q) ℂ)‖ ≤ ‖X-Y‖ := by
  let x : ∀ q, A q := fun _ => Classical.arbitrary _
  exact ⟨Y x x,disjoint_site_diagonal_bound hST hX hY x⟩

/-- Deleting the terms incident on a circuit's sites costs at most twice the
elapsed time times their total operator norm when testing against scalars. -/
theorem truncated_local_evolution_scalar_bound {S T : Finset Q} (hST : Disjoint S T)
    (H K : selfAdjoint (Matrix (∀ q, A q) (∀ q, A q) ℂ)) (hK : IsSiteSupported S K.val)
    (C : Matrix (∀ q, A q) (∀ q, A q) ℂ) (hC : IsSiteSupported T C) (t : ℝ) :
    ∃ z : ℂ, ‖unitaryEvolution H.val t - z • (1 : Matrix (∀ q, A q) (∀ q, A q) ℂ)‖ ≤
      ‖unitaryEvolution H.val t-C‖ + 2 * |t| * ‖H.val-K.val‖ := by
  let U := unitaryEvolution H.val t
  let V := unitaryEvolution K.val t
  obtain ⟨z,hz⟩ := disjoint_site_scalar_bound hST (isSiteSupported_unitaryEvolution hK t) hC
  refine ⟨z,?_⟩
  have hUV : ‖U-V‖ ≤ |t| * ‖H.val-K.val‖ := norm_unitaryEvolution_sub_le _ _ H.2 K.2 t
  have hVC := norm_sub_le_norm_sub_add_norm_sub V U C
  rw [norm_sub_rev V U] at hVC
  have hU := norm_sub_le_norm_sub_add_norm_sub U V (z • 1)
  change ‖V-z • 1‖ ≤ ‖V-C‖ at hz
  change ‖U-z • 1‖ ≤ ‖U-C‖+2 * |t| * ‖H.val-K.val‖
  linarith only [hUV,hVC,hz,hU]
end Site
#print axioms truncated_local_evolution_scalar_bound

section Gap
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- Every spectral point is within the full operator error of a proposed
scalar. The scalar may be anywhere in the complex plane. -/
theorem spectral_point_scalar_error_le {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (i : I) (t : ℝ) (z : ℂ) :
    ‖anchorPhase hH.eigenvalues i t - z‖ ≤ ‖unitaryEvolution H t-z • (1 : Matrix I I ℂ)‖ := by
  let V := (hH.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V ∈ unitary (Matrix I I ℂ) := hH.eigenvectorUnitary.2
  have hone : z • (1 : Matrix I I ℂ) = V * Matrix.diagonal (fun _ : I => z) * star V := by
    rw [← smul_one_eq_diagonal_const z,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
      (Unitary.mem_iff.mp hV).2]
  rw [unitaryEvolution_spectral hH t,hone,← Matrix.sub_mul,← Matrix.mul_sub,Matrix.diagonal_sub,
    l2_opNorm_unitary_conj_eq hV,Matrix.l2_opNorm_diagonal]
  exact norm_le_pi_norm (fun k => anchorPhase hH.eigenvalues k t - z) i

/-- At the half period of any nonzero energy gap the evolution is at least
unit distance from every scalar, including nonunit scalars. -/
theorem half_gap_time_scalar_error_ge_one {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (i j : I) (hgap : hH.eigenvalues i ≠ hH.eigenvalues j) (z : ℂ) :
    1 ≤ ‖unitaryEvolution H (Real.pi/(hH.eigenvalues i - hH.eigenvalues j)) - z • (1 : Matrix I I ℂ)‖ := by
  let t := Real.pi/(hH.eigenvalues i - hH.eigenvalues j)
  let c := anchorPhase hH.eigenvalues j t
  have htn : t*(hH.eigenvalues i - hH.eigenvalues j) = Real.pi := div_mul_cancel₀ _ (sub_ne_zero.mpr hgap)
  have ha : anchorPhase hH.eigenvalues i t = -c := by
    have he : -(Complex.I * ((t:ℂ) * hH.eigenvalues i)) =
        -(Complex.I * ((t:ℂ) * hH.eigenvalues j)) + (-(Real.pi : ℂ)*Complex.I) := by
      have hh := congrArg Complex.ofReal htn
      push_cast at hh
      rw [← hh]; ring
    change Complex.exp _ = -Complex.exp _
    have hpi : Complex.exp (-(Real.pi : ℂ)*Complex.I) = -1 := by
      rw [neg_mul,Complex.exp_neg,Complex.exp_pi_mul_I]; norm_num
    rw [he,Complex.exp_add,hpi,mul_neg_one]
  have hc : ‖c‖ = 1 := by simp [c,anchorPhase,Complex.norm_exp]
  have hchord : ‖c-anchorPhase hH.eigenvalues i t‖ = 2 := by
    rw [ha,sub_neg_eq_add,← two_mul c,norm_mul,hc]; norm_num
  have htri := norm_sub_le_norm_sub_add_norm_sub c z (anchorPhase hH.eigenvalues i t)
  rw [hchord,norm_sub_rev z] at htri
  have h1 := spectral_point_scalar_error_le hH i t z
  have h2 := spectral_point_scalar_error_le hH j t z
  change ‖c-z‖ ≤ _ at h2
  linarith only [htri,h1,h2]
end Gap
#print axioms half_gap_time_scalar_error_ge_one

end
end GaloisForLFunctions.HTGeometry
