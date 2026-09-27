import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpIsoclinicFrame
import GaloisForLFunctions.HTGeometry.DifferentialVariationalWeightedFlags
import GaloisForLFunctions.HTGeometry.DifferentialVariationalCartanTranslationVector
import GaloisForLFunctions.HTGeometry.DifferentialOperatorCompletedCartanBalanceEveryLattice

/-!
# The Cartan translation vector is the slope vector

For a differential field automorphism `σ` with canonical variational action `T` on the completed
coordinate space `𝔻^r`, the rational slope decomposition `𝔻^r = ⊕_s E_s` determines the asymptotic
Cartan vector completely:

```text
exists_variationalSlopes_cartanTranslationVector
    λ(σ) = -(sl 0, …, sl (r-1)),   sl sorted,   #{i | sl i = t} = dim E_t,   Σ sl = 0.
```

The weights of the opposite weighted flags are therefore exactly the coordinates of the Cartan
translation vector, with multiplicities the dimensions of the slope parts, and they are rational.

The proof chooses the slope-adapted frame `B` of `DiffOp.exists_slope_adapted_basis`.  In the frame
`B` the base lattice is the standard lattice and `T^{D n}` moves it to the standard lattice at the
coweight `-n D sl`, which is dominant because the slopes are sorted.  Uniqueness of dominant Cartan
coordinates identifies this coweight with the relative position of the orbit, the balance law
gives `Σ sl = 0`, and the normalized relative positions along the subsequence `D n` are constant.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

/-- Pulling the standard lattice at coweight `m` back along the coordinate map of a skew basis `B`
gives the coordinate lattice of `B` with valuation bounds `m`. -/
theorem mem_mapCompletedPseudoDiffOpLatticeLinear_symm_iff {r : ℕ}
    (B : Module.Basis (Fin r) (CompletedPseudoDiffOp K) (Fin r → CompletedPseudoDiffOp K))
    (m : Fin r → ℤ) (y : Fin r → CompletedPseudoDiffOp K) :
    y ∈ (mapCompletedPseudoDiffOpLatticeLinear B.equivFun.symm
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m)).carrier ↔
      y ∈ coordinateLattice B fun j => ((m j : ℤ) : WithTop ℤ) := by
  have hcoe : ∀ j, (((completedPseudoDiffOpUniformizerCoweight (K := K) m j)⁻¹ :
      (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K) = uniformizerZPow (-m j) := by
    intro j
    rw [completedPseudoDiffOpUniformizerCoweight, ← zpow_neg]
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff, mem_coordinateLattice]
  constructor
  · rintro ⟨x, hx, rfl⟩ j
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hx
    have hj := hx j
    rw [hcoe, mul_uniformizerZPow_neg_mem_integer_iff] at hj
    rwa [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  · intro hy
    refine ⟨B.equivFun y, ?_, B.equivFun.symm_apply_apply y⟩
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
    intro j
    rw [hcoe, mul_uniformizerZPow_neg_mem_integer_iff, Module.Basis.equivFun_apply]
    exact hy j

theorem mapCompletedPseudoDiffOpLatticeLinear_symm_cancel {r : ℕ}
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K)) (X : CompletedPseudoDiffOpLattice K (Fin r)) :
    mapCompletedPseudoDiffOpLatticeLinear e (mapCompletedPseudoDiffOpLatticeLinear e.symm X) = X := by
  rw [mapCompletedPseudoDiffOpLatticeLinear_trans, LinearEquiv.symm_trans_self,
    mapCompletedPseudoDiffOpLatticeLinear_refl]

end DiffOp

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

attribute [local instance] DiffOp.completedPseudoDiffOpIntegerSMul

/-- The lattice action of `σ^k` is the image under the `k`-th power of the vector action. -/
theorem DifferentialFieldAut.pow_latticeBuildingAction_carrier (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (k : ℕ) :
    ((σ ^ k).latticeBuildingAction b L).carrier =
      DiffOp.semilinearImage (σ.vecBuildingActionEquiv b ^ k)
        ((σ.isUniformizerSemilinear_vecBuildingActionEquiv b).pow k) L.carrier := by
  ext w
  rw [DifferentialFieldAut.mem_latticeBuildingAction_iff, DiffOp.mem_semilinearImage_iff_exists]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [DifferentialFieldAut.vecBuildingActionEquiv_pow_apply]

/-- **The Cartan translation vector is the slope vector.**  There are sorted rational slopes
`sl`, slope `t` occurring exactly `dim E_t` times, summing to zero, such that for every base vertex
the asymptotic Cartan vector of `σ` is `-sl`. -/
theorem exists_variationalSlopes_cartanTranslationVector (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    ∃ sl : Fin r → ℚ, Monotone sl ∧
      (∀ t : ℚ, (Finset.univ.filter fun i => sl i = t).card =
        Module.finrank (DiffOp.CompletedPseudoDiffOp K) (variationalSlopeSubspace σ b t)) ∧
      ∑ i, sl i = 0 ∧
      ∀ x, differentialVariationalCartanTranslationVector b x σ = fun i => -(sl i : ℝ) := by
  have hT := σ.isUniformizerSemilinear_vecBuildingActionEquiv b
  obtain ⟨B, sl, D, A, hsl, hD, hA, hfib, hdyn⟩ := DiffOp.exists_slope_adapted_basis hT
  have hAmono : Monotone A := fun i j hij => by
    have h : (A i : ℚ) ≤ A j := by
      rw [hA, hA]
      exact mul_le_mul_of_nonneg_left (hsl hij) (Nat.cast_nonneg D)
    exact_mod_cast h
  let m : ℕ → Fin r → ℤ := fun n j => -((n : ℤ) * A j)
  have hmanti : ∀ n, Antitone (m n) := fun n i j hij =>
    neg_le_neg (mul_le_mul_of_nonneg_left (hAmono hij) (Int.natCast_nonneg n))
  let e := B.equivFun
  let L0 := DiffOp.mapCompletedPseudoDiffOpLatticeLinear e.symm
    (DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) fun _ : Fin r => 0)
  have hL0 : L0.carrier = DiffOp.coordinateLattice B fun _ => ((0 : ℤ) : WithTop ℤ) := by
    ext y
    exact DiffOp.mem_mapCompletedPseudoDiffOpLatticeLinear_symm_iff B _ y
  have hlat : ∀ n, (σ ^ (D * n)).latticeBuildingAction b L0 =
      DiffOp.mapCompletedPseudoDiffOpLatticeLinear e.symm
        (DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) (m n)) := by
    intro n
    apply DiffOp.CompletedPseudoDiffOpLattice.ext
    ext y
    rw [DifferentialFieldAut.pow_latticeBuildingAction_carrier, hL0, hdyn n,
      DiffOp.mem_mapCompletedPseudoDiffOpLatticeLinear_symm_iff]
  have hL0e : DiffOp.mapCompletedPseudoDiffOpLatticeLinear e L0 =
      DiffOp.standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [DiffOp.mapCompletedPseudoDiffOpLatticeLinear_symm_cancel,
      DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  have hdom : ∀ n, DiffOp.completedPseudoDiffOpDominantRelativePosition L0
      ((σ ^ (D * n)).latticeBuildingAction b L0) = m n := fun n =>
    (DiffOp.completedPseudoDiffOpDominantRelativePosition_eq L0 _ e (m n) hL0e
      (by rw [hlat, DiffOp.mapCompletedPseudoDiffOpLatticeLinear_symm_cancel]) (hmanti n)).symm
  -- balance: the slopes sum to zero
  have hbal : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L0
      ((σ ^ (D * 1)).latticeBuildingAction b L0) i = 0 :=
    (σ ^ (D * 1)).variationalOreCartanBalance_everyLattice b L0
  rw [hdom 1] at hbal
  have hAsum : ∑ i, A i = 0 := by
    simp only [m, Nat.cast_one, one_mul, Finset.sum_neg_distrib, neg_eq_zero] at hbal
    exact hbal
  have hslsum : ∑ i, sl i = 0 := by
    have h : (D : ℚ) * ∑ i, sl i = 0 := by
      rw [Finset.mul_sum]
      simp_rw [← hA]
      exact_mod_cast hAsum
    exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hD.ne')
  refine ⟨sl, hsl, hfib, hslsum, fun x => ?_⟩
  rw [differentialVariationalCartanTranslationVector_base_independent b x (Quotient.mk _ L0)]
  -- the normalized relative positions along the subsequence `D n`
  have hsub : Tendsto (fun n : ℕ => D * n) atTop atTop :=
    tendsto_id.const_mul_atTop' hD
  have hlim := (tendsto_differentialVariationalCartanTranslationVector b
    (Quotient.mk _ L0) σ).comp hsub
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  funext i
  have hval : (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition
      (Quotient.mk _ L0) ((σ ^ (D * n)).projectiveBuildingAction b (Quotient.mk _ L0)) :
        Fin r → ℝ) i = DiffOp.centeredCoweight (m n) i := by
    rw [DifferentialFieldAut.projectiveBuildingAction_mk,
      DiffOp.differentialVariationalProjectiveEuclideanRelativePosition_mk, ← hdom n]
    rfl
  have hmsum : ∑ j, m n j = 0 := by
    simp only [m, ← Finset.mul_sum, Finset.sum_neg_distrib, hAsum, mul_zero, neg_zero]
  have hcent : DiffOp.centeredCoweight (m n) i = (m n i : ℝ) := by
    simp only [DiffOp.centeredCoweight]
    rw [← Int.cast_sum, hmsum, Int.cast_zero, zero_div, sub_zero]
  simp only [Function.comp_apply]
  rw [hval, hcent]
  have hDn : ((D * n : ℕ) : ℝ) ≠ 0 := by
    have : 0 < D * n := Nat.mul_pos hD hn
    exact_mod_cast this.ne'
  have hAi : (A i : ℝ) = D * sl i := by exact_mod_cast hA i
  simp only [m]
  rw [eq_div_iff hDn]
  push_cast
  rw [hAi]
  ring

/-- **Phase dichotomy in slope form.**  The Cartan translation vector vanishes exactly when the
whole coordinate space has slope zero; otherwise some slope part of nonzero slope is nonzero, and the
attracting and repelling flags are proper and opposite. -/
theorem differentialVariationalCartanTranslationVector_eq_zero_iff (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalCartanTranslationVector b x σ = 0 ↔
      variationalSlopeSubspace σ b 0 = ⊤ := by
  classical
  obtain ⟨sl, -, hfib, -, hvec⟩ := exists_variationalSlopes_cartanTranslationVector σ b
  rw [hvec x]
  have hzero : ((fun i => -(sl i : ℝ)) = 0) ↔ ∀ i, sl i = 0 := by
    constructor
    · intro h i
      have h' := congrFun h i
      simp only [Pi.zero_apply, neg_eq_zero, Rat.cast_eq_zero] at h'
      exact h'
    · intro h
      funext i
      simp [h i]
  rw [hzero]
  have hcard := hfib 0
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [← hcard, Module.finrank_fin_fun, Finset.filter_true_of_mem (fun i _ => h i),
      Finset.card_univ, Fintype.card_fin]
  · intro h i
    rw [h, finrank_top, Module.finrank_fin_fun] at hcard
    have huniv : (Finset.univ.filter fun i => sl i = 0) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, Fintype.card_fin])
    have hi := Finset.mem_univ i
    rw [← huniv] at hi
    exact (Finset.mem_filter.1 hi).2

end

end GaloisForLFunctions.HTGeometry
