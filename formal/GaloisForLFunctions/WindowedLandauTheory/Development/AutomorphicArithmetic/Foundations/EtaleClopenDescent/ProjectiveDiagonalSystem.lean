import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCupResidue
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ComplementaryRegularForms

/-! The diagonal's homogeneous Koszul weights and its regular form
lattices on pairs of projective charts. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

/-- Regular forms on a normalized chart are stable under scalars from
the base chart algebra. -/
theorem smul_mem_regularExteriorLattice
    (I : Finset (Fin (d + 1))) (p : ℕ)
    (u : F) (hu : u ∈ rA k x I) (v : ExteriorDifferentials k E p)
    (hv : v ∈ regularExteriorLattice (rB k E x I) p) :
    u • v ∈ regularExteriorLattice (rB k E x I) p := by
  change (algebraMap F E u) • (v : DR k E) ∈ omB k E (rB k E x I) p
  exact smul_mem_omB (isIntegral_algebraMap (x := (⟨u, hu⟩ : rA k x I))) hv

private theorem tensorChartRing_mono {A B C D : Subalgebra k F}
    (hAC : A ≤ C) (hBD : B ≤ D) : tensorChartRing A B ≤ tensorChartRing C D := by
  rintro _ ⟨r, rfl⟩
  let f := Subalgebra.inclusion hAC
  let g := Subalgebra.inclusion hBD
  refine ⟨Algebra.TensorProduct.map f g r, ?_⟩
  change ((Algebra.TensorProduct.map C.val D.val).comp (Algebra.TensorProduct.map f g)) r =
    Algebra.TensorProduct.map A.val B.val r
  rw [← Algebra.TensorProduct.map_comp]
  rfl

private def diagonalLeftUnit (h : IsPd k x) (i : Fin (d + 1)) : (F ⊗[k] F)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := F) (B := F)).toMonoidHom
    (Units.mk0 (x i) (h.ne i))

private def diagonalRightUnit (h : IsPd k x) (i : Fin (d + 1)) : (F ⊗[k] F)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight (R := k) (A := F)).toMonoidHom
    (Units.mk0 (x i) (h.ne i))

/-- The regular chart tensors in the complementary exterior degrees. -/
def diagonalChartSystem (h : IsPd k x) (a b : ℕ) : WeightedChartSystem k d (F ⊗[k] F)
    (ExteriorDifferentials k E a ⊗[k] ExteriorDifferentials k E b) where
  act := tensorScalarAction
  X := diagonalLeftUnit h
  Y := diagonalRightUnit h
  R I J := tensorChartRing (rA k x I) (rA k x J)
  M I J := tensorChartLattice (regularExteriorLattice (rB k E x I) a)
    (regularExteriorLattice (rB k E x J) b)

variable (h : IsPd k x) (a b : ℕ)

private theorem units_map_ratio {S : Type} [Monoid S] (f : F →* S)
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    (((Units.map f (Units.mk0 u hu) * (Units.map f (Units.mk0 v hv))⁻¹ : Sˣ)) : S) =
      f (u / v) := by
  rw [← map_inv, ← map_mul, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_mk0, Units.val_mk0, div_eq_mul_inv]

private theorem diagonalChartSystem_X_ratio (i j : Fin (d + 1)) :
    (((diagonalChartSystem (E := E) h a b).X j *
      ((diagonalChartSystem (E := E) h a b).X i)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) =
      (x j / x i) ⊗ₜ[k] (1 : F) := by
  change ((diagonalLeftUnit h j * (diagonalLeftUnit h i)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) = _
  unfold diagonalLeftUnit
  rw [units_map_ratio]
  rfl

private theorem diagonalChartSystem_Y_ratio (i j : Fin (d + 1)) :
    (((diagonalChartSystem (E := E) h a b).Y j *
      ((diagonalChartSystem (E := E) h a b).Y i)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) =
      (1 : F) ⊗ₜ[k] (x j / x i) := by
  change ((diagonalRightUnit h j * (diagonalRightUnit h i)⁻¹ : (F ⊗[k] F)ˣ) : F ⊗[k] F) = _
  unfold diagonalRightUnit
  rw [units_map_ratio]
  rfl

/-- Coordinate ratios and restriction preserve the regular lattices
on chart pairs. -/
theorem diagonalChartSystem_good : (diagonalChartSystem (E := E) h a b).Good := by
  constructor
  · intro I I' J J' _ _ hI hJ
    exact tensorChartRing_mono (rA_mono hI) (rA_mono hJ)
  · intro I I' J J' _ _ hI hJ
    refine Submodule.map₂_le.mpr fun u hu v hv => Submodule.apply_mem_map₂ _ ?_ ?_
    · change (u : DR k E) ∈ omB k E (rB k E x I') a
      exact omB_mono (rB_mono (E := E) (x := x) hI) a hu
    · change (v : DR k E) ∈ omB k E (rB k E x J') b
      exact omB_mono (rB_mono (E := E) (x := x) hJ) b hv
  · intro I J _ _ s hs t ht
    exact tensorScalarAction_mem_chartLattice (smul_mem_regularExteriorLattice I a)
      (smul_mem_regularExteriorLattice J b) hs ht
  · intro I J _ i hi j
    rw [diagonalChartSystem_X_ratio]
    let u : rA k x I := ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
    refine ⟨u ⊗ₜ[k] (1 : rA k x J), ?_⟩
    change Algebra.TensorProduct.map (rA k x I).val (rA k x J).val (u ⊗ₜ[k] (1 : rA k x J)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  · intro I J _ i hi j
    rw [diagonalChartSystem_Y_ratio]
    let u : rA k x J := ⟨x j / x i, Algebra.subset_adjoin ⟨i, hi, j, rfl⟩⟩
    refine ⟨(1 : rA k x I) ⊗ₜ[k] u, ?_⟩
    change Algebra.TensorProduct.map (rA k x I).val (rA k x J).val ((1 : rA k x I) ⊗ₜ[k] u) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

/-- The homogeneous equation that compares a pair of projective coordinates. -/
abbrev diagonalMinor (l : WeightedChartSystem.DiagonalIndex d) : F ⊗[k] F :=
  (diagonalChartSystem (E := E) h a b).homogeneousMinor l

/-- The normalized equation on a chart pair is a difference of
tensors of affine coordinate ratios. -/
theorem diagonalMinor_normalized (i j : Fin (d + 1)) (a' b' : Fin (d + 1)) :
    (diagonalChartSystem (E := E) h a b).normalizedWeight (fun _ => (1, 1))
        (diagonalMinor (E := E) h a b) i j (toLex (a', b')) =
      (x a' / x i) ⊗ₜ[k] (x b' / x j) - (x b' / x i) ⊗ₜ[k] (x a' / x j) := by
  let T := diagonalChartSystem (E := E) h a b
  let U := T.X i * T.Y j
  have he (u v : Fin (d + 1)) :
      (T.X u : F ⊗[k] F) * (T.Y v : F ⊗[k] F) * (U⁻¹ : (F ⊗[k] F)ˣ) =
        (x u / x i) ⊗ₜ[k] (x v / x j) := by
    calc
      _ = (↑(T.X u * (T.X i)⁻¹) : F ⊗[k] F) *
          (↑(T.Y v * (T.Y j)⁻¹) : F ⊗[k] F) := by
        have hu : T.X u * T.Y v * U⁻¹ =
            (T.X u * (T.X i)⁻¹) * (T.Y v * (T.Y j)⁻¹) := by
          dsimp only [U]
          rw [mul_inv]
          ac_rfl
        simpa only [Units.val_mul] using congrArg (fun u : (F ⊗[k] F)ˣ => (u : F ⊗[k] F)) hu
      _ = _ := by
        rw [diagonalChartSystem_X_ratio, diagonalChartSystem_Y_ratio,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change T.normalizedWeight _ _ i j _ = _
  unfold WeightedChartSystem.normalizedWeight WeightedChartSystem.weightUnit
    diagonalMinor WeightedChartSystem.homogeneousMinor
  simp only [ofLex_toLex, pow_one, sub_mul]
  change (T.X a' : F ⊗[k] F) * (T.Y b' : F ⊗[k] F) * (U⁻¹ : (F ⊗[k] F)ˣ) -
    (T.X b' : F ⊗[k] F) * (T.Y a' : F ⊗[k] F) * (U⁻¹ : (F ⊗[k] F)ˣ) = _
  rw [he, he]

/-- Every homogeneous diagonal minor is integral after normalization
on both charts. -/
theorem diagonalChartSystem_admitted :
    (diagonalChartSystem (E := E) h a b).Admitted (fun _ => (1, 1))
      (diagonalMinor (E := E) h a b) := by
  let T := diagonalChartSystem (E := E) h a b
  have hT := diagonalChartSystem_good (E := E) h a b
  intro i j l
  obtain ⟨⟨u, v⟩, rfl⟩ := toLex.surjective l
  have hm (u' v' : Fin (d + 1)) :
      (x u' / x i) ⊗ₜ[k] (x v' / x j) ∈ T.R {i} {j} := by
    have hX := hT.memX {i} {j} (Finset.singleton_nonempty j) i (Finset.mem_singleton_self i) u'
    have hY := hT.memY {i} {j} (Finset.singleton_nonempty i) j (Finset.mem_singleton_self j) v'
    rw [diagonalChartSystem_X_ratio] at hX
    rw [diagonalChartSystem_Y_ratio] at hY
    have hp := (T.R {i} {j}).mul_mem hX hY
    rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hp
  rw [diagonalMinor_normalized]
  exact (T.R {i} {j}).sub_mem (hm u v) (hm v u)

end GlobalTheory.PD
