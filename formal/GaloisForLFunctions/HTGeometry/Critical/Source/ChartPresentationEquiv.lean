import GaloisForLFunctions.HTGeometry.Critical.Schur.UniqueRamifiedPrime
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartObservationTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.CoordinateIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

noncomputable local instance criticalSourceChartAlgebraGroundAlgebra :
    Algebra K (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  ((algebraMap (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n))).comp
    (algebraMap K (criticalObservationChartRing K m n))).toAlgebra

local instance criticalSourceChartAlgebraGroundTower :
    IsScalarTower K (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

local instance criticalSourceChartAlgebraFieldGroundTower :
    IsScalarTower K (criticalSourceChartAlgebra K (m := m) (n := n))
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap K (criticalSourceField K m n) c =
      algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
        (algebraMap K (criticalObservationChartRing K m n) c)
    exact IsScalarTower.algebraMap_apply K
      (criticalObservationChartRing K m n) (criticalSourceField K m n) c

/-- A raw coordinate, regarded as an element of the adjoined source chart algebra. -/
noncomputable def criticalSourceRawInChartAlgebra (j : Fin (m + n)) :
    criticalSourceChartAlgebra K (m := m) (n := n) :=
  ⟨criticalSourceRaw K m n j,
    Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩

/-- Evaluation of raw-coordinate polynomials in the adjoined source chart algebra. -/
noncomputable def criticalSourceRawToChartAlgebra :
    MvPolynomial (Fin (m + n)) K →ₐ[K]
      criticalSourceChartAlgebra K (m := m) (n := n) :=
  MvPolynomial.aeval (criticalSourceRawInChartAlgebra K)

theorem coe_criticalSourceRawToChartAlgebra
    (p : MvPolynomial (Fin (m + n)) K) :
    ((criticalSourceRawToChartAlgebra K (m := m) (n := n) p :
        criticalSourceChartAlgebra K (m := m) (n := n)) :
      criticalSourceField K m n) =
      MvPolynomial.aeval (criticalSourceRaw K m n) p := by
  have h := MvPolynomial.comp_aeval
    (R := K) (f := criticalSourceRawInChartAlgebra K (m := m) (n := n))
    (φ := IsScalarTower.toAlgHom K
      (criticalSourceChartAlgebra K (m := m) (n := n))
      (criticalSourceField K m n))
  exact DFunLike.congr_fun h p

theorem aeval_criticalSourceRaw_chartPoly_eq_clearingElement :
    MvPolynomial.aeval (criticalSourceRaw K m n) (criticalSourceChartPoly K m n) =
      criticalSchurClearingElement K (m := m) (n := n) := by
  rw [criticalSourceChartPoly_eq, map_mul, map_mul, MvPolynomial.aeval_X,
    MvPolynomial.aeval_X, aeval_criticalSourceRecipNumerator,
    criticalSchurClearingElement, criticalSourceMarked_eq, criticalSourceScale]
  ring

/-- The source-chart denominator remains a unit in the adjoined chart algebra. -/
theorem isUnit_criticalSourceRawToChartAlgebra_chartPoly :
    IsUnit (criticalSourceRawToChartAlgebra K (m := m) (n := n)
      (criticalSourceChartPoly K m n)) := by
  let v : criticalSourceChartAlgebra K (m := m) (n := n) :=
    ⟨(criticalSchurClearingElement K (m := m) (n := n))⁻¹,
      criticalSchurClearingElement_inv_mem_chartAlgebra K⟩
  refine ⟨{
    val := criticalSourceRawToChartAlgebra K (m := m) (n := n)
      (criticalSourceChartPoly K m n)
    inv := v
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
    dsimp only [v]
    calc
      ((criticalSourceRawToChartAlgebra K (m := m) (n := n)
          (criticalSourceChartPoly K m n) :
        criticalSourceChartAlgebra K (m := m) (n := n)) :
          criticalSourceField K m n) *
          (criticalSchurClearingElement K (m := m) (n := n))⁻¹ =
        MvPolynomial.aeval (criticalSourceRaw K m n)
            (criticalSourceChartPoly K m n) *
          (criticalSchurClearingElement K (m := m) (n := n))⁻¹ := by
            rw [coe_criticalSourceRawToChartAlgebra]
      _ = 1 := by
        rw [aeval_criticalSourceRaw_chartPoly_eq_clearingElement]
        exact mul_inv_cancel₀ (criticalSchurClearingElement_ne_zero K)
  · apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one]
    dsimp only [v]
    calc
      (criticalSchurClearingElement K (m := m) (n := n))⁻¹ *
          ((criticalSourceRawToChartAlgebra K (m := m) (n := n)
            (criticalSourceChartPoly K m n) :
          criticalSourceChartAlgebra K (m := m) (n := n)) :
            criticalSourceField K m n) =
        (criticalSchurClearingElement K (m := m) (n := n))⁻¹ *
          MvPolynomial.aeval (criticalSourceRaw K m n)
            (criticalSourceChartPoly K m n) := by
              rw [coe_criticalSourceRawToChartAlgebra]
      _ = 1 := by
        rw [aeval_criticalSourceRaw_chartPoly_eq_clearingElement]
        exact inv_mul_cancel₀ (criticalSchurClearingElement_ne_zero K)

/-- Canonical map from the principal-open source chart to the adjoined chart algebra. -/
noncomputable def criticalSourceChartRingToAlgebraRingHom :
    criticalSourceChartRing K m n →+*
      criticalSourceChartAlgebra K (m := m) (n := n) :=
  IsLocalization.Away.lift (S := criticalSourceChartRing K m n)
    (criticalSourceChartPoly K m n)
    (g := (criticalSourceRawToChartAlgebra K (m := m) (n := n)).toRingHom)
    (isUnit_criticalSourceRawToChartAlgebra_chartPoly K)

theorem coe_criticalSourceChartRingToAlgebraRingHom
    (d : criticalSourceChartRing K m n) :
    ((criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n) d :
        criticalSourceChartAlgebra K (m := m) (n := n)) :
      criticalSourceField K m n) =
      algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) d := by
  let f : criticalSourceChartRing K m n →+* criticalSourceField K m n :=
    (criticalSourceChartAlgebra K (m := m) (n := n)).val.toRingHom.comp
      (criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n))
  have hf : f = algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n) := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (criticalSourceChartPoly K m n))
    apply RingHom.ext
    intro p
    dsimp only [f]
    simp only [RingHom.comp_apply]
    simp only [criticalSourceChartRingToAlgebraRingHom, IsLocalization.Away.lift_eq]
    change ((criticalSourceRawToChartAlgebra K (m := m) (n := n) p :
        criticalSourceChartAlgebra K (m := m) (n := n)) :
      criticalSourceField K m n) = _
    rw [coe_criticalSourceRawToChartAlgebra,
      algebraMap_criticalSourceChartRing_apply]
  exact DFunLike.congr_fun hf d

/-- The canonical chart map, as an algebra map over the observation chart. -/
noncomputable def criticalSourceChartRingToAlgebra :
    criticalSourceChartRing K m n →ₐ[criticalObservationChartRing K m n]
      criticalSourceChartAlgebra K (m := m) (n := n) :=
  { criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n) with
    commutes' := fun r => by
      apply Subtype.ext
      calc
        ((criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n)
            (algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartRing K m n) r) :
            criticalSourceChartAlgebra K (m := m) (n := n)) :
          criticalSourceField K m n) =
            algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
              (algebraMap (criticalObservationChartRing K m n)
                (criticalSourceChartRing K m n) r) :=
          coe_criticalSourceChartRingToAlgebraRingHom K _
        _ = algebraMap (criticalObservationChartRing K m n)
              (criticalSourceField K m n) r := by
          exact IsScalarTower.algebraMap_apply
            (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
              (criticalSourceField K m n) r |>.symm
        _ = ((algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartAlgebra K (m := m) (n := n)) r :
            criticalSourceChartAlgebra K (m := m) (n := n)) :
          criticalSourceField K m n) := rfl }

theorem criticalSourceChartRingToAlgebra_injective :
    Function.Injective (criticalSourceChartRingToAlgebra K (m := m) (n := n)) := by
  intro x y hxy
  apply algebraMap_criticalSourceChartRing_injective K m n
  rw [← coe_criticalSourceChartRingToAlgebraRingHom K x,
    ← coe_criticalSourceChartRingToAlgebraRingHom K y]
  exact congrArg Subtype.val hxy

theorem criticalSourceChartRingToAlgebra_surjective :
    Function.Surjective (criticalSourceChartRingToAlgebra K (m := m) (n := n)) := by
  intro y
  have hy : IsIntegral (criticalObservationChartRing K m n)
      (y : criticalSourceField K m n) := by
    exact (Algebra.IsIntegral.isIntegral y).map
      (criticalSourceChartAlgebra K (m := m) (n := n)).val
  obtain ⟨d, hd⟩ := exists_criticalSourceChart_of_isIntegral K hy
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change ((criticalSourceChartRingToAlgebraRingHom K (m := m) (n := n) d :
      criticalSourceChartAlgebra K (m := m) (n := n)) :
    criticalSourceField K m n) = (y : criticalSourceField K m n)
  rw [coe_criticalSourceChartRingToAlgebraRingHom K, hd]

/-- **The localization and adjoin presentations of the critical source chart coincide.** -/
noncomputable def criticalSourceChartRingAlgEquiv :
    criticalSourceChartRing K m n ≃ₐ[criticalObservationChartRing K m n]
      criticalSourceChartAlgebra K (m := m) (n := n) :=
  AlgEquiv.ofBijective (criticalSourceChartRingToAlgebra K (m := m) (n := n))
    ⟨criticalSourceChartRingToAlgebra_injective K,
      criticalSourceChartRingToAlgebra_surjective K⟩

end

end GaloisForLFunctions.HTGeometry
