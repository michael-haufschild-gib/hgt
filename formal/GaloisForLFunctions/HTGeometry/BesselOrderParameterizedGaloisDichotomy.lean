import GaloisForLFunctions.HTGeometry.BesselOrderParameterizedComparisonJet
import GaloisForLFunctions.HTGeometry.DifferenceGaloisIrreducibilityTensor
import GaloisForLFunctions.HTGeometry.DifferenceGaloisImprimitivityTensor
import GaloisForLFunctions.HTGeometry.GaloisMonoidTensorDescent
import GaloisForLFunctions.HTGeometry.GaloisComparisonJetGroupStructure
import GaloisForLFunctions.HTGeometry.Sl2TangentSpanNormalForm
import GaloisForLFunctions.HTGeometry.MatrixDeterminantZeroTangentFinite

namespace GaloisForLFunctions.HTGeometry.BesselDifferentialClosure

noncomputable section

open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped TensorProduct Differential

local instance besselOrderParameterizedEndgameBaseDifferential :
    Differential (RatFunc Constants) := coordinateTotalDifferential

local instance besselOrderParameterizedEndgameConstantsRatDifferentialAlgebra :
    DifferentialAlgebra Constants (RatFunc Constants) :=
  coordinateTotalDifferentialAlgebra

local instance besselOrderParameterizedEndgameRatCharZero : CharZero (RatFunc Constants) :=
  charZero_of_injective_ringHom (algebraMap ℚ (RatFunc Constants)).injective

local instance besselOrderParameterizedEndgamePPVDifferential {s : ℝ}
    (data : BesselOrderParameterizedPVData s) : Differential data.PPVRing :=
  quotientDifferential data.M data.isSigmaDeltaIdeal.2

local instance besselOrderParameterizedEndgamePPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra (RatFunc Constants) data.PPVRing :=
  ppvQuotientDifferentialAlgebra data.M data.isSigmaDeltaIdeal.2

local instance besselOrderParameterizedEndgameConstantsPPVDifferentialAlgebra {s : ℝ}
    (data : BesselOrderParameterizedPVData s) :
    DifferentialAlgebra Constants data.PPVRing :=
  differentialAlgebra_trans (C := Constants) (K := RatFunc Constants) (E := data.PPVRing)

theorem BesselOrderParameterizedPVData.ComparisonJetData.sl2_or_isomonodromy_of_tangentDensity
    {s : ℝ} (data : BesselOrderParameterizedPVData s)
    (comparison : data.ComparisonJetData) (hs : 0 < s) :
    ((∀ g : Matrix (Fin 2) (Fin 2) Constants, g.det = 1 →
        g ∈ matrixZeroSet (C := Constants) (A := Constants)
          (matrixVanishingIdeal
            {h ∈ galoisMonoid
                (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                comparison.Z
                (fun i j => mem_comparisonJetAlgebra_entry comparison.Z comparison.w i j)
                (tensorDifferentialPoints
                  (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                  comparison.deriv_stable) |
              h.det = 1})) ∨
      ∃ B : Matrix (Fin 2) (Fin 2) (RatFunc Constants),
        B.map FieldShift.ratShift * FieldShift.besselOrderCompanion (slope s) =
          matrixDeriv (FieldShift.besselOrderCompanion (slope s)) +
            FieldShift.besselOrderCompanion (slope s) * B) := by
  let R := data.PPVRing
  let K := RatFunc Constants
  let Y := data.fundamentalMatrix
  let E := comparisonJetAlgebra (C := Constants) comparison.Z comparison.w
  let hZE : ∀ i j, comparison.Z i j ∈ E :=
    fun i j => mem_comparisonJetAlgebra_entry comparison.Z comparison.w i j
  let hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E := comparison.deriv_stable
  let v : Fin 5 → R ⊗[K] R := comparisonJetGeneratorsTwo comparison.Z comparison.w
  letI : Nontrivial R := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact data.ne_top
  letI : IsReduced R := data.isReduced
  letI : IsReduced E := by simpa [E] using comparison.reduced
  letI : IsAlgClosed (differentialConstants Constants) :=
    isAlgClosed_differentialConstants Constants
  letI : Invertible Y := Matrix.invertibleOfIsUnitDet Y data.fundamental_det_isUnit
  have hsys : Y.map data.sigmaEquiv =
      (FieldShift.besselOrderCompanion (slope s)).map (algebraMap K R) * Y := by
    ext i j
    exact data.fundamental i j
  have hv : ∀ i, v i ∈ E := by
    intro i
    fin_cases i
    · simpa [v, E, comparisonJetGeneratorsTwo] using
        mem_comparisonJetAlgebra_entry comparison.Z comparison.w 0 0
    · simpa [v, E, comparisonJetGeneratorsTwo] using
        mem_comparisonJetAlgebra_entry comparison.Z comparison.w 0 1
    · simpa [v, E, comparisonJetGeneratorsTwo] using
        mem_comparisonJetAlgebra_entry comparison.Z comparison.w 1 0
    · simpa [v, E, comparisonJetGeneratorsTwo] using
        mem_comparisonJetAlgebra_entry comparison.Z comparison.w 1 1
    · simpa [v, E, comparisonJetGeneratorsTwo] using
        mem_comparisonJetAlgebra_w comparison.Z comparison.w
  have hsep : ∀ e : E,
      (∀ χ ∈ tensorDifferentialPoints E hEδ, χ e = 0) → e = 0 := by
    intro e he
    exact eq_zero_of_forall_mem_tensorDifferentialPoints_of_jetAdjoin E hEδ v hv
      comparison.differential_generated e he
  have hY1 : ∀ j, Y 1 j = data.sigmaEquiv (Y 0 j) := by
    intro j
    have h := congrFun (congrFun hsys 0) j
    simpa [Y, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      FieldShift.besselOrderCompanion] using h.symm
  have hYrec : ∀ j, data.sigmaEquiv (Y 1 j) =
      algebraMap K R (FieldShift.orderShiftCoeff (slope s)) * Y 1 j +
        algebraMap K R 1 * Y 0 j := by
    intro j
    have h := congrFun (congrFun hsys 1) j
    simpa [Y, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
      FieldShift.besselOrderCompanion, add_comm] using h
  have hric : ∀ r : K,
      FieldShift.ratShiftEquiv r * r ≠
        FieldShift.orderShiftCoeff (slope s) * r + 1 := by
    intro r hr
    apply modifiedBesselOrder_no_riccati_in_differentialClosure s hs
    exact ⟨r, by
      rw [FieldShift.ratShiftEquiv_apply] at hr
      change r * FieldShift.ratShift r -
        FieldShift.orderShiftCoeff (slope s) * r - 1 = 0
      rw [mul_comm r, hr]
      ring⟩
  have hnoSym : ¬ ∃ (a : Fin 3 → K) (lam : K), a ≠ 0 ∧ lam ≠ 0 ∧ ∀ i,
      FieldShift.ratShiftEquiv (a i) = lam *
        (symmetricSquareMatrix
          (FieldShift.besselOrderCompanion (slope s))).mulVec a i := by
    apply not_symmetricSquare_semiInvariant_of_no_imprimitive
      FieldShift.ratShiftEquiv (FieldShift.orderShiftCoeff (slope s))
        (FieldShift.orderShiftCoeff_ne_zero (slope_ne_zero hs))
    intro e p hp hE hP
    apply modifiedBesselOrder_no_imprimitive_pair_in_differentialClosure s hs
    exact ⟨e, p, hp,
      by simpa only [FieldShift.ratShiftEquiv_apply] using hE,
      by simpa only [FieldShift.ratShiftEquiv_apply] using hP⟩
  have hconst : ∀ c : Constants,
      data.sigmaEquiv (algebraMap Constants data.PPVRing c) =
        algebraMap Constants data.PPVRing c := by
    intro c
    rw [IsScalarTower.algebraMap_apply Constants (RatFunc Constants) data.PPVRing,
      show data.sigmaEquiv
          (algebraMap (RatFunc Constants) data.PPVRing
            (algebraMap Constants (RatFunc Constants) c)) =
          algebraMap (RatFunc Constants) data.PPVRing
            (FieldShift.ratShiftEquiv (algebraMap Constants (RatFunc Constants) c)) from
        data.baseCompatible (algebraMap Constants (RatFunc Constants) c),
      FieldShift.ratShiftEquiv_apply, FieldShift.ratShift_const]
  have hirr : ∀ q : Fin 2 → Constants, q ≠ 0 → ∀ u : Fin 2 → Constants,
      u ∈ Submodule.span Constants {x : Fin 2 → Constants |
        ∃ g ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ),
          g.mulVec q = x} := by
    apply galoisMonoid_irreducible_of_no_riccati_of_pointSeparation E
      (tensorDifferentialPoints E hEδ) hsep data.baseCompatible
      hconst hric Y data.fundamental_det_isUnit hY1 hYrec
      comparison.Z hZE comparison.factorization
  have hdetK : ∀ g ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ),
      g.det ∈ differentialConstants Constants := by
    intro g hg
    exact galoisMonoid_det_mem_differentialConstants_of_sq_eq_one E comparison.Z hZE
      comparison.det_sq_eq_one _ hg
  have hdet0 : ∀ g ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ),
      g.det ≠ 0 := by
    intro g hg
    exact galoisMonoid_det_ne_zero_of_sq_eq_one E comparison.Z hZE
      comparison.det_sq_eq_one _ hg
  have hinv : ∀ g ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ),
      ∃ g' : Matrix (Fin 2) (Fin 2) Constants, g * g' = 1 ∧
        ∀ W ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ) |
              h.det = 1})
          (subset_matrixZeroSet_vanishingIdeal _ ⟨Submonoid.one_mem _, Matrix.det_one⟩),
          g * W * g' ∈ matrixTangentM (matrixVanishingIdeal
            {h ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ) |
              h.det = 1})
            (subset_matrixZeroSet_vanishingIdeal _ ⟨Submonoid.one_mem _, Matrix.det_one⟩) := by
    exact comparisonJetGaloisMonoid_detOne_inverse_adjoint_of_det_inverse Y comparison.Z
      comparison.w comparison.factorization comparison.det_mul_inverse data.detInverse
      data.fundamental_det_mul_inverse
  have hnoForms :
      ¬ HasInvariantLineNormalForm
          (galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)) ∧
        ¬ HasInvariantPairNormalForm
          (galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)) := by
    exact not_invariantLine_orPair_of_no_riccati_no_symmetricSquare
      E (tensorDifferentialPoints E hEδ) hsep data.baseCompatible hconst hric
      (FieldShift.besselOrderCompanion (slope s)) Y data.fundamental_det_isUnit hsys
      hY1 hYrec comparison.Z hZE comparison.factorization hnoSym
  have htangent := tangentSpan_eq_bot_or_dense_of_no_invariantNormalForm
    (C := Constants)
    (H := {h ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ) |
      h.det = 1})
    (fun a ha b hb => ⟨Submonoid.mul_mem _ ha.1 hb.1, by
      rw [Matrix.det_mul, ha.2, hb.2, one_mul]⟩)
    ⟨Submonoid.one_mem _, Matrix.det_one⟩ (fun h hh => hh.2)
    (galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)) hinv
    hnoForms.1 hnoForms.2
  rcases htangent with hzero | hdense
  · let G : Set (Matrix (Fin 2) (Fin 2) Constants) :=
      galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)
    have hGone : (1 : Matrix (Fin 2) (Fin 2) Constants) ∈ G := by
      change (1 : Matrix (Fin 2) (Fin 2) Constants) ∈
        galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)
      exact Submonoid.one_mem _
    have hGmul : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G := by
      intro a ha b hb
      change a ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ) at ha
      change b ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ) at hb
      change a * b ∈ galoisMonoid E comparison.Z hZE (tensorDifferentialPoints E hEδ)
      exact Submonoid.mul_mem _ ha hb
    have hGinv : ∀ a ∈ G, ∃ b ∈ G, a * b = 1 := by
      intro a ha
      exact comparisonJetGaloisMonoid_exists_inverse_mem_of_det_inverse
        Y data.detInverse data.fundamental_det_mul_inverse comparison.Z comparison.w
        comparison.factorization comparison.det_mul_inverse (by simpa only [G] using ha)
    have hGdetSq : ∀ a ∈ G, a.det ^ 2 = 1 := by
      intro a ha
      exact galoisMonoid_det_pow_eq_one E comparison.Z hZE comparison.det_sq_eq_one
        (tensorDifferentialPoints E hEδ) (by simpa only [G] using ha)
    have htangentBot :
        matrixTangentM (matrixVanishingIdeal {g ∈ G | g.det = 1})
          (subset_matrixZeroSet_vanishingIdeal {g ∈ G | g.det = 1}
            ⟨hGone, Matrix.det_one⟩) = ⊥ := by
      have hspan : Submodule.span Constants
          ((matrixTangentM (matrixVanishingIdeal {g ∈ G | g.det = 1})
            (subset_matrixZeroSet_vanishingIdeal {g ∈ G | g.det = 1}
              ⟨hGone, Matrix.det_one⟩) : Submodule _ _) :
              Set (Matrix (Fin 2) (Fin 2) Constants)) = ⊥ := by
        simpa only [G] using hzero
      apply le_bot_iff.mp
      intro x hx
      have hxspan : x ∈ Submodule.span Constants
          ((matrixTangentM (matrixVanishingIdeal {g ∈ G | g.det = 1})
            (subset_matrixZeroSet_vanishingIdeal {g ∈ G | g.det = 1}
              ⟨hGone, Matrix.det_one⟩) : Submodule _ _) :
                Set (Matrix (Fin 2) (Fin 2) Constants)) :=
        Submodule.subset_span hx
      rw [hspan] at hxspan
      exact hxspan
    have hfinite : G.Finite := finite_matrixSet_of_detOne_tangent_eq_bot
      G hGone hGmul hGinv hGdetSq htangentBot
    exact Or.inr (isomonodromy_of_finite_galoisMonoid_irreducible_jetAdjoin
      E hEδ v hv comparison.differential_generated
      data.baseCompatible hconst data.commutesDeriv
      (FieldShift.besselOrderCompanion (slope s)) Y hsys comparison.Z hZE
      comparison.factorization hirr hfinite)
  · exact isomonodromy_or_sl2_galoisMonoid_detOne_irreducible_jetAdjoin
      constants_noUniversalJetRelation E hEδ v hv comparison.differential_generated
      data.baseCompatible hconst data.commutesDeriv
      (FieldShift.besselOrderCompanion (slope s)) Y hsys comparison.Z hZE
      comparison.factorization hirr hdense hdetK hdet0 hinv

/-- The determinant-one comparison Galois monoid of a concrete positive-scale Bessel order system
is Kolchin dense in `SL₂`.  All PPV, comparison, tangent, and isomonodromy alternatives are
discharged internally. -/
theorem modifiedBesselOrder_sl2_galoisClosure :
    ∀ s : ℝ, 0 < s →
      ∃ data : BesselOrderParameterizedPVData s,
        ∃ comparison : data.ComparisonJetData,
          ∀ g : Matrix (Fin 2) (Fin 2) Constants, g.det = 1 →
            g ∈ matrixZeroSet (C := Constants) (A := Constants)
              (matrixVanishingIdeal
                {h ∈ galoisMonoid
                    (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                    comparison.Z
                    (fun i j => mem_comparisonJetAlgebra_entry comparison.Z comparison.w i j)
                    (tensorDifferentialPoints
                      (comparisonJetAlgebra (C := Constants) comparison.Z comparison.w)
                      comparison.deriv_stable) |
                  h.det = 1}) := by
  intro s hs
  obtain ⟨data, hcomparison⟩ :=
    besselOrder_parameterizedPicardVessiot_comparisonJet_exists s
  obtain ⟨comparison⟩ := hcomparison
  refine ⟨data, comparison, ?_⟩
  rcases comparison.sl2_or_isomonodromy_of_tangentDensity data hs with hsl2 | hiso
  · exact hsl2
  · exact (modifiedBesselOrder_no_isomonodromy_in_differentialClosure s hs hiso).elim

end

end GaloisForLFunctions.HTGeometry.BesselDifferentialClosure
