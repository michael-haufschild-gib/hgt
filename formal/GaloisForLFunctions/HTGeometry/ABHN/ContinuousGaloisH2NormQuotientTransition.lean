import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisNormQuotientTransition
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisH2InflationInvariantDefect

/-!
# Norm-defined transitions on finite continuous Galois `H²`

The cyclic norm-quotient transition transports through the finite continuous-to-ordinary
comparison to a canonical transition on continuous unit `H²`.  It satisfies identity and
composition and, under split valuation coordinates, is exactly finite torsion inclusion.

Actual group-cohomological inflation is independently defined.  Equality of the two maps is
proved equivalent to one explicit base-unit formula: inflation must send the class of `a` to
the class of `a ^ [M : L]`.  The same formula is equivalent to vanishing of the previously
defined inflation-invariant defect.  This isolates the remaining cyclic-resolution naturality
statement without assuming it.
-/

open CategoryTheory Representation

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- Continuous unit-`H²` transition transported from the cyclic norm quotient. -/
def finiteGaloisContinuousH2NormQuotientTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    continuousGaloisH2 K L →+ continuousGaloisH2 K M :=
  (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).symm.toAddMonoidHom.comp
    ((cyclicGaloisH2NormQuotientTransition K L M).comp
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).toAddMonoidHom)

/-- Ordinary coordinates of the continuous norm-quotient transition. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
        (finiteGaloisContinuousH2NormQuotientTransition K L M z) =
      cyclicGaloisH2NormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) := by
  exact (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).apply_symm_apply _

/-- Identity law for continuous norm-quotient transition. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_self
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    finiteGaloisContinuousH2NormQuotientTransition K L L = AddMonoidHom.id _ := by
  ext z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).injective
  rw [finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply,
    cyclicGaloisH2NormQuotientTransition_self]
  rfl

/-- Composition law for continuous norm-quotient transition. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_comp
    (K L M N : Type) [Field K] [Field L] [Field M] [Field N]
    [Algebra K L] [Algebra K M] [Algebra K N]
    [Algebra L M] [Algebra L N] [Algebra M N]
    [IsScalarTower K L M] [IsScalarTower K L N]
    [IsScalarTower K M N] [IsScalarTower L M N]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K N]
    [FiniteDimensional L M] [FiniteDimensional L N] [FiniteDimensional M N]
    [IsGalois K L] [IsGalois K M] [IsGalois K N]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] [IsCyclic Gal(N/K)] :
    (finiteGaloisContinuousH2NormQuotientTransition K M N).comp
        (finiteGaloisContinuousH2NormQuotientTransition K L M) =
      finiteGaloisContinuousH2NormQuotientTransition K L N := by
  ext z
  apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K N).injective
  rw [AddMonoidHom.comp_apply,
    finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply,
    finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply,
    finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply,
    ← AddMonoidHom.comp_apply, cyclicGaloisH2NormQuotientTransition_comp]

/-- Exact comparison criterion between actual inflation and norm-defined transition. -/
theorem finiteGaloisContinuousH2Inflation_eq_normQuotientTransition_iff_baseProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)] :
    finiteGaloisContinuousH2Inflation K L M =
        finiteGaloisContinuousH2NormQuotientTransition K L M ↔
      ∀ a : Additive Kˣ,
        (groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom
            (cyclicGaloisH2BaseProjection K L a) =
          cyclicGaloisH2BaseProjection K M (Module.finrank L M • a) := by
  constructor
  · intro h a
    let z : continuousGaloisH2 K L :=
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm
        (cyclicGaloisH2BaseProjection K L a)
    have hz := congrArg
      (fun f : continuousGaloisH2 K L →+ continuousGaloisH2 K M => f z) h
    have hz' := congrArg (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M) hz
    rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
      finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply] at hz'
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) =
      cyclicGaloisH2NormQuotientTransition K L M
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z) at hz'
    change (groupCohomology.map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
        (galoisTowerUnitsRepresentationHom K L M) 2).hom
          ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)
            ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm
              (cyclicGaloisH2BaseProjection K L a))) =
      cyclicGaloisH2NormQuotientTransition K L M
        ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L)
          ((finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).symm
            (cyclicGaloisH2BaseProjection K L a))) at hz'
    rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).apply_symm_apply,
      cyclicGaloisH2NormQuotientTransition_baseProjection] at hz'
    exact hz'
  · intro h
    apply AddMonoidHom.ext
    intro z
    apply (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M).injective
    rw [finiteGaloisContinuousH2Inflation_toOrdinary_apply,
      finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply]
    obtain ⟨a, ha⟩ := cyclicGaloisH2BaseProjection_surjective K L
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)
    rw [← ha, h, cyclicGaloisH2NormQuotientTransition_baseProjection]

/-- Continuous cyclic `H²` in split valuation coordinates. -/
noncomputable def finiteGaloisContinuousH2SplitValuationEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    continuousGaloisH2 K L ≃+ ZMod n :=
  (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).trans
    (cyclicGaloisH2SplitValuationEquiv K L vK vL n u hu hfinrank hval hzero)

/-- Continuous split valuation coordinates commute with norm-defined transition. -/
theorem finiteGaloisContinuousH2SplitValuationEquiv_transition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    (finiteGaloisContinuousH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM).toAddMonoidHom.comp
        (finiteGaloisContinuousH2NormQuotientTransition K L M) =
      (zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩).comp
        (finiteGaloisContinuousH2SplitValuationEquiv K L vK vL
          (Module.finrank K L) u hu rfl hvalKL hzeroKL).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  change finiteGaloisContinuousH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM
        (finiteGaloisContinuousH2NormQuotientTransition K L M z) =
    zmodRatModIntTransition Module.finrank_pos.ne' Module.finrank_pos.ne'
      ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
      (finiteGaloisContinuousH2SplitValuationEquiv K L vK vL
        (Module.finrank K L) u hu rfl hvalKL hzeroKL z)
  change cyclicGaloisH2SplitValuationEquiv K M vK vM
      (Module.finrank K M) u hu rfl hvalKM hzeroKM
        (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K M
          (finiteGaloisContinuousH2NormQuotientTransition K L M z)) = _
  rw [finiteGaloisContinuousH2NormQuotientTransition_toOrdinary_apply]
  have hnat := congrArg
    (fun f : cyclicGaloisH2 K L →+ ZMod (Module.finrank K M) =>
      f (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z))
    (cyclicGaloisH2SplitValuationEquiv_transition K L M vK vL vM u hu
      hvalKL hzeroKL hvalKM hzeroKM)
  exact hnat

/-- Continuous split valuation coordinates with codomain restricted to finite `ℚ/ℤ` torsion. -/
noncomputable def finiteGaloisContinuousH2SplitValuationNTorsionEquiv
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ))) (n : ℕ) (hn : n ≠ 0) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hfinrank : Module.finrank K L = n)
    (hval : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ n)
    (hzero : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a) :
    continuousGaloisH2 K L ≃+ ratModIntNTorsion n :=
  (finiteGaloisContinuousH2SplitValuationEquiv K L vK vL n u hu hfinrank hval hzero).trans
    (zmodRatModIntAddEquivNTorsion n hn)

/-- Norm-defined transition is finite torsion inclusion in local invariant coordinates. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_torsionInvariant
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a)
    (z : continuousGaloisH2 K L) :
    finiteGaloisContinuousH2SplitValuationNTorsionEquiv K M vK vM
        (Module.finrank K M) Module.finrank_pos.ne' u hu rfl hvalKM hzeroKM
        (finiteGaloisContinuousH2NormQuotientTransition K L M z) =
      ratModIntNTorsionInclusion
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K L vK vL
          (Module.finrank K L) Module.finrank_pos.ne' u hu rfl hvalKL hzeroKL z) := by
  apply Subtype.ext
  change zmodRatModIntAddHom (Module.finrank K M) Module.finrank_pos.ne'
      (finiteGaloisContinuousH2SplitValuationEquiv K M vK vM
        (Module.finrank K M) u hu rfl hvalKM hzeroKM
          (finiteGaloisContinuousH2NormQuotientTransition K L M z)) =
    zmodRatModIntAddHom (Module.finrank K L) Module.finrank_pos.ne'
      (finiteGaloisContinuousH2SplitValuationEquiv K L vK vL
        (Module.finrank K L) u hu rfl hvalKL hzeroKL z)
  rw [← zmodRatModIntAddHom_transition Module.finrank_pos.ne'
    Module.finrank_pos.ne'
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩]
  congr 1
  have hnat := congrArg
    (fun f : continuousGaloisH2 K L →+ ZMod (Module.finrank K M) => f z)
    (finiteGaloisContinuousH2SplitValuationEquiv_transition K L M vK vL vM u hu
      hvalKL hzeroKL hvalKM hzeroKM)
  exact hnat

/-- Norm-defined transition equals abstract torsion-coordinate transport. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_eq_torsionTransition
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    finiteGaloisContinuousH2NormQuotientTransition K L M =
      continuousGaloisH2TorsionTransition K L M
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K L vK vL
          (Module.finrank K L) Module.finrank_pos.ne' u hu rfl hvalKL hzeroKL)
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K M vK vM
          (Module.finrank K M) Module.finrank_pos.ne' u hu rfl hvalKM hzeroKM)
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩ := by
  apply finiteTorsionInvariantTransition_unique
  intro z
  exact finiteGaloisContinuousH2NormQuotientTransition_torsionInvariant
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM z

/-- Under split valuation classification, continuous norm-defined transition is injective. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_injective_of_splitValuation
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    Function.Injective (finiteGaloisContinuousH2NormQuotientTransition K L M) := by
  rw [finiteGaloisContinuousH2NormQuotientTransition_eq_torsionTransition
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM]
  exact finiteTorsionInvariantTransition_injective _ _ _

/-- Standard nonlinear local phases are stable under norm-defined refinement. -/
theorem finiteGaloisContinuousH2NormQuotientTransition_character
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a)
    (z : continuousGaloisH2 K L) :
    continuousGaloisH2TorsionStdAddChar K M (Module.finrank K M)
        Module.finrank_pos.ne'
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K M vK vM
          (Module.finrank K M) Module.finrank_pos.ne' u hu rfl hvalKM hzeroKM)
        (finiteGaloisContinuousH2NormQuotientTransition K L M z) =
      continuousGaloisH2TorsionStdAddChar K L (Module.finrank K L)
        Module.finrank_pos.ne'
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K L vK vL
          (Module.finrank K L) Module.finrank_pos.ne' u hu rfl hvalKL hzeroKL) z := by
  rw [finiteGaloisContinuousH2NormQuotientTransition_eq_torsionTransition
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM]
  exact continuousGaloisH2TorsionTransition_character K L M
    Module.finrank_pos.ne' Module.finrank_pos.ne' _ _
    ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩ z

/-- Vanishing of inflation defect is exactly the base-unit power formula. -/
theorem finiteGaloisContinuousH2InflationInvariantDefect_eq_zero_iff_baseProjection
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ))) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalKL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vL x) ^ Module.finrank K L)
    (hzeroKL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalKM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) =
        (tameValHom vM x) ^ Module.finrank K M)
    (hzeroKM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    finiteGaloisContinuousH2InflationInvariantDefect K L M
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K L vK vL
          (Module.finrank K L) Module.finrank_pos.ne' u hu rfl hvalKL hzeroKL)
        (finiteGaloisContinuousH2SplitValuationNTorsionEquiv K M vK vM
          (Module.finrank K M) Module.finrank_pos.ne' u hu rfl hvalKM hzeroKM)
        ⟨Module.finrank L M, (Module.finrank_mul_finrank K L M).symm⟩ = 0 ↔
      ∀ a : Additive Kˣ,
        (groupCohomology.map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
          (galoisTowerUnitsRepresentationHom K L M) 2).hom
            (cyclicGaloisH2BaseProjection K L a) =
          cyclicGaloisH2BaseProjection K M (Module.finrank L M • a) := by
  rw [finiteGaloisContinuousH2InflationInvariantDefect_eq_zero_iff]
  rw [← finiteGaloisContinuousH2NormQuotientTransition_eq_torsionTransition
    K L M vK vL vM u hu hvalKL hzeroKL hvalKM hzeroKM]
  exact finiteGaloisContinuousH2Inflation_eq_normQuotientTransition_iff_baseProjection K L M

end

end GaloisForLFunctions.HTGeometry.ABHN
