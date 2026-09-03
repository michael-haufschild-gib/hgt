import GaloisForLFunctions.HTGeometry.CriticalBlockSchurLocalizationUnramified

/-!
# Schur-local block unramifiedness over `Localization.AtPrime`

The observation Schur valuation ring and `Localization.AtPrime` at the Schur divisor are two
localization models of the same chart.  Their canonical equivalence transports the proved Schur
unramifiedness to the base model used by height-one purity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 3000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The block normalization localized at the Schur divisor is formally unramified over the
ordinary prime localization of the observation chart. -/
theorem criticalBlockSchurAtPrime_formallyUnramified [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y) :
    Algebra.FormallyUnramified
      (Localization.AtPrime (criticalSchurChartUnder K (m := m) (n := n)))
      (Localization (Algebra.algebraMapSubmonoid (CriticalBlockNormalization K B)
        (criticalSchurChartUnder K (m := m) (n := n)).primeCompl)) := by
  let A := criticalObservationChartRing K m n
  let P := criticalSchurChartUnder K (m := m) (n := n)
  let Ap := Localization.AtPrime P
  let R := CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  let C := CriticalBlockNormalization K B
  let Cp := Localization (Algebra.algebraMapSubmonoid C P.primeCompl)
  let eA : Ap ≃ₐ[A] R := IsLocalization.algEquiv P.primeCompl Ap R
  letI : Algebra Ap R := eA.toAlgHom.toAlgebra
  letI : IsScalarTower A Ap R := IsScalarTower.of_algHom eA.toAlgHom
  have hmaps : (algebraMap R Cp).comp (algebraMap Ap R) = algebraMap Ap Cp := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro a
    change algebraMap R Cp (eA (algebraMap A Ap a)) =
      algebraMap Ap Cp (algebraMap A Ap a)
    calc
      algebraMap R Cp (eA (algebraMap A Ap a)) =
          algebraMap R Cp (algebraMap A R a) :=
        congrArg (algebraMap R Cp) (eA.commutes a)
      _ = algebraMap A Cp a :=
        (IsScalarTower.algebraMap_apply A R Cp a).symm
      _ = algebraMap Ap Cp (algebraMap A Ap a) :=
        IsScalarTower.algebraMap_apply A Ap Cp a
  letI : IsScalarTower Ap R Cp := IsScalarTower.of_algebraMap_eq fun x =>
    (DFunLike.congr_fun hmaps x).symm
  let eAAp : Ap ≃ₐ[Ap] R :=
    AlgEquiv.ofBijective (Algebra.ofId Ap R) eA.bijective
  letI : Algebra.FormallyUnramified Ap R :=
    Algebra.FormallyUnramified.of_equiv eAAp
  letI : Algebra.FormallyUnramified R Cp :=
    criticalBlockSchurLocalization_formallyUnramified K hm hn hB hB2
  exact Algebra.FormallyUnramified.comp Ap R Cp

end
end GaloisForLFunctions.HTGeometry
