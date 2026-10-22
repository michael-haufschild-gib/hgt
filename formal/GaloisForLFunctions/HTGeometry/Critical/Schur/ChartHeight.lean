import GaloisForLFunctions.HTGeometry.Critical.Schur.ChartAlgebra
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.PID

/-!
# The Schur place is a height-one point of the chart algebra

Because the Schur coordinate ring sits inside the chart algebra which sits inside the Schur
valuation ring, and the valuation ring is the localization of the Schur coordinate ring at the
Schur prime, it is also the localization of the chart algebra at the centre of the place.  A
discrete valuation ring has Krull dimension one, so that centre has height one.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- The Schur coordinate ring maps into the chart algebra. -/
noncomputable def schurRingToChartAlgebra (p : criticalSchurSourceRing K m n) :
    criticalSourceChartAlgebra K (m := m) (n := n) :=
  ⟨MvPolynomial.aeval
      (criticalSourceSchurCoordinates K (Fact.out : 0 < m) (Fact.out : 0 < n)) p,
    schurCoordinateAeval_mem_chartAlgebra K p⟩

theorem chartAlgebraToSchur_schurRingToChartAlgebra (p : criticalSchurSourceRing K m n) :
    chartAlgebraToSchur K (schurRingToChartAlgebra K p)
      = algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) p := by
  apply Subtype.ext
  exact (coe_algebraMap_criticalSchurSourceValuation K Fact.out Fact.out p).symm

/-- The centre of the Schur place on the chart algebra. -/
noncomputable def criticalSchurChartPrime : Ideal (criticalSourceChartAlgebra K (m := m) (n := n)) :=
  (maximalIdeal (criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
    (Fact.out : 0 < n))).comap (algebraMap _ _)

instance criticalSchurChartPrime_isPrime :
    (criticalSchurChartPrime K (m := m) (n := n)).IsPrime :=
  Ideal.comap_isPrime _ _

/-- **The Schur valuation ring is the localization of the chart algebra at that centre.** -/
instance criticalSchurChartPrime_isLocalization :
    IsLocalization (criticalSchurChartPrime K (m := m) (n := n)).primeCompl
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) := by
  constructor; constructor
  · rintro ⟨y, hy⟩
    exact IsLocalRing.notMem_maximalIdeal.mp hy
  · intro z
    obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj
      (M := (criticalSchurPrimeDivisor K (Fact.out : 0 < m) (Fact.out : 0 < n)).1.primeCompl) z
    refine ⟨⟨schurRingToChartAlgebra K p, ⟨schurRingToChartAlgebra K (s : _), ?_⟩⟩, ?_⟩
    · show schurRingToChartAlgebra K (s : criticalSchurSourceRing K m n) ∉
        criticalSchurChartPrime K
      intro hmem
      have hunit := IsLocalization.map_units
        (M := (criticalSchurPrimeDivisor K (Fact.out : 0 < m) (Fact.out : 0 < n)).1.primeCompl)
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) s
      rw [← chartAlgebraToSchur_schurRingToChartAlgebra K] at hunit
      exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hmem
    · have e1 := chartAlgebraToSchur_schurRingToChartAlgebra K p
      have e2 := chartAlgebraToSchur_schurRingToChartAlgebra K
        (s : criticalSchurSourceRing K m n)
      show z * chartAlgebraToSchur K (schurRingToChartAlgebra K
        (s : criticalSchurSourceRing K m n))
        = chartAlgebraToSchur K (schurRingToChartAlgebra K p)
      rw [e1, e2]
      exact hs
  · intro x y hxy
    exact ⟨1, congrArg (fun t => (1 : criticalSourceChartAlgebra K (m := m) (n := n)) * t)
      (chartAlgebraToSchur_injective K hxy)⟩

/-- **The centre of the Schur place on the chart algebra has height one.** -/
theorem criticalSchurChartPrime_height :
    (criticalSchurChartPrime K (m := m) (n := n)).height = 1 := by
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height
    (criticalSchurChartPrime K (m := m) (n := n))
    (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
  rw [IsPrincipalIdealRing.ringKrullDim_eq_one _
    (IsDiscreteValuationRing.not_isField
      (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))] at h
  exact_mod_cast h.symm

end

end GaloisForLFunctions.HTGeometry
