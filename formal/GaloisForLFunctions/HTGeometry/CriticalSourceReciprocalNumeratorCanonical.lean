import GaloisForLFunctions.HTGeometry.CriticalSourceChartObservationTower
import GaloisForLFunctions.HTGeometry.CriticalReciprocalNumerator
import GaloisForLFunctions.HTGeometry.LocalizationAwayRingEquiv

/-!
# Canonical reciprocal numerator for the critical source chart

The source-chart construction originally selected a cleared reciprocal numerator from an
existence theorem.  The reciprocal-jet development later supplied an explicit recursive
numerator.  Injectivity of evaluation at the algebraically independent raw source coordinates
identifies the two polynomials.  Consequently the polynomial inverted by the source chart has a
fully explicit recursive presentation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable (K : Type*) [Field K] (m n : ℕ)

/-- The chosen source-chart numerator is the explicit recursively defined reciprocal numerator. -/
theorem criticalSourceRecipNumerator_eq_criticalReciprocalNumerator
    {k : ℕ} (hk : k < m + n) :
    criticalSourceRecipNumerator K m n hk =
      criticalReciprocalNumerator K (m + n) k := by
  apply aeval_criticalSourceRaw_injective K m n
  rw [aeval_criticalSourceRecipNumerator]
  have h := criticalSourceRecip_eq_numerator_div K hk
  have hx : criticalSourceRaw K m n ⟨0, by omega⟩ ≠ 0 := by
    intro hzero
    exact ((algebraicIndependent_criticalSourceRaw K m n).transcendental
      ⟨0, by omega⟩) (hzero ▸ isAlgebraic_zero)
  rw [eq_div_iff (pow_ne_zero (k + 1) hx)] at h
  simpa only [mul_comm] using h

variable [Fact (0 < m)] [Fact (0 < n)]

/-- Explicit polynomial inverted by the canonical critical source chart. -/
def criticalCanonicalSourceChartPoly : MvPolynomial (Fin (m + n)) K :=
  MvPolynomial.X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n)) *
    MvPolynomial.X (⟨m, by have := (Fact.out : 0 < n); omega⟩ : Fin (m + n)) *
      criticalReciprocalNumerator K (m + n) n

/-- The source-chart denominator is the marked raw product times the canonical reciprocal
numerator. -/
theorem criticalSourceChartPoly_eq_canonical :
    criticalSourceChartPoly K m n = criticalCanonicalSourceChartPoly K m n := by
  rw [criticalCanonicalSourceChartPoly]
  rw [criticalSourceChartPoly_eq,
    criticalSourceRecipNumerator_eq_criticalReciprocalNumerator K m n]

/-- Canonical recursive presentation of the critical source chart ring. -/
abbrev criticalCanonicalSourceChartRing :=
  Localization.Away (criticalCanonicalSourceChartPoly K m n)

/-- The original source chart and its explicit recursive presentation are the same ring. -/
noncomputable def criticalSourceChartCanonicalEquiv :
    criticalSourceChartRing K m n ≃+* criticalCanonicalSourceChartRing K m n :=
  awayRingEquiv (RingEquiv.refl _) (criticalSourceChartPoly_eq_canonical K m n)

/-- The canonical chart equivalence fixes every raw-coordinate polynomial. -/
theorem criticalSourceChartCanonicalEquiv_algebraMap
    (p : MvPolynomial (Fin (m + n)) K) :
    criticalSourceChartCanonicalEquiv K m n
        (algebraMap (MvPolynomial (Fin (m + n)) K)
          (criticalSourceChartRing K m n) p) =
      algebraMap (MvPolynomial (Fin (m + n)) K)
        (criticalCanonicalSourceChartRing K m n) p := by
  exact awayRingEquiv_algebraMap (RingEquiv.refl _)
    (criticalSourceChartPoly_eq_canonical K m n) p

variable [CharZero K] [IsAlgClosed K]

/-- The inverse constant coordinate transported to the canonical chart. -/
def criticalCanonicalChartInvX0 : criticalCanonicalSourceChartRing K m n :=
  criticalSourceChartCanonicalEquiv K m n (chartInvX0 K (m := m) (n := n))

/-- The transported inverse is an actual inverse of the canonical raw constant coordinate. -/
theorem criticalCanonicalChartInvX0_mul_X0 :
    criticalCanonicalChartInvX0 K m n *
        algebraMap (MvPolynomial (Fin (m + n)) K)
          (criticalCanonicalSourceChartRing K m n)
          (X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n))) = 1 := by
  have h := (isUnit_algebraMap_chartX0 K (m := m) (n := n)).val_inv_mul
  change chartInvX0 K (m := m) (n := n) *
      algebraMap (MvPolynomial (Fin (m + n)) K) (criticalSourceChartRing K m n)
        (X (⟨0, by have := (Fact.out : 0 < m); omega⟩ : Fin (m + n))) = 1 at h
  have hmapped := congrArg (criticalSourceChartCanonicalEquiv K m n) h
  simpa [criticalCanonicalChartInvX0, map_mul,
    criticalSourceChartCanonicalEquiv_algebraMap] using hmapped

/-- Every reciprocal chart coordinate has the explicit recursive numerator in the canonical
presentation. -/
theorem criticalSourceChartCanonicalEquiv_chartRecip {k : ℕ} (hk : k < m + n) :
    criticalSourceChartCanonicalEquiv K m n (chartRecip K (m := m) (n := n) hk) =
      algebraMap (MvPolynomial (Fin (m + n)) K)
          (criticalCanonicalSourceChartRing K m n)
          (criticalReciprocalNumerator K (m + n) k) *
        criticalCanonicalChartInvX0 K m n ^ (k + 1) := by
  rw [chartRecip, map_mul, map_pow, criticalCanonicalChartInvX0,
    criticalSourceChartCanonicalEquiv_algebraMap,
    criticalSourceRecipNumerator_eq_criticalReciprocalNumerator K m n hk]

/-- Raw observation generators become the corresponding explicit raw variables in the canonical
source chart. -/
theorem criticalSourceChartCanonicalEquiv_observation_X_inl (i : Fin n) :
    criticalSourceChartCanonicalEquiv K m n
        (observationRingToChart K (m := m) (n := n) (X (Sum.inl i))) =
      algebraMap (MvPolynomial (Fin (m + n)) K)
        (criticalCanonicalSourceChartRing K m n)
        (X (⟨m + (i : ℕ), by omega⟩ : Fin (m + n))) := by
  rw [observationRingToChart, MvPolynomial.aeval_X, chartObservationCoord,
    criticalSourceChartCanonicalEquiv_algebraMap]

/-- Reciprocal observation generators become their recursive numerator divided by the explicit
constant-coordinate power in the canonical source chart. -/
theorem criticalSourceChartCanonicalEquiv_observation_X_inr (j : Fin m) :
    criticalSourceChartCanonicalEquiv K m n
        (observationRingToChart K (m := m) (n := n) (X (Sum.inr j))) =
      algebraMap (MvPolynomial (Fin (m + n)) K)
          (criticalCanonicalSourceChartRing K m n)
          (criticalReciprocalNumerator K (m + n) (n + (j : ℕ))) *
        criticalCanonicalChartInvX0 K m n ^ (n + (j : ℕ) + 1) := by
  rw [observationRingToChart, MvPolynomial.aeval_X, chartObservationCoord,
    criticalSourceChartCanonicalEquiv_chartRecip]

end

end GaloisForLFunctions.HTGeometry
