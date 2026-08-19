import GaloisForLFunctions.HTGeometry.CriticalChartTowerFinite

/-!
# The centre of the Schur place on the observation chart has height one

Going down holds for the integral extension of the integrally closed chart ring by the chart
algebra, so the height of the centre upstairs splits as the height of the centre downstairs plus
the height in the fibre.  The centre upstairs has height one, so the centre downstairs has height
at most one; and it is not the zero ideal, because otherwise every element of the observation field
would be integral at the Schur place, contradicting nontriviality of the observation valuation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial IsLocalRing

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

instance chartRing_isDomain : IsDomain (criticalObservationChartRing K m n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (criticalObservationChartRing K m n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (criticalObservationMarked_ne_zero K (m := m) (n := n)))

instance chartRingSourceTower :
    IsScalarTower (criticalObservationChartRing K m n) (criticalObservationField K m n)
      (criticalSourceField K m n) := by
  refine IsScalarTower.of_algebraMap_eq' ?_
  refine (IsLocalization.ringHom_ext
    (Submonoid.powers (criticalObservationMarked K (m := m) (n := n))) ?_).symm
  refine RingHom.ext fun p => ?_
  show algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n)
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) p))
      = algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n)
        (algebraMap (criticalObservationRing K m n)
          (criticalObservationChartRing K m n) p)
  rw [← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationChartRing K m n) (criticalObservationField K m n),
    ← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationChartRing K m n) (criticalSourceField K m n),
    ← IsScalarTower.algebraMap_apply (criticalObservationRing K m n)
      (criticalObservationField K m n) (criticalSourceField K m n)]

/-- The centre of the Schur place on the chart ring. -/
noncomputable def criticalSchurChartUnder : Ideal (criticalObservationChartRing K m n) :=
  (criticalSchurChartPrime K (m := m) (n := n)).under (criticalObservationChartRing K m n)

instance criticalSchurChartUnder_isPrime :
    (criticalSchurChartUnder K (m := m) (n := n)).IsPrime :=
  Ideal.comap_isPrime _ _

instance criticalSchurChartPrime_liesOver :
    (criticalSchurChartPrime K (m := m) (n := n)).LiesOver
      (criticalSchurChartUnder K (m := m) (n := n)) := ⟨rfl⟩

theorem criticalSchurChartUnder_ne_bot :
    criticalSchurChartUnder K (m := m) (n := n) ≠ ⊥ := by
  intro hbot
  apply criticalSchurObservationValuationSubring_ne_top K
    (Fact.out : 0 < m) (Fact.out : 0 < n)
  ext a
  simp only [ValuationSubring.mem_top, iff_true]
  rw [mem_criticalSchurObservationValuationSubring_iff]
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective
    (A := criticalObservationChartRing K m n) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsT : algebraMap (criticalObservationChartRing K m n)
      (criticalSourceChartAlgebra K (m := m) (n := n)) s ∉
      criticalSchurChartPrime K (m := m) (n := n) := by
    intro hmem
    exact hs0 (by
      have : s ∈ criticalSchurChartUnder K (m := m) (n := n) := hmem
      rw [hbot, Ideal.mem_bot] at this
      exact this)
  set bs : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
    algebraMap (criticalSourceChartAlgebra K (m := m) (n := n)) _
      (algebraMap (criticalObservationChartRing K m n) _ s) with hbs
  set br : criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n) :=
    algebraMap (criticalSourceChartAlgebra K (m := m) (n := n)) _
      (algebraMap (criticalObservationChartRing K m n) _ r) with hbr
  have hbsunit : IsUnit bs := IsLocalRing.notMem_maximalIdeal.mp hsT
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hbsunit
  have hcoe : ∀ z : criticalObservationChartRing K m n,
      ((algebraMap (criticalSourceChartAlgebra K (m := m) (n := n))
        (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
        (algebraMap (criticalObservationChartRing K m n) _ z) :
          criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :
        criticalSourceField K m n)
      = algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) z := by
    intro z; rfl
  have hE : algebraMap (criticalObservationField K m n) (criticalSourceField K m n)
      (algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) r /
        algebraMap (criticalObservationChartRing K m n) (criticalObservationField K m n) s)
      = ((br * v : criticalSchurSourceValuationSubring K (Fact.out : 0 < m)
          (Fact.out : 0 < n)) : criticalSourceField K m n) := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hbsv : (bs : criticalSourceField K m n) * (v : criticalSourceField K m n) = 1 :=
      congrArg Subtype.val hv
    rw [hbs, hcoe] at hbsv
    have hsne : algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) s ≠ 0 :=
      fun h => by rw [h, zero_mul] at hbsv; exact zero_ne_one hbsv
    show _ = (br : criticalSourceField K m n) * (v : criticalSourceField K m n)
    rw [hbr, hcoe]
    field_simp
    linear_combination
      (algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) r) * hbsv.symm
  rw [hE]
  exact Subtype.property _

/-- **The centre of the Schur place on the chart ring has height one.** -/
theorem criticalSchurChartUnder_height :
    (criticalSchurChartUnder K (m := m) (n := n)).height = 1 := by
  have hform := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := criticalObservationChartRing K m n)
    (S := criticalSourceChartAlgebra K (m := m) (n := n))
    (criticalSchurChartUnder K (m := m) (n := n))
    (criticalSchurChartPrime K (m := m) (n := n))
  rw [criticalSchurChartPrime_height K] at hform
  have hle : (criticalSchurChartUnder K (m := m) (n := n)).height ≤ 1 := by
    rw [hform]
    exact le_self_add
  have hne : (criticalSchurChartUnder K (m := m) (n := n)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff]
    intro hmin
    exact criticalSchurChartUnder_ne_bot K
      (le_antisymm (hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le) bot_le)
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

end

end GaloisForLFunctions.HTGeometry
