import GaloisForLFunctions.HTGeometry.Critical.Chart.CentreHeight
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower

/-!
# Every point of the reduced fibre is a divisorial point

The chart algebra is module-finite over the observation chart ring, which is integrally closed, so
going down holds and the height of a prime is the height of its contraction plus its height in the
fibre.  A prime lying over the centre of the Schur place is minimal over the extended centre — that
is incomparability — so its fibre height is zero:

```text
criticalSchurChartOverPrime_height_eq_one
    ** every prime of the chart algebra over the centre of the Schur place has height one **
```

So the points of the reduced fibre are exactly the height-one primes of the chart algebra above the
branch divisor, and the ramified ones are those containing the Jacobian.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- **Every point of the reduced fibre is a divisorial point.**  A prime of the chart algebra lying
over the centre of the Schur place has height one. -/
theorem criticalSchurChartOverPrime_height_eq_one
    (P : Ideal (criticalSourceChartAlgebra K (m := m) (n := n))) [P.IsPrime]
    [P.LiesOver (criticalSchurChartUnder K (m := m) (n := n))] :
    P.height = 1 := by
  classical
  have hunder : P.under (criticalObservationChartRing K m n)
      = criticalSchurChartUnder K (m := m) (n := n) :=
    (Ideal.LiesOver.over (p := criticalSchurChartUnder K (m := m) (n := n)) (P := P)).symm
  have hform := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (criticalSchurChartUnder K (m := m) (n := n)) P
  rw [criticalSchurChartUnder_height K] at hform
  have hmin : P ∈ ((criticalSchurChartUnder K (m := m) (n := n)).map
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)))).minimalPrimes := by
    have h := Ideal.IsIntegral.mem_minimalPrimes_map_under
      (R := criticalObservationChartRing K m n) P
    rwa [hunder] at h
  haveI : (P.map (Ideal.Quotient.mk ((criticalSchurChartUnder K (m := m) (n := n)).map
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)))))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hmin.1.2)
  have hzero : (P.map (Ideal.Quotient.mk ((criticalSchurChartUnder K (m := m) (n := n)).map
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAlgebra K (m := m) (n := n)))))).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    have hmin' : P ∈ Ideal.comap (Ideal.Quotient.mk
        ((criticalSchurChartUnder K (m := m) (n := n)).map
          (algebraMap (criticalObservationChartRing K m n)
            (criticalSourceChartAlgebra K (m := m) (n := n))))) ''
        minimalPrimes ((criticalSourceChartAlgebra K (m := m) (n := n)) ⧸
          ((criticalSchurChartUnder K (m := m) (n := n)).map
            (algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartAlgebra K (m := m) (n := n))))) := by
      rw [← Ideal.minimalPrimes_eq_comap]
      exact hmin
    obtain ⟨Q, hQmin, hQ⟩ := hmin'
    have hPQ : P.map (Ideal.Quotient.mk ((criticalSchurChartUnder K (m := m) (n := n)).map
        (algebraMap (criticalObservationChartRing K m n)
          (criticalSourceChartAlgebra K (m := m) (n := n))))) = Q := by
      rw [← hQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [hPQ]
    exact hQmin
  rw [hzero, add_zero] at hform
  exact hform

end

end GaloisForLFunctions.HTGeometry
