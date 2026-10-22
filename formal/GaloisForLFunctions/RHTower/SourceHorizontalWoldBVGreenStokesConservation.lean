import GaloisForLFunctions.RHTower.SourceHorizontalWoldEulerGreenAnomaly
import GaloisForLFunctions.RHTower.Deninger.DeningerOrdinaryIntegerBVGreenStokesRadialComparison

/-!
# Wold prime-clock profile as an ordinary-integer BV Green--Stokes boundary

The inverse-Euler Green profile selected by the source-horizontal Wold clock is not only a
coefficientwise analogy.  At finite prime-clock depth, every hyperbolic-sine atom is exactly the
reflected physical evaluation of the genuine ordinary-integer Hochschild boundary
`[S_n^*, Q S_n]`.

For the `n`-th prime and terminal clock `N`, the source point is chosen before any Xi-divisor
specialization with real grade

`2 Re(s) - 1 = u / log(p_N)`.

Multiplying the reflected BV boundary difference by `p_n / 2` recovers the corresponding Wold
atom without changing its prime label.  Summation gives an exact finite completed-source
conservation law.  Cofinally, the BV interior current tends to the inverse-Euler Green average,
and its endpoint defect is precisely the full Wold profile.

On the positive horizontal ray the interior current is strictly smaller than the endpoint, so the
endpoint defect has exactly the useful Wold sign.  This supplies the source-clock conservation but
not the missing order transport: selected CCM--Gamma residue would still have to preserve this
specific defect, and the pre-divisor firewall shows that such preservation is already RH-strength.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Source point whose ordinary-prime radial grade is the exact normalized Wold clock height. -/
def sourceHorizontalWoldBVGreenStokesScaledPoint
    (N _n : ℕ) (u : ℝ) : ℂ :=
  Complex.ofReal ((1 / 2 : ℝ) +
    u / (2 * xiMassNthPrimeLogHeight N))

@[simp] theorem sourceHorizontalWoldBVGreenStokesScaledPoint_re
    (N n : ℕ) (u : ℝ) :
    (sourceHorizontalWoldBVGreenStokesScaledPoint N n u).re =
      (1 / 2 : ℝ) +
        u / (2 * xiMassNthPrimeLogHeight N) := by
  rw [sourceHorizontalWoldBVGreenStokesScaledPoint, Complex.ofReal_re]

/-- One labelled Wold hyperbolic atom is exactly one reflected ordinary-prime BV
Green--Stokes boundary evaluation. -/
theorem sourceHorizontalWoldBVGreenStokesScaledBoundary_eq_sinh
    (N n : ℕ) (u : ℝ) :
    ((nthPrimeSubtype n : ℕ) : ℝ) / 2 *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
            (nthPrimeSubtype n) (sourceHorizontalWoldBVGreenStokesScaledPoint N n u) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
            (nthPrimeSubtype n)
            (1 - star (sourceHorizontalWoldBVGreenStokesScaledPoint N n u))) =
      Real.sinh
        (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) := by
  have hp : 0 < (nthPrimeSubtype n : ℕ) :=
    (nthPrimeSubtype n).property.pos
  have hclock : xiMassNthPrimeLogHeight N ≠ 0 :=
    (xiMassNthPrimeLogHeight_pos N).ne'
  calc
    ((nthPrimeSubtype n : ℕ) : ℝ) / 2 *
          (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
              (nthPrimeSubtype n) (sourceHorizontalWoldBVGreenStokesScaledPoint N n u) -
            deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
              (nthPrimeSubtype n)
              (1 - star (sourceHorizontalWoldBVGreenStokesScaledPoint N n u))) =
        (1 / 2 : ℝ) *
          (((nthPrimeSubtype n : ℕ) : ℝ) *
            (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
                (nthPrimeSubtype n)
                (sourceHorizontalWoldBVGreenStokesScaledPoint N n u) -
              deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
                (nthPrimeSubtype n)
                (1 - star
                  (sourceHorizontalWoldBVGreenStokesScaledPoint N n u)))) := by ring
    _ = (1 / 2 : ℝ) *
        deningerTensorSquareRadialMateCurvature
          (nthPrimeSubtype n)
          (sourceHorizontalWoldBVGreenStokesScaledPoint N n u) := by
      rw [deningerOrdinaryIntegerBVGreenStokes_reflectedDifference hp]
    _ = Real.sinh
        (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) := by
      rw [deningerTensorSquareRadialMateCurvature_eq_sinh _ _ hp,
        sourceHorizontalWoldBVGreenStokesScaledPoint_re]
      norm_num
      rw [show Real.log (((nthPrimeSubtype n : ℕ) : ℝ)) =
          xiMassNthPrimeLogHeight n by rfl]
      field_simp [hclock]
      ring_nf

/-- Finite source current obtained from the actual ordinary-prime BV Green--Stokes boundaries,
with Wold weights and every prime label retained. -/
def sourceHorizontalWoldBVGreenStokesInteriorCurrent
    (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (woldCoeff 1 (nthPrimeSubtype n) / xiMassNthPrimeLogHeight n) *
      (((nthPrimeSubtype n : ℕ) : ℝ) / 2 *
        (deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
            (nthPrimeSubtype n) (sourceHorizontalWoldBVGreenStokesScaledPoint N n u) -
          deningerOrdinaryIntegerBVGreenStokesBoundaryEvaluation
            (nthPrimeSubtype n)
            (1 - star (sourceHorizontalWoldBVGreenStokesScaledPoint N n u))))

/-- Coefficient-faithful identification of the BV interior current with the finite Wold Green
average. -/
theorem sourceHorizontalWoldBVGreenStokesInteriorCurrent_eq
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldBVGreenStokesInteriorCurrent N u =
      ∑ n ∈ Finset.range (N + 1),
        woldCoeff 1 (nthPrimeSubtype n) *
          (Real.sinh
              (u * xiMassNthPrimeLogHeight n / xiMassNthPrimeLogHeight N) /
            xiMassNthPrimeLogHeight n) := by
  rw [sourceHorizontalWoldBVGreenStokesInteriorCurrent]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sourceHorizontalWoldBVGreenStokesScaledBoundary_eq_sinh]
  ring

/-- **Finite completed-source conservation.**  Endpoint equals genuine BV interior current minus
the complete Wold residual, before any Xi-divisor residue is taken. -/
theorem sourceHorizontalWoldBVGreenStokes_finite_conservation
    (N : ℕ) (u : ℝ) :
    sourceHorizontalWoldBVGreenStokesInteriorCurrent N u =
      Real.sinh u + sourceHorizontalWoldPrimeClockProfileSeries N u := by
  rw [sourceHorizontalWoldPrimeClockProfileSeries_eq_finiteDeformation,
    sourceHorizontalWoldBVGreenStokesInteriorCurrent_eq]
  ring

/-- The genuine BV interior current converges to the inverse-Euler Green profile. -/
theorem tendsto_sourceHorizontalWoldBVGreenStokesInteriorCurrent
    (u : ℝ) :
    Tendsto (fun N : ℕ => sourceHorizontalWoldBVGreenStokesInteriorCurrent N u)
      atTop (nhds (sourceHorizontalWoldEulerGreenProfile u)) := by
  have hprofile := tendsto_sourceHorizontalWoldPrimeClockProfileSeries u
  have hconst : Tendsto (fun _ : ℕ => Real.sinh u) atTop (nhds (Real.sinh u)) :=
    tendsto_const_nhds
  have hsum := hconst.add hprofile
  rw [show sourceHorizontalWoldEulerGreenProfile u =
      Real.sinh u + sourceHorizontalWoldPrimeClockUniversalProfile u by
    rw [sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh]
    ring]
  exact hsum.congr' (Eventually.of_forall fun N =>
    (sourceHorizontalWoldBVGreenStokes_finite_conservation N u).symm)

/-- Cofinal completed-source conservation: the Wold residual is exactly the endpoint-minus-Green
defect of the actual BV boundary current. -/
theorem sourceHorizontalWoldBVGreenStokes_limit_conservation
    (u : ℝ) :
    sourceHorizontalWoldEulerGreenProfile u - Real.sinh u =
      sourceHorizontalWoldPrimeClockUniversalProfile u := by
  exact (sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh u).symm

/-- Positive source split: on every positive horizontal grade the genuine BV Green interior
carries strictly less than the endpoint.  This is the exact scalar defect later amplified by the
Wold--Julia orbit; it does not assert that divisor residue preserves the resulting order. -/
theorem sourceHorizontalWoldBVGreenStokesInterior_lt_endpoint
    {u : ℝ} (hu : 0 < u) :
    sourceHorizontalWoldEulerGreenProfile u < Real.sinh u := by
  have hneg := sourceHorizontalWoldPrimeClockUniversalProfile_neg_of_pos hu
  rw [sourceHorizontalWoldPrimeClockUniversalProfile_eq_eulerGreen_sub_sinh] at hneg
  linarith

end

end RHTower
