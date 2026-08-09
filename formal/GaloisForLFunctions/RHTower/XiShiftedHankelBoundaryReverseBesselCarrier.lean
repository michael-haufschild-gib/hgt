import GaloisForLFunctions.RHTower.ReverseBesselPositiveIntegral
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundarySourceJet

/-!
# Reverse-Bessel carrier of the shifted-Xi Hankel boundary source

The sole shifted-Hankel extension coordinate is a coefficient combination of consecutive
normalized completed source moments.  On the Euler ray, each prime-discrepancy kernel has the
positive Gamma representation of the reverse-Bessel polynomial.  This file combines those
representations before discarding the adaptive null polynomial.

For a coefficient vector `c`, base order `r`, and

`A(u,x,w) = u * (w * log x + u / 2)`, `T(u,x,w) = A(u,x,w) / (2 * w^2)`,

the exact combined radial kernel is

`x^(-(1/2+w)) / (2^r w^(2r+1)) *
  integral exp(-u) A(u,x,w)^r P^sharp(T(u,x,w)) du`,

where

`P^sharp(T) = sum_j c_j T^j / ((r+j)!)^2`.

Both the density and carrier argument are positive on `w > 0`, `x >= 1`, `u > 0`.  Therefore the
remaining sign is exactly the distribution of the positive Gamma carrier across the sign
intervals of the factorial-diagonal transform `P^sharp`; positivity of the reverse-Bessel kernel
alone cannot orient it.
-/

open Complex Matrix MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Factorial-diagonal transform selected by a consecutive shifted-Hankel coefficient vector. -/
def xiShiftedBoundaryFactorialCarrierPolynomial
    (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin N,
    (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2)) * t ^ (j : ℕ)

/-- Coefficient-combined radial kernel occurring inside the normalized prime-discrepancy source
jet. -/
def xiShiftedHankelBoundaryRadialKernel
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin N,
    c j * radialBesselKernel (r + (j : ℕ)) (1 / 2 + w) x /
      completedSourceMomentScale (r + (j : ℕ)) w

/-- Lebesgue-minus-Chebyshev discrepancy tested against one coefficient-combined radial packet. -/
def xiShiftedHankelBoundaryRadialDiscrepancy
    (w : ℝ) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  (∫ x in Ioi (1 : ℝ), xiShiftedHankelBoundaryRadialKernel w r c x) -
    ∫ x, xiShiftedHankelBoundaryRadialKernel w r c x
      ∂chebyshevPsiStieltjes.measure

/-- On the physical Euler ray, the factorial carrier variable is nonnegative. -/
theorem xiShiftedBoundaryFactorialCarrierArgument_nonneg
    {w x u : ℝ} (hw : 0 < w) (hx : 1 ≤ x) (hu : 0 ≤ u) :
    0 ≤ u * (w * Real.log x + u / 2) / (2 * w ^ 2) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  positivity

/-- The Gamma density multiplying the transformed polynomial is strictly positive away from the
endpoint `u = 0`. -/
theorem xiShiftedBoundaryFactorialCarrierDensity_pos
    (r : ℕ) {w x u : ℝ} (hw : 0 < w) (hx : 1 ≤ x) (hu : 0 < u) :
    0 < Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsum : 0 < w * Real.log x + u / 2 := by positivity
  positivity

/-- The radial kernel is the reverse-Bessel polynomial at `w * log x`. -/
theorem radialBesselKernel_half_add_eq_reverseBesselPoly
    (n : ℕ) (w x : ℝ) :
    radialBesselKernel n (1 / 2 + w) x =
      x ^ (-(1 / 2 + w)) * reverseBesselPoly n (w * Real.log x) := by
  simp only [radialBesselKernel, reverseBesselPoly]
  congr 2
  funext j
  congr 1
  ring

private theorem integrableOn_factorialCarrierTerm
    (r j : ℕ) (w z : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-u) * (u * (z + u / 2)) ^ r *
        (u * (z + u / 2) / (2 * w ^ 2)) ^ j)
      (Ioi (0 : ℝ)) := by
  have hbase := integrableOn_reverseBesselPositiveIntegrand (r + j) z
  have hscaled := hbase.const_mul ((2 * w ^ 2) ^ j)⁻¹
  refine hscaled.congr ?_
  filter_upwards with u
  rw [div_pow]
  simp only [mul_pow, div_eq_mul_inv]
  rw [pow_add, pow_add]
  ring

/-- **Adaptive reverse-Bessel carrier law.**  A whole consecutive boundary-source packet is one
positive Gamma carrier tested against the factorial-diagonal transform of its coefficient
polynomial.  The result is pointwise in the arithmetic variable `x`; no asymptotic or numerical
input is used. -/
theorem xiShiftedHankelBoundaryRadialKernel_eq_factorialCarrierIntegral
    {w : ℝ} (hw : w ≠ 0) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) (x : ℝ) :
    xiShiftedHankelBoundaryRadialKernel w r c x =
      x ^ (-(1 / 2 + w)) / ((2 : ℝ) ^ r * w ^ (2 * r + 1)) *
        ∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
            xiShiftedBoundaryFactorialCarrierPolynomial r c
              (u * (w * Real.log x + u / 2) / (2 * w ^ 2)) := by
  have hIntegral :
      (∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
            xiShiftedBoundaryFactorialCarrierPolynomial r c
              (u * (w * Real.log x + u / 2) / (2 * w ^ 2))) =
        ∑ j : Fin N,
          (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2)) *
            ∫ u in Ioi (0 : ℝ),
              Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
                (u * (w * Real.log x + u / 2) / (2 * w ^ 2)) ^ (j : ℕ) := by
    have hpoint :
        (fun u : ℝ =>
          Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
            xiShiftedBoundaryFactorialCarrierPolynomial r c
              (u * (w * Real.log x + u / 2) / (2 * w ^ 2))) =
        fun u : ℝ => ∑ j : Fin N,
          (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2)) *
            (Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
              (u * (w * Real.log x + u / 2) / (2 * w ^ 2)) ^ (j : ℕ)) := by
      funext u
      unfold xiShiftedBoundaryFactorialCarrierPolynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hpoint, MeasureTheory.integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _
      rw [MeasureTheory.integral_const_mul]
    · intro j _
      exact (integrableOn_factorialCarrierTerm r (j : ℕ) w
        (w * Real.log x)).const_mul
          (c j / (((r + (j : ℕ)).factorial : ℝ) ^ 2))
  rw [xiShiftedHankelBoundaryRadialKernel, hIntegral, Finset.mul_sum]
  simp_rw [radialBesselKernel_half_add_eq_reverseBesselPoly,
    reverseBesselPoly_eq_positiveIntegral]
  apply Finset.sum_congr rfl
  intro j _
  have hterm :
      (∫ u in Ioi (0 : ℝ),
          Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ r *
            (u * (w * Real.log x + u / 2) / (2 * w ^ 2)) ^ (j : ℕ)) =
        ((2 * w ^ 2) ^ (j : ℕ))⁻¹ *
          ∫ u in Ioi (0 : ℝ),
            Real.exp (-u) * u ^ (r + (j : ℕ)) *
              (w * Real.log x + u / 2) ^ (r + (j : ℕ)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [div_pow, mul_pow, mul_pow]
    field_simp [hw]
    rw [pow_add, pow_add]
    ring
  rw [hterm, completedSourceMomentScale, pow_add]
  rw [show 2 * (r + (j : ℕ)) + 1 = (2 * r + 1) + 2 * (j : ℕ) by omega,
    pow_add]
  rw [show w ^ (2 * (j : ℕ)) = (w ^ 2) ^ (j : ℕ) by rw [← pow_mul]]
  rw [mul_pow]
  field_simp [hw, Nat.factorial_ne_zero]

/-- A finite normalized boundary packet is Lebesgue-integrable on the Euler ray. -/
theorem integrableOn_xiShiftedHankelBoundaryRadialKernel
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    IntegrableOn (xiShiftedHankelBoundaryRadialKernel w r c) (Ioi (1 : ℝ)) := by
  unfold xiShiftedHankelBoundaryRadialKernel
  apply integrable_finsetSum Finset.univ
  intro j _
  have hs : 1 < 1 / 2 + w := by linarith
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (integrableOn_radialBesselKernel
      (n := r + (j : ℕ)) hs).const_mul
        (c j / completedSourceMomentScale (r + (j : ℕ)) w)

/-- A finite normalized boundary packet is integrable against the Chebyshev--Stieltjes measure. -/
theorem integrable_xiShiftedHankelBoundaryRadialKernel_chebyshev
    {w : ℝ} (hw : 1 / 2 < w) (r : ℕ) {N : ℕ} (c : Fin N → ℝ) :
    Integrable (xiShiftedHankelBoundaryRadialKernel w r c)
      chebyshevPsiStieltjes.measure := by
  unfold xiShiftedHankelBoundaryRadialKernel
  apply integrable_finsetSum Finset.univ
  intro j _
  have hs : 1 < 1 / 2 + w := by linarith
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (integrable_chebyshevPsiStieltjes
      (summable_vonMangoldt_mul_norm_radialBesselKernel
        (n := r + (j : ℕ)) hs)).const_mul
          (c j / completedSourceMomentScale (r + (j : ℕ)) w)

/-- **Combined discrepancy law.**  The coefficient-combined radial discrepancy is exactly the
prime-discrepancy part of the normalized completed boundary source jet.  Finite combination is
performed before either integral, so no componentwise estimate or loss of null cancellation is
introduced. -/
theorem xiShiftedHankelBoundaryDiscrepancyJet_eq_radialDiscrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelBoundaryDiscrepancyJet w n c =
      xiShiftedHankelBoundaryRadialDiscrepancy w n c := by
  have hLeb (j : Fin n) : IntegrableOn
      (fun x : ℝ => c j * radialBesselKernel (n + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (n + (j : ℕ)) w) (Ioi (1 : ℝ)) := by
    have hs : 1 < 1 / 2 + w := by linarith
    change Integrable
      (fun x : ℝ => c j * radialBesselKernel (n + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (n + (j : ℕ)) w)
      (volume.restrict (Ioi (1 : ℝ)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_radialBesselKernel
        (n := n + (j : ℕ)) hs).const_mul
          (c j / completedSourceMomentScale (n + (j : ℕ)) w)
  have hCheb (j : Fin n) : Integrable
      (fun x : ℝ => c j * radialBesselKernel (n + (j : ℕ)) (1 / 2 + w) x /
        completedSourceMomentScale (n + (j : ℕ)) w)
      chebyshevPsiStieltjes.measure := by
    have hs : 1 < 1 / 2 + w := by linarith
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_chebyshevPsiStieltjes
        (summable_vonMangoldt_mul_norm_radialBesselKernel
          (n := n + (j : ℕ)) hs)).const_mul
            (c j / completedSourceMomentScale (n + (j : ℕ)) w)
  simp only [xiShiftedHankelBoundaryDiscrepancyJet,
    normalizedChebyshevDiscrepancyMoment]
  simp only [xiShiftedHankelBoundaryRadialDiscrepancy,
    xiShiftedHankelBoundaryRadialKernel]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hLeb j),
    MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hCheb j)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_div, MeasureTheory.integral_const_mul]
  ring

/-- **Arithmetic carrier discrepancy law.**  The actual prime-discrepancy boundary jet is the
Lebesgue-minus-Chebyshev action on one positive Gamma carrier tested against the
factorial-diagonal adaptive polynomial. -/
theorem xiShiftedHankelBoundaryDiscrepancyJet_eq_factorialCarrierDiscrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelBoundaryDiscrepancyJet w n c =
      (∫ x in Ioi (1 : ℝ),
        x ^ (-(1 / 2 + w)) / ((2 : ℝ) ^ n * w ^ (2 * n + 1)) *
          ∫ u in Ioi (0 : ℝ),
            Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ n *
              xiShiftedBoundaryFactorialCarrierPolynomial n c
                (u * (w * Real.log x + u / 2) / (2 * w ^ 2))) -
        ∫ x,
          (x ^ (-(1 / 2 + w)) / ((2 : ℝ) ^ n * w ^ (2 * n + 1)) *
            ∫ u in Ioi (0 : ℝ),
              Real.exp (-u) * (u * (w * Real.log x + u / 2)) ^ n *
                xiShiftedBoundaryFactorialCarrierPolynomial n c
                  (u * (w * Real.log x + u / 2) / (2 * w ^ 2)))
          ∂chebyshevPsiStieltjes.measure := by
  rw [xiShiftedHankelBoundaryDiscrepancyJet_eq_radialDiscrepancy hw]
  unfold xiShiftedHankelBoundaryRadialDiscrepancy
  congr 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact xiShiftedHankelBoundaryRadialKernel_eq_factorialCarrierIntegral
      (ne_of_gt (by linarith : 0 < w)) n c x
  · apply integral_congr_ae
    filter_upwards with x
    exact xiShiftedHankelBoundaryRadialKernel_eq_factorialCarrierIntegral
      (ne_of_gt (by linarith : 0 < w)) n c x

/-- The first omitted shifted-Xi coupling is exactly its archimedean source jet plus the combined
factorial-carrier arithmetic discrepancy. -/
theorem xiShiftedHankelFirstOmittedCoupling_eq_archimedean_add_radialDiscrepancy
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin n → ℝ) :
    xiShiftedHankelFirstOmittedCoupling (w ^ 2) n c =
      xiShiftedHankelBoundaryArchimedeanJet w n c +
        xiShiftedHankelBoundaryRadialDiscrepancy w n c := by
  rw [xiShiftedHankelFirstOmittedCoupling_eq_archimedean_add_discrepancy hw,
    xiShiftedHankelBoundaryDiscrepancyJet_eq_radialDiscrepancy hw]

end

end RHTower
