import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedMomentFarRightAsymptotic
import GaloisForLFunctions.HTGeometry.CentralBinomialAbelTransfer

/-!
# Far-right positivity of the adaptive mixed arithmetic source

The source-first adaptive packet has a literal Archimedean-plus-Lebesgue-minus-von-Mangoldt
formation, but its mixed kernel is signed.  This module proves a stronger source-specific fact:
every fixed nonzero amplitude nevertheless gives a strictly positive completed arithmetic source
sufficiently far right.

The mechanism is the least coefficient, not pointwise kernel positivity.  If `d` is the least
nonzero degree of `A`, then the adaptive shear polynomial has least degree `2d+2` and least
coefficient `(d+1) A.trailingCoeff^2 > 0`.  The shifted-Xi moments recede to the arcsine moments
after mass dilation, so this coefficient is the unique surviving term.  Thus any persistent
obstruction must escape through a moving, nonuniform admission rather than a fixed reporter.
-/

open Filter Polynomial Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The shifted Euler connection acts diagonally on polynomial coefficients. -/
theorem xiShiftedBoundaryShiftedEuler_coeff (a : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (xiShiftedBoundaryShiftedEuler a P).coeff n =
      (n + a) * P.coeff n := by
  cases n with
  | zero => simp [xiShiftedBoundaryShiftedEuler]
  | succ n =>
      simp [xiShiftedBoundaryShiftedEuler, Polynomial.coeff_X_mul,
        Polynomial.coeff_derivative]
      ring

/-- Mass dilation of a finite shifted-Xi polynomial packet isolates its least nonzero
coefficient and the matching arcsine moment.  No uniformity in polynomial degree is used. -/
theorem tendsto_scaled_xiShiftedPolynomialMoment_sum (q : Polynomial ℝ) :
    Tendsto
      (fun w : ℝ => 2 * w ^ (2 * q.natTrailingDegree + 1) / Real.log w *
        (∑ k ∈ Finset.range (q.natDegree + 1),
          q.coeff k * (xiShiftedReciprocalMoment (w ^ 2) k).re))
      atTop
      (nhds (q.trailingCoeff *
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom q.natTrailingDegree)) := by
  let d := q.natTrailingDegree
  let C : ℕ → ℝ := fun k =>
    if k = d then q.coeff k *
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom k else 0
  have hterms : ∀ k ∈ Finset.range (q.natDegree + 1),
      Tendsto
        (fun w : ℝ => 2 * w ^ (2 * d + 1) / Real.log w *
          (q.coeff k * (xiShiftedReciprocalMoment (w ^ 2) k).re))
        atTop (nhds (C k)) := by
    intro k hk
    by_cases hlt : k < d
    · have hcoeff : q.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
      simp [C, hcoeff, ne_of_lt hlt]
    · by_cases heq : k = d
      · subst k
        have h :=
          (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam d).const_mul
            (q.coeff d)
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using h
      · have hdk : d < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        have hinv := (tendsto_inv_atTop_zero :
          Tendsto (fun w : ℝ => w⁻¹) atTop (nhds 0)).pow (2 * (k - d))
        have hprod := hinv.mul
          (tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam k)
        have hscaled := hprod.const_mul (q.coeff k)
        have hexp : 2 * (k - d) ≠ 0 := by omega
        have hlim : q.coeff k *
            (0 ^ (2 * (k - d)) *
              GaloisForLFunctions.HTGeometry.normalizedCentralBinom k) = 0 := by
          simp [hexp]
        rw [hlim] at hscaled
        have hevent :
            (fun w : ℝ => q.coeff k * ((w⁻¹) ^ (2 * (k - d)) *
                (2 * w ^ (2 * k + 1) / Real.log w *
                  (xiShiftedReciprocalMoment (w ^ 2) k).re))) =ᶠ[atTop]
              (fun w : ℝ => 2 * w ^ (2 * d + 1) / Real.log w *
                (q.coeff k * (xiShiftedReciprocalMoment (w ^ 2) k).re)) := by
          filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
          have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
          have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
          rw [show 2 * k + 1 = (2 * d + 1) + 2 * (k - d) by omega, pow_add]
          rw [inv_pow]
          field_simp [hw0, hlog]
        have ht := hscaled.congr' hevent
        simpa [C, heq] using ht
  have hsum := tendsto_finsetSum (Finset.range (q.natDegree + 1)) hterms
  have hdmem : d ∈ Finset.range (q.natDegree + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree q)
  have hCsum : (∑ k ∈ Finset.range (q.natDegree + 1), C k) =
      q.trailingCoeff * GaloisForLFunctions.HTGeometry.normalizedCentralBinom d := by
    rw [Finset.sum_eq_single d]
    · simp [C, d, Polynomial.trailingCoeff]
    · intro b hb hbd
      simp [C, hbd]
    · exact fun h => (h hdmem).elim
  rw [hCsum] at hsum
  simpa [d, Finset.mul_sum] using hsum

/-- Coordinate-free version of least-coefficient shifted-Xi recession. -/
theorem tendsto_scaled_xiShiftedMomentFunctional (q : Polynomial ℝ) :
    Tendsto
      (fun w : ℝ => 2 * w ^ (2 * q.natTrailingDegree + 1) / Real.log w *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) q)
      atTop
      (nhds (q.trailingCoeff *
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom q.natTrailingDegree)) := by
  have h := tendsto_scaled_xiShiftedPolynomialMoment_sum q
  apply h.congr'
  filter_upwards with w
  congr 1
  have hrange := q.sum_over_range
    (f := fun k c => c * (xiShiftedReciprocalMoment (w ^ 2) k).re) (by simp)
  rw [Polynomial.sum_def] at hrange
  rw [HTGeometry.momentFunctional_eq_support_sum, hrange]

/-- Exact least-degree law for the adaptive shear polynomial.  Its least coefficient is a
positive square times the Euler weight `d+1`. -/
theorem xiShiftedBoundaryAdaptiveShearPolynomial_trailing
    {A : Polynomial ℝ} (hA : A ≠ 0) :
    let d := A.natTrailingDegree
    let Q := xiShiftedBoundaryAdaptiveShearPolynomial A
    Q.natTrailingDegree = 2 * d + 2 ∧
      Q.trailingCoeff = (d + 1 : ℕ) * A.trailingCoeff ^ 2 := by
  dsimp only
  let d := A.natTrailingDegree
  let E := xiShiftedBoundaryShiftedEuler 1 A
  have hAd : A.coeff d ≠ 0 := by
    simpa [d, Polynomial.trailingCoeff] using
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hA)
  have hEcoeff : E.coeff d = ((d : ℝ) + 1) * A.coeff d := by
    simpa [E] using xiShiftedBoundaryShiftedEuler_coeff (1 : ℝ) A d
  have hEcoeff0 : E.coeff d ≠ 0 := by
    rw [hEcoeff]
    exact mul_ne_zero (by positivity) hAd
  have hE : E ≠ 0 := by
    intro hz
    rw [hz] at hEcoeff0
    exact hEcoeff0 (by simp)
  have hEtrail : E.natTrailingDegree = d := by
    apply le_antisymm
    · exact Polynomial.natTrailingDegree_le_of_ne_zero hEcoeff0
    · apply Polynomial.le_natTrailingDegree hE
      intro k hk
      rw [xiShiftedBoundaryShiftedEuler_coeff]
      rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk]
      ring
  have hEtc : E.trailingCoeff = ((d : ℝ) + 1) * A.trailingCoeff := by
    rw [Polynomial.trailingCoeff, hEtrail, hEcoeff]
    rfl
  have hX : (X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
  have hXtc : (X : Polynomial ℝ).trailingCoeff = 1 := by
    rw [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X]
    simp
  have hXA : X * A ≠ 0 := mul_ne_zero hX hA
  have hXE : X * E ≠ 0 := mul_ne_zero hX hE
  constructor
  · rw [xiShiftedBoundaryAdaptiveShearPolynomial,
      Polynomial.natTrailingDegree_mul hXA hXE,
      Polynomial.natTrailingDegree_mul hX hA,
      Polynomial.natTrailingDegree_mul hX hE,
      hEtrail]
    simp [d]
    omega
  · rw [xiShiftedBoundaryAdaptiveShearPolynomial,
      Polynomial.trailingCoeff_mul,
      Polynomial.trailingCoeff_mul,
      Polynomial.trailingCoeff_mul, hEtc]
    simp [hXtc, d]
    ring

/-- The adaptive shear itself has a strictly positive arcsine recession constant. -/
theorem tendsto_scaled_xiShiftedAdaptiveShear
    {A : Polynomial ℝ} (hA : A ≠ 0) :
    let d := A.natTrailingDegree
    Tendsto
      (fun w : ℝ => 2 * w ^ (4 * d + 5) / Real.log w *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (xiShiftedBoundaryAdaptiveShearPolynomial A))
      atTop
      (nhds ((((d + 1 : ℕ) : ℝ) * A.trailingCoeff ^ 2) *
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom (2 * d + 2))) := by
  dsimp only
  obtain ⟨hdeg, hcoeff⟩ := xiShiftedBoundaryAdaptiveShearPolynomial_trailing hA
  have h := tendsto_scaled_xiShiftedMomentFunctional
    (xiShiftedBoundaryAdaptiveShearPolynomial A)
  rw [hdeg, hcoeff] at h
  have hexp : 2 * (2 * A.natTrailingDegree + 2) + 1 =
      4 * A.natTrailingDegree + 5 := by omega
  simpa only [hexp] using h

/-- **Adaptive arithmetic-source recession law.**  The literal completed source, before any
reflection aggregation, has a positive exact far-right asymptotic selected by the admitted
amplitude's least coefficient. -/
theorem tendsto_scaled_xiShiftedAdaptiveArithmeticSource
    {A : Polynomial ℝ} (hA : A ≠ 0) :
    let d := A.natTrailingDegree
    Tendsto
      (fun w : ℝ => w ^ (4 * d + 5) / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w A)
      atTop
      (nhds ((((d + 1 : ℕ) : ℝ) * A.trailingCoeff ^ 2) *
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom (2 * d + 2))) := by
  dsimp only
  have h := tendsto_scaled_xiShiftedAdaptiveShear hA
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hsource : xiShiftedAdaptiveMixedCompletedArithmeticSource w A =
      2 * HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
        (xiShiftedBoundaryAdaptiveShearPolynomial A) := by
    rw [← xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource
        (by linarith : 1 / 2 < w) A,
      xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear
        (sq_pos_of_pos (lt_trans zero_lt_one hw)) A]
    simp only [HTGeometry.momentInner_def,
      xiShiftedBoundaryAdaptiveShearPolynomial]
  rw [hsource]
  ring

/-- Every fixed nonzero admission makes the actual adaptive Archimedean--Lebesgue--von-Mangoldt
source strictly positive sufficiently far right. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_eventually_pos
    {A : Polynomial ℝ} (hA : A ≠ 0) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  let d := A.natTrailingDegree
  have htc : A.trailingCoeff ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hA
  have hlimit : 0 < (((d + 1 : ℕ) : ℝ) * A.trailingCoeff ^ 2) *
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom (2 * d + 2) := by
    exact mul_pos
      (mul_pos (by positivity) (sq_pos_of_ne_zero htc))
      (GaloisForLFunctions.HTGeometry.normalizedCentralBinom_pos _)
  have hscaled :=
    (tendsto_scaled_xiShiftedAdaptiveArithmeticSource hA).eventually
      (Ioi_mem_nhds hlimit)
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hs hw
  have hscale : 0 < w ^ (4 * d + 5) / Real.log w :=
    div_pos (pow_pos (lt_trans zero_lt_one hw) _) (Real.log_pos hw)
  rcases mul_pos_iff.mp hs with h | h
  · exact h.2
  · exact (not_lt_of_ge hscale.le h.1).elim

/-- Horizon form of fixed-admission source positivity. -/
theorem exists_xiShiftedAdaptiveMixedCompletedArithmeticSource_pos_horizon
    {A : Polynomial ℝ} (hA : A ≠ 0) :
    ∃ W : ℝ, ∀ w ≥ W,
      0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w A := by
  exact eventually_atTop.1
    (xiShiftedAdaptiveMixedCompletedArithmeticSource_eventually_pos hA)

end

end RHTower
