import GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelExteriorFlowNoGo
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoalescingXiSourceRate
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveArithmeticSourceArcsineAdmissionMargin
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.C5JensenPerturbation
import GaloisForLFunctions.HTGeometry.EnvelopeFromLogDerivative


/-!
# Interior first-zero reduction for the even Li completed-Abel current

This module proves LI-CAB6, a corpus-derived reduction of the remaining LI-CAB5 sign problem.
The fixed unit flux has the exact odd-Chebyshev normal form

`-(n+1) * (1-X) * U_[2n+1](2X-1)`.

After dilation by squared mass `v`, its Xi reciprocal-moment functional is the real adjacent
completed-Abel current.  Every polynomial moment has a right limit at `v = 0`; only its constant
coefficient survives.  The current therefore has the strictly positive central trace

`2 * (n+1)^(2 : ℕ) * normalizedPrimeArchMoment 0`.

Continuity then turns every nonpositive interior current value into an actual positive-mass zero.
Consequently, excluding zeros of this one explicit current for every mode on `0 < v <= 1/4`
forces positive current there, hence the LI-CAB5 endpoint inequality, LI-CAB3, and RH:

no interior current zero
`=>` positive current
`=>` nonnegative completed-Abel endpoint
`=>` LI-CAB3
`=>` RH.

All theorems are unconditional.  This module does not assert zero-exclusion; it isolates that
zero-exclusion as the exact remaining burden and proves that any failure produces a concrete
positive-mass zero.
-/

open Polynomial Real Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

theorem derivative_liEvenCrossUnitAmplitude (n : ℕ) :
    (liEvenCrossUnitAmplitude n).derivative =
      2 * Polynomial.C ((n : ℝ) + 1) *
        ((Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) := by
  rw [liEvenCrossUnitAmplitude, Polynomial.derivative_comp,
    derivative_chebyshevT_succ]
  simp only [mul_comp, Polynomial.C_comp]
  have haff : liEvenCrossUnitAffine.derivative = 2 := by
    simp [liEvenCrossUnitAffine]
  rw [haff]
  ring

theorem liEvenCrossUnitFluxQuotient_eq_oddChebyshev (n : ℕ) :
    liEvenCrossUnitFluxQuotient n =
      -((n : Polynomial ℝ) + 1) * (1 - X) *
        ((Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp
          liEvenCrossUnitAffine) := by
  have hder := congrArg Polynomial.derivative
    (two_mul_liEvenCrossUnitDefect n)
  simp only [Polynomial.derivative_mul, Polynomial.derivative_ofNat,
    zero_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_pow, Nat.cast_ofNat] at hder
  rw [derivative_liEvenCrossUnitAmplitude] at hder
  rw [liEvenCrossUnitAmplitude] at hder
  have hC2 : Polynomial.C (2 : ℝ) = (2 : Polynomial ℝ) := by
    change Polynomial.C (2 : ℝ) = Polynomial.C (2 : ℝ)
    rfl
  rw [hC2] at hder
  norm_num at hder
  have hprod := congrArg (fun P : Polynomial ℝ => P.comp liEvenCrossUnitAffine)
    (XiShiftedArcsineAdmission.two_mul_T_mul_U_pred
      (n := n + 1) (by omega))
  have hprod' :
      2 * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).comp liEvenCrossUnitAffine *
          (Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine =
        (Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp
          liEvenCrossUnitAffine := by
    simpa [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
      show (((n + 1 : ℕ) - 1 : ℕ) : ℤ) = (n : ℤ) by omega,
      show ((2 * (n + 1) - 1 : ℕ) : ℤ) = ((2 * n + 1 : ℕ) : ℤ) by omega]
      using hprod
  have hdu :
      (liEvenCrossUnitDefect n).derivative =
        -((n : Polynomial ℝ) + 1) *
          ((Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp
            liEvenCrossUnitAffine) := by
    have hfactor :
        2 * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).comp liEvenCrossUnitAffine *
            (2 * ((n : Polynomial ℝ) + 1) *
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) =
          2 * ((n : Polynomial ℝ) + 1) *
            (2 * (Polynomial.Chebyshev.T ℝ ((n : ℤ) + 1)).comp liEvenCrossUnitAffine *
              (Polynomial.Chebyshev.U ℝ (n : ℤ)).comp liEvenCrossUnitAffine) := by
      ring
    rw [hfactor, hprod'] at hder
    have htwo :
        2 * (liEvenCrossUnitDefect n).derivative =
          2 * (-((n : Polynomial ℝ) + 1) *
            ((Polynomial.Chebyshev.U ℝ ((2 * n + 1 : ℕ) : ℤ)).comp
              liEvenCrossUnitAffine)) := by
      rw [hder]
      ring
    exact mul_left_cancel₀ (by norm_num : (2 : Polynomial ℝ) ≠ 0) htwo
  rw [liEvenCrossUnitFluxQuotient]
  rw [hdu]
  ring

theorem eval_liEvenCrossUnitFluxQuotient_zero (n : ℕ) :
    (liEvenCrossUnitFluxQuotient n).eval 0 = 2 * ((n : ℝ) + 1) ^ (2 : ℕ) := by
  rw [liEvenCrossUnitFluxQuotient_eq_oddChebyshev]
  simp [liEvenCrossUnitAffine, Polynomial.Chebyshev.U_eval_neg_one]
  ring

def liEvenCrossSquareMassAdjacentCurrent (v : ℝ) (n : ℕ) : ℝ :=
  HTGeometry.momentFunctional
    (fun k => (xiShiftedReciprocalMoment v k).re)
    ((liEvenCrossUnitFluxQuotient n).comp (Polynomial.C v * X))

theorem liEvenCrossSquareMassAdjacentCurrent_eq_re_tsum {v : ℝ} (hv : 0 < v) (n : ℕ) :
    liEvenCrossSquareMassAdjacentCurrent v n =
      (∑' q : XiZeroCopy, liEvenCrossSquareMassAdjacentFlux v n q).re := by
  exact (re_tsum_liEvenCrossSquareMassAdjacentFlux_eq_momentFunctional hv n).symm

theorem momentFunctional_monomial_comp_scale (s : ℕ → ℝ) (r a : ℝ) (n : ℕ) :
    HTGeometry.momentFunctional s
        ((Polynomial.monomial n a).comp (Polynomial.C r * X)) =
      a * r ^ n * s n := by
  have h := momentFunctional_scaledSequence_eq_comp_scale s 1 r
    (Polynomial.monomial n a)
  rw [HTGeometry.momentFunctional_monomial] at h
  simpa [mul_assoc] using h.symm

theorem tendsto_xiShiftedPolynomialMoment_zero (P : Polynomial ℝ) :
    Tendsto
      (fun v : ℝ => HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment v k).re)
        (P.comp (Polynomial.C v * X)))
      (𝓝[≥] (0 : ℝ))
      (𝓝 (P.eval 0 * normalizedPrimeArchMoment 0)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [Polynomial.add_comp, HTGeometry.momentFunctional_add,
        Polynomial.eval_add, add_mul] using hp.add hq
  | monomial n a =>
      have heq :
          (fun v : ℝ => HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment v k).re)
            ((Polynomial.monomial n a).comp (Polynomial.C v * X))) =
          (fun v : ℝ => a * v ^ n * (xiShiftedReciprocalMoment v n).re) := by
        funext v
        exact momentFunctional_monomial_comp_scale _ _ _ _
      rw [heq]
      cases n with
      | zero =>
          have hm := Complex.continuous_re.continuousAt.tendsto.comp
            (tendsto_xiShiftedReciprocalMoment_nhdsGE_zero 0)
          simpa [Polynomial.eval_monomial] using hm.const_mul a
      | succ n =>
          have hv : Tendsto (fun v : ℝ => v) (𝓝[≥] (0 : ℝ)) (𝓝 0) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          have hm := Complex.continuous_re.continuousAt.tendsto.comp
            (tendsto_xiShiftedReciprocalMoment_nhdsGE_zero (n + 1))
          have hprod := (hv.pow (n + 1)).mul hm
          simpa [Polynomial.eval_monomial, mul_assoc] using
            hprod.const_mul a

theorem tendsto_liEvenCrossSquareMassAdjacentCurrent_zero (n : ℕ) :
    Tendsto (fun v : ℝ => liEvenCrossSquareMassAdjacentCurrent v n)
      (𝓝[≥] (0 : ℝ))
      (𝓝 (2 * ((n : ℝ) + 1) ^ (2 : ℕ) * normalizedPrimeArchMoment 0)) := by
  have h := tendsto_xiShiftedPolynomialMoment_zero (liEvenCrossUnitFluxQuotient n)
  rw [eval_liEvenCrossUnitFluxQuotient_zero] at h
  exact h

theorem liEvenCrossSquareMassAdjacentCurrent_limit_pos (n : ℕ) :
    0 < 2 * ((n : ℝ) + 1) ^ (2 : ℕ) * normalizedPrimeArchMoment 0 := by
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by positivity)))
    normalizedPrimeArchMoment_zero_pos

theorem eventually_liEvenCrossSquareMassAdjacentCurrent_pos (n : ℕ) :
    ∀ᶠ v : ℝ in 𝓝[≥] (0 : ℝ), 0 < liEvenCrossSquareMassAdjacentCurrent v n := by
  exact (tendsto_liEvenCrossSquareMassAdjacentCurrent_zero n).eventually
    (Ioi_mem_nhds (liEvenCrossSquareMassAdjacentCurrent_limit_pos n))

theorem liEvenCrossSquareMassAdjacentCurrent_zero (n : ℕ) :
    liEvenCrossSquareMassAdjacentCurrent 0 n =
      2 * ((n : ℝ) + 1) ^ (2 : ℕ) * normalizedPrimeArchMoment 0 := by
  have hpoly :
      (liEvenCrossUnitFluxQuotient n).comp (Polynomial.C (0 : ℝ) * X) =
        Polynomial.C ((liEvenCrossUnitFluxQuotient n).eval 0) := by
    ext k
    simp
  rw [liEvenCrossSquareMassAdjacentCurrent, hpoly, HTGeometry.momentFunctional_C,
    eval_liEvenCrossUnitFluxQuotient_zero, xiShiftedReciprocalMoment_zero_eq_normalizedPrimeArchMoment]
  norm_num

theorem continuousWithinAt_liEvenCrossSquareMassAdjacentCurrent_zero (n : ℕ) :
    ContinuousWithinAt (fun v : ℝ => liEvenCrossSquareMassAdjacentCurrent v n) (Ici 0) 0 := by
  rw [ContinuousWithinAt, liEvenCrossSquareMassAdjacentCurrent_zero]
  exact tendsto_liEvenCrossSquareMassAdjacentCurrent_zero n

theorem continuousAt_xiShiftedPolynomialMoment {v : ℝ} (hv : 0 < v) (P : Polynomial ℝ) :
    ContinuousAt
      (fun y : ℝ => HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (P.comp (Polynomial.C y * X))) v := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      have heq :
          (fun y : ℝ => HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment y k).re)
            ((p + q).comp (Polynomial.C y * X))) =
          (fun y : ℝ => HTGeometry.momentFunctional
              (fun k => (xiShiftedReciprocalMoment y k).re)
              (p.comp (Polynomial.C y * X))) +
            (fun y : ℝ => HTGeometry.momentFunctional
              (fun k => (xiShiftedReciprocalMoment y k).re)
              (q.comp (Polynomial.C y * X))) := by
        funext y
        simp [Polynomial.add_comp, HTGeometry.momentFunctional_add]
      rw [heq]
      exact hp.add hq
  | monomial n a =>
      have heq :
          (fun y : ℝ => HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment y k).re)
            ((Polynomial.monomial n a).comp (Polynomial.C y * X))) =
          (fun y : ℝ => a * y ^ n * (xiShiftedReciprocalMoment y n).re) := by
        funext y
        exact momentFunctional_monomial_comp_scale _ _ _ _
      rw [heq]
      exact (continuousAt_const.mul (continuousAt_id.pow n)).mul
        (hasDerivAt_re_xiShiftedReciprocalMoment hv n).continuousAt

theorem continuousAt_liEvenCrossSquareMassAdjacentCurrent {v : ℝ} (hv : 0 < v) (n : ℕ) :
    ContinuousAt (fun y : ℝ => liEvenCrossSquareMassAdjacentCurrent y n) v := by
  exact continuousAt_xiShiftedPolynomialMoment hv _

theorem continuousOn_liEvenCrossSquareMassAdjacentCurrent_Icc {b : ℝ} (_hb : 0 ≤ b) (n : ℕ) :
    ContinuousOn (fun v : ℝ => liEvenCrossSquareMassAdjacentCurrent v n) (Icc 0 b) := by
  intro v hv
  rcases hv.1.eq_or_lt with rfl | hvpos
  · exact (continuousWithinAt_liEvenCrossSquareMassAdjacentCurrent_zero n).mono (Icc_subset_Ici_self)
  · exact (continuousAt_liEvenCrossSquareMassAdjacentCurrent hvpos n).continuousWithinAt

theorem exists_liEvenCrossInteriorCurrent_zero_of_nonpos
    {b : ℝ} (hb : 0 < b) (n : ℕ) (hnonpos : liEvenCrossSquareMassAdjacentCurrent b n ≤ 0) :
    ∃ c ∈ Ioc 0 b, liEvenCrossSquareMassAdjacentCurrent c n = 0 := by
  obtain ⟨c, hc, hzero⟩ :=
    GaloisForLFunctions.exists_zero_Icc_of_nonneg_of_nonpos hb.le
      (continuousOn_liEvenCrossSquareMassAdjacentCurrent_Icc hb.le n)
      (by rw [liEvenCrossSquareMassAdjacentCurrent_zero]; exact (liEvenCrossSquareMassAdjacentCurrent_limit_pos n).le)
      hnonpos
  refine ⟨c, ⟨?_, hc.2⟩, hzero⟩
  have hcne : c ≠ 0 := by
    intro h
    subst c
    rw [liEvenCrossSquareMassAdjacentCurrent_zero] at hzero
    exact (ne_of_gt (liEvenCrossSquareMassAdjacentCurrent_limit_pos n)) hzero
  exact lt_of_le_of_ne hc.1 (Ne.symm hcne)

theorem liEvenCrossInteriorCurrent_pos_iff_no_zero (n : ℕ) :
    (∀ v ∈ Ioc (0 : ℝ) (1 / 4), liEvenCrossSquareMassAdjacentCurrent v n ≠ 0) ↔
      ∀ v ∈ Ioc (0 : ℝ) (1 / 4), 0 < liEvenCrossSquareMassAdjacentCurrent v n := by
  constructor
  · intro hno v hv
    by_contra hnot
    obtain ⟨c, hc, hzero⟩ :=
      exists_liEvenCrossInteriorCurrent_zero_of_nonpos hv.1 n (not_lt.mp hnot)
    exact hno c ⟨hc.1, hc.2.trans hv.2⟩ hzero
  · intro hpos v hv hzero
    exact (ne_of_gt (hpos v hv)) hzero

theorem liEvenCrossEndpoint_nonneg_of_no_interiorCurrent_zero
    (n : ℕ) (hno : ∀ v ∈ Ioc (0 : ℝ) (1 / 4), liEvenCrossSquareMassAdjacentCurrent v n ≠ 0) :
    0 ≤ (liEvenCrossSquareMassValue (1 / 4) n).re := by
  have hpos := (liEvenCrossInteriorCurrent_pos_iff_no_zero n).mp hno
  have hlim : Tendsto
      (fun v : ℝ => (liEvenCrossSquareMassValue v n).re)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_liEvenCrossSquareMassValue_zero_right n)
    exact h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hlt : ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ), v < 1 / 4 :=
    Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds (by norm_num))
  have hcompare : ∀ᶠ v : ℝ in 𝓝[>] (0 : ℝ),
      (liEvenCrossSquareMassValue v n).re ≤
        (liEvenCrossSquareMassValue (1 / 4) n).re := by
    filter_upwards [self_mem_nhdsWithin, hlt] with v hv0 hvb
    apply GaloisForLFunctions.HTGeometry.le_of_hasDerivAt_nonneg hvb.le
    · intro t ht
      have htpos : 0 < t := hv0.trans_le ht.1
      have hd := hasDerivAt_re_liEvenCrossSquareMassValue_adjacentFlux htpos n
      rw [← liEvenCrossSquareMassAdjacentCurrent_eq_re_tsum htpos n] at hd
      exact hd
    · intro t ht
      exact (hpos t ⟨hv0.trans_le ht.1, ht.2⟩).le
  exact le_of_tendsto hlim hcompare

theorem riemannHypothesis_of_no_liEvenCrossInteriorCurrent_zero
    (hno : ∀ n : ℕ, ∀ v ∈ Ioc (0 : ℝ) (1 / 4), liEvenCrossSquareMassAdjacentCurrent v n ≠ 0) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_liEvenCompletedAbelClockNonnegative]
  intro n
  have hend := liEvenCrossEndpoint_nonneg_of_no_interiorCurrent_zero n (hno n)
  have hsq := congrArg Complex.re (liEvenCrossSquareMassValue_sq (1 / 2) n)
  norm_num at hsq
  rw [← hsq]
  exact hend

end
end RHTower

