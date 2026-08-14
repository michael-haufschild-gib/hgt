import GaloisForLFunctions.RHTower.XiShiftedHardEdgeParabolicNyquistParity
import GaloisForLFunctions.HTGeometry.TwoChannelRelativeCapacityNoGo

/-!
# Route U Nyquist null-form rigidity

The parabolic shell is the pure detail mode `(E,O)=(h,-h)`.  Any quadratic current that kills
this mode factors through reconstruction `S=E+O`.  Positivity kills its remaining mixed
reconstruction/detail coefficient, leaving only a multiple of `S²`.  The signed quotient current
`S D=E²-O²` is the unique nontrivial safe direction and vanishes at both the fixed-divisor and
parabolic ends.
-/

open scoped BigOperators SchwartzMap FourierTransform
open Complex Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A real quadratic current in reconstruction/detail coordinates pulled back to even/odd
polyphase coordinates. -/
def routeUNyquistChannelCurrent
    (reconstructionWeight mixedWeight detailWeight even odd : ℝ) : ℝ :=
  twoChannelLinearCurrent reconstructionWeight mixedWeight detailWeight
    (even + odd) (even - odd)

/-- A nonnegative two-channel current whose pure ultraviolet detail coefficient vanishes. -/
structure RouteUNonnegativeUVSafeNyquistCurrent where
  reconstructionWeight : ℝ
  mixedWeight : ℝ
  detailWeight : ℝ
  nonnegative : ∀ even odd : ℝ,
    0 ≤ routeUNyquistChannelCurrent
      reconstructionWeight mixedWeight detailWeight even odd
  uvSafe : detailWeight = 0

/-- Positivity and ultraviolet safety kill the mixed reconstruction/detail coefficient. -/
theorem RouteUNonnegativeUVSafeNyquistCurrent.mixedWeight_eq_zero
    (Q : RouteUNonnegativeUVSafeNyquistCurrent) : Q.mixedWeight = 0 := by
  have hnonnegative : ∀ reconstruction detail : ℝ,
      0 ≤ twoChannelLinearCurrent Q.reconstructionWeight Q.mixedWeight
        Q.detailWeight reconstruction detail := by
    intro reconstruction detail
    have h := Q.nonnegative
      ((reconstruction + detail) / 2) ((reconstruction - detail) / 2)
    have hsum :
        (reconstruction + detail) / 2 + (reconstruction - detail) / 2 =
          reconstruction := by ring
    have hdiff :
        (reconstruction + detail) / 2 - (reconstruction - detail) / 2 =
          detail := by ring
    simpa only [routeUNyquistChannelCurrent, hsum, hdiff] using h
  exact
    twoChannelLinearCurrent_mixedWeight_eq_zero_of_nonnegative_of_badWeight_eq_zero
      hnonnegative Q.uvSafe

/-- **PSD ultraviolet-safe collapse.**  Every nonnegative ultraviolet-safe quadratic current is
exactly a nonnegative multiple of reconstructed fine-channel energy. -/
theorem RouteUNonnegativeUVSafeNyquistCurrent.classification
    (Q : RouteUNonnegativeUVSafeNyquistCurrent) :
    Q.mixedWeight = 0 ∧ 0 ≤ Q.reconstructionWeight ∧
      ∀ even odd : ℝ,
        routeUNyquistChannelCurrent Q.reconstructionWeight Q.mixedWeight
            Q.detailWeight even odd =
          Q.reconstructionWeight * (even + odd) ^ 2 := by
  have hmixed := Q.mixedWeight_eq_zero
  have hweight : 0 ≤ Q.reconstructionWeight := by
    have h := Q.nonnegative (1 / 2) (1 / 2)
    norm_num [routeUNyquistChannelCurrent, twoChannelLinearCurrent] at h ⊢
    exact h
  refine ⟨hmixed, hweight, ?_⟩
  intro even odd
  rw [routeUNyquistChannelCurrent, Q.uvSafe, hmixed]
  simp [twoChannelLinearCurrent]

/-- Complexification of a reconstruction/detail current. -/
def routeUNyquistComplexChannelCurrent
    (reconstructionWeight mixedWeight detailWeight : ℝ)
    (even odd : ℂ) : ℂ :=
  (reconstructionWeight : ℂ) * (even + odd) ^ 2 +
    2 * (mixedWeight : ℂ) * (even + odd) * (even - odd) +
    (detailWeight : ℂ) * (even - odd) ^ 2

/-- The PSD ultraviolet-safe collapse remains exact after complexifying the channel values. -/
theorem RouteUNonnegativeUVSafeNyquistCurrent.complex_classification
    (Q : RouteUNonnegativeUVSafeNyquistCurrent) (even odd : ℂ) :
    routeUNyquistComplexChannelCurrent Q.reconstructionWeight Q.mixedWeight
        Q.detailWeight even odd =
      (Q.reconstructionWeight : ℂ) * (even + odd) ^ 2 := by
  rw [routeUNyquistComplexChannelCurrent, Q.mixedWeight_eq_zero, Q.uvSafe]
  norm_num

/-- On the actual parabolic samples, every PSD ultraviolet-safe quadratic current is exactly a
multiple of the full fine sample square at every finite scale. -/
theorem RouteUNonnegativeUVSafeNyquistCurrent.parabolic_eq_full_sq
    (Q : RouteUNonnegativeUVSafeNyquistCurrent)
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) :
    routeUNyquistComplexChannelCurrent Q.reconstructionWeight Q.mixedWeight
        Q.detailWeight
        (routeUDyadicParabolicEvenSample n f u k)
        (routeUDyadicParabolicOddSample n f u k) =
      (Q.reconstructionWeight : ℂ) *
        routeUDyadicParabolicFullSample n f u k ^ 2 := by
  rw [Q.complex_classification, routeUDyadicParabolicOddSample]
  ring

/-- General complex quadratic polyphase observable. -/
def routeUNyquistComplexQuadraticForm
    (a b c even odd : ℂ) : ℂ :=
  a * even ^ 2 + 2 * b * even * odd + c * odd ^ 2

/-- Exact factorization criterion: a quadratic polyphase observable annihilates the anti-diagonal
coefficient precisely when it contains the reconstructed factor `even + odd`. -/
theorem routeUNyquistComplexQuadraticForm_factor_iff_uvSafe
    (a b c : ℂ) :
    (∀ even odd : ℂ,
      routeUNyquistComplexQuadraticForm a b c even odd =
        (even + odd) * (a * even + c * odd)) ↔
      a - 2 * b + c = 0 := by
  constructor
  · intro h
    have h11 := h 1 1
    norm_num [routeUNyquistComplexQuadraticForm] at h11
    linear_combination -h11
  · intro hsafe even odd
    have hb : 2 * b = a + c := by linear_combination -hsafe
    rw [routeUNyquistComplexQuadraticForm, hb]
    ring

/-- In reconstruction/detail coordinates every ultraviolet-safe quadratic is a combination of
the reconstructed square and the mixed Nyquist current. -/
theorem routeUNyquistComplexSafeQuadraticForm_decomposition
    (a c even odd : ℂ) :
    routeUNyquistComplexQuadraticForm a ((a + c) / 2) c even odd =
      (even + odd) *
        (((a + c) / 2) * (even + odd) +
          ((a - c) / 2) * (even - odd)) := by
  rw [routeUNyquistComplexQuadraticForm]
  ring

/-- Every quadratic form has an exact parabolic-shell limit; its pure detail coefficient is
`a - 2b + c`. -/
theorem tendsto_routeUDyadicParabolicQuadraticForm
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (u : RouteUPositiveParabolicScale)
    (a b c : ℂ) :
    Tendsto (fun k : ℕ =>
      routeUNyquistComplexQuadraticForm a b c
        (routeUDyadicParabolicEvenSample n f u k)
        (routeUDyadicParabolicOddSample n f u k)) atTop
      (nhds ((a - 2 * b + c) *
        ((1 / 2 : ℂ) * routeUComplexPositiveFourierExtension n f
          ((-4 / (u : ℝ) : ℝ) : ℂ)) ^ 2)) := by
  let h : ℂ := (1 / 2 : ℂ) * routeUComplexPositiveFourierExtension n f
    ((-4 / (u : ℝ) : ℝ) : ℂ)
  have heven : Tendsto (routeUDyadicParabolicEvenSample n f u) atTop (nhds h) := by
    simpa only [h] using tendsto_routeUDyadicParabolicEvenSample n f u
  have hodd : Tendsto (routeUDyadicParabolicOddSample n f u) atTop (nhds (-h)) := by
    simpa only [h, neg_mul] using tendsto_routeUDyadicParabolicOddSample n f u
  have hpair := heven.prodMk_nhds hodd
  have hcontinuous : Continuous (fun p : ℂ × ℂ =>
      routeUNyquistComplexQuadraticForm a b c p.1 p.2) := by
    unfold routeUNyquistComplexQuadraticForm
    fun_prop
  have hlimit := (hcontinuous.tendsto (h, -h)).comp hpair
  change Tendsto (fun k : ℕ =>
      routeUNyquistComplexQuadraticForm a b c
        (routeUDyadicParabolicEvenSample n f u k)
        (routeUDyadicParabolicOddSample n f u k)) atTop
    (nhds ((a - 2 * b + c) * h ^ 2))
  convert hlimit using 1
  · funext k
    rfl
  · rw [routeUNyquistComplexQuadraticForm]
    ring

/-- Every coefficient-safe quadratic has zero parabolic-shell limit. -/
theorem tendsto_routeUDyadicParabolicSafeQuadraticForm_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (u : RouteUPositiveParabolicScale)
    (a c : ℂ) :
    Tendsto (fun k : ℕ =>
      routeUNyquistComplexQuadraticForm a ((a + c) / 2) c
        (routeUDyadicParabolicEvenSample n f u k)
        (routeUDyadicParabolicOddSample n f u k)) atTop (nhds 0) := by
  have hlimit := tendsto_routeUDyadicParabolicQuadraticForm n f u
    a ((a + c) / 2) c
  convert hlimit using 1
  ring

/-- Signed parabolic Nyquist current in reconstruction/detail form. -/
def routeUDyadicParabolicNyquistCurrent
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) : ℂ :=
  routeUDyadicParabolicFullSample n f u k *
    (routeUDyadicParabolicEvenSample n f u k -
      routeUDyadicParabolicOddSample n f u k)

/-- Exact difference-of-squares form of the parabolic Nyquist current. -/
theorem routeUDyadicParabolicNyquistCurrent_eq_sq_sub_sq
    (n : ℕ) (f : SchwartzMap ℝ ℂ)
    (u : RouteUPositiveParabolicScale) (k : ℕ) :
    routeUDyadicParabolicNyquistCurrent n f u k =
      routeUDyadicParabolicEvenSample n f u k ^ 2 -
        routeUDyadicParabolicOddSample n f u k ^ 2 := by
  rw [routeUDyadicParabolicNyquistCurrent,
    routeUDyadicParabolicOddSample]
  ring

/-- The signed Nyquist current vanishes on every positive parabolic shell. -/
theorem tendsto_routeUDyadicParabolicNyquistCurrent_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (u : RouteUPositiveParabolicScale) :
    Tendsto (routeUDyadicParabolicNyquistCurrent n f u) atTop (nhds 0) := by
  have hproduct := (tendsto_routeUDyadicParabolicFullSample_zero n f u).mul
    ((tendsto_routeUDyadicParabolicEvenSample n f u).sub
      (tendsto_routeUDyadicParabolicOddSample n f u))
  convert hproduct using 1
  · funext k
    rfl
  · ring

/-- Signed Nyquist current at a fixed Xi divisor copy. -/
def routeUDyadicXiNyquistCurrent
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) : ℂ :=
  routeUXiComplexHardEdgeSample n f (routeUDyadicFineIndex k : ℝ) q *
    (routeUDyadicEvenSample n f k q - routeUDyadicOddSample n f k q)

/-- Exact fixed-divisor difference-of-squares identity. -/
theorem routeUDyadicXiNyquistCurrent_eq_sq_sub_sq
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (k : ℕ) (q : XiZeroCopy) :
    routeUDyadicXiNyquistCurrent n f k q =
      routeUDyadicEvenSample n f k q ^ 2 -
        routeUDyadicOddSample n f k q ^ 2 := by
  rw [routeUDyadicXiNyquistCurrent, routeUDyadicOddSample]
  ring

/-- The same current vanishes in the fixed-divisor infrared chart. -/
theorem tendsto_routeUDyadicXiNyquistCurrent_zero
    (n : ℕ) (f : SchwartzMap ℝ ℂ) (q : XiZeroCopy) :
    Tendsto (fun k : ℕ => routeUDyadicXiNyquistCurrent n f k q)
      atTop (nhds 0) := by
  have hproduct := (tendsto_routeUXiComplexHardEdgeSample_fine n f q).mul
    ((tendsto_routeUDyadicEvenSample_half n f q).sub
      (tendsto_routeUDyadicOddSample_half n f q))
  convert hproduct using 1
  · funext k
    rfl
  · ring

end RHTower

