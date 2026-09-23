import GaloisForLFunctions.RHTower.DeningerFailureNerveSingularCartierMetric
import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaTensorSquareMateIdentification

/-!
# Source reversal versus analytic dagger on a failure-nerve edge

A face edge of the failure nerve carries the transition coefficient `R = λ · Q`, where `λ` is the
radial half-density character and `Q` the normalized Euler gauge, and the face vertices carry the
forced inverse-square metric `h_F = ‖Q_F‖⁻²`.  Two reverse laws are available on such an edge: the
algebraic source reversal `S = R⁻¹` and the Hermitian adjoint `A = (h_target/h_source)·conj R` for
the metric.  Both are defined before any zero of `Ξ` is named.

Their modular ratio is `‖λ‖⁻²` and their difference is

`Δ = S − A = Q⁻¹(λ⁻¹ − conj λ) = Q⁻¹ conj λ (‖λ‖⁻² − 1)`,

which vanishes exactly on the unimodular locus of `λ`, hence — for a prime power at least two —
exactly on the critical line.

The defect is nevertheless always closed and always exact.  Source reversal and metric dagger are
both contravariantly multiplicative, so `Δ` obeys the mixed Leibniz law `Δ₂₁ = S₁Δ₂ + Δ₁A₂`, and
around a commuting square of two distinct prime edges the two expansions agree.  More strongly, for
the mixed cobar differential `(δ_{S,A}H)_e = S_e H_{t(e)} − H_{s(e)} A_e` the constant identity
cochain has `δ_{S,A}𝟏 = Δ`.  So `Δ` is mixed-Bianchi closed and mixed-cobar exact at *every*
parameter, including the off-critical ones where it is nonzero: linear Bianchi closedness and
linear null-homotopy carry no information about the critical line.

What does carry that information is quadratic.  The uniquely purified relative squared gains of the
two reverse laws are `‖λ‖⁻²` and `‖λ‖²`, and their difference is the tensor-square radial mate
curvature, which at the ordered `(2,3)` witness is a strictly positive calibration of the actual
Gamma boundary defect.  A linear coboundary does not annihilate that quadratic reporter.

* `RHTower.deningerMixedSourceReversal`, `RHTower.deningerMixedAdjoint` — the two reverse laws.
* `RHTower.deningerMixedAdjoint_metric_eq` — the weighted Hermitian adjunction identity.
* `RHTower.deningerMixedModularRatio` — the modular ratio `S A⁻¹ = ‖λ‖⁻²`.
* `RHTower.deningerMixedDefect_eq_mul_sub_one` — the closed formula for `Δ`.
* `RHTower.deningerMixedDefect_eq_zero_iff_norm_one` — `Δ = 0` is unimodularity.
* `RHTower.deningerMixedDefect_comp` — the mixed Leibniz law.
* `RHTower.deningerMixedDefect_bianchi` — the commuting-square Bianchi identity.
* `RHTower.DeningerMixedEdgeSystem.cobar_one` — `Δ = δ_{S,A}𝟏`.
* `RHTower.deningerFailureNerveMixedDefect_eq_zero_iff` — the actual edge detects the critical line.
* `RHTower.deningerFailureNerveReverseGainDifference_eq` — the reverse-gain difference is the
  tensor-square radial mate curvature.
-/

namespace RHTower

noncomputable section

section WeightedHermitianEdge

/-- The weighted Hermitian pairing of a face line, `⟨z, w⟩_h = h · conj z · w`. -/
def deningerMixedPairing (hw : ℝ) (z w : ℂ) : ℂ := (hw : ℂ) * (starRingEnd ℂ) z * w

/-- **Algebraic source reversal** of an edge whose transition coefficient is `R = λ Q`. -/
def deningerMixedSourceReversal (lam Q : ℂ) : ℂ := (lam * Q)⁻¹

/-- **Analytic dagger** of the same edge for the forced inverse-square face metric. -/
def deningerMixedAdjoint (lam Q : ℂ) : ℂ := Q⁻¹ * (starRingEnd ℂ) lam

/-- The linear mate defect of the two reverse laws. -/
def deningerMixedDefect (lam Q : ℂ) : ℂ :=
  deningerMixedSourceReversal lam Q - deningerMixedAdjoint lam Q

/-- Source reversal in split coordinates. -/
theorem deningerMixedSourceReversal_eq (lam Q : ℂ) :
    deningerMixedSourceReversal lam Q = Q⁻¹ * lam⁻¹ := by
  rw [deningerMixedSourceReversal, mul_inv]
  ring

/-- `‖Q‖²` as a product with the conjugate. -/
theorem deningerNormSq_eq_mul_conj (Q : ℂ) :
    ((‖Q‖ ^ (2 : ℕ) : ℝ) : ℂ) = Q * (starRingEnd ℂ) Q := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The analytic dagger is the metric adjoint coefficient.**  With the forced weights
`h_{F∪{p}} = h_F ‖Q‖⁻²`, the ratio of weights times the conjugate transition is exactly
`Q⁻¹ conj λ`. -/
theorem deningerMixedAdjoint_metric_eq (lam Q : ℂ) (hQ : Q ≠ 0) :
    ((‖Q‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ) (lam * Q) = deningerMixedAdjoint lam Q := by
  have hQc : (starRingEnd ℂ) Q ≠ 0 := by simpa using hQ
  have hns : ((‖Q‖ ^ (2 : ℕ) : ℝ) : ℂ) = Q * (starRingEnd ℂ) Q := deningerNormSq_eq_mul_conj Q
  have hns0 : ((‖Q‖ ^ (2 : ℕ) : ℝ) : ℂ) ≠ 0 := by rw [hns]; exact mul_ne_zero hQ hQc
  have hinv : ((‖Q‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) = (Q * (starRingEnd ℂ) Q)⁻¹ := by
    rw [← hns]
    push_cast
    ring
  rw [deningerMixedAdjoint, map_mul, hinv]
  field_simp

/-- **The adjunction identity `(5)`.**  The analytic dagger is characterized by moving the
transition across the two weighted Hermitian pairings. -/
theorem deningerMixed_adjunction (lam Q : ℂ) (hQ : Q ≠ 0) (hF : ℝ) (z w : ℂ) :
    deningerMixedPairing (hF * ‖Q‖⁻¹ ^ (2 : ℕ)) (lam * Q * z) w =
      deningerMixedPairing hF z (deningerMixedAdjoint lam Q * w) := by
  have hadj := deningerMixedAdjoint_metric_eq lam Q hQ
  rw [deningerMixedPairing, deningerMixedPairing, ← hadj]
  simp only [map_mul]
  push_cast
  ring

/-- **The modular ratio `(6)`.**  The two reverse laws differ by the inverse squared radial
modulus; the Euler gauge cancels. -/
theorem deningerMixedModularRatio (lam Q : ℂ) (hlam : lam ≠ 0) (hQ : Q ≠ 0) :
    deningerMixedSourceReversal lam Q * (deningerMixedAdjoint lam Q)⁻¹ =
      ((‖lam‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hlc : (starRingEnd ℂ) lam ≠ 0 := by simpa using hlam
  have hns : ((‖lam‖ ^ (2 : ℕ) : ℝ) : ℂ) = lam * (starRingEnd ℂ) lam := deningerNormSq_eq_mul_conj lam
  have hinv : ((‖lam‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) = (lam * (starRingEnd ℂ) lam)⁻¹ := by
    rw [← hns]
    push_cast
    ring
  rw [deningerMixedSourceReversal_eq, deningerMixedAdjoint, hinv]
  field_simp

/-- **The defect `(7)`, first form.** -/
theorem deningerMixedDefect_eq (lam Q : ℂ) :
    deningerMixedDefect lam Q = Q⁻¹ * (lam⁻¹ - (starRingEnd ℂ) lam) := by
  rw [deningerMixedDefect, deningerMixedSourceReversal_eq, deningerMixedAdjoint]
  ring

/-- **The defect `(7)`, second form.**  All factors outside `‖λ‖⁻² − 1` are nonzero. -/
theorem deningerMixedDefect_eq_mul_sub_one (lam Q : ℂ) (hlam : lam ≠ 0) :
    deningerMixedDefect lam Q =
      Q⁻¹ * (starRingEnd ℂ) lam * (((‖lam‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) - 1) := by
  have hlc : (starRingEnd ℂ) lam ≠ 0 := by simpa using hlam
  have hns : ((‖lam‖ ^ (2 : ℕ) : ℝ) : ℂ) = lam * (starRingEnd ℂ) lam := deningerNormSq_eq_mul_conj lam
  have hinv : ((‖lam‖⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) = (lam * (starRingEnd ℂ) lam)⁻¹ := by
    rw [← hns]
    push_cast
    ring
  rw [deningerMixedDefect_eq, hinv]
  field_simp

/-- **`(8)` in its abstract form.**  The linear mate defect vanishes exactly on the unimodular
locus of the radial character. -/
theorem deningerMixedDefect_eq_zero_iff_norm_one (lam Q : ℂ) (hlam : lam ≠ 0) (hQ : Q ≠ 0) :
    deningerMixedDefect lam Q = 0 ↔ ‖lam‖ = 1 := by
  have hQinv : Q⁻¹ ≠ 0 := inv_ne_zero hQ
  have hns : ((‖lam‖ ^ (2 : ℕ) : ℝ) : ℂ) = lam * (starRingEnd ℂ) lam := deningerNormSq_eq_mul_conj lam
  rw [deningerMixedDefect_eq, mul_eq_zero]
  simp only [hQinv, false_or]
  rw [sub_eq_zero]
  constructor
  · intro h
    have h2 : lam * (starRingEnd ℂ) lam = 1 := by
      rw [← h]
      field_simp
    have h3 : ((‖lam‖ ^ (2 : ℕ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hns, h2]; norm_num
    have h4 : ‖lam‖ ^ (2 : ℕ) = 1 := by exact_mod_cast h3
    nlinarith [norm_nonneg lam]
  · intro h
    have h2 : lam * (starRingEnd ℂ) lam = 1 := by
      rw [← hns, h]; norm_num
    exact inv_eq_of_mul_eq_one_right h2

end WeightedHermitianEdge

section MixedCobar

/-- **The mixed Leibniz law `(9)`.**  Source reversal and metric dagger are both contravariantly
multiplicative, so the defect of a composite is the stated combination. -/
theorem deningerMixedDefect_comp (S₁ S₂ A₁ A₂ : ℂ) :
    S₁ * S₂ - A₁ * A₂ = S₁ * (S₂ - A₂) + (S₁ - A₁) * A₂ := by ring

/-- **The square Bianchi identity `(10)`.**  Around a commuting square of two distinct prime
edges the two expansions of the composite defect agree. -/
theorem deningerMixedDefect_bianchi (Sp Sq Ap Aq : ℂ) :
    Sp * (Sq - Aq) + (Sp - Ap) * Aq = Sq * (Sp - Ap) + (Sq - Aq) * Ap := by ring

/-- An edge system carrying a source reversal and an analytic dagger on every edge. -/
structure DeningerMixedEdgeSystem (E V : Type*) where
  /-- Source vertex of an edge. -/
  src : E → V
  /-- Target vertex of an edge. -/
  tgt : E → V
  /-- Source-reversal coefficient. -/
  S : E → ℂ
  /-- Analytic-dagger coefficient. -/
  A : E → ℂ

namespace DeningerMixedEdgeSystem

variable {E V : Type*} (X : DeningerMixedEdgeSystem E V)

/-- **The mixed cobar differential `(11)`** on vertex cochains. -/
def cobar (H : V → ℂ) (e : E) : ℂ := X.S e * H (X.tgt e) - H (X.src e) * X.A e

/-- The edgewise linear mate defect of the system. -/
def defect (e : E) : ℂ := X.S e - X.A e

/-- **`(12)`: the defect is the mixed coboundary of the constant identity cochain.**  So the
linear source-inverse/analytic-dagger defect is mixed-cobar exact at every parameter, including
every off-critical one where it is nonzero. -/
theorem cobar_one (e : E) : X.cobar (fun _ => (1 : ℂ)) e = X.defect e := by
  simp [cobar, defect]

/-- The defect is in the image of the mixed cobar differential. -/
theorem defect_mem_range (e : E) : ∃ H : V → ℂ, X.cobar H e = X.defect e :=
  ⟨fun _ => (1 : ℂ), X.cobar_one e⟩

end DeningerMixedEdgeSystem

end MixedCobar

section ActualEdge

variable (p : Nat.Primes) (m : ℕ) (s : ℂ)

/-- Source reversal of the actual normalized failure-nerve face transition. -/
def deningerFailureNerveMixedSourceReversal : ℂ :=
  deningerMixedSourceReversal (bilateralHalfDensityCharacter ((p : ℕ) ^ m) s)
    (deningerFailureNerveEulerGauge p m s)

/-- Analytic dagger of the actual normalized failure-nerve face transition. -/
def deningerFailureNerveMixedAdjoint : ℂ :=
  deningerMixedAdjoint (bilateralHalfDensityCharacter ((p : ℕ) ^ m) s)
    (deningerFailureNerveEulerGauge p m s)

/-- Linear mate defect of the actual edge. -/
def deningerFailureNerveMixedDefect : ℂ :=
  deningerMixedDefect (bilateralHalfDensityCharacter ((p : ℕ) ^ m) s)
    (deningerFailureNerveEulerGauge p m s)

variable {p m s}

/-- The actual transition is the product of the two split factors. -/
theorem deningerFailureNerveMixedSourceReversal_eq :
    deningerFailureNerveMixedSourceReversal p m s =
      (deningerFailureNerveActualTransition m s p)⁻¹ := by
  rw [deningerFailureNerveMixedSourceReversal, deningerMixedSourceReversal,
    deningerFailureNerveActualTransition]

/-- **`(8)` on the actual edge.**  For a prime power at least two and a parameter in the open right
half-plane, the linear mate defect of the actual failure-nerve edge vanishes exactly on the
critical line. -/
theorem deningerFailureNerveMixedDefect_eq_zero_iff (hpm : 2 ≤ (p : ℕ) ^ m) (hs : 0 < s.re) :
    deningerFailureNerveMixedDefect p m s = 0 ↔ s.re = 1 / 2 := by
  have hp0 : 0 < (p : ℕ) ^ m := lt_of_lt_of_le two_pos hpm
  have hlam : bilateralHalfDensityCharacter ((p : ℕ) ^ m) s ≠ 0 :=
    bilateralHalfDensityCharacter_ne_zero hp0 s
  have hQ : deningerFailureNerveEulerGauge p m s ≠ 0 :=
    deningerFailureNerveEulerGauge_ne_zero p m s hs
  rw [deningerFailureNerveMixedDefect,
    deningerMixedDefect_eq_zero_iff_norm_one _ _ hlam hQ,
    norm_bilateralHalfDensityCharacter_eq_one_iff hpm]

/-- **`(13)`: the reverse-gain difference.**  The uniquely purified relative squared gains of
source reversal and analytic dagger are `‖λ‖⁻²` and `‖λ‖²`, and their difference is the
tensor-square radial mate curvature. -/
theorem deningerFailureNerveReverseGainDifference_eq :
    ‖bilateralHalfDensityCharacter ((p : ℕ) ^ m) s‖⁻¹ ^ (2 : ℕ) -
        ‖bilateralHalfDensityCharacter ((p : ℕ) ^ m) s‖ ^ (2 : ℕ) =
      deningerTensorSquareRadialMateCurvature ((p : ℕ) ^ m) s := rfl

/-- **The linear defect and the quadratic reporter vanish together on the actual edge, but only
the quadratic one survives the passage to the Gamma reporter.**  Both criteria cut out the
critical line, which is exactly why linear cobar exactness of `Δ` — which holds identically, on
and off the line — cannot annihilate the Gamma curvature. -/
theorem deningerFailureNerveMixedDefect_eq_zero_iff_reverseGainDifference_eq_zero
    (hpm : 2 ≤ (p : ℕ) ^ m) (hs : 0 < s.re) :
    deningerFailureNerveMixedDefect p m s = 0 ↔
      deningerTensorSquareRadialMateCurvature ((p : ℕ) ^ m) s = 0 := by
  rw [deningerFailureNerveMixedDefect_eq_zero_iff hpm hs,
    deningerTensorSquareRadialMateCurvature_eq_zero_iff _ _ hpm]

end ActualEdge

section GammaSpecialization

/-- **`(14)`: the actual Gamma specialization.**  The canonical Gamma boundary defect coefficient
is a strictly positive calibration of the tensor-square radial mate curvature at the forced
composite degree `6`, so the actual Gamma reporter is a secondary norm transgression of the
linear mixed-exact defect. -/
theorem deningerFailureNerveGammaSecondaryTransgression (r : XiZeroCopy) :
    0 < deningerCalderonWittBaseGammaMateCalibration ∧
      deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
        ((deningerCalderonWittBaseGammaMateCalibration *
          deningerTensorSquareRadialMateCurvature 6 (r.1 : ℂ) : ℝ) : ℂ) :=
  ⟨deningerCalderonWittBaseGammaMateCalibration_pos,
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature r⟩

end GammaSpecialization

end

end RHTower
