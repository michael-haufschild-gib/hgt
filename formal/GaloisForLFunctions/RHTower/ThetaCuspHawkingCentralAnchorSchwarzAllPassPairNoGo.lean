import GaloisForLFunctions.RHTower.ThetaCuspHawkingWignerSmithWindingEndpoint

/-!
# Central-anchor Schwarz all-pass pair no-go

Every upper theta-Hawking/Xi resonance `r` forces the second upper resonance `-conj r` by the
evenness and Schwarz reality of centered `XiC`.  The product of their two causal all-pass boundary
factors is invisible to every physical-frequency intensity, equals exactly one at zero frequency,
and obeys the real-time boundary symmetry `A(-x) = conj(A(x))`.  Nevertheless its pointwise
Wigner--Smith clock is strictly positive and its winding charge is two.

Thus a zero-frequency complex calibration does not remove the all-pass ambiguity, even after
imposing the source's reality symmetry.  The surviving HB burden is genuinely nonlocal phase
transport, a frequency-derivative/clock law, or a global winding law derived from source dynamics.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- The upper FE--Schwarz partner forced by centered Xi evenness and reality. -/
def thetaCuspHawkingBackreactionUpperSchwarzResonantMode
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    ThetaCuspHawkingBackreactionResonantMode := by
  refine ⟨-star r.1, ?_⟩
  apply (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance (-star r.1)).mp
  calc
    XiC (-star r.1) = XiC (star r.1) := XiC_even (star r.1)
    _ = star (XiC r.1) := XiC_conj r.1
    _ = 0 := by
      rw [thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero]
      simp

@[simp] theorem thetaCuspHawkingBackreactionUpperSchwarzResonantMode_coe
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r).1 = -star r.1 := rfl

@[simp] theorem thetaCuspHawkingBackreactionUpperSchwarzResonantMode_re
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r).1.re = -r.1.re := by
  simp [thetaCuspHawkingBackreactionUpperSchwarzResonantMode]

@[simp] theorem thetaCuspHawkingBackreactionUpperSchwarzResonantMode_im
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r).1.im = r.1.im := by
  simp [thetaCuspHawkingBackreactionUpperSchwarzResonantMode]

@[simp] theorem thetaCuspHawkingBackreactionUpperSchwarzResonantMode_involutive
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingBackreactionUpperSchwarzResonantMode
        (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) = r := by
  apply Subtype.ext
  simp [thetaCuspHawkingBackreactionUpperSchwarzResonantMode]

/-- Product of the two source-forced upper causal all-pass boundary factors. -/
def thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) : ℂ :=
  thetaCuspHawkingCausalAllPassBoundary r x *
    thetaCuspHawkingCausalAllPassBoundary
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) x

/-- At zero frequency, one causal factor is the resonance divided by its conjugate. -/
theorem thetaCuspHawkingCausalAllPassBoundary_zero_eq_div_star
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingCausalAllPassBoundary r 0 = r.1 / star r.1 := by
  rw [thetaCuspHawkingCausalAllPassBoundary_eq_poleFactor]
  have hr : ((r.1.re : ℂ) + (r.1.im : ℂ) * Complex.I) = r.1 := by
    apply Complex.ext <;> simp
  have hrc : ((r.1.re : ℂ) - (r.1.im : ℂ) * Complex.I) = star r.1 := by
    apply Complex.ext <;> simp
  rw [hr, hrc]
  simp

/-- The source-forced pair has exact intrinsic central phase normalization. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r 0 = 1 := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary,
    thetaCuspHawkingCausalAllPassBoundary_zero_eq_div_star,
    thetaCuspHawkingCausalAllPassBoundary_zero_eq_div_star]
  simp [thetaCuspHawkingBackreactionUpperSchwarzResonantMode,
    thetaCuspHawkingBackreactionResonantMode_ne_zero r]

/-- The paired factor remains invisible to every physical-frequency intensity. -/
theorem norm_thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) (x : ℝ) :
    ‖thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r x‖ = 1 := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary, norm_mul,
    norm_thetaCuspHawkingCausalAllPassBoundary r hr x,
    norm_thetaCuspHawkingCausalAllPassBoundary
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) (by simpa) x,
    one_mul]

/-- Negative frequency for one factor is the conjugate of its upper Schwarz partner. -/
theorem thetaCuspHawkingCausalAllPassBoundary_neg_eq_star_upperSchwarz
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) :
    thetaCuspHawkingCausalAllPassBoundary r (-x) =
      star (thetaCuspHawkingCausalAllPassBoundary
        (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) x) := by
  rw [thetaCuspHawkingCausalAllPassBoundary_eq_poleFactor,
    thetaCuspHawkingCausalAllPassBoundary_eq_poleFactor]
  simp [thetaCuspHawkingBackreactionUpperSchwarzResonantMode, div_eq_mul_inv]
  have hnum :
      (-(x : ℂ) - r.1) =
        -((x : ℂ) - (-(r.1.re : ℂ) + -((r.1.im : ℂ) * Complex.I))) := by
    apply Complex.ext
    · simp [Complex.mul_re]
      ring
    · simp [Complex.mul_im]
  have hden :
      (-(x : ℂ) - ((r.1.re : ℂ) - (r.1.im : ℂ) * Complex.I)) =
        -((x : ℂ) - (-(r.1.re : ℂ) + (r.1.im : ℂ) * Complex.I)) := by
    ring
  rw [hnum, hden, inv_neg]
  ring

/-- The degree-two paired all-pass boundary obeys the real-time Fourier symmetry. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary_neg
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) :
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r (-x) =
      star (thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r x) := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary,
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary,
    thetaCuspHawkingCausalAllPassBoundary_neg_eq_star_upperSchwarz r x,
    thetaCuspHawkingCausalAllPassBoundary_neg_eq_star_upperSchwarz
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) x]
  simpa only [thetaCuspHawkingBackreactionUpperSchwarzResonantMode_involutive] using
    (star_mul
      (thetaCuspHawkingCausalAllPassBoundary r x)
      (thetaCuspHawkingCausalAllPassBoundary
        (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) x)).symm

/-- Literal theta-Born response dressed by the source-forced paired all-pass factor. -/
def thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) : ℂ :=
  thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r x *
    thetaCuspFourierLaplace (x : ℂ)

/-- The paired dressing preserves the exact complex source value at the central anchor. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor_zero
    (r : ThetaCuspHawkingBackreactionResonantMode) :
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r 0 =
      thetaCuspFourierLaplace 0 := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor,
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary_zero, one_mul]
  norm_num

/-- Every physical-frequency theta-Born intensity remains unchanged by the paired dressing. -/
theorem norm_thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) (x : ℝ) :
    ‖thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r x‖ =
      ‖thetaCuspFourierLaplace (x : ℂ)‖ := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor,
    norm_mul, norm_thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r hr x,
    one_mul]

/-- The literal theta-Born boundary response has real-time Fourier symmetry. -/
theorem thetaCuspHawkingBornBoundary_neg_eq_star (x : ℝ) :
    thetaCuspFourierLaplace ((-x : ℝ) : ℂ) =
      star (thetaCuspFourierLaplace (x : ℂ)) := by
  rw [HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all,
    HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all]
  rw [show ((-x : ℝ) : ℂ) = -(x : ℂ) by norm_num, XiC_even]
  simpa using XiC_conj (x : ℂ)

/-- The dressed response preserves the source's real-time Fourier symmetry. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor_neg
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) :
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r (-x) =
      star (thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r x) := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor,
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor,
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary_neg,
    thetaCuspHawkingBornBoundary_neg_eq_star]
  simpa only [mul_comm] using
    (star_mul
      (thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r x)
      (thetaCuspFourierLaplace (x : ℂ))).symm

/-- Pointwise Wigner--Smith clock of the source-forced degree-two all-pass packet. -/
def thetaCuspHawkingCentralAnchoredSchwarzAllPassPairClock
    (r : ThetaCuspHawkingBackreactionResonantMode) (x : ℝ) : ℝ :=
  thetaCuspHawkingCausalAllPassClock r x +
    thetaCuspHawkingCausalAllPassClock
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) x

/-- The paired clock is strictly positive at every physical frequency. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairClock_pos
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) (x : ℝ) :
    0 < thetaCuspHawkingCentralAnchoredSchwarzAllPassPairClock r x := by
  exact add_pos
    (thetaCuspHawkingCausalAllPassClock_pos r hr x)
    (thetaCuspHawkingCausalAllPassClock_pos
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) (by simpa) x)

/-- Winding charge of the source-forced degree-two all-pass packet. -/
def thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℝ :=
  thetaCuspHawkingAllPassWindingCharge r +
    thetaCuspHawkingAllPassWindingCharge
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r)

/-- The paired packet carries exactly two normalized winding units. -/
theorem thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge_eq_two
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge r = 2 := by
  rw [thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge,
    thetaCuspHawkingAllPassWindingCharge_eq_one r hr,
    thetaCuspHawkingAllPassWindingCharge_eq_one
      (thetaCuspHawkingBackreactionUpperSchwarzResonantMode r) (by simpa)]
  norm_num

/-- Closed no-go proposition for central complex calibration plus source reality. -/
def D4ThetaCuspHawkingCentralAnchorSchwarzAllPassPairRouteKilled : Prop :=
  ∀ r : ThetaCuspHawkingBackreactionResonantMode,
    0 < r.1.im →
      thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary r 0 = 1 ∧
      thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r 0 =
        thetaCuspFourierLaplace 0 ∧
      (∀ x : ℝ,
        ‖thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r x‖ =
            ‖thetaCuspFourierLaplace (x : ℂ)‖ ∧
          thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r (-x) =
            star (thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r x) ∧
          0 < thetaCuspHawkingCentralAnchoredSchwarzAllPassPairClock r x) ∧
      thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge r = 2

/-- **Central-anchor HB route killed.**  Every hypothetical upper Xi resonance automatically
produces a nontrivial degree-two causal all-pass dressing which preserves all intensities, the
exact complex zero-frequency source value, and real-time Schwarz symmetry, while retaining a
strictly positive clock and winding charge two. -/
theorem d4ThetaCuspHawkingCentralAnchorSchwarzAllPassPairRouteKilled :
    D4ThetaCuspHawkingCentralAnchorSchwarzAllPassPairRouteKilled := by
  intro r hr
  refine ⟨thetaCuspHawkingCentralAnchoredSchwarzAllPassPairBoundary_zero r,
    thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor_zero r,
    ?_, thetaCuspHawkingCentralAnchoredSchwarzAllPassPairWindingCharge_eq_two r hr⟩
  intro x
  exact
    ⟨norm_thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor r hr x,
      thetaCuspHawkingCentralAnchoredSchwarzAllPassPairDressedBornFormFactor_neg r x,
      thetaCuspHawkingCentralAnchoredSchwarzAllPassPairClock_pos r hr x⟩

end RHTower
