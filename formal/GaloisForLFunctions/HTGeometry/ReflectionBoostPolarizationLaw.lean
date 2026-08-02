import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-!
# Reflection--boost polarization law

A reflected real character has two channels with reciprocal rates.  This file classifies the
quadratic geometry of that pair.

Every real quadratic form invariant under channel exchange has two coefficients,

`Q_{α,β}(u,v) = α(u²+v²) + 2βuv`.

Reciprocal transport `(u,v) ↦ (exp(dt)u, exp(-dt)v)` preserves the cross coefficient and
hyperbolically stretches the diagonal coefficient.  For nonzero rate, exact transport invariance
therefore forces `α = 0`; positivity then forces `β = 0`.  The only nonzero conservative forms are
cross forms, hence indefinite.

The positive survivor is the nonconservative reciprocal double.  On its balanced vector `(c,c)`,
the first metric jet vanishes and the second metric jet is `8 α (cd)²`.  For a centered complex
point, the reciprocal-square orientation factors exactly as

`Im(a⁻²) = (-Re(a)/|a|⁴) * (2 Im(a))`.

Thus its squared orientation is precisely normalized positive polarization curvature.  The
two-by-two algebra is classical; the reusable result is the exact classification and curvature
normalization needed by reflection-symmetric source/divisor problems.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- General real binary quadratic form, with the mixed coefficient normalized as `2Buv`. -/
def binaryQuadraticForm (A B C : ℝ) (v : ℝ × ℝ) : ℝ :=
  A * v.1 ^ 2 + 2 * B * v.1 * v.2 + C * v.2 ^ 2

/-- Exchange of the two reflected channels. -/
def reflectionChannelSwap (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.2, v.1)

/-- A binary quadratic form is channel-exchange invariant exactly when its two diagonal
coefficients agree. -/
theorem binaryQuadraticForm_swap_invariant_iff
    (A B C : ℝ) :
    (∀ v,
      binaryQuadraticForm A B C (reflectionChannelSwap v) =
        binaryQuadraticForm A B C v) ↔
      A = C := by
  constructor
  · intro h
    have h10 := h (1, 0)
    simpa [binaryQuadraticForm, reflectionChannelSwap] using h10.symm
  · rintro rfl v
    unfold binaryQuadraticForm reflectionChannelSwap
    ring_nf

/-- Normal form of a channel-exchange-invariant quadratic form. -/
def binaryReflectionForm (α β : ℝ) (v : ℝ × ℝ) : ℝ :=
  α * (v.1 ^ 2 + v.2 ^ 2) + 2 * β * v.1 * v.2

/-- Reciprocal real-character transport. -/
def reflectionBoost (d t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (d * t) * v.1, Real.exp (-d * t) * v.2)

/-- Exact transport law: reciprocal transport leaves the cross term fixed and stretches the two
diagonal terms by opposite exponential weights. -/
theorem binaryReflectionForm_reflectionBoost
    (α β d t : ℝ) (v : ℝ × ℝ) :
    binaryReflectionForm α β (reflectionBoost d t v) =
      α * (Real.exp (2 * d * t) * v.1 ^ 2 +
        Real.exp (-2 * d * t) * v.2 ^ 2) +
      2 * β * v.1 * v.2 := by
  unfold binaryReflectionForm reflectionBoost
  have hplus :
      Real.exp (2 * d * t) =
        Real.exp (d * t) * Real.exp (d * t) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hminus :
      Real.exp (-2 * d * t) =
        Real.exp (-d * t) * Real.exp (-d * t) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hexp : Real.exp (d * t) * Real.exp (-d * t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hplus, hminus]
  calc
    α * ((Real.exp (d * t) * v.1) ^ 2 +
          (Real.exp (-d * t) * v.2) ^ 2) +
        2 * β * (Real.exp (d * t) * v.1) *
          (Real.exp (-d * t) * v.2) =
        α * ((Real.exp (d * t) * Real.exp (d * t)) * v.1 ^ 2 +
          (Real.exp (-d * t) * Real.exp (-d * t)) * v.2 ^ 2) +
        2 * β * (Real.exp (d * t) * Real.exp (-d * t)) *
          v.1 * v.2 := by ring_nf
    _ = _ := by rw [hexp]; simp

/-- For a nonzero reflected rate, a channel-exchange-invariant quadratic form is transport
invariant exactly when its diagonal coefficient vanishes. -/
theorem binaryReflectionForm_boost_invariant_iff
    {α β d : ℝ} (hd : d ≠ 0) :
    (∀ t v, binaryReflectionForm α β (reflectionBoost d t v) =
      binaryReflectionForm α β v) ↔
      α = 0 := by
  constructor
  · intro h
    have htest := h 1 (1, 0)
    rw [binaryReflectionForm_reflectionBoost] at htest
    simp [binaryReflectionForm] at htest
    have hexp : Real.exp (2 * d) ≠ 1 := by
      intro he
      have hzero := (Real.exp_eq_one_iff (2 * d)).mp he
      exact hd (by linarith)
    have hprod : α * (Real.exp (2 * d) - 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hα | he
    · exact hα
    · exact False.elim (hexp (sub_eq_zero.mp he))
  · rintro rfl t v
    simpa [binaryReflectionForm] using
      (binaryReflectionForm_reflectionBoost 0 β d t v)

/-- A pure cross form is positive semidefinite only when it is zero. -/
theorem binaryReflectionForm_posSemidefinite_alpha_zero_iff
    (β : ℝ) :
    (∀ v, 0 ≤ binaryReflectionForm 0 β v) ↔ β = 0 := by
  constructor
  · intro h
    have hp := h (1, 1)
    have hm := h (1, -1)
    simp [binaryReflectionForm] at hp hm
    linarith
  · rintro rfl v
    simp [binaryReflectionForm]

/-- **Positive-conservative no-go.**  At nonzero reflected rate, every positive semidefinite,
channel-exchange-invariant, transport-invariant quadratic form is zero. -/
theorem no_nonzero_positive_boostInvariant_reflectionForm
    {α β d : ℝ} (hd : d ≠ 0)
    (hinv : ∀ t v, binaryReflectionForm α β (reflectionBoost d t v) =
      binaryReflectionForm α β v)
    (hpos : ∀ v, 0 ≤ binaryReflectionForm α β v) :
    α = 0 ∧ β = 0 := by
  have hα := (binaryReflectionForm_boost_invariant_iff hd).mp hinv
  refine ⟨hα, ?_⟩
  exact (binaryReflectionForm_posSemidefinite_alpha_zero_iff β).mp (by
    simpa [hα] using hpos)

/-- A nonzero positive semidefinite reflection form has strictly positive diagonal coefficient. -/
theorem binaryReflectionForm_alpha_pos_of_posSemidefinite_of_nonzero
    {α β : ℝ}
    (hpos : ∀ v, 0 ≤ binaryReflectionForm α β v)
    (hne : α ≠ 0 ∨ β ≠ 0) :
    0 < α := by
  have hα : 0 ≤ α := by
    have h := hpos (1, 0)
    simpa [binaryReflectionForm] using h
  exact hα.lt_of_ne (by
    intro hzero
    have hβ :
        β = 0 :=
      (binaryReflectionForm_posSemidefinite_alpha_zero_iff β).mp (by
        simpa [hzero] using hpos)
    exact hne.elim (fun h => h hzero.symm) (fun h => h hβ))

/-- Positive energy of the balanced reciprocal pair. -/
def balancedReflectionBoostEnergy
    (α β c d t : ℝ) : ℝ :=
  binaryReflectionForm α β (reflectionBoost d t (c, c))

/-- Balanced positive energy is hyperbolic. -/
theorem balancedReflectionBoostEnergy_eq
    (α β c d t : ℝ) :
    balancedReflectionBoostEnergy α β c d t =
      2 * c ^ 2 * (α * Real.cosh (2 * d * t) + β) := by
  rw [balancedReflectionBoostEnergy, binaryReflectionForm_reflectionBoost]
  rw [Real.cosh_eq]
  ring_nf

/-- First metric jet of balanced reciprocal transport. -/
def balancedReflectionBoostEnergyVelocity
    (α c d t : ℝ) : ℝ :=
  4 * α * c ^ 2 * d * Real.sinh (2 * d * t)

/-- Second metric jet of balanced reciprocal transport. -/
def balancedReflectionBoostEnergyAcceleration
    (α c d t : ℝ) : ℝ :=
  8 * α * c ^ 2 * d ^ 2 * Real.cosh (2 * d * t)

theorem hasDerivAt_balancedReflectionBoostEnergy
    (α β c d t : ℝ) :
    HasDerivAt (balancedReflectionBoostEnergy α β c d)
      (balancedReflectionBoostEnergyVelocity α c d t) t := by
  have hlin :
      HasDerivAt (fun u : ℝ => 2 * d * u) (2 * d) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (2 * d)
  have hcosh :=
    (Real.hasDerivAt_cosh (2 * d * t)).comp t hlin
  have hscaled :=
    hcosh.const_mul (2 * c ^ 2 * α)
  have hout :
      HasDerivAt
        (fun u => 2 * c ^ 2 * α * Real.cosh (2 * d * u))
        (2 * c ^ 2 * α * (Real.sinh (2 * d * t) * (2 * d))) t := by
    simpa only [Function.comp_apply] using hscaled
  have hfun :
      balancedReflectionBoostEnergy α β c d =
        fun u => 2 * c ^ 2 * α * Real.cosh (2 * d * u) +
          2 * c ^ 2 * β := by
    funext u
    rw [balancedReflectionBoostEnergy_eq]
    ring_nf
  rw [hfun]
  have hvelocity :
      balancedReflectionBoostEnergyVelocity α c d t =
        2 * c ^ 2 * α * (Real.sinh (2 * d * t) * (2 * d)) := by
    unfold balancedReflectionBoostEnergyVelocity
    ring_nf
  rw [hvelocity]
  exact hout.add_const (2 * c ^ 2 * β)

theorem hasDerivAt_balancedReflectionBoostEnergyVelocity
    (α c d t : ℝ) :
    HasDerivAt (balancedReflectionBoostEnergyVelocity α c d)
      (balancedReflectionBoostEnergyAcceleration α c d t) t := by
  have hlin :
      HasDerivAt (fun u : ℝ => 2 * d * u) (2 * d) t := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id t).const_mul (2 * d)
  have hsinh :=
    (Real.hasDerivAt_sinh (2 * d * t)).comp t hlin
  have hscaled :=
    hsinh.const_mul (4 * α * c ^ 2 * d)
  have hout :
      HasDerivAt
        (fun u => 4 * α * c ^ 2 * d * Real.sinh (2 * d * u))
        (4 * α * c ^ 2 * d *
          (Real.cosh (2 * d * t) * (2 * d))) t := by
    simpa only [Function.comp_apply] using hscaled
  change HasDerivAt
    (fun u => 4 * α * c ^ 2 * d * Real.sinh (2 * d * u))
    (8 * α * c ^ 2 * d ^ 2 * Real.cosh (2 * d * t)) t
  convert hout using 1
  ring_nf

/-- Balanced positivity has no first-order orientation signal. -/
theorem balancedReflectionBoostEnergyVelocity_zero
    (α c d : ℝ) :
    balancedReflectionBoostEnergyVelocity α c d 0 = 0 := by
  simp [balancedReflectionBoostEnergyVelocity]

/-- Balanced positive curvature is exactly eight times the squared unsquared orientation `c*d`. -/
theorem balancedReflectionBoostEnergyAcceleration_zero
    (α c d : ℝ) :
    balancedReflectionBoostEnergyAcceleration α c d 0 =
      8 * α * (c * d) ^ 2 := by
  simp [balancedReflectionBoostEnergyAcceleration]
  ring_nf

/-- Upper probability of the reflected two-channel exponential family. -/
def reflectedBernoulliPlusProbability (d t : ℝ) : ℝ :=
  _root_.HTGeometry.logisticVar (d * t)

/-- Lower probability of the reflected two-channel exponential family. -/
def reflectedBernoulliMinusProbability (d t : ℝ) : ℝ :=
  1 - reflectedBernoulliPlusProbability d t

theorem reflectedBernoulliPlusProbability_zero (d : ℝ) :
    reflectedBernoulliPlusProbability d 0 = 1 / 2 := by
  simp [reflectedBernoulliPlusProbability, _root_.HTGeometry.logisticVar]

theorem reflectedBernoulliMinusProbability_zero (d : ℝ) :
    reflectedBernoulliMinusProbability d 0 = 1 / 2 := by
  rw [reflectedBernoulliMinusProbability,
    reflectedBernoulliPlusProbability_zero]
  norm_num

theorem log_reflectedBernoulliPlusProbability
    (d t : ℝ) :
    Real.log (reflectedBernoulliPlusProbability d t) =
      d * t - Real.log (2 * Real.cosh (d * t)) := by
  exact _root_.HTGeometry.log_logisticVar (d * t)

theorem log_reflectedBernoulliMinusProbability
    (d t : ℝ) :
    Real.log (reflectedBernoulliMinusProbability d t) =
      -(d * t) - Real.log (2 * Real.cosh (d * t)) := by
  unfold reflectedBernoulliMinusProbability reflectedBernoulliPlusProbability
  exact _root_.HTGeometry.log_one_sub_logisticVar (d * t)

/-- The upper-channel log-score at the balanced point is the unsquared reflected rate. -/
theorem hasDerivAt_log_reflectedBernoulliPlusProbability_zero
    (d : ℝ) :
    HasDerivAt
      (fun t => Real.log (reflectedBernoulliPlusProbability d t))
      d 0 := by
  have hlin : HasDerivAt (fun t : ℝ => d * t) d 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (𝕜 := ℝ) 0).const_mul d
  have hcoshInner :=
    (Real.hasDerivAt_cosh (d * 0)).comp 0 hlin
  have htwoCosh :=
    hcoshInner.const_mul 2
  have hlog :
      HasDerivAt (fun t => Real.log (2 * Real.cosh (d * t))) 0 0 := by
    have hraw := htwoCosh.log (by norm_num)
    simpa using hraw
  have hsub := hlin.sub hlog
  have hfun :
      (fun t => Real.log (reflectedBernoulliPlusProbability d t)) =
        fun t => d * t - Real.log (2 * Real.cosh (d * t)) := by
    funext t
    exact log_reflectedBernoulliPlusProbability d t
  rw [hfun]
  change HasDerivAt
    ((fun t : ℝ => d * t) -
      fun t => Real.log (2 * Real.cosh (d * t))) d 0
  simpa only [sub_zero] using hsub

/-- The lower-channel log-score at the balanced point is the negative reflected rate. -/
theorem hasDerivAt_log_reflectedBernoulliMinusProbability_zero
    (d : ℝ) :
    HasDerivAt
      (fun t => Real.log (reflectedBernoulliMinusProbability d t))
      (-d) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => d * t) d 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (𝕜 := ℝ) 0).const_mul d
  have hcoshInner :=
    (Real.hasDerivAt_cosh (d * 0)).comp 0 hlin
  have htwoCosh :=
    hcoshInner.const_mul 2
  have hlog :
      HasDerivAt (fun t => Real.log (2 * Real.cosh (d * t))) 0 0 := by
    have hraw := htwoCosh.log (by norm_num)
    simpa using hraw
  have hsub := hlin.neg.sub hlog
  have hfun :
      (fun t => Real.log (reflectedBernoulliMinusProbability d t)) =
        fun t => -(d * t) - Real.log (2 * Real.cosh (d * t)) := by
    funext t
    exact log_reflectedBernoulliMinusProbability d t
  rw [hfun]
  change HasDerivAt
    ((-(fun t : ℝ => d * t)) -
      fun t => Real.log (2 * Real.cosh (d * t))) (-d) 0
  simpa only [sub_zero] using hsub

/-- Fisher information at the balanced point of the reflected Bernoulli family. -/
def reflectedBernoulliFisherAtZero (d : ℝ) : ℝ :=
  reflectedBernoulliPlusProbability d 0 *
      deriv (fun t => Real.log (reflectedBernoulliPlusProbability d t)) 0 ^ 2 +
    reflectedBernoulliMinusProbability d 0 *
      deriv (fun t => Real.log (reflectedBernoulliMinusProbability d t)) 0 ^ 2

/-- Balanced reflected Bernoulli Fisher information is the squared unsquared rate. -/
theorem reflectedBernoulliFisherAtZero_eq_sq
    (d : ℝ) :
    reflectedBernoulliFisherAtZero d = d ^ 2 := by
  rw [reflectedBernoulliFisherAtZero,
    (hasDerivAt_log_reflectedBernoulliPlusProbability_zero d).deriv,
    (hasDerivAt_log_reflectedBernoulliMinusProbability_zero d).deriv,
    reflectedBernoulliPlusProbability_zero,
    reflectedBernoulliMinusProbability_zero]
  ring_nf

/-- Odd first-order score of a balanced reciprocal character pair. -/
def balancedReflectionScore (c d : ℝ) : ℝ × ℝ :=
  (c * d, -(c * d))

/-- The balanced character score is reflection-odd. -/
theorem reflectionChannelSwap_balancedReflectionScore
    (c d : ℝ) :
    reflectionChannelSwap (balancedReflectionScore c d) =
      -(balancedReflectionScore c d) := by
  simp [reflectionChannelSwap, balancedReflectionScore]

/-- Scalar reflection-even readout of the two channels. -/
def reflectionSymmetricReadout (v : ℝ × ℝ) : ℝ :=
  v.1 + v.2

/-- Reflection-even scalarization erases the unsquared character score. -/
theorem reflectionSymmetricReadout_balancedReflectionScore
    (c d : ℝ) :
    reflectionSymmetricReadout (balancedReflectionScore c d) = 0 := by
  simp [reflectionSymmetricReadout, balancedReflectionScore]

/-- The conservative cross form reads the odd score as a negative square. -/
theorem binaryReflectionForm_cross_balancedReflectionScore
    (c d : ℝ) :
    binaryReflectionForm 0 1 (balancedReflectionScore c d) =
      -2 * (c * d) ^ 2 := by
  simp [binaryReflectionForm, balancedReflectionScore]
  ring

/-- Amplitude-weighted Fisher information is the square of the odd score. -/
theorem weighted_reflectedBernoulliFisherAtZero_eq_score_sq
    (c d : ℝ) :
    c ^ 2 * reflectedBernoulliFisherAtZero d = (c * d) ^ 2 := by
  rw [reflectedBernoulliFisherAtZero_eq_sq]
  ring

/--
**Reflection-information identity.**  The negative conservative cross square, the Fisher
information of the normalized reciprocal character, and the curvature of its positive
reciprocal double are one quantity with universal normalizations.
-/
theorem reflectionInformationIdentity
    (c d : ℝ) :
    -(binaryReflectionForm 0 1 (balancedReflectionScore c d)) / 2 =
        c ^ 2 * reflectedBernoulliFisherAtZero d ∧
      c ^ 2 * reflectedBernoulliFisherAtZero d =
        balancedReflectionBoostEnergyAcceleration 1 c d 0 / 8 := by
  rw [binaryReflectionForm_cross_balancedReflectionScore,
    weighted_reflectedBernoulliFisherAtZero_eq_score_sq,
    balancedReflectionBoostEnergyAcceleration_zero]
  constructor <;> ring

/-- Tangential amplitude in the reciprocal-square orientation factorization. -/
def reciprocalSquareTangentialAmplitude (a : ℂ) : ℝ :=
  -a.re / Complex.normSq a ^ 2

/-- Signed transverse rate of a point relative to the reflection axis. -/
def reflectionTransverseRate (a : ℂ) : ℝ :=
  2 * a.im

/-- Reciprocal-square orientation is tangential amplitude times transverse boost rate. -/
theorem reciprocalSquare_im_eq_tangentialAmplitude_mul_transverseRate
    (a : ℂ) :
    (a⁻¹ ^ 2).im =
      reciprocalSquareTangentialAmplitude a *
        reflectionTransverseRate a := by
  rw [pow_two, mul_im, Complex.inv_re, Complex.inv_im]
  unfold reciprocalSquareTangentialAmplitude reflectionTransverseRate
  ring_nf

/-- **Orientation-curvature law.**  Squared reciprocal-square orientation is exactly one eighth
of balanced positive reciprocal-polarization curvature for the unit diagonal form. -/
theorem reciprocalSquareOrientation_eq_boostEnergyCurvature
    (α : ℝ) (a : ℂ) :
    balancedReflectionBoostEnergyAcceleration α
        (reciprocalSquareTangentialAmplitude a)
        (reflectionTransverseRate a) 0 =
      8 * α * (a⁻¹ ^ 2).im ^ 2 := by
  rw [balancedReflectionBoostEnergyAcceleration_zero,
    reciprocalSquare_im_eq_tangentialAmplitude_mul_transverseRate]

/-- **Orientation--Fisher law.**  Squared reciprocal-square orientation is the tangentially
weighted Fisher information of the reflected two-channel character. -/
theorem reciprocalSquareOrientation_sq_eq_tangentialFisher
    (a : ℂ) :
    (a⁻¹ ^ 2).im ^ 2 =
      reciprocalSquareTangentialAmplitude a ^ 2 *
        reflectedBernoulliFisherAtZero (reflectionTransverseRate a) := by
  rw [reflectedBernoulliFisherAtZero_eq_sq,
    reciprocalSquare_im_eq_tangentialAmplitude_mul_transverseRate]
  ring_nf

/--
**Reciprocal-square reflection-information law.**  For the canonical reciprocal-square
orientation, conservative Krein square, normalized Fisher information, positive polarization
curvature, and squared orientation are exactly the same local information with fixed universal
normalizations.
-/
theorem reciprocalSquareReflectionInformationIdentity
    (a : ℂ) :
    -(binaryReflectionForm 0 1
        (balancedReflectionScore
          (reciprocalSquareTangentialAmplitude a)
          (reflectionTransverseRate a))) / 2 =
        (a⁻¹ ^ 2).im ^ 2 ∧
      (a⁻¹ ^ 2).im ^ 2 =
        balancedReflectionBoostEnergyAcceleration 1
          (reciprocalSquareTangentialAmplitude a)
          (reflectionTransverseRate a) 0 / 8 := by
  have h :=
    reflectionInformationIdentity
      (reciprocalSquareTangentialAmplitude a)
      (reflectionTransverseRate a)
  rw [← reciprocalSquareOrientation_sq_eq_tangentialFisher] at h
  exact h

/-- Positive reciprocal-polarization curvature, weighted Fisher information, and squared
orientation are the same local object up to the universal factor `8α`. -/
theorem boostEnergyCurvature_eq_eight_mul_tangentialFisher
    (α : ℝ) (a : ℂ) :
    balancedReflectionBoostEnergyAcceleration α
        (reciprocalSquareTangentialAmplitude a)
        (reflectionTransverseRate a) 0 =
      8 * α * reciprocalSquareTangentialAmplitude a ^ 2 *
        reflectedBernoulliFisherAtZero (reflectionTransverseRate a) := by
  rw [reciprocalSquareOrientation_eq_boostEnergyCurvature,
    reciprocalSquareOrientation_sq_eq_tangentialFisher]
  ring_nf

end

end GaloisForLFunctions.HTGeometry
