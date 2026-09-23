import GaloisForLFunctions.RHTower.DeningerHarmonicCup
import GaloisForLFunctions.RHTower.DeningerWeylCriterion

/-!
# The harmonic modes on the leaf cylinder

The mode attached to a character of the phase torus is the character times the radial mode of its
frequency.  Distinct characters are Haar orthogonal, so the modes are mutually orthogonal for the
measured leafwise inner product, and each has squared norm the reciprocal of its frequency.  The
same orthogonality makes the leafwise cup trace vanish unless the two characters are opposite, in
which case it is the radial pairing already computed.

The frequency of a character along the Kronecker direction is the pairing `⟨n, λ⟩`, so the
nondegeneracy hypothesis of the mode theorem is exactly the triviality of the annihilator that
makes the Kronecker orbit dense.

* `deningerCylinderMode` : the mode attached to a character.
* `deningerCylinderInner_mode` : orthogonality and the norm `1 / |μ|`.
* `deningerCylinderCup_mode` : the cup pairing vanishes unless the characters are opposite.
* `deningerNormalizedCylinderMode_orthonormal` : the normalized modes are orthonormal.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set Filter Topology

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance deningerCylinderModesMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerCylinderModesIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerCylinderModesIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Cylinder

variable {d : Type*} [Fintype d]

/-- The frequency is additive in the character. -/
theorem deningerFrequency_neg (n : d → ℤ) (lam : d → ℝ) :
    deningerFrequency (-n) lam = -deningerFrequency n lam := by
  rw [deningerFrequency, deningerFrequency, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply]
  push_cast
  ring

/-- **The harmonic mode attached to a character**: the character times the radial mode of its
frequency. -/
noncomputable def deningerCylinderMode (lam : d → ℝ) (n : d → ℤ) (r : ℝ)
    (η : UnitAddTorus d) : ℂ × ℂ :=
  (mFourier n η) • deningerMode (deningerFrequency n lam) r

@[simp] theorem deningerCylinderMode_fst (lam : d → ℝ) (n : d → ℤ) (r : ℝ)
    (η : UnitAddTorus d) :
    (deningerCylinderMode lam n r η).1
      = mFourier n η * (deningerMode (deningerFrequency n lam) r).1 := rfl

@[simp] theorem deningerCylinderMode_snd (lam : d → ℝ) (n : d → ℤ) (r : ℝ)
    (η : UnitAddTorus d) :
    (deningerCylinderMode lam n r η).2
      = mFourier n η * (deningerMode (deningerFrequency n lam) r).2 := rfl

/-- The measured leafwise inner product of two one-forms on the cylinder. -/
noncomputable def deningerCylinderInner (α β : ℝ → UnitAddTorus d → ℂ × ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), ∫ η : UnitAddTorus d,
    ((α r η).1 * (starRingEnd ℂ) ((β r η).1) + (α r η).2 * (starRingEnd ℂ) ((β r η).2))

/-- The leafwise cup trace of two one-forms on the cylinder. -/
noncomputable def deningerCylinderCup (α β : ℝ → UnitAddTorus d → ℂ × ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), ∫ η : UnitAddTorus d, deningerCxWedge (α r η) (β r η)

/-- The character factor of the inner product of two modes. -/
private theorem deningerCharacterInner (n m : d → ℤ) (η : UnitAddTorus d) :
    mFourier n η * (starRingEnd ℂ) (mFourier m η) = mFourier (n - m) η := by
  rw [← mFourier_neg, ← mFourier_add, show n + -m = n - m by abel]

/-- The character factor of the cup pairing of two modes. -/
private theorem deningerCharacterWedge (n m : d → ℤ) (η : UnitAddTorus d) :
    mFourier n η * mFourier m η = mFourier (n + m) η := (mFourier_add).symm

/-- **The inner product of two cylinder modes.**  Distinct characters are Haar orthogonal, and the
diagonal value is the radial squared norm. -/
theorem deningerCylinderInner_mode (lam : d → ℝ) {n m : d → ℤ} (hnm : n ≠ m) :
    deningerCylinderInner (deningerCylinderMode lam n) (deningerCylinderMode lam m) = 0 := by
  have hsub : n - m ≠ 0 := sub_ne_zero_of_ne hnm
  have hinner : ∀ r : ℝ, (∫ η : UnitAddTorus d,
      ((deningerCylinderMode lam n r η).1
          * (starRingEnd ℂ) ((deningerCylinderMode lam m r η).1)
        + (deningerCylinderMode lam n r η).2
          * (starRingEnd ℂ) ((deningerCylinderMode lam m r η).2))) = 0 := by
    intro r
    have hpt : ∀ η : UnitAddTorus d,
        ((deningerCylinderMode lam n r η).1
            * (starRingEnd ℂ) ((deningerCylinderMode lam m r η).1)
          + (deningerCylinderMode lam n r η).2
            * (starRingEnd ℂ) ((deningerCylinderMode lam m r η).2))
          = ((deningerMode (deningerFrequency n lam) r).1
                * (starRingEnd ℂ) ((deningerMode (deningerFrequency m lam) r).1)
              + (deningerMode (deningerFrequency n lam) r).2
                * (starRingEnd ℂ) ((deningerMode (deningerFrequency m lam) r).2))
            * mFourier (n - m) η := by
      intro η
      rw [deningerCylinderMode_fst, deningerCylinderMode_snd, deningerCylinderMode_fst,
        deningerCylinderMode_snd, map_mul, map_mul, ← deningerCharacterInner]
      ring
    rw [funext hpt, integral_const_mul, deningerMFourier_integral_eq_zero hsub, mul_zero]
  rw [deningerCylinderInner, funext hinner, integral_zero]

/-- **The squared norm of a cylinder mode** is the reciprocal of its frequency. -/
theorem deningerCylinderInner_self (lam : d → ℝ) {n : d → ℤ}
    (hn : deningerFrequency n lam ≠ 0) :
    deningerCylinderInner (deningerCylinderMode lam n) (deningerCylinderMode lam n)
      = ((1 / |deningerFrequency n lam| : ℝ) : ℂ) := by
  set μ := deningerFrequency n lam with hμdef
  have hsq : (deningerFreqSign μ : ℂ) * (deningerFreqSign μ : ℂ) = 1 := by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (deningerFreqSign_sq μ)
  have hinner : ∀ r : ℝ, (∫ η : UnitAddTorus d,
      ((deningerCylinderMode lam n r η).1
          * (starRingEnd ℂ) ((deningerCylinderMode lam n r η).1)
        + (deningerCylinderMode lam n r η).2
          * (starRingEnd ℂ) ((deningerCylinderMode lam n r η).2)))
      = 2 * ((deningerModeProfile μ r ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro r
    have hpt : ∀ η : UnitAddTorus d,
        ((deningerCylinderMode lam n r η).1
            * (starRingEnd ℂ) ((deningerCylinderMode lam n r η).1)
          + (deningerCylinderMode lam n r η).2
            * (starRingEnd ℂ) ((deningerCylinderMode lam n r η).2))
          = (2 * ((deningerModeProfile μ r ^ (2 : ℕ) : ℝ) : ℂ)) * mFourier (0 : d → ℤ) η := by
      intro η
      have hchar : mFourier n η * (starRingEnd ℂ) (mFourier n η) = mFourier (0 : d → ℤ) η := by
        rw [deningerCharacterInner, sub_self]
      rw [deningerCylinderMode_fst, deningerCylinderMode_snd, map_mul, map_mul,
        deningerMode_fst, deningerMode_snd]
      rw [show mFourier n η * (deningerModeProfile μ r : ℂ)
            * ((starRingEnd ℂ) (mFourier n η) * (starRingEnd ℂ) ((deningerModeProfile μ r : ℂ)))
          + mFourier n η * (-(Complex.I * (deningerFreqSign μ : ℂ))
              * (deningerModeProfile μ r : ℂ))
            * ((starRingEnd ℂ) (mFourier n η)
              * (starRingEnd ℂ) (-(Complex.I * (deningerFreqSign μ : ℂ))
                * (deningerModeProfile μ r : ℂ)))
          = (mFourier n η * (starRingEnd ℂ) (mFourier n η))
            * ((deningerModeProfile μ r : ℂ)
                * (starRingEnd ℂ) ((deningerModeProfile μ r : ℂ))
              + (-(Complex.I * (deningerFreqSign μ : ℂ)) * (deningerModeProfile μ r : ℂ))
                * (starRingEnd ℂ) (-(Complex.I * (deningerFreqSign μ : ℂ))
                  * (deningerModeProfile μ r : ℂ))) by ring, hchar]
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      linear_combination ((mFourier (0 : d → ℤ) η) * (deningerModeProfile μ r : ℂ) ^ (2 : ℕ)) * hsq
        - ((mFourier (0 : d → ℤ) η) * (deningerFreqSign μ : ℂ) ^ (2 : ℕ)
            * (deningerModeProfile μ r : ℂ) ^ (2 : ℕ)) * Complex.I_sq
    rw [funext hpt, integral_const_mul, deningerMFourier_integral_zero, mul_one]
  rw [deningerCylinderInner, funext hinner, integral_const_mul, integral_complex_ofReal,
    deningerModeProfile_integral hn]
  have habs : (|μ| : ℝ) ≠ 0 := abs_ne_zero.mpr hn
  push_cast
  field_simp

/-- **The cup pairing of two cylinder modes vanishes unless the characters are opposite.** -/
theorem deningerCylinderCup_mode (lam : d → ℝ) {n m : d → ℤ} (hnm : n + m ≠ 0) :
    deningerCylinderCup (deningerCylinderMode lam n) (deningerCylinderMode lam m) = 0 := by
  have hinner : ∀ r : ℝ, (∫ η : UnitAddTorus d,
      deningerCxWedge (deningerCylinderMode lam n r η) (deningerCylinderMode lam m r η)) = 0 := by
    intro r
    have hpt : ∀ η : UnitAddTorus d,
        deningerCxWedge (deningerCylinderMode lam n r η) (deningerCylinderMode lam m r η)
          = deningerCxWedge (deningerMode (deningerFrequency n lam) r)
              (deningerMode (deningerFrequency m lam) r) * mFourier (n + m) η := by
      intro η
      rw [deningerCylinderMode, deningerCylinderMode, deningerCxWedge_smul_left,
        deningerCxWedge_smul_right, ← deningerCharacterWedge]
      ring
    rw [funext hpt, integral_const_mul, deningerMFourier_integral_eq_zero hnm, mul_zero]
  rw [deningerCylinderCup, funext hinner, integral_zero]

/-- **The cup pairing of opposite cylinder modes** is the radial pairing `i / μ`. -/
theorem deningerCylinderCup_mode_neg (lam : d → ℝ) {n : d → ℤ}
    (hn : deningerFrequency n lam ≠ 0) :
    deningerCylinderCup (deningerCylinderMode lam n) (deningerCylinderMode lam (-n))
      = Complex.I / (deningerFrequency n lam : ℂ) := by
  have hinner : ∀ r : ℝ, (∫ η : UnitAddTorus d,
      deningerCxWedge (deningerCylinderMode lam n r η) (deningerCylinderMode lam (-n) r η))
      = deningerCxWedge (deningerMode (deningerFrequency n lam) r)
          (deningerMode (-deningerFrequency n lam) r) := by
    intro r
    have hpt : ∀ η : UnitAddTorus d,
        deningerCxWedge (deningerCylinderMode lam n r η) (deningerCylinderMode lam (-n) r η)
          = deningerCxWedge (deningerMode (deningerFrequency n lam) r)
              (deningerMode (-deningerFrequency n lam) r)
            * mFourier (0 : d → ℤ) η := by
      intro η
      rw [deningerCylinderMode, deningerCylinderMode, deningerCxWedge_smul_left,
        deningerCxWedge_smul_right, deningerFrequency_neg, ← mul_assoc,
        deningerCharacterWedge, show n + -n = (0 : d → ℤ) by abel]
      ring
    rw [funext hpt, integral_const_mul, deningerMFourier_integral_zero, mul_one]
  rw [deningerCylinderCup, funext hinner]
  exact deningerMode_cup hn

/-- The normalized cylinder mode. -/
noncomputable def deningerNormalizedCylinderMode (lam : d → ℝ) (n : d → ℤ) (r : ℝ)
    (η : UnitAddTorus d) : ℂ × ℂ :=
  ((Real.sqrt |deningerFrequency n lam| : ℝ) : ℂ) • deningerCylinderMode lam n r η

/-- The inner product is conjugate linear in each slot on scalar multiples. -/
private theorem deningerCylinderInner_smul (c e : ℂ) (α β : ℝ → UnitAddTorus d → ℂ × ℂ) :
    deningerCylinderInner (fun r η => c • α r η) (fun r η => e • β r η)
      = c * (starRingEnd ℂ) e * deningerCylinderInner α β := by
  rw [deningerCylinderInner, deningerCylinderInner, ← integral_const_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show (c * (α r η).1) * (starRingEnd ℂ) (e * (β r η).1)
      + (c * (α r η).2) * (starRingEnd ℂ) (e * (β r η).2)
    = c * (starRingEnd ℂ) e * ((α r η).1 * (starRingEnd ℂ) ((β r η).1)
      + (α r η).2 * (starRingEnd ℂ) ((β r η).2))
  rw [map_mul, map_mul]
  ring

/-- **The normalized modes are orthonormal.**  This is the orthogonality of the mode packet: the
one-dimensional mode spaces are mutually orthogonal and each is spanned by a unit vector. -/
theorem deningerNormalizedCylinderMode_orthonormal (lam : d → ℝ) {n m : d → ℤ}
    (hn : deningerFrequency n lam ≠ 0) :
    deningerCylinderInner (deningerNormalizedCylinderMode lam n)
        (deningerNormalizedCylinderMode lam m) = if n = m then 1 else 0 := by
  have hfun : ∀ k : d → ℤ, deningerNormalizedCylinderMode lam k
      = fun r η =>
        ((Real.sqrt |deningerFrequency k lam| : ℝ) : ℂ) • deningerCylinderMode lam k r η :=
    fun _ => rfl
  rw [hfun n, hfun m, deningerCylinderInner_smul]
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl, deningerCylinderInner_self lam hn, Complex.conj_ofReal]
    have habs : (0 : ℝ) < |deningerFrequency n lam| := abs_pos.mpr hn
    rw [show ((Real.sqrt |deningerFrequency n lam| : ℝ) : ℂ)
          * ((Real.sqrt |deningerFrequency n lam| : ℝ) : ℂ)
        = ((Real.sqrt |deningerFrequency n lam| * Real.sqrt |deningerFrequency n lam| : ℝ) : ℂ) by
      push_cast; ring, Real.mul_self_sqrt habs.le]
    have habsc : ((|deningerFrequency n lam| : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt habs
    push_cast
    field_simp
  · rw [if_neg hnm, deningerCylinderInner_mode lam hnm, mul_zero]

end Cylinder

end RHTower
