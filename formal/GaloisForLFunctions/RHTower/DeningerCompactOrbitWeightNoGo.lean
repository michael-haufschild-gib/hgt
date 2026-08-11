import GaloisForLFunctions.RHTower.DeningerMeyerPeriodization

/-!
# Compact orbit energies have flow weight zero

Periodization is invariant under a translation by its own period, `Per_L ∘ T_L = Per_L`, so any
functional that factors through a compact orbit is invariant under that translation.  A functional
of arithmetic weight one is multiplied by `e^L` under the same translation.  For `L > 0` the two
laws are incompatible unless the functional vanishes identically.

The conclusion is independent of any positivity or rotation hypothesis on the functional: only the
two transformation laws are used.

* `deningerPeriodizationSum_shift` : **`Per_L(T_L h) = Per_L h`.**
* `deningerWeightOne_eq_zero_of_period_invariant` : an invariant weight-one functional vanishes.
* `deningerCompactOrbitEnergy_weight_one_eq_zero` : **a weight-one functional factoring through a
  compact orbit vanishes.**
* `deningerRotationInvariantEnergy_weight_one_eq_zero` : the same for a rotation-invariant
  cross-prime energy.
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- **Periodization is invariant under translation by its own period.** -/
theorem deningerPeriodizationSum_shift (f : 𝓢(ℝ, ℂ)) (L t : ℝ) :
    deningerPeriodizationSum (deningerExpShift L f) L t = deningerPeriodizationSum f L t := by
  rw [deningerPeriodizationSum, deningerPeriodizationSum,
    ← (Equiv.addRight (1 : ℤ)).tsum_eq (fun j : ℤ => (f : ℝ → ℂ) (t + (j : ℝ) * L))]
  refine tsum_congr fun j => ?_
  show ((deningerExpShift L f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (t + (j : ℝ) * L)
    = (f : ℝ → ℂ) (t + (((j + 1 : ℤ) : ℝ)) * L)
  rw [deningerExpShift_apply]
  congr 1
  push_cast
  ring

/-- A functional invariant under one translation and of arithmetic weight one vanishes. -/
theorem deningerWeightOne_eq_zero_of_period_invariant (Q : DeningerExpSchwartz → ℝ) {L : ℝ}
    (hL : 0 < L) (hinv : ∀ f, Q (deningerExpShiftSource L f) = Q f)
    (hwt : ∀ (a : ℝ) (f : DeningerExpSchwartz),
      Q (deningerExpShiftSource a f) = Real.exp a * Q f) (f : DeningerExpSchwartz) :
    Q f = 0 := by
  have hfix : Q f = Real.exp L * Q f := by rw [← hwt L f, hinv f]
  have hne : Real.exp L ≠ 1 := by
    have h1 := Real.add_one_le_exp L
    exact ne_of_gt (by linarith)
  have : (Real.exp L - 1) * Q f = 0 := by linarith [hfix]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (by linarith [h] : Real.exp L = 1) hne
  · exact h

/-- **A weight-one functional factoring through a compact orbit vanishes.**  Factoring through the
`L`-periodization forces invariance under translation by `L`, which contradicts the weight-one law
`Q(T_a h) = e^a Q(h)` at `a = L`. -/
theorem deningerCompactOrbitEnergy_weight_one_eq_zero (Q : DeningerExpSchwartz → ℝ) {L : ℝ}
    (hL : 0 < L)
    (hfac : ∀ f g : DeningerExpSchwartz,
      (∀ t : ℝ, deningerPeriodizationSum (f : 𝓢(ℝ, ℂ)) L t
        = deningerPeriodizationSum (g : 𝓢(ℝ, ℂ)) L t) → Q f = Q g)
    (hwt : ∀ (a : ℝ) (f : DeningerExpSchwartz),
      Q (deningerExpShiftSource a f) = Real.exp a * Q f) (f : DeningerExpSchwartz) :
    Q f = 0 := by
  refine deningerWeightOne_eq_zero_of_period_invariant Q hL (fun g => hfac _ _ fun t => ?_) hwt f
  show deningerPeriodizationSum
      ((deningerExpShiftSource L g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t
    = deningerPeriodizationSum ((g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t
  have hcoe : ((deningerExpShiftSource L g : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
      = deningerExpShift L (g : 𝓢(ℝ, ℂ)) := rfl
  rw [hcoe, deningerPeriodizationSum_shift]

/-- **Rotation-invariant cross-prime energies have weight zero.**  A form on the family of compact
orbits that is invariant under the simultaneous rotations pulls back to a translation-invariant
functional, and translation invariance is incompatible with weight one. -/
theorem deningerRotationInvariantEnergy_weight_one_eq_zero (Q : DeningerExpSchwartz → ℝ)
    (hinv : ∀ (a : ℝ) (f : DeningerExpSchwartz), Q (deningerExpShiftSource a f) = Q f)
    (hwt : ∀ (a : ℝ) (f : DeningerExpSchwartz),
      Q (deningerExpShiftSource a f) = Real.exp a * Q f) (f : DeningerExpSchwartz) :
    Q f = 0 :=
  deningerWeightOne_eq_zero_of_period_invariant Q (zero_lt_one' ℝ) (hinv 1) hwt f

end

end RHTower
