import GaloisForLFunctions.RHTower.ThetaCuspHawkingNonlinearResonanceVelocityEndpoint
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.ThetaCuspReflection

/-!
# Dihedral symmetry and one-sided damping no-go for nonlinear Hawking resonance velocity

The exact Davies--Fulling second-coupling moment and the theta/Xi reflection laws force the
nonlinear resonance velocity into a dihedral quartet. For real frequency,

`V(a,-w) = conj (V(a,w))`, `V(-a,w) = -conj (V(a,w))`, and
`V(-a,-w) = -V(a,w)`.

Consequently an inversion-complete resonance pair cannot have both vertical velocities in one
closed half-plane unless both velocities are tangent to the real-frequency sheet. If the vertical
velocity is nonzero, one member strictly escapes upward. Thus unweighted one-sided passive pole
motion cannot be the RH-bearing orientation principle; any survivor must break the inversion pair
by a chiral/tilt-weighted observable or force zero vertical velocity.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

open HedenmalmThetaSource

/-- Simultaneous tilt/frequency inversion leaves the exact quadratic Hawking moment fixed. -/
theorem thetaCuspHawkingSecondCouplingMoment_inversion (a : ℝ) (w : ℂ) :
    thetaCuspHawkingSecondCouplingMoment (-a) (-w) =
      thetaCuspHawkingSecondCouplingMoment a w := by
  rw [thetaCuspHawkingSecondCouplingMoment,
    thetaCuspHawkingSecondCouplingMoment]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards with x
  rw [thetaCuspTiltedSource, thetaCuspTiltedSource,
    thetaCuspFullSource_neg]
  push_cast
  ring_nf

/-- At real frequency, frequency reflection conjugates the exact quadratic Hawking moment. -/
theorem thetaCuspHawkingSecondCouplingMoment_frequency_conj (a w : ℝ) :
    thetaCuspHawkingSecondCouplingMoment a (-(w : ℂ)) =
      starRingEnd ℂ (thetaCuspHawkingSecondCouplingMoment a (w : ℂ)) := by
  rw [thetaCuspHawkingSecondCouplingMoment,
    thetaCuspHawkingSecondCouplingMoment, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, map_pow, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_I,
    Complex.conj_ofReal, mul_neg, neg_mul, neg_neg]

/-- At real frequency, tilt reflection conjugates the exact quadratic Hawking moment. -/
theorem thetaCuspHawkingSecondCouplingMoment_tilt_conj (a w : ℝ) :
    thetaCuspHawkingSecondCouplingMoment (-a) (w : ℂ) =
      starRingEnd ℂ (thetaCuspHawkingSecondCouplingMoment a (w : ℂ)) := by
  calc
    thetaCuspHawkingSecondCouplingMoment (-a) (w : ℂ) =
        thetaCuspHawkingSecondCouplingMoment a (-(w : ℂ)) := by
      simpa using thetaCuspHawkingSecondCouplingMoment_inversion a (-(w : ℂ))
    _ = starRingEnd ℂ
        (thetaCuspHawkingSecondCouplingMoment a (w : ℂ)) :=
      thetaCuspHawkingSecondCouplingMoment_frequency_conj a w

/-- Exact first-coupling velocity of a simple nonlinear theta-Hawking resonance. -/
def thetaCuspHawkingNonlinearResonanceVelocity (a : ℝ) (w : ℂ) : ℂ :=
  Complex.I * thetaCuspHawkingSecondCouplingMoment a w /
    deriv XiC (w + (a : ℂ) * Complex.I)

/-- Full inversion reverses the exact complex resonance velocity. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_inversion (a : ℝ) (w : ℂ) :
    thetaCuspHawkingNonlinearResonanceVelocity (-a) (-w) =
      -thetaCuspHawkingNonlinearResonanceVelocity a w := by
  rw [thetaCuspHawkingNonlinearResonanceVelocity,
    thetaCuspHawkingNonlinearResonanceVelocity,
    thetaCuspHawkingSecondCouplingMoment_inversion]
  have harg : -w + ((-a : ℝ) : ℂ) * Complex.I =
      -(w + (a : ℂ) * Complex.I) := by push_cast; ring
  rw [harg, deriv_XiC_neg]
  ring

/-- At real frequency, tilt reflection is negative conjugation of velocity. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_tilt_conj (a w : ℝ) :
    thetaCuspHawkingNonlinearResonanceVelocity (-a) (w : ℂ) =
      -starRingEnd ℂ (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)) := by
  rw [thetaCuspHawkingNonlinearResonanceVelocity,
    thetaCuspHawkingNonlinearResonanceVelocity,
    thetaCuspHawkingSecondCouplingMoment_tilt_conj]
  have harg : (w : ℂ) + ((-a : ℝ) : ℂ) * Complex.I =
      starRingEnd ℂ ((w : ℂ) + (a : ℂ) * Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg, deriv_XiC_conj]
  change Complex.I * star (thetaCuspHawkingSecondCouplingMoment a (w : ℂ)) /
      star (deriv XiC ((w : ℂ) + (a : ℂ) * Complex.I)) =
    -star (Complex.I * thetaCuspHawkingSecondCouplingMoment a (w : ℂ) /
      deriv XiC ((w : ℂ) + (a : ℂ) * Complex.I))
  rw [star_div₀, star_mul]
  have hI : star (Complex.I : ℂ) = -Complex.I := Complex.conj_I
  rw [hI]
  ring

/-- Tilt reflection reverses horizontal velocity at real frequency. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_tilt_re (a w : ℝ) :
    (thetaCuspHawkingNonlinearResonanceVelocity (-a) (w : ℂ)).re =
      -(thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)).re := by
  rw [thetaCuspHawkingNonlinearResonanceVelocity_tilt_conj]
  simp

/-- Tilt reflection preserves vertical velocity at real frequency. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_tilt_im (a w : ℝ) :
    (thetaCuspHawkingNonlinearResonanceVelocity (-a) (w : ℂ)).im =
      (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)).im := by
  rw [thetaCuspHawkingNonlinearResonanceVelocity_tilt_conj]
  simp

/-- Frequency reflection conjugates velocity at real frequency. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_frequency_conj (a w : ℝ) :
    thetaCuspHawkingNonlinearResonanceVelocity a (-(w : ℂ)) =
      starRingEnd ℂ (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)) := by
  calc
    thetaCuspHawkingNonlinearResonanceVelocity a (-(w : ℂ)) =
        -thetaCuspHawkingNonlinearResonanceVelocity (-a) (w : ℂ) := by
      simpa using thetaCuspHawkingNonlinearResonanceVelocity_inversion (-a) (w : ℂ)
    _ = starRingEnd ℂ
        (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)) := by
      rw [thetaCuspHawkingNonlinearResonanceVelocity_tilt_conj]
      ring

/-- Exact dihedral quartet generated by tilt and real-frequency reflections. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_dihedral_quartet (a w : ℝ) :
    thetaCuspHawkingNonlinearResonanceVelocity a (-(w : ℂ)) =
        starRingEnd ℂ (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)) ∧
      thetaCuspHawkingNonlinearResonanceVelocity (-a) (w : ℂ) =
        -starRingEnd ℂ (thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ)) ∧
      thetaCuspHawkingNonlinearResonanceVelocity (-a) (-(w : ℂ)) =
        -thetaCuspHawkingNonlinearResonanceVelocity a (w : ℂ) := by
  exact ⟨thetaCuspHawkingNonlinearResonanceVelocity_frequency_conj a w,
    thetaCuspHawkingNonlinearResonanceVelocity_tilt_conj a w,
    thetaCuspHawkingNonlinearResonanceVelocity_inversion a (w : ℂ)⟩

/-- Inversion reverses vertical resonance velocity. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_pair_im (a : ℝ) (w : ℂ) :
    (thetaCuspHawkingNonlinearResonanceVelocity (-a) (-w)).im =
      -(thetaCuspHawkingNonlinearResonanceVelocity a w).im := by
  rw [thetaCuspHawkingNonlinearResonanceVelocity_inversion]
  simp

/-- Closed no-go: an inversion-complete pair is simultaneously nonpositive exactly when both
vertical velocities vanish. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_uniform_nonpos_iff_zero
    (a : ℝ) (w : ℂ) :
    ((thetaCuspHawkingNonlinearResonanceVelocity a w).im ≤ 0 ∧
        (thetaCuspHawkingNonlinearResonanceVelocity (-a) (-w)).im ≤ 0) ↔
      ((thetaCuspHawkingNonlinearResonanceVelocity a w).im = 0 ∧
        (thetaCuspHawkingNonlinearResonanceVelocity (-a) (-w)).im = 0) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [thetaCuspHawkingNonlinearResonanceVelocity_pair_im] at h₂
    have hv : (thetaCuspHawkingNonlinearResonanceVelocity a w).im = 0 := by
      linarith
    exact ⟨hv, by rw [thetaCuspHawkingNonlinearResonanceVelocity_pair_im, hv, neg_zero]⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.le, h₂.le⟩

/-- Unless vertical velocity vanishes, one inversion partner strictly escapes upward. -/
theorem thetaCuspHawkingNonlinearResonanceVelocity_pair_strict_escape (a : ℝ) (w : ℂ) :
    (thetaCuspHawkingNonlinearResonanceVelocity a w).im = 0 ∨
      0 < (thetaCuspHawkingNonlinearResonanceVelocity a w).im ∨
      0 < (thetaCuspHawkingNonlinearResonanceVelocity (-a) (-w)).im := by
  rcases lt_trichotomy (thetaCuspHawkingNonlinearResonanceVelocity a w).im 0 with h | h | h
  · exact Or.inr (Or.inr (by
      rw [thetaCuspHawkingNonlinearResonanceVelocity_pair_im]
      linarith))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end RHTower
