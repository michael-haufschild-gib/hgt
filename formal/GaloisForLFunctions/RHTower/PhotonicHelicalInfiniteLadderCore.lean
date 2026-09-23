import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalDynamicChirality

/-!
# Literal helical material action on the full Floquet/OAM ladder

The rotating constitutive harmonics shift both temporal frequency and OAM
by one shared Floquet grade at every integer channel. This is the exact
all-grade material-multiplication law, including finite packets. It does not
identify multiplication with a complete Maxwell boundary transfer.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section
set_option autoImplicit false

/-- A simultaneous temporal-frequency and orbital-angular-momentum Fourier
channel of the rotating material. -/
def ptrFloquetMode (ω Ω θ t : ℝ) (ℓ m n : ℤ) : ℂ :=
  Complex.exp (Complex.I *
    (((floquetSidebandAngularMomentum ℓ m n : ℝ) * θ -
      floquetSidebandFrequency ω Ω n * t : ℝ) : ℂ))

/-- The literal positive helical material harmonic raises both locked labels
by exactly one grade. -/
theorem ptr_positive_helical_mode_shift (ω Ω θ t : ℝ) (ℓ m n : ℤ) :
    rotatingPositiveHarmonic m θ Ω t * ptrFloquetMode ω Ω θ t ℓ m n =
      ptrFloquetMode ω Ω θ t ℓ m (n + 1) := by
  unfold rotatingPositiveHarmonic ptrFloquetMode
  rw [← Complex.exp_add]
  congr 1
  simp only [rotatingModulationPhase, floquetSidebandAngularMomentum,
    floquetSidebandFrequency]
  push_cast
  ring

/-- The negative companion lowers both labels by exactly one grade. -/
theorem ptr_negative_helical_mode_shift (ω Ω θ t : ℝ) (ℓ m n : ℤ) :
    rotatingNegativeHarmonic m θ Ω t * ptrFloquetMode ω Ω θ t ℓ m n =
      ptrFloquetMode ω Ω θ t ℓ m (n - 1) := by
  unfold rotatingNegativeHarmonic ptrFloquetMode
  rw [← Complex.exp_add]
  congr 1
  simp only [rotatingModulationPhase, floquetSidebandAngularMomentum,
    floquetSidebandFrequency]
  push_cast
  ring

/-- The exact helical action on an arbitrary finite Floquet packet, not only
the first sideband or a three-port truncation. -/
theorem ptr_positive_helical_packet_shift (F : Finset ℤ) (c : ℤ → ℂ)
    (a : ℂ) (ω Ω θ t : ℝ) (ℓ m : ℤ) :
    a * rotatingPositiveHarmonic m θ Ω t *
        (∑ n ∈ F, c n * ptrFloquetMode ω Ω θ t ℓ m n) =
      ∑ n ∈ F, (a * c n) * ptrFloquetMode ω Ω θ t ℓ m (n + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (a * rotatingPositiveHarmonic m θ Ω t) *
        (c n * ptrFloquetMode ω Ω θ t ℓ m n) =
      (a * c n) * (rotatingPositiveHarmonic m θ Ω t *
        ptrFloquetMode ω Ω θ t ℓ m n) := by ring
    _ = _ := by rw [ptr_positive_helical_mode_shift]

/-- Nonzero helical charge gives a faithful OAM label at every integer
sideband grade. -/
theorem ptr_all_grade_oam_injective (ℓ m : ℤ) (hm : m ≠ 0) :
    Function.Injective (floquetSidebandAngularMomentum ℓ m) := by
  intro n k h
  dsimp [floquetSidebandAngularMomentum] at h
  exact mul_right_cancel₀ hm (add_left_cancel h)

/-- Thus the literal OAM ladder has infinitely many distinct channels; no
finite set of absolute OAM labels contains its full range. -/
theorem ptr_all_grade_oam_range_infinite (ℓ m : ℤ) (hm : m ≠ 0) :
    (Set.range (floquetSidebandAngularMomentum ℓ m)).Infinite :=
  Set.infinite_range_of_injective (ptr_all_grade_oam_injective ℓ m hm)

end

end RHTower
