import GaloisForLFunctions.RHTower.SoninApertureCyclicMassConservation

/-!
# The aperture-layer algebra and its cyclic reader

Aperture defects are represented by scale-one shells.  Those shells are closed under the canonical
normal-state product: the composite of two of them is the scale-one shell on the intersection of
the two annuli, because the base-cutoff normalization is inert at scale one.

The cyclic reader on this subalgebra is therefore completely explicit — it is the logarithmic
length of the intersection — and manifestly symmetric in the two factors.  On the aperture-layer
algebra the reader is not merely cyclic, it is commutative.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

variable {a s₁ t₁ s₂ t₂ : ℝ}

theorem soninLiveComposeScale_scaleOneShell
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninLiveComposeScale (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
      (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') = 1 := by
  simp [soninLiveComposeScale, soninScaleOneShellWindow]

theorem soninLiveComposeCeiling_scaleOneShell
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninLiveComposeCeiling (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
      (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') = min t₁ t₂ := by
  simp [soninLiveComposeCeiling, soninWindowComposeCeiling, soninScaleOneShellWindow]

/-- At scale one the base-cutoff normalization is inert, so the composed floor is the larger of the
two floors clamped to the smaller of the two ceilings. -/
theorem soninLiveComposeFloor_scaleOneShell
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninLiveComposeFloor (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
        (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') =
      min (max s₁ s₂) (min t₁ t₂) := by
  have hbase : a ≤ min (max s₁ s₂) (min t₁ t₂) :=
    le_min (h₁.trans (le_max_left _ _))
      (le_min (h₁.trans h₁'.le) (h₂.trans h₂'.le))
  unfold soninLiveComposeFloor soninWindowComposeNormalizedFloor
    soninWindowNormalizedFloor soninWindowComposeFloor soninWindowComposeCeiling
    soninScaleOneShellWindow
  simp only [inv_one, one_mul, mul_one]
  rw [max_eq_left hbase, min_eq_left (min_le_right _ _)]

/-- The composite is live exactly when the two annuli overlap. -/
theorem soninLiveComposeFloor_lt_ceiling_scaleOneShell_iff
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninLiveComposeFloor (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
        (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') <
      soninLiveComposeCeiling (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
        (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') ↔
      max s₁ s₂ < min t₁ t₂ := by
  rw [soninLiveComposeFloor_scaleOneShell h₁ h₁' h₂ h₂',
    soninLiveComposeCeiling_scaleOneShell h₁ h₁' h₂ h₂']
  constructor
  · intro h
    rcases min_cases (max s₁ s₂) (min t₁ t₂) with ⟨heq, _⟩ | ⟨heq, _⟩
    · rwa [heq] at h
    · rw [heq] at h
      exact absurd h (lt_irrefl _)
  · intro h
    rwa [min_eq_left h.le]

/-- **Explicit reader on the aperture-layer algebra.**  The cyclic logarithmic trace of a product
of two scale-one shells is the logarithmic length of the intersection of the two annuli, and zero
when they do not overlap. -/
theorem soninWindowStateCyclicLogTrace_composeScaleOneShells
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninWindowStateCyclicLogTrace
        (composeSoninWindowStates
          (SoninWindowState.live (soninScaleOneShellWindow a s₁ t₁ h₁ h₁'))
          (SoninWindowState.live (soninScaleOneShellWindow a s₂ t₂ h₂ h₂'))) =
      if max s₁ s₂ < min t₁ t₂ then
        Real.log (min t₁ t₂) - Real.log (max s₁ s₂) else 0 := by
  classical
  by_cases hlive : max s₁ s₂ < min t₁ t₂
  · have hcond := (soninLiveComposeFloor_lt_ceiling_scaleOneShell_iff
      h₁ h₁' h₂ h₂').mpr hlive
    rw [if_pos hlive]
    simp only [composeSoninWindowStates, composeSoninLiveWindows, dif_pos hcond,
      soninWindowStateCyclicLogTrace, soninLiveWindowCyclicLogWeight]
    rw [soninLiveComposeScale_scaleOneShell h₁ h₁' h₂ h₂', if_pos rfl,
      soninLiveComposeCeiling_scaleOneShell h₁ h₁' h₂ h₂',
      soninLiveComposeFloor_scaleOneShell h₁ h₁' h₂ h₂',
      min_eq_left hlive.le]
  · have hcond : ¬ soninLiveComposeFloor (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
        (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') <
      soninLiveComposeCeiling (soninScaleOneShellWindow a s₁ t₁ h₁ h₁')
        (soninScaleOneShellWindow a s₂ t₂ h₂ h₂') := by
      intro h
      exact hlive ((soninLiveComposeFloor_lt_ceiling_scaleOneShell_iff
        h₁ h₁' h₂ h₂').mp h)
    rw [if_neg hlive]
    simp only [composeSoninWindowStates, composeSoninLiveWindows, dif_neg hcond,
      soninWindowStateCyclicLogTrace]

/-- **Commutativity of the reader on the aperture-layer algebra.**  On scale-one shells the reader
is symmetric in the two factors, a strictly stronger statement than general cyclicity. -/
theorem soninWindowStateCyclicLogTrace_composeScaleOneShells_comm
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) (h₂ : a ≤ s₂) (h₂' : s₂ < t₂) :
    soninWindowStateCyclicLogTrace
        (composeSoninWindowStates
          (SoninWindowState.live (soninScaleOneShellWindow a s₁ t₁ h₁ h₁'))
          (SoninWindowState.live (soninScaleOneShellWindow a s₂ t₂ h₂ h₂'))) =
      soninWindowStateCyclicLogTrace
        (composeSoninWindowStates
          (SoninWindowState.live (soninScaleOneShellWindow a s₂ t₂ h₂ h₂'))
          (SoninWindowState.live (soninScaleOneShellWindow a s₁ t₁ h₁ h₁'))) := by
  rw [soninWindowStateCyclicLogTrace_composeScaleOneShells h₁ h₁' h₂ h₂',
    soninWindowStateCyclicLogTrace_composeScaleOneShells h₂ h₂' h₁ h₁',
    max_comm s₂ s₁, min_comm t₂ t₁]

/-- The reader of a scale-one shell against itself is its own logarithmic length: the layer
algebra is idempotent on the diagonal. -/
theorem soninWindowStateCyclicLogTrace_composeScaleOneShells_self
    (h₁ : a ≤ s₁) (h₁' : s₁ < t₁) :
    soninWindowStateCyclicLogTrace
        (composeSoninWindowStates
          (SoninWindowState.live (soninScaleOneShellWindow a s₁ t₁ h₁ h₁'))
          (SoninWindowState.live (soninScaleOneShellWindow a s₁ t₁ h₁ h₁'))) =
      Real.log t₁ - Real.log s₁ := by
  rw [soninWindowStateCyclicLogTrace_composeScaleOneShells h₁ h₁' h₁ h₁',
    max_self, min_self, if_pos h₁']

end RHTower
