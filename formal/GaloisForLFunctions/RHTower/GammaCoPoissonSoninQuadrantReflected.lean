import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSection
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinReflection

/-!
# The quadrant section below the critical line

Burnol's continued completed-Mellin evaluation on the left half of the strip is the right-half
evaluation at the reflected point composed with the cosine involution.  That involution commutes
with the co-Poisson quotient projection and exchanges the two normalized dilations, hence exchanges
the two bonding maps.  Since the ladder character at `1 - w` is the inverse of the character at
`w`, the reflected quotient kernels satisfy the *same* two bonding laws with the *same* character
`r^(w-1/2)`, and therefore the same forced escape law.  Together with the right-half section this
covers every point of the open strip off the critical line.
-/

open Complex Real
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {w : ℂ} {a r : ℝ}

/-- The cosine involution exchanges the two bonding maps. -/
theorem coPoissonQuotientForward_cosine (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (x : evenSubspace) :
    coPoissonQuotientForward a r ha hr j (soninCosineUnitary x) =
      soninCosineUnitary (coPoissonQuotientInverse a r ha hr j x) := by
  have hdil : evenDilationCLM r⁻¹ (inv_pos.mpr hr) (soninCosineUnitary x) =
      soninCosineUnitary (evenDilationCLM r hr x) :=
    (soninCosineUnitary_evenDilation r hr x).symm
  have hproj := evenFourierTransform_burnolCoPoissonQuotientProjection
    (soninAperture a r j) (soninAperture_pos ha hr j) (evenDilationCLM r hr x)
  rw [coPoissonQuotientForward, ContinuousLinearMap.comp_apply, hdil,
    coPoissonQuotientInverse, ContinuousLinearMap.comp_apply]
  exact hproj.symm

/-- The cosine involution exchanges the two bonding maps, other direction. -/
theorem coPoissonQuotientInverse_cosine (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ)
    (x : evenSubspace) :
    coPoissonQuotientInverse a r ha hr j (soninCosineUnitary x) =
      soninCosineUnitary (coPoissonQuotientForward a r ha hr j x) := by
  have hdil : evenDilationCLM r hr (soninCosineUnitary x) =
      soninCosineUnitary (evenDilationCLM r⁻¹ (inv_pos.mpr hr) x) := by
    have h := soninCosineUnitary_evenDilation r hr (soninCosineUnitary x)
    rw [soninCosineUnitary_involutive] at h
    have h2 := congrArg soninCosineUnitary h
    rw [soninCosineUnitary_involutive] at h2
    exact h2
  have hproj := evenFourierTransform_burnolCoPoissonQuotientProjection
    (soninAperture a r j) (soninAperture_pos ha hr j)
    (evenDilationCLM r⁻¹ (inv_pos.mpr hr) x)
  rw [coPoissonQuotientInverse, ContinuousLinearMap.comp_apply, hdil,
    coPoissonQuotientForward, ContinuousLinearMap.comp_apply]
  exact hproj.symm

/-- The ladder character at the reflected point is the inverse character. -/
theorem soninLadderCharacter_one_sub (hr : 0 < r) (w : ℂ) :
    soninLadderCharacter (1 - w) r = (soninLadderCharacter w r)⁻¹ := by
  have hrne : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  rw [soninLadderCharacter, soninLadderCharacter, ← Complex.cpow_neg]
  congr 1
  ring

section Reflected

variable (w) in
/-- The reflection of a left-half point into the right half of the strip. -/
theorem one_sub_re_lo (hhi : w.re < 1 / 2) : 1 / 2 < (1 - w).re := by
  rw [Complex.sub_re, Complex.one_re]; linarith

variable (w) in
theorem one_sub_re_hi (hlo : 0 < w.re) : (1 - w).re < 1 := by
  rw [Complex.sub_re, Complex.one_re]; linarith

/-- The co-Poisson quotient kernel of the continued left-half-plane evaluation: the cosine
involution applied to the right-half kernel at the reflected point. -/
def coPoissonReflectedLadderKernel (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2)
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) : evenSubspace :=
  soninCosineUnitary
    (coPoissonLadderKernel (1 - w) (one_sub_re_lo w hhi) (one_sub_re_hi w hlo) a r ha hr j)

/-- The definition agrees with the genuine co-Poisson quotient kernel of the continued
left-half-plane evaluation. -/
theorem coPoissonReflectedLadderKernel_eq (hlo : 0 < w.re) (hhi : w.re < 1 / 2)
    (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    coPoissonReflectedLadderKernel w hlo hhi a r ha hr j =
      (burnolCoPoissonQuotientReflectedEvaluationVector w (soninAperture a r j) hlo hhi
        (soninAperture_pos ha hr j) : evenSubspace) :=
  (coe_burnolCoPoissonQuotientReflectedEvaluationVector_eq_cosine w (soninAperture a r j)
    hlo hhi (soninAperture_pos ha hr j)).symm

theorem norm_coPoissonReflectedLadderKernel (hlo : 0 < w.re) (hhi : w.re < 1 / 2)
    (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    ‖coPoissonReflectedLadderKernel w hlo hhi a r ha hr j‖ =
      ‖coPoissonLadderKernel (1 - w) (one_sub_re_lo w hhi) (one_sub_re_hi w hlo) a r ha hr j‖ :=
  soninCosineUnitary.norm_map _

/-- **The forward bonding character below the critical line.**  The character is the same
`r^(w-1/2)` as above the line. -/
theorem coPoissonQuotientForward_reflectedLadderKernel {hlo : 0 < w.re} {hhi : w.re < 1 / 2}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator (1 - w) (one_sub_re_lo w hhi) (one_sub_re_hi w hlo)
      a r ha hr) (j : ℕ) :
    coPoissonQuotientForward a r ha hr j
        (coPoissonReflectedLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) (soninLadderCharacter w r) •
        coPoissonReflectedLadderKernel w hlo hhi a r ha hr j := by
  rw [coPoissonReflectedLadderKernel, coPoissonQuotientForward_cosine,
    coPoissonQuotientInverse_ladderKernel hr1 hann j, map_smul,
    coPoissonReflectedLadderKernel, soninLadderCharacter_one_sub hr, inv_inv]

/-- **The inverse bonding character below the critical line.** -/
theorem coPoissonQuotientInverse_reflectedLadderKernel {hlo : 0 < w.re} {hhi : w.re < 1 / 2}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator (1 - w) (one_sub_re_lo w hhi) (one_sub_re_hi w hlo)
      a r ha hr) (j : ℕ) :
    coPoissonQuotientInverse a r ha hr j
        (coPoissonReflectedLadderKernel w hlo hhi a r ha hr (j + 1)) =
      (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
        coPoissonReflectedLadderKernel w hlo hhi a r ha hr j := by
  rw [coPoissonReflectedLadderKernel, coPoissonQuotientInverse_cosine,
    coPoissonQuotientForward_ladderKernel hr1 hann j, map_smul,
    coPoissonReflectedLadderKernel, soninLadderCharacter_one_sub hr]

/-- **The forced escape law below the critical line.** -/
theorem norm_coPoissonReflectedLadderKernel_max_le {hlo : 0 < w.re} {hhi : w.re < 1 / 2}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator (1 - w) (one_sub_re_lo w hhi) (one_sub_re_hi w hlo)
      a r ha hr) (N : ℕ) :
    max (‖soninLadderCharacter w r‖ ^ N) ((‖soninLadderCharacter w r‖⁻¹) ^ N) *
        ‖coPoissonReflectedLadderKernel w hlo hhi a r ha hr 0‖ ≤
      ‖coPoissonReflectedLadderKernel w hlo hhi a r ha hr N‖ := by
  have hchar : ‖soninLadderCharacter w r‖ = ‖soninLadderCharacter (1 - w) r‖⁻¹ := by
    rw [soninLadderCharacter_one_sub hr, norm_inv, inv_inv]
  rw [norm_coPoissonReflectedLadderKernel, norm_coPoissonReflectedLadderKernel, hchar,
    inv_inv, max_comm]
  exact norm_coPoissonLadderKernel_max_le hr1 hann N

end Reflected

end RHTower
