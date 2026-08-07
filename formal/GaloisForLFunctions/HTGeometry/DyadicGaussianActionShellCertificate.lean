import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw

/-!
# Dyadic Gaussian action-shell certificate

A two-scale Gaussian difference deletes every exact zero-action contribution,
while a finite dyadic telescope recovers the whole deviation from the
zero-action plateau.  Consequently, any packet excess above that plateau must
be visible on one collision-free dyadic action shell, up to an explicit
terminal spectral-gap remainder.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι : Type*}

/-- Real two-scale Gaussian band-pass kernel. -/
def dyadicGaussianActionKernel (action : ℝ) : ℝ :=
  Real.exp (-(action ^ 2) / 2) -
    Real.exp (-((2 * action) ^ 2) / 2)

/-- The complex Gaussian action difference is the real dyadic kernel. -/
theorem gaussianObserverActionKernel_sub_two_eq_dyadic
    (action : ℝ) :
    gaussianObserverActionKernel action -
        gaussianObserverActionKernel (2 * action) =
      (dyadicGaussianActionKernel action : ℂ) := by
  unfold gaussianObserverActionKernel dyadicGaussianActionKernel
  push_cast
  rfl

/-- The dyadic Gaussian kernel is nonnegative. -/
theorem dyadicGaussianActionKernel_nonneg (action : ℝ) :
    0 ≤ dyadicGaussianActionKernel action := by
  unfold dyadicGaussianActionKernel
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg action]

/-- Large actions have the original Gaussian exponential envelope. -/
theorem dyadicGaussianActionKernel_le_far (action : ℝ) :
    dyadicGaussianActionKernel action ≤
      Real.exp (-(action ^ 2) / 2) := by
  unfold dyadicGaussianActionKernel
  linarith [Real.exp_nonneg (-((2 * action) ^ 2) / 2)]

/-- Near zero the collision-free reporter vanishes quadratically. -/
theorem dyadicGaussianActionKernel_le_near (action : ℝ) :
    dyadicGaussianActionKernel action ≤ 3 * action ^ 2 / 2 := by
  let y : ℝ := 3 * action ^ 2 / 2
  have hy : 0 ≤ y := by
    dsimp [y]
    nlinarith [sq_nonneg action]
  have hfactor : Real.exp (-(action ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg action]
  have hsecond : 0 ≤ 1 - Real.exp (-y) := by
    rw [sub_nonneg, Real.exp_le_one_iff]
    linarith
  have hone : 1 - Real.exp (-y) ≤ y := by
    have h := Real.add_one_le_exp (-y)
    linarith
  have hidentity :
      dyadicGaussianActionKernel action =
        Real.exp (-(action ^ 2) / 2) *
          (1 - Real.exp (-y)) := by
    unfold dyadicGaussianActionKernel
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    dsimp [y]
    ring_nf
  rw [hidentity]
  calc
    Real.exp (-(action ^ 2) / 2) * (1 - Real.exp (-y)) ≤
        1 * y := mul_le_mul hfactor hone hsecond (by norm_num)
    _ = 3 * action ^ 2 / 2 := by simp [y]

/-- Exact norm of the complex two-scale kernel. -/
theorem norm_gaussianObserverActionKernel_sub_two (action : ℝ) :
    ‖gaussianObserverActionKernel action -
        gaussianObserverActionKernel (2 * action)‖ =
      dyadicGaussianActionKernel action := by
  rw [gaussianObserverActionKernel_sub_two_eq_dyadic,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dyadicGaussianActionKernel_nonneg action)]

/-- **Two-sided action localization.**  The dyadic reporter pays a quadratic
cost near a collision and an exponential cost at large action. -/
theorem norm_gaussianObserverActionKernel_sub_two_le_min
    (action : ℝ) :
    ‖gaussianObserverActionKernel action -
        gaussianObserverActionKernel (2 * action)‖ ≤
      min (3 * action ^ 2 / 2)
        (Real.exp (-(action ^ 2) / 2)) := by
  rw [norm_gaussianObserverActionKernel_sub_two]
  exact le_min (dyadicGaussianActionKernel_le_near action)
    (dyadicGaussianActionKernel_le_far action)

/-- Gaussian-smoothed value of a finite signed spectral packet. -/
def gaussianActionHeatPacket
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) : ℂ :=
  ∑ i ∈ support, coefficient i *
    gaussianObserverActionKernel (time * detuning i)

/-- Difference between adjacent dyadic Gaussian observation scales. -/
def dyadicGaussianActionWavelet
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) : ℂ :=
  gaussianActionHeatPacket support coefficient detuning time -
    gaussianActionHeatPacket support coefficient detuning (2 * time)

/-- Subtracting the zero-action plateau leaves exactly the nonzero-action
part of the Gaussian packet. -/
theorem gaussianActionHeatPacket_sub_zeroAction_eq_nonzero_sum
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) :
    gaussianActionHeatPacket support coefficient detuning time -
        zeroActionSpectralPacket support coefficient detuning =
      ∑ i ∈ support,
        if detuning i = 0 then 0 else
          coefficient i *
            gaussianObserverActionKernel (time * detuning i) := by
  classical
  unfold gaussianActionHeatPacket zeroActionSpectralPacket
  rw [Finset.sum_filter]
  rw [show
      (∑ i ∈ support, if detuning i = 0 then coefficient i else 0) =
        ∑ i ∈ support, if detuning i = 0 then coefficient i else 0 by rfl]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : detuning i = 0
  · simp [hzero, gaussianObserverActionKernel_zero]
  · simp [hzero]

/-- **Exact collision erasure.**  Every zero-action term vanishes from a
two-scale Gaussian wavelet. -/
theorem dyadicGaussianActionWavelet_eq_nonzero_sum
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) :
    dyadicGaussianActionWavelet support coefficient detuning time =
      ∑ i ∈ support,
        if detuning i = 0 then 0 else
          coefficient i *
            (gaussianObserverActionKernel (time * detuning i) -
              gaussianObserverActionKernel ((2 * time) * detuning i)) := by
  classical
  unfold dyadicGaussianActionWavelet gaussianActionHeatPacket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : detuning i = 0
  · simp [hzero, gaussianObserverActionKernel_zero]
  · simp [hzero]
    ring_nf

/-- **Finite dyadic action telescope.**  Adjacent two-scale wavelets recover
the difference between the initial and terminal Gaussian scales exactly. -/
theorem sum_dyadicGaussianActionWavelet_eq_sub
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) (levels : ℕ) :
    (∑ j ∈ Finset.range levels,
        dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)) =
      gaussianActionHeatPacket support coefficient detuning time -
        gaussianActionHeatPacket support coefficient detuning
          ((2 : ℝ) ^ levels * time) := by
  let packet : ℕ → ℂ := fun j =>
    gaussianActionHeatPacket support coefficient detuning
      ((2 : ℝ) ^ j * time)
  calc
    (∑ j ∈ Finset.range levels,
        dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)) =
        ∑ j ∈ Finset.range levels, (packet j - packet (j + 1)) := by
          apply Finset.sum_congr rfl
          intro j hj
          unfold dyadicGaussianActionWavelet packet
          congr 2
          rw [pow_succ]
          ring_nf
    _ = packet 0 - packet levels := Finset.sum_range_sub' packet levels
    _ = gaussianActionHeatPacket support coefficient detuning time -
        gaussianActionHeatPacket support coefficient detuning
          ((2 : ℝ) ^ levels * time) := by
          simp [packet]

/-- A positive nonzero-action gap gives exponential control of the terminal
Gaussian remainder, with coefficient total variation as the only prefactor. -/
theorem norm_gaussianActionHeatPacket_sub_zeroAction_le
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) {time gap : ℝ}
    (htime : 0 < time) (hgap : 0 < gap)
    (hdetuning : ∀ i ∈ support, detuning i ≠ 0 → gap ≤ |detuning i|) :
    ‖gaussianActionHeatPacket support coefficient detuning time -
        zeroActionSpectralPacket support coefficient detuning‖ ≤
      (∑ i ∈ support, ‖coefficient i‖) *
        Real.exp (-((time * gap) ^ 2) / 2) := by
  classical
  rw [gaussianActionHeatPacket_sub_zeroAction_eq_nonzero_sum]
  calc
    ‖∑ i ∈ support,
        if detuning i = 0 then 0 else
          coefficient i *
            gaussianObserverActionKernel (time * detuning i)‖ ≤
        ∑ i ∈ support,
          ‖if detuning i = 0 then 0 else
            coefficient i *
              gaussianObserverActionKernel (time * detuning i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ support,
        ‖coefficient i‖ * Real.exp (-((time * gap) ^ 2) / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero : detuning i = 0
      · simp [hzero]
        exact mul_nonneg (norm_nonneg _ ) (Real.exp_nonneg _)
      · simp only [hzero, ↓reduceIte, norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_gaussianObserverActionKernel_mul_le
            htime hgap (hdetuning i hi hzero)) (norm_nonneg _)
    _ = (∑ i ∈ support, ‖coefficient i‖) *
        Real.exp (-((time * gap) ^ 2) / 2) := by
      rw [Finset.sum_mul]

/-- **Dyadic Gaussian action-shell upper certificate.**  The complete excess
above the collision plateau is bounded by the sum of collision-free shell
reporters and one explicit terminal gap remainder. -/
theorem norm_gaussianActionHeatPacket_sub_zeroAction_le_shells_add_tail
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) {time gap : ℝ} (levels : ℕ)
    (htime : 0 < time) (hgap : 0 < gap)
    (hdetuning : ∀ i ∈ support, detuning i ≠ 0 → gap ≤ |detuning i|) :
    ‖gaussianActionHeatPacket support coefficient detuning time -
        zeroActionSpectralPacket support coefficient detuning‖ ≤
      (∑ j ∈ Finset.range levels,
        ‖dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)‖) +
      (∑ i ∈ support, ‖coefficient i‖) *
        Real.exp (-((((2 : ℝ) ^ levels * time) * gap) ^ 2) / 2) := by
  have hterminalTime : 0 < (2 : ℝ) ^ levels * time :=
    mul_pos (pow_pos (by norm_num) _) htime
  have htel := sum_dyadicGaussianActionWavelet_eq_sub
    support coefficient detuning time levels
  have hdecomposition :
      gaussianActionHeatPacket support coefficient detuning time -
          zeroActionSpectralPacket support coefficient detuning =
        (∑ j ∈ Finset.range levels,
          dyadicGaussianActionWavelet support coefficient detuning
            ((2 : ℝ) ^ j * time)) +
        (gaussianActionHeatPacket support coefficient detuning
            ((2 : ℝ) ^ levels * time) -
          zeroActionSpectralPacket support coefficient detuning) := by
    rw [htel]
    ring_nf
  rw [hdecomposition]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · exact norm_sum_le _ _
  · exact norm_gaussianActionHeatPacket_sub_zeroAction_le
      support coefficient detuning hterminalTime hgap hdetuning

/-- **Inverse dyadic shell certificate.**  If a Gaussian packet differs from
its exact collision plateau by `η`, while the terminal scale contributes at
most `η/2`, some collision-free shell carries at least the average residual
`η/(2L)`. -/
theorem exists_large_dyadicGaussianActionWavelet
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) {time gap η : ℝ} {levels : ℕ}
    (htime : 0 < time) (hgap : 0 < gap) (_hη : 0 ≤ η)
    (hlevels : 0 < levels)
    (hdetuning : ∀ i ∈ support, detuning i ≠ 0 → gap ≤ |detuning i|)
    (hexcess : η ≤
      ‖gaussianActionHeatPacket support coefficient detuning time -
        zeroActionSpectralPacket support coefficient detuning‖)
    (htail :
      (∑ i ∈ support, ‖coefficient i‖) *
          Real.exp (-((((2 : ℝ) ^ levels * time) * gap) ^ 2) / 2) ≤
        η / 2) :
    ∃ j ∈ Finset.range levels,
      η / (2 * (levels : ℝ)) ≤
        ‖dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)‖ := by
  have hbound :=
    norm_gaussianActionHeatPacket_sub_zeroAction_le_shells_add_tail
      support coefficient detuning levels htime hgap hdetuning
  have hsum :
      η / 2 ≤ ∑ j ∈ Finset.range levels,
        ‖dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)‖ := by
    linarith
  by_contra hlarge
  simp only [not_exists, not_and, not_le] at hlarge
  have hstrict :
      (∑ j ∈ Finset.range levels,
        ‖dyadicGaussianActionWavelet support coefficient detuning
          ((2 : ℝ) ^ j * time)‖) <
        ∑ _j ∈ Finset.range levels, η / (2 * (levels : ℝ)) := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact (hlarge j hj).le
    · exact ⟨0, Finset.mem_range.mpr hlevels, hlarge 0 (Finset.mem_range.mpr hlevels)⟩
  have hlevelsReal : (levels : ℝ) ≠ 0 := by
    exact_mod_cast hlevels.ne'
  have hconstant :
      (∑ _j ∈ Finset.range levels, η / (2 * (levels : ℝ))) = η / 2 := by
    simp
    field_simp
  rw [hconstant] at hstrict
  exact (not_lt_of_ge hsum) hstrict

end GaloisForLFunctions.HTGeometry
