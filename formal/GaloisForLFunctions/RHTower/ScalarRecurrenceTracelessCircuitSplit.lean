import GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiShortcutActionLaw
import GaloisForLFunctions.HTGeometry.TracelessReplicaCancellationLaw

/-!
# Scalar recurrence / traceless circuit split

Every normalized static-Choi target splits canonically into its component
along the identity Choi state and an orthogonal residual.  A large overlap
with any target therefore forces either one common return amplitude or the
target-specific residual amplitude to be large.  The common return channel
can be charged once before taking a circuit union.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- A large linear combination with a contractive scalar coefficient forces
one of its two summands to be large. -/
theorem norm_common_or_residual_of_norm_linear_split_ge
    {alpha common residual : ℂ} {theta : ℝ}
    (halpha : ‖alpha‖ ≤ 1)
    (hlarge : theta ≤ ‖alpha * common + residual‖) :
    theta / 2 ≤ ‖common‖ ∨ theta / 2 ≤ ‖residual‖ := by
  by_contra h
  push Not at h
  rcases h with ⟨hcommon, hresidual⟩
  have halphaCommon : ‖alpha * common‖ < theta / 2 := by
    calc
      ‖alpha * common‖ = ‖alpha‖ * ‖common‖ := norm_mul _ _
      _ ≤ 1 * ‖common‖ :=
        mul_le_mul_of_nonneg_right halpha (norm_nonneg common)
      _ < theta / 2 := by simpa using hcommon
  have hsmall : ‖alpha * common + residual‖ < theta := by
    calc
      ‖alpha * common + residual‖ ≤
          ‖alpha * common‖ + ‖residual‖ := norm_add_le _ _
      _ < theta / 2 + theta / 2 := add_lt_add halphaCommon hresidual
      _ = theta := by ring
  exact (not_lt_of_ge hlarge) hsmall

/-- Adjustable-budget form of the scalar/residual split.  The common channel
may be assigned any threshold `eta`; the residual pays exactly the remaining
threshold `theta - eta`. -/
theorem norm_common_or_residual_of_norm_linear_split_ge_budget
    {alpha common residual : ℂ} {theta eta : ℝ}
    (halpha : ‖alpha‖ ≤ 1)
    (hlarge : theta ≤ ‖alpha * common + residual‖) :
    eta ≤ ‖common‖ ∨ theta - eta ≤ ‖residual‖ := by
  by_cases hcommon : eta ≤ ‖common‖
  · exact Or.inl hcommon
  · right
    have hcommon' : ‖common‖ < eta := lt_of_not_ge hcommon
    have halphaCommon : ‖alpha * common‖ < eta := by
      calc
        ‖alpha * common‖ = ‖alpha‖ * ‖common‖ := norm_mul _ _
        _ ≤ 1 * ‖common‖ :=
          mul_le_mul_of_nonneg_right halpha (norm_nonneg common)
        _ < eta := by simpa using hcommon'
    have hadd : ‖alpha * common‖ + ‖residual‖ < eta + ‖residual‖ := by
      simpa [add_comm] using add_lt_add_right halphaCommon ‖residual‖
    have hstrict : ‖alpha * common + residual‖ < eta + ‖residual‖ :=
      (norm_add_le _ _).trans_lt hadd
    linarith

/-- Component of a Choi target along the identity Choi state. -/
def staticChoiScalarComponent
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) : ℂ :=
  inner ℂ (staticSpectralChoiVector d 0 energy) target

/-- Orthogonal complement of the identity-Choi component.  In operator
language this is the normalized-trace-zero part of the target. -/
def staticChoiTracelessResidual
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  target - staticChoiScalarComponent energy target •
    staticSpectralChoiVector d 0 energy

theorem staticChoiTarget_eq_scalar_add_traceless
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiScalarComponent energy target •
          staticSpectralChoiVector d 0 energy +
        staticChoiTracelessResidual energy target = target := by
  simp [staticChoiTracelessResidual]

theorem inner_staticChoiTracelessResidual_zero
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d 0 energy)
      (staticChoiTracelessResidual energy target) = 0 := by
  rw [staticChoiTracelessResidual, inner_sub_right, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, staticSpectralChoiVector_norm hd]
  simp [staticChoiScalarComponent]

theorem norm_staticChoiScalarComponent_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiScalarComponent energy target‖ ≤ 1 := by
  calc
    ‖staticChoiScalarComponent energy target‖ =
        ‖inner ℂ (staticSpectralChoiVector d 0 energy) target‖ := rfl
    _ ≤ ‖staticSpectralChoiVector d 0 energy‖ * ‖target‖ :=
      norm_inner_le_norm _ _
    _ = 1 := by rw [staticSpectralChoiVector_norm hd, htarget, one_mul]

theorem inner_staticChoiTarget_scalar_traceless_decomposition
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d t energy) target =
      staticChoiScalarComponent energy target *
          inner ℂ (staticSpectralChoiVector d t energy)
            (staticSpectralChoiVector d 0 energy) +
        inner ℂ (staticSpectralChoiVector d t energy)
          (staticChoiTracelessResidual energy target) := by
  nth_rewrite 1 [← staticChoiTarget_eq_scalar_add_traceless energy target]
  rw [inner_add_right, inner_smul_right]

/-- **Scalar-once shortcut split.**  Capture of any normalized target at
threshold `theta` forces either the same identity-recurrence amplitude for
all targets or that target's orthogonal residual amplitude. -/
theorem staticChoiTarget_capture_scalar_or_traceless
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) {theta : ℝ}
    (hlarge : theta ≤
      ‖inner ℂ (staticSpectralChoiVector d t energy) target‖) :
    theta / 2 ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticSpectralChoiVector d 0 energy)‖ ∨
      theta / 2 ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticChoiTracelessResidual energy target)‖ := by
  rw [inner_staticChoiTarget_scalar_traceless_decomposition] at hlarge
  exact norm_common_or_residual_of_norm_linear_split_ge
    (norm_staticChoiScalarComponent_le_one hd energy htarget) hlarge

/-- Adjustable-budget Choi specialization. -/
theorem staticChoiTarget_capture_scalar_or_traceless_budget
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) {theta eta : ℝ}
    (hlarge : theta ≤
      ‖inner ℂ (staticSpectralChoiVector d t energy) target‖) :
    eta ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticSpectralChoiVector d 0 energy)‖ ∨
      theta - eta ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticChoiTracelessResidual energy target)‖ := by
  rw [inner_staticChoiTarget_scalar_traceless_decomposition] at hlarge
  exact norm_common_or_residual_of_norm_linear_split_ge_budget
    (norm_staticChoiScalarComponent_le_one hd energy htarget) hlarge

/-- Times at which the static Choi orbit has overlap at least `theta` with a
specified target. -/
def staticChoiOverlapCaptureSet
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (theta : ℝ) : Set ℝ :=
  {t | theta ≤ ‖inner ℂ (staticSpectralChoiVector d t energy) target‖}

/-- The common identity-recurrence channel, independent of circuit target. -/
def staticChoiScalarReturnSet
    {d : ℕ} (energy : Fin d → ℝ) (theta : ℝ) : Set ℝ :=
  staticChoiOverlapCaptureSet energy
    (staticSpectralChoiVector d 0 energy) theta

/-- Target-specific capture by the component orthogonal to identity. -/
def staticChoiTracelessCaptureSet
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (theta : ℝ) : Set ℝ :=
  staticChoiOverlapCaptureSet energy
    (staticChoiTracelessResidual energy target) theta

/-- **Common recurrence is charged once.**  An arbitrary target union splits
into one identity-return event and the union of target-specific traceless
events.  No finiteness or measurability assumption on the target family is
needed for this deterministic inclusion. -/
theorem iUnion_staticChoiOverlapCaptureSet_subset_scalar_union_traceless
    {d : ℕ} (hd : 0 < d) {W : Type*} (energy : Fin d → ℝ)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1) (theta : ℝ) :
    (⋃ w, staticChoiOverlapCaptureSet energy (target w) theta) ⊆
      staticChoiScalarReturnSet energy (theta / 2) ∪
        ⋃ w, staticChoiTracelessCaptureSet energy (target w) (theta / 2) := by
  intro t ht
  simp only [Set.mem_iUnion, staticChoiOverlapCaptureSet] at ht
  obtain ⟨w, hw⟩ := ht
  rcases staticChoiTarget_capture_scalar_or_traceless
      hd t energy (htarget w) hw with hscalar | htraceless
  · exact Set.mem_union_left _ hscalar
  · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨w, htraceless⟩)

/-- Adjustable-budget union law.  One may optimize the threshold assigned to
the common recurrence channel without paying target cardinality for it. -/
theorem iUnion_staticChoiOverlapCaptureSet_subset_scalar_union_traceless_budget
    {d : ℕ} (hd : 0 < d) {W : Type*} (energy : Fin d → ℝ)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1) (theta eta : ℝ) :
    (⋃ w, staticChoiOverlapCaptureSet energy (target w) theta) ⊆
      staticChoiScalarReturnSet energy eta ∪
        ⋃ w, staticChoiTracelessCaptureSet energy (target w) (theta - eta) := by
  intro t ht
  simp only [Set.mem_iUnion, staticChoiOverlapCaptureSet] at ht
  obtain ⟨w, hw⟩ := ht
  rcases staticChoiTarget_capture_scalar_or_traceless_budget
      hd t energy (htarget w) hw with hscalar | htraceless
  · exact Set.mem_union_left _ hscalar
  · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨w, htraceless⟩)

/-- Complex spectral coefficient of the target component orthogonal to the
identity Choi state. -/
def staticChoiTracelessSpectralCoefficient
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) (i : Fin d) : ℂ :=
  ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
    staticChoiTracelessResidual energy target (i, i)

/-- Traceless Choi coefficients sum to zero in every spectral basis. -/
theorem sum_staticChoiTracelessSpectralCoefficient_eq_zero
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∑ i, staticChoiTracelessSpectralCoefficient energy target i = 0 := by
  have hzero := inner_staticChoiTracelessResidual_zero hd energy target
  rw [inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at hzero
  unfold twistedFiniteSpectralAmplitude at hzero
  simp only [mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] at hzero
  rw [show (∑ i, staticChoiTracelessSpectralCoefficient energy target i) =
      ∑ i, (directStaticChoiTargetWeight d
          (staticChoiTracelessResidual energy target) i : ℂ) *
        directStaticChoiTargetTwist
          (staticChoiTracelessResidual energy target) i by
    apply Finset.sum_congr rfl
    intro i hi
    exact (directStaticChoiTargetWeight_mul_twist
      (staticChoiTracelessResidual energy target) i).symm]
  exact hzero

/-- **All-order Choi traceless cancellation.**  At every positive replica
order, the signed mass of any spectral multiplicity sector is exactly the
negative of its complement. -/
theorem staticChoiTracelessReplicaSectorMass_eq_neg_complement
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    {n : ℕ} (hn : 0 < n)
    (relation : (Fin d → ℕ) → (Fin d → ℕ) → Prop) :
    complexReplicaSectorMass
        (staticChoiTracelessSpectralCoefficient energy target) n relation =
      -complexReplicaSectorMass
        (staticChoiTracelessSpectralCoefficient energy target) n
          (fun p q => ¬ relation p q) := by
  exact complexReplicaSectorMass_eq_neg_complement_of_sum_eq_zero
    (sum_staticChoiTracelessSpectralCoefficient_eq_zero hd energy target)
    hn relation

end RHTower
