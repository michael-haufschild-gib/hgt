import GaloisForLFunctions.HTGeometry.FiniteResponseLiouvillian

open scoped InnerProductSpace

namespace HTGeometry

noncomputable section

/-- Zero-gap (stationary) component of a finite transition vector. -/
def transitionGapStationaryPart {α : Type*}
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) :
    EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 fun ab =>
    if energy ab.1 = energy ab.2 then x ab else 0

/-- Green primitive of the nonstationary component, defined by division by
the nonzero transition gap and set to zero on the stationary sector. -/
def transitionGapGreenPrimitive {α : Type*}
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) :
    EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 fun ab =>
    if energy ab.1 = energy ab.2 then 0
    else x ab / ((energy ab.1 - energy ab.2 : ℝ) : ℂ)

@[simp] theorem transitionGapStationaryPart_apply {α : Type*}
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) (ab : α × α) :
    transitionGapStationaryPart energy x ab =
      if energy ab.1 = energy ab.2 then x ab else 0 := rfl

@[simp] theorem transitionGapGreenPrimitive_apply {α : Type*}
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) (ab : α × α) :
    transitionGapGreenPrimitive energy x ab =
      if energy ab.1 = energy ab.2 then 0
      else x ab / ((energy ab.1 - energy ab.2 : ℝ) : ℂ) := rfl

/-- The stationary part lies in the exact kernel of the spectral
Liouvillian. -/
theorem transitionGapLiouvillian_stationaryPart_eq_zero
    {α : Type*} [Fintype α]
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) :
    transitionGapLiouvillian energy
        (transitionGapStationaryPart energy x) = 0 := by
  ext ab
  by_cases h : energy ab.1 = energy ab.2
  · simp [h]
  · simp [h]

/-- **Finite Liouvillian Hodge--Green decomposition.** Every transition
vector is the sum of its stationary component and one exact Liouvillian
coboundary. -/
theorem transitionGap_hodgeGreen_decomposition
    {α : Type*} [Fintype α]
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) :
    transitionGapStationaryPart energy x +
        transitionGapLiouvillian energy
          (transitionGapGreenPrimitive energy x) = x := by
  ext ab
  by_cases h : energy ab.1 = energy ab.2
  · simp [PiLp.add_apply, h]
  · have hneC : (energy ab.1 : ℂ) ≠ (energy ab.2 : ℂ) := by
      exact_mod_cast h
    have hgapC : (energy ab.1 : ℂ) - (energy ab.2 : ℂ) ≠ 0 :=
      sub_ne_zero.mpr hneC
    simp only [PiLp.add_apply, transitionGapStationaryPart_apply,
      transitionGapLiouvillian_apply, transitionGapGreenPrimitive_apply,
      h, ↓reduceIte, zero_add]
    push_cast
    exact mul_div_cancel₀ (x ab) hgapC

end

end HTGeometry
