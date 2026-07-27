import GaloisForLFunctions.HTGeometry.UnitaryReflectionPhaseHalving

/-!
# Unitary phases with reflected values

The phase-halving layer consumes `IsUnitaryPhase w` (`conj w · w = 1`) together with
`IsPhaseReflected w z` (`w² · conj z = z`), and neither is exhibited on a common pair.

The two fit together for a structural reason: the reflected values of a unitary phase `w` are exactly
its real multiples.  Indeed `w² · conj (t w) = t w (w · conj w) = t w` for real `t`.  So every unitary
phase carries a whole real line of reflected values, and both premises hold on `(w, t w)`.

* **`isPhaseReflected_real_mul`** — real multiples of a unitary phase are reflected;
* `isUnitaryPhase_one`, `isUnitaryPhase_I`;
* **`exists_unitaryPhase_phaseReflected`** — the pair, jointly realized with a nonzero value.
-/

namespace GaloisForLFunctions.HTGeometry

theorem isUnitaryPhase_one : IsUnitaryPhase 1 := by
  simp [IsUnitaryPhase]

theorem isUnitaryPhase_I : IsUnitaryPhase Complex.I := by
  simp [IsUnitaryPhase, Complex.I_mul_I]

/-- **Reflected values of a unitary phase.**  Every real multiple of a unitary phase obeys the real
structure carried by its square. -/
theorem isPhaseReflected_real_mul {w : ℂ} (hw : IsUnitaryPhase w) (t : ℝ) :
    IsPhaseReflected w ((t : ℂ) * w) := by
  have hcomm : w * (starRingEnd ℂ) w = 1 := by
    rw [mul_comm]; exact hw
  show w * w * (starRingEnd ℂ) ((t : ℂ) * w) = (t : ℂ) * w
  rw [map_mul, Complex.conj_ofReal]
  calc w * w * ((t : ℂ) * (starRingEnd ℂ) w)
      = (t : ℂ) * w * (w * (starRingEnd ℂ) w) := by ring
    _ = (t : ℂ) * w := by rw [hcomm, mul_one]

/-- **Joint realization**, with a nonzero reflected value. -/
theorem exists_unitaryPhase_phaseReflected :
    ∃ w z : ℂ, IsUnitaryPhase w ∧ IsPhaseReflected w z ∧ z ≠ 0 := by
  refine ⟨Complex.I, ((1 : ℝ) : ℂ) * Complex.I, isUnitaryPhase_I,
    isPhaseReflected_real_mul isUnitaryPhase_I 1, ?_⟩
  simp [Complex.I_ne_zero]

end GaloisForLFunctions.HTGeometry
