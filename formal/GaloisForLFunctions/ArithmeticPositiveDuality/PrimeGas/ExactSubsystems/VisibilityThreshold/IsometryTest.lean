import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.VisibilityThreshold.Overlap

/-! # A single clock tests norm-preserving composition at every complex parameter -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- The damping at the onset of a uniform overlap identifies every isometric split.
The readout clock can be chosen independently of the imaginary part of the split parameter. -/
theorem fixed_clock_tests_composition (s : ℂ) {t : ℝ} (ht : t ≠ 0) :
    (¬uniformOverlap s.re t ∧ ∀ ε : ℝ, 0 < ε → uniformOverlap (s.re+ε) t) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  by_cases hp : 0 < s.re
  · have he := overlap_boundary_iff_isometric hp ht
    rwa [split_isometric_iff,thermalPoint_re] at he
  · have hle := le_of_not_gt hp
    constructor
    · rintro ⟨_,h⟩
      have hδ : 0 < 1/4-s.re := by linarith
      have hq := h _ hδ
      rw [show s.re+(1/4-s.re) = 1/4 by ring] at hq
      have hh := (uniformOverlap_iff (by positivity : (0:ℝ)<1/4) ht).mp hq
      linarith
    · intro he
      exfalso
      linarith

/-- An unconditional detector for all complex split parameters, at the single clock time one. -/
theorem unit_clock_tests_composition (s : ℂ) :
    (¬uniformOverlap s.re 1 ∧ ∀ ε : ℝ, 0 < ε → uniformOverlap (s.re+ε) 1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  fixed_clock_tests_composition s one_ne_zero

#print axioms fixed_clock_tests_composition
#print axioms unit_clock_tests_composition

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
