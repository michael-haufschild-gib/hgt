import GaloisForLFunctions.HTGeometry.InfiniteTorusCharacter
import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageCharacterLaw

/-!
# Time averages along an infinite Kronecker flow

The symmetric time average of a continuous function along the phase flow of a frequency family is a
linear functional bounded by the supremum norm.  On a character it is the elementary phase average
of the character's detuning, which converges to one at zero detuning and to zero otherwise.

Under rational independence the detuning vanishes only for the trivial character, so on every
character the time average converges to the character's Haar mean -- the first half of unique
ergodicity of the flow on the product torus.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-- Symmetric time average of a continuous torus function along a phase flow. -/
def flowAverage (omega : ι → ℝ) (T : ℝ) (f : C(UnitAddTorus ι, ℂ)) : ℂ :=
  (2 * T : ℂ)⁻¹ * ∫ t in -T..T, f (clockPhasePoint omega t)

theorem flowAverage_torusCharacter (omega : ι → ℝ) (n : ι →₀ ℤ) (T : ℝ) :
    flowAverage omega T (torusCharacter n)
      = symmetricPhaseAverage T (characterDetuning n omega) := by
  rw [flowAverage, symmetricPhaseAverage]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact torusCharacter_clockPhasePoint n omega t

theorem characterDetuning_zero (omega : ι → ℝ) :
    characterDetuning (0 : ι →₀ ℤ) omega = 0 := by
  rw [characterDetuning]
  simp

/-- Under rational independence only the trivial character is resonant. -/
theorem characterDetuning_eq_zero_iff {omega : ι → ℝ} (h : RationallyIndependentSequence omega)
    (n : ι →₀ ℤ) : characterDetuning n omega = 0 ↔ n = 0 := by
  classical
  constructor
  · intro hzero
    have hsum : (∑ i : (n.support : Set ι), ((fun j : (n.support : Set ι) => (n j : ℤ)) i : ℝ) *
        omega i) = 0 := by
      rw [← Finset.sum_subtype n.support (fun x => Finset.mem_coe.symm)
        (fun i => (n i : ℝ) * omega i)]
      exact hzero
    have hvec := h n.support (fun i : (n.support : Set ι) => n i) hsum
    refine Finsupp.ext fun i => ?_
    by_cases hi : i ∈ n.support
    · have := congrFun hvec ⟨i, hi⟩
      simpa using this
    · simpa using Finsupp.notMem_support_iff.mp hi
  · intro hn
    subst hn
    exact characterDetuning_zero omega

/-- **The time average of a character converges to its Haar mean.** -/
theorem tendsto_flowAverage_torusCharacter [Countable ι] [DecidableEq ι] {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) (n : ι →₀ ℤ) :
    Tendsto (fun T => flowAverage omega T (torusCharacter n)) atTop
      (𝓝 (∫ x, torusCharacter n x ∂(torusHaar ι))) := by
  classical
  have hfun : (fun T => flowAverage omega T (torusCharacter n))
      = fun T => symmetricPhaseAverage T (characterDetuning n omega) :=
    funext fun T => flowAverage_torusCharacter omega n T
  rw [hfun, integral_torusCharacter]
  have hlim := symmetricPhaseAverage_tendsto_resonanceIndicator (characterDetuning n omega)
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    rwa [if_pos (characterDetuning_zero omega)] at hlim
  · rw [if_neg hn]
    rwa [if_neg (fun hcon => hn ((characterDetuning_eq_zero_iff h n).mp hcon))] at hlim

end

end GaloisForLFunctions.HTGeometry
