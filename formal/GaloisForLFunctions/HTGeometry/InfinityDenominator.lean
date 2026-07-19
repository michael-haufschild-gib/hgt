import GaloisForLFunctions.HTGeometry.LeafConstruction
import GaloisForLFunctions.HTGeometry.NevanlinnaRealMatrix

/-!
# The leaf at the parameter infinity, and the fiber form of the finite leaves

At `τ = ∞` the denominator is `B` alone.  `nevBreal_closed` already writes it as
`(h₀/hₙ)·(Rₙ(0)·Q_{n+1}(x) − R_{n+1}(0)·Qₙ(x))`, so the whole finite-parameter development applies
verbatim with `αₙ = Rₙ(0)` and `βₙ = −R_{n+1}(0)`.  The non-degeneracy is again the Wronskian at the
origin: `Rₙ(0)` and `R_{n+1}(0)` cannot both vanish.

The finite leaves are also restated here against the denominator fibers of `nevMatrixDataInf`, which
is the form the packaged family consumes.
-/

open scoped BigOperators
open MeasureTheory

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## The finite leaves in fiber form -/

/-- **The leaf of a finite parameter, in the form the family interface uses.** -/
theorem exists_leaf_finiteDenominatorFiber (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (tau : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (fun k => (s 0)⁻¹ * s k)
          (μ : Measure ℝ) ∧
        (μ : Measure ℝ) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 := by
  obtain ⟨μ, hmom, hcar⟩ := exists_leaf h h0b tau
  refine ⟨μ, fun k => hmom k, ?_⟩
  have hset : ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ
      = {x : ℝ | nevBrealInf s x * tau - nevDrealInf s x ≠ 0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
      GaloisForLFunctions.HTGeometry.ClassicalNevanlinnaMatrixData.finiteDenominatorFiber,
      nevMatrixDataInf]
  rw [hset]
  exact hcar

/-- For a normalised moment sequence the leaf represents it on the nose. -/
theorem exists_leaf_finiteDenominatorFiber_of_moment_zero_eq_one (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (tau : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (μ : Measure ℝ) ∧
        (μ : Measure ℝ) ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)ᶜ = 0 := by
  obtain ⟨μ, hmom, hcar⟩ := exists_leaf_finiteDenominatorFiber h h0b tau
  refine ⟨μ, fun k => ⟨(hmom k).1, ?_⟩, hcar⟩
  simpa [h0] using (hmom k).2

/-! ## The denominator at infinity -/

/-- The leading coefficient of `B` in the quasi-orthogonal basis. -/
noncomputable def nevAlphaInf (s : ℕ → ℝ) (n : ℕ) : ℝ := (secondKind s n).eval 0

/-- The trailing coefficient of `B` in the quasi-orthogonal basis. -/
noncomputable def nevBetaInf (s : ℕ → ℝ) (n : ℕ) : ℝ := -(secondKind s (n + 1)).eval 0

theorem nevBetaInf_eq_neg_nevAlphaInf_succ (s : ℕ → ℝ) (n : ℕ) :
    nevBetaInf s n = -nevAlphaInf s (n + 1) := rfl

/-- **`B` never degenerates.**  Both coefficients vanishing would zero the Wronskian at the
origin. -/
theorem nevAlphaInf_beta_ne_zero (h : PositiveMomentForm s) (n : ℕ) :
    ¬ (nevAlphaInf s n = 0 ∧ nevBetaInf s n = 0) := by
  rintro ⟨ha, hb⟩
  have hRn : (secondKind s n).eval 0 = 0 := ha
  have hRn1 : (secondKind s (n + 1)).eval 0 = 0 := by
    rw [nevBetaInf, neg_eq_zero] at hb
    exact hb
  have hw := wronskian_eval_zero h n
  rw [hRn, hRn1, mul_zero, mul_zero, sub_zero] at hw
  have hpos : 0 < momentInner s (monicOrtho s n) (monicOrtho s n) /
      momentInner s (monicOrtho s 0) (monicOrtho s 0) :=
    div_pos (monicOrtho_inner_self_pos h n) (monicOrtho_inner_self_pos h 0)
  linarith

theorem nevAlphaInf_succ_ne_zero_of_eq_zero (h : PositiveMomentForm s) (n : ℕ)
    (hz : nevAlphaInf s n = 0) : nevAlphaInf s (n + 1) ≠ 0 := by
  intro hz2
  refine nevAlphaInf_beta_ne_zero h n ⟨hz, ?_⟩
  rw [nevBetaInf_eq_neg_nevAlphaInf_succ, hz2, neg_zero]

/-- **The good levels for `B` are cofinal.** -/
theorem exists_ge_nevAlphaInf_ne_zero (h : PositiveMomentForm s) (N : ℕ) :
    ∃ n, N ≤ n ∧ nevAlphaInf s n ≠ 0 := by
  by_cases hN : nevAlphaInf s N = 0
  · exact ⟨N + 1, by omega, nevAlphaInf_succ_ne_zero_of_eq_zero h N hN⟩
  · exact ⟨N, le_rfl, hN⟩

/-- **`B` at level `n` is a multiple of a quasi-orthogonal polynomial.** -/
theorem nevBreal_eq_quasiOrtho (h : PositiveMomentForm s) (n : ℕ)
    (hα : nevAlphaInf s n ≠ 0) (x : ℝ) :
    nevBreal s n x
      = momentInner s (monicOrtho s 0) (monicOrtho s 0) /
          momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlphaInf s n *
        (quasiOrtho s n (nevBetaInf s n / nevAlphaInf s n)).eval x := by
  rw [nevBreal_closed h n x, quasiOrtho_eval, nevAlphaInf, nevBetaInf]
  rw [nevAlphaInf] at hα
  set A := (monicOrtho s (n + 1)).eval x with hA
  set Bv := (monicOrtho s n).eval x with hBv
  set R0 := (secondKind s n).eval 0 with hR0
  set R1 := (secondKind s (n + 1)).eval 0 with hR1
  field_simp
  try ring

/-- **The zeros of `Bₙ` are exactly the quasi-orthogonal nodes.** -/
theorem nevBreal_zero_iff (h : PositiveMomentForm s) (n : ℕ) (hα : nevAlphaInf s n ≠ 0) (x : ℝ) :
    nevBreal s n x = 0 ↔ x ∈ quasiNodes s n (nevBetaInf s n / nevAlphaInf s n) := by
  have hc : momentInner s (monicOrtho s 0) (monicOrtho s 0) /
      momentInner s (monicOrtho s n) (monicOrtho s n) * nevAlphaInf s n ≠ 0 :=
    mul_ne_zero (div_ne_zero (monicOrtho_inner_self_pos h 0).ne'
      (monicOrtho_inner_self_pos h n).ne') hα
  rw [nevBreal_eq_quasiOrtho h n hα x, mem_quasiNodes_iff, mul_eq_zero]
  constructor
  · rintro (hcz | hz)
    · exact absurd hcz hc
    · exact hz
  · exact Or.inr

end HTGeometry
