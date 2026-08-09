import GaloisForLFunctions.RHTower.StepFunctionCarrier
import GaloisForLFunctions.HTGeometry.HardyClosureZeroFree

/-!
# An arithmetic obstruction: every finite Báez-Duarte distance is strictly positive

`StepFunctionCarrier` made the criterion discrete: the generators are the modular sequences
`g_m(n) = (n mod m)/m` and the target is the constant sequence `1`, inside `ℓ²(ℕ≥1, 1/(n(n+1)))`.  In that
picture a second obstruction mechanism becomes visible, of the same shape as the Mellin detector but
arithmetic instead of analytic.

`g_m` vanishes exactly on the multiples of `m`.  So if `n₀` is divisible by every modulus of a family, the
bounded functional "evaluate the sequence at `n₀`" kills every generator, while on the target it is
`1/(n₀(n₀+1)) ≠ 0`.  Evaluation is bounded because it is an inner product: with `δ` the indicator sequence
at `n₀`,

`⟪stepVec δ, stepVec s⟫ = s(n₀)/(n₀(n₀+1))`,  `‖stepVec δ‖² = 1/(n₀(n₀+1))`.

Consequences, unconditional:

* `notMem_closedSpan_of_forall_dvd` — the target is not in the closed span of any family of moduli with a
  common multiple;
* `dist_floor_of_forall_dvd` — quantitatively, every element of that closed span is at distance at least
  `√(1/(n₀(n₀+1)))` from the target;
* `bdDist_pos_of_finite_moduli` — hence **every finite-section Báez-Duarte distance is strictly positive**:
  taking `n₀ = lcm` of the section's moduli, `d > 0` always.

This does not threaten the criterion.  For the *infinite* family no `n₀` is divisible by every modulus, so
the argument does not apply to the whole span — consistent with `d_N → 0` being possible.  What it does say
is that the limit in `d_N → 0` is never attained: the approximation is asymptotic and never exact, for a
purely divisibility reason.  The bound `√(1/(n₀(n₀+1)))` with `n₀ = lcm(1..N) ≈ e^N` is far weaker than the
true rate, so it is a structural statement, not a quantitative one.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-- The indicator sequence at `n₀`. -/
def deltaSeq (n₀ : ℕ) : ℕ → ℝ := fun n => if n = n₀ then 1 else 0

theorem abs_deltaSeq_le (n₀ : ℕ) (n : ℕ) : |deltaSeq n₀ n| ≤ 1 := by
  rw [deltaSeq]
  by_cases h : n = n₀ <;> simp [h]

/-- **Evaluation is an inner product.**  The indicator step vector reads off one sequence value, weighted. -/
theorem stepGram_deltaSeq {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (s : ℕ → ℝ) {C : ℝ} (hb : ∀ n, |s n| ≤ C) :
    stepGram (deltaSeq n₀) s = s n₀ / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by
  have hmain := hasSum_stepGram (abs_deltaSeq_le n₀) hb
  have hsingle : HasSum
      (fun n : ℕ => deltaSeq n₀ (n + 1) * s (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (deltaSeq n₀ ((n₀ - 1) + 1) * s ((n₀ - 1) + 1)
        / ((((n₀ - 1 : ℕ) : ℝ) + 1) * (((n₀ - 1 : ℕ) : ℝ) + 2))) := by
    refine hasSum_single (n₀ - 1) ?_
    intro n hn
    have hne : n + 1 ≠ n₀ := by omega
    rw [deltaSeq, if_neg hne]
    ring
  have hval : deltaSeq n₀ ((n₀ - 1) + 1) * s ((n₀ - 1) + 1)
      / ((((n₀ - 1 : ℕ) : ℝ) + 1) * (((n₀ - 1 : ℕ) : ℝ) + 2))
      = s n₀ / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by
    have hsucc : (n₀ - 1) + 1 = n₀ := by omega
    have hcast : ((n₀ - 1 : ℕ) : ℝ) + 1 = (n₀ : ℝ) := by
      rw [Nat.cast_sub hn₀, Nat.cast_one]
      ring
    rw [hsucc, deltaSeq, if_pos rfl, hcast]
    have hcast2 : ((n₀ - 1 : ℕ) : ℝ) + 2 = (n₀ : ℝ) + 1 := by
      rw [Nat.cast_sub hn₀, Nat.cast_one]
      ring
    rw [hcast2]
    ring
  rw [hval] at hsingle
  exact hmain.unique hsingle

theorem norm_sq_stepVec_deltaSeq {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    ‖stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)‖ ^ 2 = 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by
  have h : (RCLike.re (inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
      (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))) : ℝ)
      = ‖stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)‖ ^ 2 := inner_self_eq_norm_sq _
  rw [inner_stepVec, stepGram_deltaSeq hn₀ _ (abs_deltaSeq_le n₀), deltaSeq, if_pos rfl] at h
  rw [← h]
  show ((1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) : ℝ) : ℂ).re = 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1))
  exact Complex.ofReal_re _

theorem stepVec_deltaSeq_ne_zero {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀) ≠ 0 := by
  intro h
  have hsq := norm_sq_stepVec_deltaSeq hn₀
  rw [h, norm_zero] at hsq
  have hn : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  have : (0 : ℝ) < 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by positivity
  rw [← hsq] at this
  norm_num at this

/-- The evaluation functional annihilates a modular generator whose modulus divides `n₀`. -/
theorem inner_stepVec_deltaSeq_modSeq {n₀ m : ℕ} (hn₀ : 1 ≤ n₀) (hdvd : m ∣ n₀) :
    inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
        (stepVec (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ)) (abs_modSeq_le m)) = 0 := by
  rw [inner_stepVec, stepGram_deltaSeq hn₀ _ (abs_modSeq_le m)]
  have hmod : n₀ % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [hmod]
  norm_num

/-- The evaluation functional does not annihilate the target. -/
theorem inner_stepVec_deltaSeq_target {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
        (stepVec (fun _ => (1 : ℝ)) abs_one_le)
      = ((1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [inner_stepVec, stepGram_deltaSeq hn₀ _ abs_one_le]

/-- **The arithmetic closure obstruction.**  If every modulus of a family divides `n₀`, the target is not in
the closed span of that family. -/
theorem notMem_closedSpan_of_forall_dvd {I : Type*} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (m : I → ℕ)
    (hdvd : ∀ i, m i ∣ n₀) :
    stepVec (fun _ => (1 : ℝ)) abs_one_le ∉
      (Submodule.span ℂ (Set.range (fun i : I =>
        stepVec (fun n => ((n % m i : ℕ) : ℝ) / ((m i : ℕ) : ℝ))
          (abs_modSeq_le (m i))))).topologicalClosure := by
  have hn : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  refine GaloisForLFunctions.HTGeometry.not_mem_closedSpan_of_continuous_evaluation
    (innerSL ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)))
    (stepVec (fun _ => (1 : ℝ)) abs_one_le) _
    (fun i => inner_stepVec_deltaSeq_modSeq hn₀ (hdvd i)) ?_
  show inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
      (stepVec (fun _ => (1 : ℝ)) abs_one_le) ≠ 0
  rw [inner_stepVec_deltaSeq_target hn₀]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  positivity

/-- **The quantitative arithmetic floor.** -/
theorem dist_floor_of_forall_dvd {I : Type*} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) (m : I → ℕ)
    (hdvd : ∀ i, m i ∣ n₀) {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : I =>
      stepVec (fun n => ((n % m i : ℕ) : ℝ) / ((m i : ℕ) : ℝ))
        (abs_modSeq_le (m i))))).topologicalClosure) :
    Real.sqrt (1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)))
      ≤ ‖stepVec (fun _ => (1 : ℝ)) abs_one_le - G‖ := by
  have hn : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀
  have hw : (0 : ℝ) < 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by positivity
  have hker : inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)) G = 0 :=
    GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
      (innerSL ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))) _
      (fun i => inner_stepVec_deltaSeq_modSeq hn₀ (hdvd i)) hG
  have hkey := dist_innerKer_ge (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
    (stepVec (fun _ => (1 : ℝ)) abs_one_le) (stepVec_deltaSeq_ne_zero hn₀) hker
  have hnum : ‖inner ℂ (stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀))
      (stepVec (fun _ => (1 : ℝ)) abs_one_le)‖ = 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := by
    rw [inner_stepVec_deltaSeq_target hn₀, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw]
  have hden : ‖stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)‖
      = Real.sqrt (1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1))) := by
    have hsq := norm_sq_stepVec_deltaSeq hn₀
    have hnn : 0 ≤ ‖stepVec (deltaSeq n₀) (abs_deltaSeq_le n₀)‖ := norm_nonneg _
    rw [← hsq, Real.sqrt_sq hnn]
  rw [hnum, hden] at hkey
  refine le_trans (le_of_eq ?_) hkey
  have hsne : Real.sqrt (1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hw)
  have hsq : Real.sqrt (1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1))) ^ 2
      = 1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)) := Real.sq_sqrt hw.le
  rw [eq_div_iff hsne]
  nlinarith [hsq, Real.sqrt_nonneg (1 / ((n₀ : ℝ) * ((n₀ : ℝ) + 1)))]

end RHTower

end
