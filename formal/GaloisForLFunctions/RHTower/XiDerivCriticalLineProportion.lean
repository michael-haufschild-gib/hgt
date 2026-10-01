import GaloisForLFunctions.RHTower.XiDerivOffLineCount
import GaloisForLFunctions.RHTower.LamzouriMontgomeryTaylorXiDensity

/-!
# Two thirds of the zeros of `ξ'` lie on the critical line

**Theorem** (`eventually_deriv_xi_criticalLine_count_ge`). For every `ε > 0` and all large `T`
there are at least `(HD 1 − ε)·N(T) − 1` distinct ordinates `0 < c ≤ T` with `ξ'(1/2 + ic) = 0`.
Here `N(T)` is the number of zeros of `ξ` with ordinate in `(0, T]` (with multiplicity) and
`HD 1 = 0.6725…` is the Montgomery–Taylor constant.

**Proof.**
- On the critical line `t ↦ ξ(1/2 + it)` is real. Between two consecutive distinct critical zeros
  of `ξ`, Rolle gives a zero of `ξ'` on the line (`exists_deriv_xi_criticalLine_eq_zero`).
- So the critical zeros of `ξ'` up to height `T` are at least the distinct critical zeros of `ξ`
  minus one (`exists_finset_between_card`).
- The distinct critical zeros contain the simple ones, of which there are at least
  `(HD 1 − ε)N(T)` (`lamzouri_montgomeryTaylor_simpleCritical_epsilon`).
-/

open Complex Set Filter

namespace RHTower

noncomputable section

/-- A critical point of the strip is `1/2 + i·Im z`. -/
theorem eq_half_add_I_mul_im {z : ℂ} (hz : z.re = 1 / 2) : z = (1 / 2 : ℂ) + I * (z.im : ℂ) := by
  apply Complex.ext <;> simp [hz]

/-- **Critical zeros of `ξ'` from Rolle.** The distinct critical zeros of `ξ` with ordinate in
`(0, T]`, minus one, inject into the critical zeros of `ξ'`. -/
theorem exists_deriv_xi_criticalLine_finset (T : ℝ) :
    ∃ C : Finset ℝ, (∀ c ∈ C, 0 < c ∧ c ≤ T ∧ deriv xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0) ∧
      xiSimpleCriticalZeroCount T ≤ C.card + 1 := by
  classical
  set Z := (stripFinsetPos T).filter (fun z => z.re = 1 / 2) with hZ
  set S : Finset ℝ := Z.image Complex.im with hS
  have hmemZ : ∀ z ∈ Z, 0 < z.im ∧ z.im ≤ T ∧ xi ((1 / 2 : ℂ) + I * (z.im : ℂ)) = 0 := by
    intro z hz
    obtain ⟨hzS, hre⟩ := Finset.mem_filter.mp hz
    obtain ⟨-, -, h0, hT, hxi⟩ := mem_stripFinsetPos.mp hzS
    exact ⟨h0, hT, by rw [← eq_half_add_I_mul_im hre]; exact hxi⟩
  have hmemS : ∀ a ∈ S, 0 < a ∧ a ≤ T ∧ xi ((1 / 2 : ℂ) + I * (a : ℂ)) = 0 := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact hmemZ z hz
  obtain ⟨C, hC, hcard⟩ := exists_finset_between_card (S := S)
    (P := fun c => deriv xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0)
    (fun a ha b hb hab _ => by
      obtain ⟨c, hc, hc0⟩ := exists_deriv_xi_criticalLine_eq_zero hab (hmemS a ha).2.2
        (hmemS b hb).2.2
      exact ⟨c, hc.1, hc.2, hc0⟩)
  refine ⟨C, fun c hc => ?_, ?_⟩
  · obtain ⟨hP, a, ha, b, hb, hac, hcb⟩ := hC c hc
    exact ⟨lt_trans (hmemS a ha).1 hac, le_trans hcb.le (hmemS b hb).2.1, hP⟩
  · -- `#simple ≤ #critical = #S`
    have hinj : Set.InjOn Complex.im (Z : Set ℂ) := by
      intro z hz w hw him
      have hz' := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
      have hw' := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
      rw [eq_half_add_I_mul_im hz', eq_half_add_I_mul_im hw', him]
    have hSZ : S.card = Z.card := Finset.card_image_of_injOn hinj
    have hsub : (stripFinsetPos T).filter
        (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1) ⊆ Z := by
      intro z hz
      obtain ⟨hzS, hre, -⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzS, hre⟩
    have h1 : xiSimpleCriticalZeroCount T ≤ Z.card := Finset.card_le_card hsub
    omega

/-- **Two thirds of the zeros of `ξ'` lie on the critical line.** -/
theorem eventually_deriv_xi_criticalLine_count_ge :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∃ C : Finset ℝ,
      (∀ c ∈ C, 0 < c ∧ c ≤ T ∧ deriv xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0) ∧
      (Zeta23.ThmD.HD 1 - ε) * (xiPosZeroCount T : ℝ) - 1 ≤ C.card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := lamzouri_montgomeryTaylor_simpleCritical_epsilon ε hε
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨C, hC, hcard⟩ := exists_deriv_xi_criticalLine_finset T
  refine ⟨C, hC, ?_⟩
  have h1 := hT₀ T hT
  have h2 : (xiSimpleCriticalZeroCount T : ℝ) ≤ C.card + 1 := by exact_mod_cast hcard
  linarith

end

end RHTower
