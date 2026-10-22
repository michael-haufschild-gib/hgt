import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetExactSequence
import GaloisForLFunctions.RHTower.Deninger.DeningerTomographyInjective
import GaloisForLFunctions.RHTower.Deninger.DeningerFinitePeriodizationKernel

/-!
# Cofinal Floquet tomography

The trivialization carries the twisted prime traces to the ordinary ones, so cofinal prime
periodization tomography transfers verbatim: an infinite prime family of twisted traces is
injective, while a finite family always has a nonzero common kernel, namely the image of the
twisted depletion operator.

* `deningerExpMulLM_injective` : the trivialization is injective.
* `deningerCofinalFloquetTomography` : **an infinite prime family of twisted traces is injective.**
* `deningerFiniteFloquetTomography_kernel_nontrivial` : **no finite family is.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

theorem deningerExpMulLM_injective (α : ℝ) : Function.Injective (deningerExpMulLM α) := by
  intro u v huv
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  have hval := congrArg (fun w : DeningerExpSchwartz =>
    ((w : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) huv
  rw [deningerExpMulLM_apply, deningerExpMulLM_apply] at hval
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)) hval

theorem deningerExpMulLM_neg_cancel (α : ℝ) (g : DeningerExpSchwartz) :
    deningerExpMulLM α (deningerExpMulLM (-α) g) = g := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerExpMulLM_apply, deningerExpMulLM_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  have hzero : α * t + -α * t = 0 := by ring
  rw [hzero, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- **Cofinal Floquet tomography.**  For any infinite prime family the twisted prime traces are
jointly injective on the source. -/
theorem deningerCofinalFloquetTomography {h : DeningerExpSchwartz} (α : ℝ) {Q : Set ℕ}
    (hQinf : Q.Infinite) (hQp : ∀ q ∈ Q, Nat.Prime q)
    (hper : ∀ q ∈ Q, ∀ t : ℝ,
      deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α (Real.log q) t = 0) :
    h = 0 := by
  have huntwisted : ∀ q ∈ Q, ∀ t : ℝ,
      deningerPeriodizationSum
        ((deningerExpMulLM α h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) (Real.log q) t = 0 := by
    intro q hq t
    rw [← deningerFloquetPeriodizationSum_trivialize, hper q hq t, mul_zero]
  have hzero : ((deningerExpMulLM α h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) = 0 :=
    deningerCofinalPrimeTomography (deningerExpMulLM α h).2 hQinf hQp huntwisted
  have hmapzero : deningerExpMulLM α h = 0 := Subtype.ext hzero
  have hzeromap : deningerExpMulLM α (0 : DeningerExpSchwartz) = 0 := map_zero _
  exact deningerExpMulLM_injective α (hmapzero.trans hzeromap.symm)

/-- **No finite prime family is injective.**  The twisted depletion of the source witness is a
nonzero element of every twisted trace kernel in the family. -/
theorem deningerFiniteFloquetTomography_kernel_nontrivial (α : ℝ) (S : List ℝ)
    (hS : ∀ L ∈ S, 0 < L) :
    ∃ h : DeningerExpSchwartz, h ≠ 0 ∧ ∀ L ∈ S, ∀ t : ℝ,
      deningerFloquetPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) α L t = 0 := by
  obtain ⟨g, hgne, hgzero⟩ := deningerFinitePeriodization_kernel_nontrivial S hS
  refine ⟨deningerExpMulLM (-α) g, ?_, ?_⟩
  · intro hzero
    refine hgne ?_
    have := congrArg (deningerExpMulLM α) hzero
    rw [deningerExpMulLM_neg_cancel, map_zero] at this
    exact this
  · intro L hL t
    have hkey := deningerFloquetPeriodizationSum_trivialize (deningerExpMulLM (-α) g) α L t
    rw [deningerExpMulLM_neg_cancel, hgzero L hL t] at hkey
    exact (mul_eq_zero.1 hkey).resolve_left (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _))

end

end RHTower
