import GaloisForLFunctions.RHTower.VerifiedHeightAmplification

/-!
# Verified-height amplification from a horizontal-fibre census

`rhVerifiedThrough_amplify_of_increment_ncard_le_one` requires the *whole* height increment to
contain at most one distinct zero.  That is much more than the reflection argument needs: critical
line reflection preserves the ordinate, so the pairing that rules out an off-line zero happens
inside a single horizontal fibre.

The census below is therefore strictly weaker as a hypothesis — arbitrarily many new zeros are
allowed in `(H, U]`, provided no two of them share an ordinate — and the conclusion is the same.
This is the same predicate that
`docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/horizontal-singleton-zero-fibers.md`
studies globally, here used as a verified-height amplifier.
-/

namespace RHTower

open Complex

/-- Zeros of the height increment `(H, U]` lying at one fixed ordinate. -/
def stripZeroIncrementFiber (H U t : ℝ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ stripZeroIncrement H U ∧ ρ.im = t}

theorem stripZeroIncrementFiber_finite (H U t : ℝ) :
    (stripZeroIncrementFiber H U t).Finite :=
  (stripZeroIncrement_finite H U).subset (fun _ hρ => hρ.1)

theorem lineReflect_mem_stripZeroIncrementFiber {H U t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ stripZeroIncrementFiber H U t) :
    lineReflect ρ ∈ stripZeroIncrementFiber H U t := by
  refine ⟨lineReflect_mem_stripZeroIncrement hρ.1, ?_⟩
  have him : (lineReflect ρ).im = ρ.im := by simp [lineReflect]
  rw [him]
  exact hρ.2

/-- **A horizontal-singleton census amplifies a verified RH height.**  If RH is verified through
`H` and no ordinate in `(H, U]` carries two distinct strip zeros, then RH is verified through `U`.
Reflection acts inside each fibre, so a lone member of a fibre must be its own reflection. -/
theorem rhVerifiedThrough_amplify_of_fiber_ncard_le_one {H U : ℝ}
    (hH : RHVerifiedThrough H)
    (hcount : ∀ t : ℝ, (stripZeroIncrementFiber H U t).ncard ≤ 1) :
    RHVerifiedThrough U := by
  intro ρ hzero hre0 hre1 him0 himU
  by_cases himH : ρ.im ≤ H
  · exact hH hzero hre0 hre1 him0 himH
  · have hρinc : ρ ∈ stripZeroIncrement H U :=
      ⟨hre0, hre1, him0, lt_of_not_ge himH, himU, hzero⟩
    have hρ : ρ ∈ stripZeroIncrementFiber H U ρ.im := ⟨hρinc, rfl⟩
    have hreflect : lineReflect ρ ∈ stripZeroIncrementFiber H U ρ.im :=
      lineReflect_mem_stripZeroIncrementFiber hρ
    have heq : ρ = lineReflect ρ :=
      (Set.ncard_le_one_iff (stripZeroIncrementFiber_finite H U ρ.im)).mp
        (hcount ρ.im) hρ hreflect
    have hre : ρ.re = (lineReflect ρ).re := congrArg Complex.re heq
    rw [lineReflect_re] at hre
    linarith

/-- The fibre census is implied by the whole-increment census, so the fibre amplifier subsumes
`rhVerifiedThrough_amplify_of_increment_ncard_le_one`. -/
theorem stripZeroIncrementFiber_ncard_le_one_of_increment {H U : ℝ}
    (hcount : (stripZeroIncrement H U).ncard ≤ 1) (t : ℝ) :
    (stripZeroIncrementFiber H U t).ncard ≤ 1 := by
  refine (Set.ncard_le_one_iff (stripZeroIncrementFiber_finite H U t)).mpr ?_
  intro a b ha hb
  exact (Set.ncard_le_one_iff (stripZeroIncrement_finite H U)).mp hcount ha.1 hb.1

end RHTower
