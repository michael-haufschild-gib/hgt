import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowNoncensorship

/-!
# Entireness of the rectangular window amplitude

The rectangular window amplitude `w ↦ (1 - e^{-Lw})/w` (with removable value `L` at `w = 0`) is
entire: it is holomorphic off the origin as a quotient, and the origin is a removable singularity
because `1 - e^{-Lw} = Lw + O(w²)` gives the finite limit `L`.  The sharp-window Mellin factor
`s ↦ rectangularWindowAmplitude L (s - 1)` inherits entireness by composition.  These unblock the
parameter-holomorphy of the sharp prime-window error series and its meromorphic continuation.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The rectangular window amplitude is entire: holomorphic away from the origin as a quotient, with
a removable singularity at `w = 0` where its value is the width `L`. -/
theorem rectangularWindowAmplitude_differentiable (L : ℝ) :
    Differentiable ℂ (rectangularWindowAmplitude L) := by
  have hoff : DifferentiableOn ℂ (rectangularWindowAmplitude L) ({(0 : ℂ)}ᶜ) := by
    apply DifferentiableOn.congr (f := fun w => (1 - Complex.exp (-(L : ℂ) * w)) / w)
    · fun_prop (disch := intro x hx; simpa using hx)
    · intro w hw
      exact rectangularWindowAmplitude_eq_div (by simpa using hw)
  have hg : HasDerivAt (fun w : ℂ => 1 - Complex.exp (-(L : ℂ) * w)) (L : ℂ) 0 := by
    have hlin : HasDerivAt (fun w : ℂ => -(L : ℂ) * w) (-(L : ℂ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (-(L : ℂ)))
    have hexp := hlin.cexp
    have : HasDerivAt (fun w : ℂ => 1 - Complex.exp (-(L : ℂ) * w))
        (0 - Complex.exp (-(L : ℂ) * 0) * -(L : ℂ)) 0 :=
      (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub hexp
    simpa using this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hg
  have hEq : (rectangularWindowAmplitude L) =ᶠ[𝓝[≠] (0 : ℂ)]
      (slope (fun w : ℂ => 1 - Complex.exp (-(L : ℂ) * w)) 0) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw0 : w ≠ 0 := by simpa using hw
    rw [rectangularWindowAmplitude_eq_div hw0, slope_def_field]
    simp
  have htend : Tendsto (rectangularWindowAmplitude L) (𝓝[≠] (0 : ℂ)) (𝓝 (L : ℂ)) :=
    hslope.congr' hEq.symm
  have hcontAt : ContinuousAt (rectangularWindowAmplitude L) 0 := by
    have hval : rectangularWindowAmplitude L 0 = (L : ℂ) := by simp [rectangularWindowAmplitude]
    have hdecomp : (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure (0 : ℂ) := by
      rw [← nhdsWithin_singleton (0 : ℂ), ← nhdsWithin_union, Set.compl_union_self, nhdsWithin_univ]
    rw [ContinuousAt, hval, hdecomp, tendsto_sup]
    exact ⟨htend, by simpa [hval] using tendsto_pure_nhds (rectangularWindowAmplitude L) 0⟩
  have hmem : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) := Filter.univ_mem
  have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hmem).mp
    ⟨by simpa [Set.compl_eq_univ_sdiff] using hoff, hcontAt⟩
  simpa [differentiableOn_univ] using this

/-- The sharp-window Mellin factor `s ↦ rectangularWindowAmplitude L (s - 1)` is entire. -/
theorem sharpPrimeWindowMellin_differentiable (L : ℝ) :
    Differentiable ℂ (sharpPrimeWindowMellin L) := by
  have h := (rectangularWindowAmplitude_differentiable L).comp
    (differentiable_id.sub_const (1 : ℂ))
  simpa [sharpPrimeWindowMellin, Function.comp_def] using! h

end RHTower
