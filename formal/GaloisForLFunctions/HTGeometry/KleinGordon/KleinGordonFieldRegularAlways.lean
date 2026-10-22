import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldEvolutionFamily

/-!
# The field solution is regular at every time

The Cauchy data of the field theory are asked to have one power of `⟨D⟩⁻¹` on the position. That
hypothesis propagates: the solution *stays* in the range of `⟨D⟩⁻¹` for all time, and the regularising
curve is explicit.

The reason is that both terms of the Duhamel formula carry the factor. The free part is
`cos(t⟨D⟩)⟨D⟩⁻¹g + (sin(t⟨D⟩)/⟨D⟩)h = ⟨D⟩⁻¹(cos(t⟨D⟩)g + sin(t⟨D⟩)h)`, and the Duhamel integrand is
`(sin((t-s)⟨D⟩)/⟨D⟩)Wu(s) = ⟨D⟩⁻¹(sin((t-s)⟨D⟩)Wu(s))`, whose `⟨D⟩⁻¹` passes through the Bochner
integral because it is bounded.

So the velocity is defined at every time, and the evolution family of statement 123 can be restarted
anywhere without leaving the class where the derivative exists.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Regular

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- The regularising curve of the field solution: applying `⟨D⟩⁻¹` to it returns the solution. -/
def kgFieldReg (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) : Lp ℂ 2 (volume : Measure E) :=
  kgCosOp t g + kgSinOp t h
    + ∫ r in (0 : ℝ)..t, kgSinOp (t - r) (W (kgFieldMild W (kgFreqInvOp g) h r))

/-- The free part carries the regularising factor. -/
theorem kgFieldFree_freqInv (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree (kgFreqInvOp g) h t = kgFreqInvOp (kgCosOp t g + kgSinOp t h) := by
  rw [kgFieldFree, kgSinFreqOp_apply_freqInv, map_add, kgFreqInvOp_kgCosOp]

/-- **The field solution is regular at every time**, with the regularising curve explicit. -/
theorem kgFieldMild_freqInv (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W (kgFreqInvOp g) h t = kgFreqInvOp (kgFieldReg W g h t) := by
  have hcu : Continuous (kgFieldMild W (kgFreqInvOp g) h) :=
    continuous_kgFieldMild hb0 hW _ h
  have hk : Continuous fun r : ℝ => W (kgFieldMild W (kgFreqInvOp g) h r) :=
    W.continuous.comp hcu
  have hsin : Continuous fun r : ℝ =>
      kgSinOp (t - r) (W (kgFieldMild W (kgFreqInvOp g) h r)) :=
    continuous_of_strong_comp norm_kgSinOp_le continuous_kgSinOp_apply
      (continuous_const.sub continuous_id) hk
  have hI := hsin.intervalIntegrable (μ := volume) 0 t
  have hpoint : ∀ r ∈ Set.uIcc (0 : ℝ) t,
      kgFieldKernel W t r (kgFieldMild W (kgFreqInvOp g) h r)
        = kgFreqInvOp (kgSinOp (t - r) (W (kgFieldMild W (kgFreqInvOp g) h r))) := by
    intro r _
    rw [kgFieldKernel_apply, kgSinFreqOp_apply_freqInv]
  rw [kgFieldMild_eq hb0 hW (kgFreqInvOp g) h t, intervalIntegral.integral_congr hpoint,
    ContinuousLinearMap.intervalIntegral_comp_comm _ hI, kgFieldFree_freqInv, ← map_add,
    kgFieldReg]

/-- **The velocity of the solution restarted at any time is defined**, because the state is regular.
This is what lets the evolution family of statement 123 be iterated. -/
theorem hasDerivAt_kgFieldMild_restart (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (s t : ℝ) :
    HasDerivAt
      (kgFieldMild W (kgFieldMild W (kgFreqInvOp g) h s)
        (deriv (kgFieldMild W (kgFreqInvOp g) h) s))
      (-(kgSinOp t (kgFieldReg W g h s))
        + kgCosOp t (deriv (kgFieldMild W (kgFreqInvOp g) h) s)
        + ∫ r in (0 : ℝ)..t, kgCosOp (t - r)
            (W (kgFieldMild W (kgFreqInvOp (kgFieldReg W g h s))
              (deriv (kgFieldMild W (kgFreqInvOp g) h) s) r))) t := by
  have hreg := kgFieldMild_freqInv hb0 hW g h s
  rw [hreg]
  exact hasDerivAt_kgFieldMild hb0 hW (kgFieldReg W g h s)
    (deriv (kgFieldMild W (kgFreqInvOp g) h) s) t

end Regular

end GaloisForLFunctions.HTGeometry
