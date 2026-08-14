import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import GaloisForLFunctions.PNTPlus.PerronFormula

/-!
# Shifting a vertical contour past one simple pole

The truncated shift already available records the limit of the left truncation.  When the left
line is itself Bochner integrable the truncation converges to the full vertical integral, and the
two limits identify:

```text
(1/2πi)∫_{(σ')} f - (1/2πi)∫_{(σ)} f = A ,
```

where `A` is the residue of the single simple pole between the two lines.  This is the form a
Mellin inversion argument consumes: each crossed pole contributes exactly its residue to the
asymptotic expansion, and the remaining integral is the next error term.
-/

open Complex Filter Set MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

/-- A symmetric truncation of a vertical line converges to the full vertical integral. -/
theorem tendsto_vIntegral_verticalIntegral {σ : ℝ} {f : ℂ → ℂ}
    (hf : Integrable fun y : ℝ => f ((σ : ℂ) + (y : ℂ) * Complex.I)) :
    Filter.Tendsto (fun T : ℝ => VIntegral f σ (-T) T) atTop (nhds (VerticalIntegral f σ)) := by
  have h := intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id
  simpa [VIntegral, VerticalIntegral] using h.const_smul Complex.I

/-- **Vertical contour shift past one simple pole.**  The difference of the two normalized vertical
integrals is the residue. -/
theorem verticalIntegral'_sub_of_simple_pole {σ σ' : ℝ} {f : ℂ → ℂ} {p A : ℂ}
    (hσ : σ < p.re) (hσ' : p.re < σ')
    (hf : HolomorphicOn f (Set.Icc σ σ' ×ℂ Set.univ \ {p}))
    (hpole : (f - fun s => A / (s - p)) =O[nhdsWithin p {p}ᶜ] (1 : ℂ → ℂ))
    (hbot : Filter.Tendsto (fun y : ℝ => ∫ x in σ..σ', f ((x : ℂ) + (y : ℂ) * Complex.I))
      atBot (nhds 0))
    (htop : Filter.Tendsto (fun y : ℝ => ∫ x in σ..σ', f ((x : ℂ) + (y : ℂ) * Complex.I))
      atTop (nhds 0))
    (hleft : Integrable fun y : ℝ => f ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hright : Integrable fun y : ℝ => f ((σ' : ℂ) + (y : ℂ) * Complex.I)) :
    VerticalIntegral' f σ' - VerticalIntegral' f σ = A := by
  have h1 := tendsto_truncated_vertical_shift_with_simple_pole ⟨hσ, hσ'⟩ hf hpole hbot htop hright
  have h2 : Filter.Tendsto
      (fun T : ℝ => (1 / (2 * (Real.pi : ℂ) * Complex.I)) • VIntegral f σ (-T) T)
      atTop (nhds (VerticalIntegral' f σ)) :=
    (tendsto_vIntegral_verticalIntegral hleft).const_smul _
  have hEq := tendsto_nhds_unique h2 h1
  rw [hEq]
  ring

end GaloisForLFunctions.HTGeometry
