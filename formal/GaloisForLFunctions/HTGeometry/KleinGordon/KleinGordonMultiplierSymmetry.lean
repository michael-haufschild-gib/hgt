import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonSymmetry
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonLowPass

/-!
# Frequency-diagonal backgrounds preserve every band

Two Fourier multipliers commute, because their symbols do. The free building blocks of the flow —
`cos t⟨D⟩`, `sin t⟨D⟩`, `⟨D⟩⁻¹` — are Fourier multipliers, so *every* Fourier multiplier commutes with
them; and if the potential is a Fourier multiplier at each time, it commutes with them too. The
symmetry law therefore applies to the whole family at once: for a frequency-diagonal background, every
Fourier multiplier is a symmetry of the flow.

Two consequences. The monodromy of such a background commutes with every Fourier multiplier. And the
low-pass projections are Fourier multipliers, so a band-limited Cauchy datum stays band-limited for all
time: a background that is diagonal in frequency cannot move energy between frequency bands.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Two Fourier multipliers commute**, because their symbols do. -/
theorem fourierMulCLM_comm {φ ψ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (f : Lp (α := E) ℂ 2) :
    fourierMulCLM hφ hC0 hC (fourierMulCLM hψ hD0 hD f)
      = fourierMulCLM hψ hD0 hD (fourierMulCLM hφ hC0 hC f) := by
  have hχ : Measurable fun ξ : E => φ ξ * ψ ξ := hφ.mul hψ
  have hB0 : (0 : ℝ) ≤ C * D := mul_nonneg hC0 hD0
  have hB : ∀ ξ : E, ‖φ ξ * ψ ξ‖ ≤ C * D := by
    intro ξ
    calc ‖φ ξ * ψ ξ‖ = ‖φ ξ‖ * ‖ψ ξ‖ := norm_mul _ _
      _ ≤ C * D := mul_le_mul (hC ξ) (hD ξ) (norm_nonneg _) hC0
  have h1 : (fourierMulCLM hφ hC0 hC).comp (fourierMulCLM hψ hD0 hD) = fourierMulCLM hχ hB0 hB :=
    fourierMulCLM_comp hφ hψ hχ hC0 hC hD0 hD hB0 hB (Eventually.of_forall fun _ => rfl)
  have h2 : (fourierMulCLM hψ hD0 hD).comp (fourierMulCLM hφ hC0 hC) = fourierMulCLM hχ hB0 hB :=
    fourierMulCLM_comp hψ hφ hχ hD0 hD hC0 hC hB0 hB
      (Eventually.of_forall fun ξ => mul_comm (φ ξ) (ψ ξ))
  exact ContinuousLinearMap.ext_iff.mp (h1.trans h2.symm) f

section MultiplierSymmetry

variable {m : E → ℂ} {A b : ℝ} {w : ℝ → E → ℂ}

/-- A Fourier multiplier commutes with the cosine propagator. -/
theorem fourierMulCLM_kgCosOp_comm (hm : Measurable m) (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖m ξ‖ ≤ A)
    (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hm hA0 hA (kgCosOp t x) = kgCosOp t (fourierMulCLM hm hA0 hA x) :=
  fourierMulCLM_comm hm (measurable_kgCosSymbol (E := E) t) hA0 hA zero_le_one
    (norm_kgCosSymbol_le t) x

/-- A Fourier multiplier commutes with the sine propagator. -/
theorem fourierMulCLM_kgSinOp_comm (hm : Measurable m) (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖m ξ‖ ≤ A)
    (t : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hm hA0 hA (kgSinOp t x) = kgSinOp t (fourierMulCLM hm hA0 hA x) :=
  fourierMulCLM_comm hm (measurable_kgSinPhase (E := E) t) hA0 hA zero_le_one
    (norm_kgSinPhase_le t) x

/-- A Fourier multiplier commutes with the inverse frequency. -/
theorem fourierMulCLM_kgFreqInvOp_comm (hm : Measurable m) (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖m ξ‖ ≤ A)
    (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hm hA0 hA (kgFreqInvOp x) = kgFreqInvOp (fourierMulCLM hm hA0 hA x) :=
  fourierMulCLM_comm hm (measurable_kgFreqInv (E := E)) hA0 hA zero_le_one norm_kgFreqInv_le x

/-- **For a frequency-diagonal background, every Fourier multiplier is a symmetry of the flow.** -/
theorem kgFieldStateT_fourierMul_symmetry (hm : Measurable m) (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖m ξ‖ ≤ A)
    (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b) (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
        (fourierMulCLM hm hA0 hA g) (fourierMulCLM hm hA0 hA h) t
      = kgDiagOp (fourierMulCLM hm hA0 hA)
          (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t) :=
  kgFieldStateT_diag hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (fourierMulCLM_kgCosOp_comm hm hA0 hA) (fourierMulCLM_kgSinOp_comm hm hA0 hA)
    (fourierMulCLM_kgFreqInvOp_comm hm hA0 hA)
    (fun r x => fourierMulCLM_comm hm (hw r) hA0 hA hb0 (hwb r) x) g h t

/-- **The monodromy of a frequency-diagonal background commutes with every Fourier multiplier.** -/
theorem kgMonodromy_fourierMul_comm (hm : Measurable m) (hA0 : 0 ≤ A) (hA : ∀ ξ, ‖m ξ‖ ≤ A)
    (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b) (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    (T : ℝ) (v : KGEnergy E) :
    kgMonodromy (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) b hb0
        (fun _ => norm_fourierMulCLM_le _ _ _) hWs T (kgDiagOp (fourierMulCLM hm hA0 hA) v)
      = kgDiagOp (fourierMulCLM hm hA0 hA)
          (kgMonodromy (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) b hb0
            (fun _ => norm_fourierMulCLM_le _ _ _) hWs T v) :=
  kgMonodromy_kgDiagOp_comm hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (fourierMulCLM_kgCosOp_comm hm hA0 hA) (fourierMulCLM_kgSinOp_comm hm hA0 hA)
    (fourierMulCLM_kgFreqInvOp_comm hm hA0 hA)
    (fun r x => fourierMulCLM_comm hm (hw r) hA0 hA hb0 (hwb r) x) v

/-- **A frequency-diagonal background cannot move energy between frequency bands**: a band-limited
Cauchy datum stays band-limited for all time. -/
theorem kgFieldStateT_band_invariant (hw : ∀ r : ℝ, Measurable (w r)) (hb0 : 0 ≤ b)
    (hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) x)
    {R : ℝ} {g h : Lp ℂ 2 (volume : Measure E)} (hg : kgLowPassOp R g = g)
    (hh : kgLowPassOp R h = h) (t : ℝ) :
    kgDiagOp (kgLowPassOp R)
        (kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t)
      = kgFieldStateT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r)) g h t :=
  kgFieldStateT_fixed hb0 (fun _ => norm_fourierMulCLM_le _ _ _) hWs
    (fourierMulCLM_kgCosOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fourierMulCLM_kgSinOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fourierMulCLM_kgFreqInvOp_comm (measurable_kgLowPass (E := E) R) zero_le_one
      (norm_kgLowPass_le R))
    (fun r x => fourierMulCLM_comm (measurable_kgLowPass (E := E) R) (hw r) zero_le_one
      (norm_kgLowPass_le R) hb0 (hwb r) x)
    hg hh t

end MultiplierSymmetry

end GaloisForLFunctions.HTGeometry
