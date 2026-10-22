import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonShiftedFreeCase

/-!
# The closed form without the band

The identification of the mild solution was for the potential compressed to a band. On a
frequency-diagonal background that compression is exact for band-limited data, so the compression can
be removed: the solution of the *true* diagonal background, started from band-limited data, is the
shifted propagator.

`u(t) = cos(tΩ)Px + (sin(tΩ)/Ω)Py`,   `Ω² = ⟨ξ⟩² − p`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section ClosedForm

variable {p : E → ℝ} {b : ℝ}

/-- **The field of a real diagonal potential, started from band-limited data, is the shifted
propagator** — with no band compression of the potential. -/
theorem kgFieldMildT_diagonal_eq_kgShiftedField (hp : Measurable p) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hpb : ∀ ξ : E, |p ξ| ≤ b) (R : ℝ) (x y : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT (fun _ : ℝ => fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
          (norm_kgRealPotSymbol_le hpb))
        (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t
      = kgShiftedField hp R x y t := by
  set w : ℝ → E → ℂ := fun _ => kgRealPotSymbol p with hwdef
  have hw : ∀ r : ℝ, Measurable (w r) := fun _ => measurable_kgRealPotSymbol hp
  have hwb : ∀ (r : ℝ) (ξ : E), ‖w r ξ‖ ≤ b := fun _ => norm_kgRealPotSymbol_le hpb
  have hWs : ∀ z : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) z := by
    intro z
    have hconst : (fun r : ℝ => (fourierMulCLM (hw r) hb0 (hwb r)) z)
        = fun _ : ℝ => (fourierMulCLM (measurable_kgRealPotSymbol hp) hb0
            (norm_kgRealPotSymbol_le hpb)) z := rfl
    rw [hconst]
    exact continuous_const
  have hgb : kgLowPassOp R (kgFreqLowOp R x) = kgFreqLowOp R x := kgLowPassOp_kgFreqLowOp R x
  have hhb : kgLowPassOp R (kgLowPassOp R y) = kgLowPassOp R y := kgLowPassOp_idem R y
  -- the band compression is exact on band-limited data
  have hstate := kgFieldStateT_kgBandOp_eq hw hb0 hwb hWs (R := R) hgb hhb t
  have hgrad := congrArg (fun z : KGEnergy E => z.fst) hstate
  simp only [kgFieldStateT, kgPair_fst] at hgrad
  -- transport to the field
  have hFullb : ∀ r : ℝ, ‖fourierMulCLM (E := E) (hw r) hb0 (hwb r)‖ ≤ b :=
    fun _ => norm_fourierMulCLM_le _ _ _
  have hBandb : ∀ r : ℝ, ‖kgBandOp (fourierMulCLM (E := E) (hw r) hb0 (hwb r)) R‖ ≤ b :=
    fun r => norm_kgBandOp_le hb0 (hFullb r) R
  have hBands : ∀ z : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R z := fun z =>
    (kgLowPassOp R).continuous.comp (hWs (kgLowPassOp R z))
  have hband := kgFreqInvOp_kgFieldGradT hb0 hBandb hBands (kgFreqLowOp R x) (kgLowPassOp R y) t
  have hfull := kgFreqInvOp_kgFieldGradT hb0 hFullb hWs (kgFreqLowOp R x) (kgLowPassOp R y) t
  have hmild : kgFieldMildT (fun r : ℝ => kgBandOp (fourierMulCLM (hw r) hb0 (hwb r)) R)
        (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t
      = kgFieldMildT (fun r : ℝ => fourierMulCLM (hw r) hb0 (hwb r))
        (kgFreqInvOp (kgFreqLowOp R x)) (kgLowPassOp R y) t := by
    rw [← hband, ← hfull, hgrad]
  rw [← hmild]
  exact kgFieldMildT_eq_kgShiftedField hp hb0 hb1 hpb R x y t

end ClosedForm

end GaloisForLFunctions.HTGeometry
