import GaloisForLFunctions.RHTower.FZZCigarCubicScreeningCutoff

open Filter Topology Metric Set

namespace GaloisForLFunctions.RHTower

noncomputable section

/-!
# FZZ cubic raw-cutoff no-go

The literal raw zero-collar cubic screening integral cannot converge to a
finite value when the collar is removed. The exact counterterm-restored
finite part remains a viable source object; this file does not rule it out.
-/

/-- The cubic collision counterterm diverges to negative infinity as the
    zero collar is removed. -/
theorem fzzScreeningCubicCollisionCorrection_tendsto_atBot :
    Tendsto (fun T : ℝ =>
      2 * Real.pi *
        fzzScreeningCubicCollisionPrimitive (Real.exp (-T))) atTop atBot := by
  rw [Filter.tendsto_atBot]
  intro b
  filter_upwards [Filter.eventually_ge_atTop
    (max 0 (-b / (72 * Real.pi)))] with T hT
  have hT0 : 0 ≤ T := le_trans (le_max_left _ _) hT
  have hTlower : -b / (72 * Real.pi) ≤ T :=
    le_trans (le_max_right _ _) hT
  have hpi : 0 < 72 * Real.pi := by positivity
  have hpow4 : 0 ≤ ((Real.exp (-T)) ^ (4 : ℕ))⁻¹ := by positivity
  have hpow2 : 0 ≤ ((Real.exp (-T)) ^ (2 : ℕ))⁻¹ := by positivity
  have hlog : Real.log (Real.exp (-T)) = -T := Real.log_exp _
  have hprimitive :
      fzzScreeningCubicCollisionPrimitive (Real.exp (-T)) ≤ -36 * T := by
    unfold fzzScreeningCubicCollisionPrimitive
    rw [hlog]
    linarith
  calc
    2 * Real.pi * fzzScreeningCubicCollisionPrimitive (Real.exp (-T)) ≤
        2 * Real.pi * (-36 * T) :=
      mul_le_mul_of_nonneg_left hprimitive (by positivity)
    _ = -(72 * Real.pi * T) := by ring
    _ ≤ b := by
      have hmul : -b ≤ T * (72 * Real.pi) :=
        (div_le_iff₀ hpi).mp hTlower
      nlinarith

/-- No finite raw zero-collar limit exists for the cubic FZZ screening kernel.
    Thus a source-facing Ward law must use the independently renormalized
    finite part, not this raw local integral. -/
theorem not_exists_fzzScreeningCubicZero_raw_cutoff_limit :
    ¬ ∃ L : ℝ, Tendsto (fun T : ℝ =>
      ∫ z : ℂ in ball 0 (1 / 2) \ closedBall 0 (Real.exp (-T)),
        fzzScreeningPlaneKernel (-6) (-6) z) atTop (𝓝 L) := by
  rintro ⟨L, hraw⟩
  let raw : ℝ → ℝ := fun T =>
    ∫ z : ℂ in ball 0 (1 / 2) \ closedBall 0 (Real.exp (-T)),
      fzzScreeningPlaneKernel (-6) (-6) z
  let correction : ℝ → ℝ := fun T =>
    2 * Real.pi * fzzScreeningCubicCollisionPrimitive (Real.exp (-T))
  have hsum : Tendsto (fun T => raw T + correction T) atTop
      (𝓝 fzzScreeningCubicLocalFinitePart) := by
    simpa [raw, correction] using fzzScreeningCubicZero_cutoff_limit
  have hraw' : Tendsto raw atTop (𝓝 L) := by
    simpa [raw] using hraw
  have hcorrection : Tendsto correction atTop
      (𝓝 (fzzScreeningCubicLocalFinitePart - L)) := by
    simpa [raw, correction] using hsum.sub hraw'
  have hbot : Tendsto correction atTop atBot := by
    simpa [correction] using fzzScreeningCubicCollisionCorrection_tendsto_atBot
  have habove : ∀ᶠ T in atTop,
      correction T ∈ Set.Ioi (fzzScreeningCubicLocalFinitePart - L - 1) :=
    hcorrection.eventually
      (Ioi_mem_nhds (by linarith :
        fzzScreeningCubicLocalFinitePart - L - 1 <
          fzzScreeningCubicLocalFinitePart - L))
  have hbelow : ∀ᶠ T in atTop,
      correction T ≤ fzzScreeningCubicLocalFinitePart - L - 1 :=
    (Filter.tendsto_atBot.mp hbot) _
  have hfalse : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [habove, hbelow] with T hT hT'
    exact (not_lt_of_ge hT') hT
  rcases hfalse.exists with ⟨T, hT⟩
  exact hT

end

end GaloisForLFunctions.RHTower
