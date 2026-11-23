import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.FixedPower
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.QuarticFrontier

/-! # A fixed fourth-power clock test characterizes isometric composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Every physical rank-one trace estimate eventually holds with an arbitrarily small multiple of the fourth clock power. -/
def subquarticClockControl (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop, traceControlsAt 1 (⟨σ,t⟩:ℂ) 4 (ε*t^4)

private theorem subquartic_iff_subpower (σ : ℝ) : subquarticClockControl σ ↔ subpowerClockControl σ 4 := by
  simp only [subquarticClockControl,subpowerClockControl,show ∀ t : ℝ, t^(4:ℝ) = t^4 from fun t => Real.rpow_natCast t 4]

/-- Strict subquartic growth at fixed fourth power holds precisely to the right of the isometric line. -/
theorem subquartic_clock_iff {σ : ℝ} (hσ : 0 < σ) : subquarticClockControl σ ↔ 1/2 < σ := by
  rw [subquartic_iff_subpower,subpower_clock_iff hσ (by norm_num)]
  constructor
  · intro h
    have he := (div_lt_iff₀ hσ).mp ((le_max_right _ _).trans_lt h)
    linarith only [he]
  · intro h
    exact max_lt (by norm_num) ((div_lt_iff₀ hσ).mpr (by linarith only [h]))

/-- The fixed quartic trace bound exists but cannot grow subquartically exactly when divisor splitting is isometric. -/
theorem fixed_quartic_clock_iff_split_isometric {z : ℂ} (hz : 0 < z.re) :
    ((∃ K : ℝ, traceControlsAt 1 z 4 K) ∧ ¬ subquarticClockControl z.re) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  rw [quartic_trace_control_iff 0 hz,subquartic_clock_iff hz,split_isometric_iff]
  constructor
  · rintro ⟨hl,hn⟩
    exact le_antisymm (le_of_not_gt hn) hl
  · rintro he
    rw [he]
    exact ⟨le_rfl,lt_irrefl _⟩

#print axioms subquartic_clock_iff
#print axioms fixed_quartic_clock_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
