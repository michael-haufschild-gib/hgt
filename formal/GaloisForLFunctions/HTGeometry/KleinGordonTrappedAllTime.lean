import GaloisForLFunctions.HTGeometry.KleinGordonTrappedEnergy

/-!
# The trap holds at every instant

Statement 429 traps the energy of a clock in a weak static real potential at multiples of a period.
For a static potential the period is arbitrary — a constant background is periodic with *every* period
— so taking the period to be `t` itself and one step of the evolution puts the trap at every instant:

`E(0)·(1−b)/(1+b) ≤ E(t) ≤ (1+b)/(1−b)·E(0)`   for every `t ∈ ℝ`.

The clock's energy never leaves a fixed band. This is the strongest form the card's inequality takes:
no exponential at all, in either direction of time, with both constants read off from the potential's
strength alone.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section AllTime

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The energy of a clock in a weak static real potential is trapped at every instant.** -/
theorem kgFieldEnergy_trapped_all_time (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    (‖g‖ ^ 2 + ‖h‖ ^ 2) / ((1 + b) / (1 - b))
        ≤ ‖kgFieldGrad W₀ g h t‖ ^ 2 + ‖kgFieldVel W₀ g h t‖ ^ 2
      ∧ ‖kgFieldGrad W₀ g h t‖ ^ 2 + ‖kgFieldVel W₀ g h t‖ ^ 2
        ≤ (1 + b) / (1 - b) * (‖g‖ ^ 2 + ‖h‖ ^ 2) := by
  have hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b := fun _ => hW
  have hWs : ∀ x : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x := fun _ => continuous_const
  have hmain := kgFieldEnergy_trapped_of_small_potential (T := t) hb0 hb1 hW hsa hWb hWs g h 1
  have hcast : ((1 : ℕ) : ℝ) * t = t := by
    push_cast
    ring
  rw [hcast, kgFieldGradT_const, kgFieldVelT_const] at hmain
  exact hmain

end AllTime

end GaloisForLFunctions.HTGeometry
