import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandAdiabaticLimit
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimePotentialFlow

/-!
# A periodically driven clock: the period map

The evolution family of statement 152 restarts the solution from its own state, at the price of
shifting the background. When the background is periodic the shift changes nothing, so the evolution
over one period is the *same* map at every period, and the state after `n` periods is its `n`-th
iterate.

Getting there needs the restart at the level of the state, not only of the field. The velocity comes
from differentiating the field restart in time; the gradient comes from the field restart and the
injectivity of `⟨D⟩⁻¹`, the two being related by `⟨D⟩⁻¹⟨D⟩u = u`. The band-restricted frequency undoes
the inverse frequency exactly, `⟨D⟩_R⟨D⟩⁻¹ = P_R`, which is the missing half of the symbol calculus of
statement 222.

The consequence is the Floquet form of the energy estimate: after `n` periods the state is bounded by
`e^{n b|T|}` times the datum, with the growth carried by one operator rather than by the whole
history.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The band-restricted frequency undoes the inverse frequency -/

private theorem fourierMul_comp_apply₃ {φ ψ χ : E → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ ξ, ‖ψ ξ‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ ξ, ‖χ ξ‖ ≤ B)
    (hae : ∀ ξ, χ ξ = φ ξ * ψ ξ) (x : Lp ℂ 2 (volume : Measure E)) :
    fourierMulCLM hφ hC0 hC (fourierMulCLM hψ hD0 hD x) = fourierMulCLM hχ hB0 hB x :=
  congrArg (fun T : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) => T x)
    (fourierMulCLM_comp hφ hψ hχ hC0 hC hD0 hD hB0 hB (Filter.Eventually.of_forall hae))

/-- **The band-restricted frequency undoes the inverse frequency.** -/
theorem kgFreqLowOp_kgFreqInvOp (R : ℝ) (z : Lp ℂ 2 (volume : Measure E)) :
    kgFreqLowOp R (kgFreqInvOp z) = kgLowPassOp R z := by
  have hprod : ∀ ξ : E, kgLowPass R ξ = kgFreqLow R ξ * kgFreqInv ξ := by
    intro ξ
    have hne : ((kgFreq ξ : ℝ) : ℂ) ≠ 0 := by simpa using (kgFreq_pos ξ).ne'
    rw [kgFreqLow, kgFreqInv, Complex.ofReal_inv]
    field_simp
  rw [kgFreqLowOp, kgFreqInvOp_eq, kgLowPassOp_eq]
  exact fourierMul_comp_apply₃ _ _ _ _ _ _ _ _ _ hprod z

/-! ## The state restarts -/

section Restart

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The field restart, with the state at the restarting time in closed form. -/
theorem kgFieldMildT_restart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldMildT W (kgFreqInvOp g) h (t + s)
      = kgFieldMildT (fun ρ : ℝ => W (ρ + s)) (kgFreqInvOp (kgFieldGradT W g h s))
          (kgFieldVelT W g h s) t := by
  rw [kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h s, kgFieldVelT_eq_deriv hb0 hWb hWs g h s]
  exact kgFieldMildT_flow hb0 hWb hWs g h t s

/-- **The velocity restarts.** -/
theorem kgFieldVelT_restart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldVelT W g h (t + s)
      = kgFieldVelT (fun ρ : ℝ => W (ρ + s)) (kgFieldGradT W g h s) (kgFieldVelT W g h s) t := by
  have hSb : ∀ ρ : ℝ, ‖W (ρ + s)‖ ≤ b := fun ρ => hWb (ρ + s)
  have hSs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun ρ : ℝ => W (ρ + s) x := fun x =>
    (hWs x).comp (continuous_id.add continuous_const)
  have hR : HasDerivAt (kgFieldMildT (fun ρ : ℝ => W (ρ + s))
      (kgFreqInvOp (kgFieldGradT W g h s)) (kgFieldVelT W g h s))
      (kgFieldVelT (fun ρ : ℝ => W (ρ + s)) (kgFieldGradT W g h s) (kgFieldVelT W g h s) t) t :=
    hasDerivAt_kgFieldMildT hb0 hSb hSs _ _ t
  have hL0 : HasDerivAt (kgFieldMildT W (kgFreqInvOp g) h) (kgFieldVelT W g h (t + s)) (t + s) :=
    hasDerivAt_kgFieldMildT hb0 hWb hWs g h (t + s)
  have hL : HasDerivAt (fun τ : ℝ => kgFieldMildT W (kgFreqInvOp g) h (τ + s))
      (kgFieldVelT W g h (t + s)) t := HasDerivAt.comp_add_const t s hL0
  have hEq : (fun τ : ℝ => kgFieldMildT W (kgFreqInvOp g) h (τ + s))
      = kgFieldMildT (fun ρ : ℝ => W (ρ + s)) (kgFreqInvOp (kgFieldGradT W g h s))
          (kgFieldVelT W g h s) := by
    funext τ
    exact kgFieldMildT_restart hb0 hWb hWs g h τ s
  rw [hEq] at hL
  exact hL.unique hR

/-- **The gradient restarts.** -/
theorem kgFieldGradT_restart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldGradT W g h (t + s)
      = kgFieldGradT (fun ρ : ℝ => W (ρ + s)) (kgFieldGradT W g h s) (kgFieldVelT W g h s) t := by
  have hSb : ∀ ρ : ℝ, ‖W (ρ + s)‖ ≤ b := fun ρ => hWb (ρ + s)
  have hSs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun ρ : ℝ => W (ρ + s) x := fun x =>
    (hWs x).comp (continuous_id.add continuous_const)
  refine kgFreqInvOp_injective ?_
  rw [kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h (t + s),
    kgFreqInvOp_kgFieldGradT hb0 hSb hSs _ _ t]
  exact kgFieldMildT_restart hb0 hWb hWs g h t s

/-- **The state restarts**: the evolution of a moving background is an evolution family on the
energy space. -/
theorem kgFieldStateT_restart (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldStateT W g h (t + s)
      = kgFieldStateT (fun ρ : ℝ => W (ρ + s)) (kgFieldGradT W g h s)
          (kgFieldVelT W g h s) t := by
  rw [kgFieldStateT, kgFieldStateT, kgFieldGradT_restart hb0 hWb hWs g h t s,
    kgFieldVelT_restart hb0 hWb hWs g h t s]

end Restart

/-! ## The period map -/

section Floquet

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The period map** of a periodically driven field: the state it reaches after one period. -/
def kgPeriodMap (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (T : ℝ) : KGEnergy E → KGEnergy E := fun v => kgFieldStateT W v.fst v.snd T

theorem kgPeriodMap_apply
    (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (T : ℝ) (v : KGEnergy E) : kgPeriodMap W T v = kgFieldStateT W v.fst v.snd T := rfl

/-- The period map obeys the sharp energy estimate over one period. -/
theorem norm_kgPeriodMap_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (v : KGEnergy E) :
    ‖kgPeriodMap W T v‖ ≤ ‖v‖ * Real.exp (b * |T|) := by
  rw [kgPeriodMap, kgFieldStateT_eq_kgStateMildT hb0 hWb hWs]
  have hle := norm_kgStateMildT_le hb0 hWb hWs v.fst v.snd T
  rwa [kgPair_fst_snd] at hle

/-- A periodic background is periodic with every multiple of its period. -/
theorem periodic_shift_nat (hper : ∀ r : ℝ, W (r + T) = W r) (n : ℕ) (r : ℝ) :
    W (r + n * T) = W r := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : r + (n + 1 : ℕ) * T = (r + n * T) + T := by push_cast; ring
      rw [hstep, hper, ih]

/-- **The evolution over one period does not depend on which period.** -/
theorem kgFieldStateT_period (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    kgFieldStateT W g h (T + n * T)
      = kgPeriodMap W T (kgFieldStateT W g h (n * T)) := by
  have hshift : (fun ρ : ℝ => W (ρ + n * T)) = W := by
    funext ρ
    exact periodic_shift_nat hper n ρ
  have hrestart := kgFieldStateT_restart hb0 hWb hWs g h T (n * T)
  rw [hshift] at hrestart
  rw [hrestart]
  rfl

/-- **The state after `n` periods is the `n`-th iterate of the period map.** -/
theorem kgFieldStateT_iterate (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    kgFieldStateT W g h (n * T) = (kgPeriodMap W T)^[n] (kgPair E (g, h)) := by
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, Function.iterate_zero, id_eq]
      exact kgFieldStateT_zero g h
  | succ n ih =>
      have hsum : ((n + 1 : ℕ) : ℝ) * T = T + n * T := by push_cast; ring
      rw [hsum, kgFieldStateT_period hb0 hWb hWs hper g h n, ih,
        Function.iterate_succ_apply']

/-- **The Floquet form of the energy estimate.** After `n` periods the state is bounded by the
`n`-th power of the one-period factor. -/
theorem norm_kgFieldStateT_period_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (g h : Lp ℂ 2 (volume : Measure E)) (n : ℕ) :
    ‖kgFieldStateT W g h (n * T)‖ ≤ ‖kgPair E (g, h)‖ * Real.exp (b * |T|) ^ n := by
  rw [kgFieldStateT_iterate hb0 hWb hWs hper g h n]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine le_trans (norm_kgPeriodMap_le hb0 hWb hWs _) ?_
      have hexp : (0 : ℝ) < Real.exp (b * |T|) := Real.exp_pos _
      calc ‖(kgPeriodMap W T)^[n] (kgPair E (g, h))‖ * Real.exp (b * |T|)
          ≤ (‖kgPair E (g, h)‖ * Real.exp (b * |T|) ^ n) * Real.exp (b * |T|) :=
            mul_le_mul_of_nonneg_right ih hexp.le
        _ = ‖kgPair E (g, h)‖ * Real.exp (b * |T|) ^ (n + 1) := by ring

end Floquet

end GaloisForLFunctions.HTGeometry
