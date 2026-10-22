import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldFlow
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldVelocity

/-!
# The perturbed evolution is an evolution family

The free field evolution is a flow (statement 121). With a perturbation the same is true, and for the
same reason once the Duhamel term is handled: restarting the mild solution from its own state at time
`s` reproduces it.

The proof is uniqueness. The shifted curve `t ↦ u(t+s)` is continuous and satisfies the Duhamel
formula with data `(u(s), ∂ₜu(s))`: splitting `∫₀^{t+s}` at `s`, the early part combines with the
free field by the flow identity and the addition law under the integral sign, and the late part
becomes the Duhamel integral of the shifted curve by a change of variable.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Restarting the free field with an accumulated source -/

/-- **The free field restarted from an accumulated state.** The flow identity, carrying along the
Duhamel contributions accumulated up to time `s`. -/
theorem kgFieldFree_restart (g h : Lp ℂ 2 (volume : Measure E))
    {k : ℝ → Lp ℂ 2 (volume : Measure E)} (hk : Continuous k) (t s : ℝ) :
    kgFieldFree (kgFreqInvOp g) h (t + s)
        + ∫ r in (0 : ℝ)..s, kgSinFreqOp (t + s - r) (k r)
      = kgFieldFree
          (kgFieldFree (kgFreqInvOp g) h s + ∫ r in (0 : ℝ)..s, kgSinFreqOp (s - r) (k r))
          (kgFieldFreeVel g h s + ∫ r in (0 : ℝ)..s, kgCosOp (s - r) (k r)) t := by
  have hsf : Continuous fun r : ℝ => kgSinFreqOp (s - r) (k r) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hk
  have hcf : Continuous fun r : ℝ => kgCosOp (s - r) (k r) :=
    continuous_kgCosOp_comp (continuous_const.sub continuous_id) hk
  have hIs := hsf.intervalIntegrable (μ := volume) 0 s
  have hIc := hcf.intervalIntegrable (μ := volume) 0 s
  have hc1 : Continuous fun r : ℝ => kgCosOp t (kgSinFreqOp (s - r) (k r)) :=
    continuous_kgCosOp_comp continuous_const hsf
  have hc2 : Continuous fun r : ℝ => kgSinFreqOp t (kgCosOp (s - r) (k r)) :=
    continuous_kgSinFreqOp_comp continuous_const hcf
  have hcomb : (∫ r in (0 : ℝ)..s, kgCosOp t (kgSinFreqOp (s - r) (k r)))
      + ∫ r in (0 : ℝ)..s, kgSinFreqOp t (kgCosOp (s - r) (k r))
      = ∫ r in (0 : ℝ)..s, kgSinFreqOp (t + s - r) (k r) := by
    rw [← intervalIntegral.integral_add (hc1.intervalIntegrable (μ := volume) 0 s)
      (hc2.intervalIntegrable (μ := volume) 0 s)]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have hadd : kgSinFreqOp (E := E) (t + (s - r))
        = (kgCosOp t).comp (kgSinFreqOp (s - r)) + (kgSinFreqOp t).comp (kgCosOp (s - r)) :=
      kgSinFreqOp_add t (s - r)
    have hrw : t + s - r = t + (s - r) := by ring
    rw [hrw, hadd]
    rfl
  have hsplit : kgFieldFree
        (kgFieldFree (kgFreqInvOp g) h s + ∫ r in (0 : ℝ)..s, kgSinFreqOp (s - r) (k r))
        (kgFieldFreeVel g h s + ∫ r in (0 : ℝ)..s, kgCosOp (s - r) (k r)) t
      = kgFieldFree (kgFieldFree (kgFreqInvOp g) h s) (kgFieldFreeVel g h s) t
        + (kgCosOp t (∫ r in (0 : ℝ)..s, kgSinFreqOp (s - r) (k r))
          + kgSinFreqOp t (∫ r in (0 : ℝ)..s, kgCosOp (s - r) (k r))) := by
    simp only [kgFieldFree, map_add]
    abel
  rw [hsplit, ← kgFieldFree_flow g h t s,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hIs,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hIc, hcomb]

/-! ## The evolution family property -/

section Family

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

/-- **The perturbed evolution is an evolution family.** Restarting the mild solution from its own
state at time `s` reproduces it. -/
theorem kgFieldMild_flow (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldMild W (kgFreqInvOp g) h (t + s)
      = kgFieldMild W (kgFieldMild W (kgFreqInvOp g) h s)
          (deriv (kgFieldMild W (kgFreqInvOp g) h) s) t := by
  set u := kgFieldMild W (kgFreqInvOp g) h with hu
  have hcu : Continuous u := continuous_kgFieldMild hb0 hW _ h
  have hk : Continuous fun r : ℝ => W (u r) := W.continuous.comp hcu
  have hsf : ∀ τ : ℝ, Continuous fun r : ℝ => kgSinFreqOp (τ - r) (W (u r)) := fun τ =>
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hk
  have hvel : deriv u s = kgFieldFreeVel g h s
      + ∫ r in (0 : ℝ)..s, kgCosOp (s - r) (W (u r)) := by
    rw [hu, deriv_kgFieldMild hb0 hW g h s, kgFieldFreeVel]
  have hstate : u s = kgFieldFree (kgFreqInvOp g) h s
      + ∫ r in (0 : ℝ)..s, kgSinFreqOp (s - r) (W (u r)) := by
    have hEq := kgFieldMild_eq hb0 hW (kgFreqInvOp g) h s
    rw [hu, hEq]
    congr 1
  have hshiftc : Continuous fun τ : ℝ => u (τ + s) :=
    hcu.comp (continuous_id.add continuous_const)
  have hduh : ∀ τ : ℝ, u (τ + s) = kgFieldFree (u s) (deriv u s) τ
      + ∫ ρ in (0 : ℝ)..τ, kgFieldKernel W τ ρ (u (ρ + s)) := by
    intro τ
    have hsplitI : (∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W (u r)))
        = (∫ r in (0 : ℝ)..s, kgSinFreqOp (τ + s - r) (W (u r)))
          + ∫ r in s..(τ + s), kgSinFreqOp (τ + s - r) (W (u r)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hsf (τ + s)).intervalIntegrable (μ := volume) 0 s)
        ((hsf (τ + s)).intervalIntegrable (μ := volume) s (τ + s))).symm
    have hshift : (∫ r in s..(τ + s), kgSinFreqOp (τ + s - r) (W (u r)))
        = ∫ ρ in (0 : ℝ)..τ, kgSinFreqOp (τ - ρ) (W (u (ρ + s))) := by
      have hcv := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := τ) (f := fun r : ℝ => kgSinFreqOp (τ + s - r) (W (u r))) s
      rw [zero_add] at hcv
      rw [← hcv]
      refine intervalIntegral.integral_congr fun ρ _ => ?_
      congr 2
      ring
    have hker : (∫ r in (0 : ℝ)..(τ + s), kgFieldKernel W (τ + s) r (u r))
        = ∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W (u r)) :=
      intervalIntegral.integral_congr fun r _ => kgFieldKernel_apply W (τ + s) r (u r)
    have hkerτ : (∫ ρ in (0 : ℝ)..τ, kgFieldKernel W τ ρ (u (ρ + s)))
        = ∫ ρ in (0 : ℝ)..τ, kgSinFreqOp (τ - ρ) (W (u (ρ + s))) :=
      intervalIntegral.integral_congr fun ρ _ => kgFieldKernel_apply W τ ρ (u (ρ + s))
    have hstart : u (τ + s) = kgFieldFree (kgFreqInvOp g) h (τ + s)
        + ∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W (u r)) := by
      rw [hu, kgFieldMild_eq hb0 hW (kgFreqInvOp g) h (τ + s), hker]
    rw [hstart, hkerτ, hstate, hvel, ← kgFieldFree_restart g h hk τ s, hsplitI, ← hshift]
    abel
  have hfin := eq_kgFieldMild_of_duhamel hb0 hW (u s) (deriv u s) hshiftc hduh
  exact congrFun hfin t

end Family

end GaloisForLFunctions.HTGeometry
