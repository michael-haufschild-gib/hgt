import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimePotentialStability
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFieldEvolutionFamily
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonRegularDense

/-!
# The moving background is determined, everywhere in time

Restarting the solution from its own state at time `s` reproduces it, provided the equation is
restarted too: the potential seen from time `s` onwards is `W(· + s)`. That is the evolution-family
property of a non-autonomous equation, and its proof is the autonomous one — split the Duhamel
integral at `s`, recombine the early part with the free field by the addition law, and change
variables in the late part.

Running it backwards is what closes the inverse problem. Given a regular target `v` and a time `r`,
solve the forward-shifted equation `W(r + ·)` from `v` and restart *that* solution at time `-r`: the
result is a solution of the original equation which passes through `v` at time `r`. So every regular
vector is reached, the reachable set is dense, and the identity `W₁(r) = W₂(r)` on the reachable set
extends to all of `L²` by continuity.

The forward map of the inverse problem is therefore injective on moving backgrounds, not merely at
the initial instant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Flow

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The non-autonomous evolution is an evolution family.** Restarting the solution from its own
state at time `s`, with the potential seen from time `s`, reproduces it. -/
theorem kgFieldMildT_flow (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t s : ℝ) :
    kgFieldMildT W (kgFreqInvOp g) h (t + s)
      = kgFieldMildT (fun ρ : ℝ => W (ρ + s))
          (kgFieldMildT W (kgFreqInvOp g) h s)
          (deriv (kgFieldMildT W (kgFreqInvOp g) h) s) t := by
  have hSb : ∀ ρ : ℝ, ‖W (ρ + s)‖ ≤ b := fun ρ => hWb (ρ + s)
  have hSs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun ρ : ℝ => W (ρ + s) x := fun x =>
    (hWs x).comp (continuous_id.add continuous_const)
  set u := kgFieldMildT W (kgFreqInvOp g) h with hu
  have hcu : Continuous u := continuous_kgFieldMildT hb0 hWb hWs _ h
  have hk : Continuous fun r : ℝ => W r (u r) :=
    continuous_kgPotentialSource hb0 hWb hWs _ h
  have hsf : ∀ τ : ℝ, Continuous fun r : ℝ => kgSinFreqOp (τ - r) (W r (u r)) := fun τ =>
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hk
  have hvel : deriv u s = kgFieldFreeVel g h s
      + ∫ r in (0 : ℝ)..s, kgCosOp (s - r) (W r (u r)) := by
    rw [hu, deriv_kgFieldMildT hb0 hWb hWs g h s, kgFieldFreeVel]
  have hstate : u s = kgFieldFree (kgFreqInvOp g) h s
      + ∫ r in (0 : ℝ)..s, kgSinFreqOp (s - r) (W r (u r)) := by
    have hEq := kgFieldMildT_eq hb0 hWb hWs (kgFreqInvOp g) h s
    rw [hu, hEq]
    congr 1
  have hshiftc : Continuous fun τ : ℝ => u (τ + s) :=
    hcu.comp (continuous_id.add continuous_const)
  have hduh : ∀ τ : ℝ, u (τ + s) = kgFieldFree (u s) (deriv u s) τ
      + ∫ ρ in (0 : ℝ)..τ, kgFieldKernelT (fun ρ' : ℝ => W (ρ' + s)) τ ρ (u (ρ + s)) := by
    intro τ
    have hsplitI : (∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W r (u r)))
        = (∫ r in (0 : ℝ)..s, kgSinFreqOp (τ + s - r) (W r (u r)))
          + ∫ r in s..(τ + s), kgSinFreqOp (τ + s - r) (W r (u r)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        ((hsf (τ + s)).intervalIntegrable (μ := volume) 0 s)
        ((hsf (τ + s)).intervalIntegrable (μ := volume) s (τ + s))).symm
    have hshift : (∫ r in s..(τ + s), kgSinFreqOp (τ + s - r) (W r (u r)))
        = ∫ ρ in (0 : ℝ)..τ, kgSinFreqOp (τ - ρ) (W (ρ + s) (u (ρ + s))) := by
      have hcv := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := τ) (f := fun r : ℝ => kgSinFreqOp (τ + s - r) (W r (u r))) s
      rw [zero_add] at hcv
      rw [← hcv]
      refine intervalIntegral.integral_congr fun ρ _ => ?_
      congr 2
      ring
    have hker : (∫ r in (0 : ℝ)..(τ + s), kgFieldKernelT W (τ + s) r (u r))
        = ∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W r (u r)) :=
      intervalIntegral.integral_congr fun r _ => kgFieldKernelT_apply W (τ + s) r (u r)
    have hkerτ : (∫ ρ in (0 : ℝ)..τ,
          kgFieldKernelT (fun ρ' : ℝ => W (ρ' + s)) τ ρ (u (ρ + s)))
        = ∫ ρ in (0 : ℝ)..τ, kgSinFreqOp (τ - ρ) (W (ρ + s) (u (ρ + s))) :=
      intervalIntegral.integral_congr fun ρ _ =>
        kgFieldKernelT_apply (fun ρ' : ℝ => W (ρ' + s)) τ ρ (u (ρ + s))
    have hstart : u (τ + s) = kgFieldFree (kgFreqInvOp g) h (τ + s)
        + ∫ r in (0 : ℝ)..(τ + s), kgSinFreqOp (τ + s - r) (W r (u r)) := by
      rw [hu, kgFieldMildT_eq hb0 hWb hWs (kgFreqInvOp g) h (τ + s), hker]
    rw [hstart, hkerτ, hstate, hvel, ← kgFieldFree_restart g h hk τ s, hsplitI, ← hshift]
    abel
  have hfin := eq_kgFieldMildT_of_duhamel hb0 hSb hSs (u s) (deriv u s) hshiftc hduh
  exact congrFun hfin t

/-- **Every regular vector is reached.** Given a target carrying one power of `⟨D⟩⁻¹` and a time `r`,
there is a Cauchy datum whose solution passes through it at time `r`. The datum is produced by
running the forward-shifted equation from the target and restarting that solution at time `-r`. -/
theorem exists_kgFieldMildT_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g : Lp ℂ 2 (volume : Measure E)) (r : ℝ) :
    ∃ f h : Lp ℂ 2 (volume : Measure E), kgFieldMildT W f h r = kgFreqInvOp g := by
  have hQb : ∀ ρ : ℝ, ‖W (r + ρ)‖ ≤ b := fun ρ => hWb (r + ρ)
  have hQs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun ρ : ℝ => W (r + ρ) x := fun x =>
    (hWs x).comp (continuous_const.add continuous_id)
  set z := kgFieldMildT (fun ρ : ℝ => W (r + ρ)) (kgFreqInvOp g) 0 with hz
  refine ⟨z (-r), deriv z (-r), ?_⟩
  have hflow := kgFieldMildT_flow hb0 hQb hQs g 0 r (-r)
  have hfun : (fun ρ : ℝ => W (r + (ρ + -r))) = W := by
    funext ρ
    congr 1
    ring
  rw [hfun] at hflow
  rw [← hz] at hflow
  have hzero : z 0 = kgFreqInvOp g := kgFieldMildT_zero hb0 hQb hQs (kgFreqInvOp g) 0
  have hsum : r + -r = (0 : ℝ) := by ring
  rw [hsum, hzero] at hflow
  exact hflow.symm

/-! ## Injectivity of the forward map -/

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))}

/-- **The moving background is determined by the field it produces.** Two uniformly bounded, strongly
continuous families of perturbations whose solutions agree for every Cauchy datum and every time are
equal at every time. -/
theorem eq_of_kgFieldMildT_eq (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x)
    (heq : ∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
      kgFieldMildT W₁ f h t = kgFieldMildT W₂ f h t) :
    W₁ = W₂ := by
  funext r
  have hreg : ∀ g : Lp ℂ 2 (volume : Measure E),
      W₁ r (kgFreqInvOp g) = W₂ r (kgFreqInvOp g) := by
    intro g
    obtain ⟨f, h, hfh⟩ := exists_kgFieldMildT_eq hb0 hW₁b hW₁s g r
    have hkey := kgFieldMildT_potential_apply_eq hb0 hW₁b hW₁s hW₂b hW₂s heq f h r
    rwa [hfh] at hkey
  have hcoe : ⇑(W₁ r) = ⇑(W₂ r) :=
    denseRange_kgFreqInvOp.equalizer (W₁ r).continuous (W₂ r).continuous (funext hreg)
  exact ContinuousLinearMap.ext fun x => congrFun hcoe x

/-- **The forward map of the inverse problem is a continuous injection**, for moving backgrounds:
the field determines the equation, and depends on it Lipschitz-continuously. -/
theorem kgFieldMildT_injective_potential (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r x)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r x) :
    (∀ (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ),
        kgFieldMildT W₁ f h t = kgFieldMildT W₂ f h t) ↔ W₁ = W₂ := by
  refine ⟨eq_of_kgFieldMildT_eq hb0 hW₁b hW₁s hW₂b hW₂s, ?_⟩
  rintro rfl f h t
  rfl

end Flow

end GaloisForLFunctions.HTGeometry
