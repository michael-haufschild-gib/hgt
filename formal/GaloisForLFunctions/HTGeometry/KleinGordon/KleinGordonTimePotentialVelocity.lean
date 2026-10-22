import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimePotential

/-!
# Velocity and reversibility with a time-dependent perturbation

The two structural facts about the autonomous field evolution that survive a moving background: it is
`C¹` with the classical variation-of-constants velocity, and it is reversible.

Both proofs are the autonomous ones with the perturbation evaluated at the source time. The
differentiation step costs nothing extra because the derivative of the Duhamel term was proved for an
*arbitrary* continuous source, and `s ↦ W(s)u(s)` is continuous exactly when `W` is uniformly bounded
and strongly continuous — the hypotheses the construction already carries.

Reversal changes the equation, not only the datum: running `W` backwards in time is running the
reflected potential `r ↦ W(-r)` forwards. That is the correct statement of reversibility for a
non-autonomous equation, and it degenerates to the autonomous one when `W` is constant.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Velocity

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The source of the Duhamel term is continuous. -/
theorem continuous_kgPotentialSource (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) :
    Continuous fun s : ℝ => W s (kgFieldMildT W f h s) :=
  continuous_of_strong_comp hWb hWs continuous_id (continuous_kgFieldMildT hb0 hWb hWs f h)

/-- **The Duhamel formula in separated form**, for a time-dependent perturbation. The observation
time appears only in two fixed operators. -/
theorem kgFieldMildT_eq_separated (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W f h t
      = kgFieldFree f h t
        + (kgSinFreqOp t (∫ s in (0 : ℝ)..t, kgCosOp s (W s (kgFieldMildT W f h s)))
          - kgCosOp t (∫ s in (0 : ℝ)..t, kgSinFreqOp s (W s (kgFieldMildT W f h s)))) := by
  have hg := continuous_kgPotentialSource hb0 hWb hWs f h
  have hker : (∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (kgFieldMildT W f h s))
      = ∫ s in (0 : ℝ)..t, kgSinFreqOp (t - s) (W s (kgFieldMildT W f h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernelT_apply W t s _
  rw [kgFieldMildT_eq hb0 hWb hWs f h t, hker, intervalIntegral_kgSinFreqOp_separated hg t]

/-- **The solution is differentiable**, with the classical velocity, for a time-dependent
perturbation. -/
theorem hasDerivAt_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (kgFieldMildT W (kgFreqInvOp g) h)
      (-(kgSinOp t g) + kgCosOp t h
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s))) t := by
  have hgf := continuous_kgPotentialSource hb0 hWb hWs (kgFreqInvOp g) h
  have hsum := (hasDerivAt_kgFieldFree g h t).add (hasDerivAt_kgDuhamel hgf t)
  rw [kgDuhamel_deriv_eq hgf t] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Pi.add_apply]
  exact kgFieldMildT_eq_separated hb0 hWb hWs (kgFreqInvOp g) h r

/-- **The velocity, in closed form.** -/
theorem deriv_kgFieldMildT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    deriv (kgFieldMildT W (kgFreqInvOp g) h) t
      = -(kgSinOp t g) + kgCosOp t h
        + ∫ s in (0 : ℝ)..t, kgCosOp (t - s) (W s (kgFieldMildT W (kgFreqInvOp g) h s)) :=
  (hasDerivAt_kgFieldMildT hb0 hWb hWs g h t).deriv

theorem kgFieldMildT_at_zero (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    kgFieldMildT W (kgFreqInvOp g) h 0 = kgFreqInvOp g :=
  kgFieldMildT_zero hb0 hWb hWs (kgFreqInvOp g) h

theorem deriv_kgFieldMildT_at_zero (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    deriv (kgFieldMildT W (kgFreqInvOp g) h) 0 = h := by
  rw [deriv_kgFieldMildT hb0 hWb hWs g h 0, intervalIntegral.integral_same, kgCosOp_zero,
    kgSinOp_zero]
  simp

/-- **The Cauchy problem with a time-dependent perturbation is solved in the `C¹` sense**, with the
data one prescribes. -/
theorem exists_kgFieldMildT_c1 (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) :
    ∃ u : ℝ → Lp ℂ 2 (volume : Measure E),
      (∀ t : ℝ, HasDerivAt u (deriv u t) t) ∧ u 0 = kgFreqInvOp g ∧ deriv u 0 = h ∧
        ∀ t : ℝ, u t = kgFieldFree (kgFreqInvOp g) h t
          + ∫ s in (0 : ℝ)..t, kgFieldKernelT W t s (u s) := by
  refine ⟨kgFieldMildT W (kgFreqInvOp g) h, fun t => ?_,
    kgFieldMildT_at_zero hb0 hWb hWs g h, deriv_kgFieldMildT_at_zero hb0 hWb hWs g h,
    kgFieldMildT_eq hb0 hWb hWs (kgFreqInvOp g) h⟩
  have hd := hasDerivAt_kgFieldMildT hb0 hWb hWs g h t
  rwa [hd.deriv]

end Velocity

/-! ## Reversibility -/

section Reverse

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The evolution is reversible, with the reflected potential.** Running the solution backwards in
time is running the solution of the time-reflected equation, with the reversed velocity datum,
forwards. -/
theorem kgFieldMildT_neg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMildT W f h (-t) = kgFieldMildT (fun r : ℝ => W (-r)) f (-h) t := by
  have hVb : ∀ r : ℝ, ‖W (-r)‖ ≤ b := fun r => hWb (-r)
  have hVs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W (-r) x := fun x =>
    (hWs x).comp continuous_neg
  have hcu : Continuous (kgFieldMildT W f h) := continuous_kgFieldMildT hb0 hWb hWs f h
  have hk : Continuous fun r : ℝ => W r (kgFieldMildT W f h r) :=
    continuous_kgPotentialSource hb0 hWb hWs f h
  have hrefl : Continuous fun τ : ℝ => kgFieldMildT W f h (-τ) := hcu.comp continuous_neg
  have hduh : ∀ τ : ℝ, kgFieldMildT W f h (-τ) = kgFieldFree f (-h) τ
      + ∫ ρ in (0 : ℝ)..τ, kgFieldKernelT (fun r : ℝ => W (-r)) τ ρ (kgFieldMildT W f h (-ρ)) := by
    intro τ
    have hF : Continuous fun r : ℝ => kgSinFreqOp (-τ - r) (W r (kgFieldMildT W f h r)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) hk
    have hker : (∫ r in (0 : ℝ)..(-τ), kgFieldKernelT W (-τ) r (kgFieldMildT W f h r))
        = ∫ r in (0 : ℝ)..(-τ), kgSinFreqOp (-τ - r) (W r (kgFieldMildT W f h r)) :=
      intervalIntegral.integral_congr fun r _ =>
        kgFieldKernelT_apply W (-τ) r (kgFieldMildT W f h r)
    have hcv : (∫ ρ in (0 : ℝ)..τ,
          kgSinFreqOp (-τ - -ρ) (W (-ρ) (kgFieldMildT W f h (-ρ))))
        = ∫ r in (-τ)..(0 : ℝ), kgSinFreqOp (-τ - r) (W r (kgFieldMildT W f h r)) := by
      have h := intervalIntegral.integral_comp_neg
        (a := (0 : ℝ)) (b := τ)
        (f := fun r : ℝ => kgSinFreqOp (-τ - r) (W r (kgFieldMildT W f h r)))
      rw [neg_zero] at h
      exact h
    have hsign : (∫ ρ in (0 : ℝ)..τ,
          kgFieldKernelT (fun r : ℝ => W (-r)) τ ρ (kgFieldMildT W f h (-ρ)))
        = ∫ r in (0 : ℝ)..(-τ), kgSinFreqOp (-τ - r) (W r (kgFieldMildT W f h r)) := by
      have hpt : ∀ ρ ∈ Set.uIcc (0 : ℝ) τ,
          kgFieldKernelT (fun r : ℝ => W (-r)) τ ρ (kgFieldMildT W f h (-ρ))
            = -(kgSinFreqOp (-τ - -ρ) (W (-ρ) (kgFieldMildT W f h (-ρ)))) := by
        intro ρ _
        rw [kgFieldKernelT_apply]
        have hneg : -τ - -ρ = -(τ - ρ) := by ring
        rw [hneg, kgSinFreqOp_neg, neg_apply, neg_neg]
      rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg, hcv,
        ← intervalIntegral.integral_symm]
    rw [hsign, ← hker, ← kgFieldFree_neg f h τ]
    exact kgFieldMildT_eq hb0 hWb hWs f h (-τ)
  have hfin := eq_kgFieldMildT_of_duhamel hb0 hVb hVs f (-h) hrefl hduh
  exact congrFun hfin t

end Reverse

end GaloisForLFunctions.HTGeometry
