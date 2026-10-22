import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonOscillatory

/-!
# Time reflection at the level of the state

The moving theory reflects time on the *field* (statement 149): running `W` backwards from `(f, h)` is
running `W(−·)` forwards from `(f, −h)`. Everything since then is stated for the state, and the
estimates that carry it — 269 and its consequences — are proved forwards in time only. To transport
them backwards the reflection has to be lifted to the state.

It lifts through the velocity flip `(g, h) ↦ (g, −h)`, an isometric involution of the energy space:
the gradient is unchanged, because `⟨D⟩⁻¹` is injective and the two fields agree, and the velocity
changes sign, because it is the derivative of a curve composed with `s ↦ −s`. So

`(⟨D⟩u, ∂ₜu)(−t) = flip of the state of the reflected background at `+t`,

and every forward statement about the state has a backward counterpart.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The velocity flip -/

variable (E) in
/-- The velocity flip of the energy space: it reverses the direction of time in a state. -/
def kgFlip : KGEnergy E →L[ℂ] KGEnergy E :=
  (kgPair E).comp ((kgFst E).prod (-(kgSnd E)))

theorem kgFlip_apply (v : KGEnergy E) : kgFlip E v = kgPair E (v.fst, -v.snd) := rfl

/-- The velocity flip is an isometry. -/
theorem norm_kgFlip_apply (v : KGEnergy E) : ‖kgFlip E v‖ = ‖v‖ := by
  have hL : ‖kgFlip E v‖ ^ (2 : ℕ) = ‖v.fst‖ ^ (2 : ℕ) + ‖v.snd‖ ^ (2 : ℕ) := by
    rw [kgFlip_apply, norm_kgPair_sq, norm_neg]
  have hR : ‖v‖ ^ (2 : ℕ) = ‖v.fst‖ ^ (2 : ℕ) + ‖v.snd‖ ^ (2 : ℕ) := by
    rw [← kgPair_fst_snd v, norm_kgPair_sq, kgPair_fst, kgPair_snd]
  have h1 : (0 : ℝ) ≤ ‖kgFlip E v‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [hL, hR, h1, h2]

/-- The velocity flip is an involution. -/
theorem kgFlip_kgFlip (v : KGEnergy E) : kgFlip E (kgFlip E v) = v := by
  rw [kgFlip_apply, kgFlip_apply, kgPair_fst, kgPair_snd, neg_neg, kgPair_fst_snd]

/-! ## The state reflects -/

section Reflection

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- The reflected background, as a curve. -/
theorem norm_neg_background_le (hWb : ∀ r : ℝ, ‖W r‖ ≤ b) (r : ℝ) : ‖W (-r)‖ ≤ b := hWb (-r)

theorem continuous_neg_background_apply
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (x : Lp ℂ 2 (volume : Measure E)) : Continuous fun r : ℝ => W (-r) x :=
  (hWs x).comp continuous_neg

/-- **The gradient is unchanged by the reflection.** -/
theorem kgFieldGradT_neg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldGradT (fun r : ℝ => W (-r)) g (-h) t = kgFieldGradT W g h (-t) := by
  have hVb : ∀ r : ℝ, ‖W (-r)‖ ≤ b := norm_neg_background_le hWb
  have hVs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W (-r) x :=
    continuous_neg_background_apply hWs
  refine kgFreqInvOp_injective ?_
  rw [kgFreqInvOp_kgFieldGradT hb0 hVb hVs g (-h) t,
    kgFreqInvOp_kgFieldGradT hb0 hWb hWs g h (-t)]
  exact (kgFieldMildT_neg hb0 hWb hWs (kgFreqInvOp g) h t).symm

/-- **The velocity changes sign under the reflection.** -/
theorem kgFieldVelT_neg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldVelT (fun r : ℝ => W (-r)) g (-h) t = -(kgFieldVelT W g h (-t)) := by
  have hVb : ∀ r : ℝ, ‖W (-r)‖ ≤ b := norm_neg_background_le hWb
  have hVs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W (-r) x :=
    continuous_neg_background_apply hWs
  have hR : HasDerivAt (kgFieldMildT (fun r : ℝ => W (-r)) (kgFreqInvOp g) (-h))
      (kgFieldVelT (fun r : ℝ => W (-r)) g (-h) t) t :=
    hasDerivAt_kgFieldMildT hb0 hVb hVs g (-h) t
  have hEq : kgFieldMildT (fun r : ℝ => W (-r)) (kgFreqInvOp g) (-h)
      = fun s : ℝ => kgFieldMildT W (kgFreqInvOp g) h (-s) := by
    funext s
    exact (kgFieldMildT_neg hb0 hWb hWs (kgFreqInvOp g) h s).symm
  rw [hEq] at hR
  have hL0 : HasDerivAt (kgFieldMildT W (kgFreqInvOp g) h) (kgFieldVelT W g h (-t)) (-t) :=
    hasDerivAt_kgFieldMildT hb0 hWb hWs g h (-t)
  have hL : HasDerivAt (fun s : ℝ => kgFieldMildT W (kgFreqInvOp g) h (-s))
      (-(kgFieldVelT W g h (-t))) t := by
    have hcomp := hL0.scomp t (hasDerivAt_neg t)
    have hval : (-1 : ℝ) • kgFieldVelT W g h (-t) = -(kgFieldVelT W g h (-t)) :=
      neg_one_smul ℝ (kgFieldVelT W g h (-t))
    rw [hval] at hcomp
    exact hcomp
  exact hR.unique hL

/-- **The state reflects through the velocity flip.** -/
theorem kgFieldStateT_neg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldStateT W g h (-t)
      = kgFlip E (kgFieldStateT (fun r : ℝ => W (-r)) g (-h) t) := by
  rw [kgFlip_apply, kgFieldStateT, kgFieldStateT, kgPair_fst, kgPair_snd,
    kgFieldGradT_neg hb0 hWb hWs g h t, kgFieldVelT_neg hb0 hWb hWs g h t, neg_neg]

/-- **The energy of the state is unchanged by the reflection.** -/
theorem norm_kgFieldStateT_neg (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (g h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldStateT W g h (-t)‖ = ‖kgFieldStateT (fun r : ℝ => W (-r)) g (-h) t‖ := by
  rw [kgFieldStateT_neg hb0 hWb hWs g h t, norm_kgFlip_apply]

end Reflection

end GaloisForLFunctions.HTGeometry
