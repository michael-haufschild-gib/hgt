import GaloisForLFunctions.HTGeometry.KleinGordonBandOscillatory

/-!
# Time reversal inverts the Floquet multipliers

The backward monodromy is the flip conjugate of the reflected background's forward one (statement
356), and the flip is an involution, hence a unit of the operator algebra. Conjugation by a unit does
not move the spectrum, so

`σ(M_W(−T)) = σ(M_{W(−·)}(T))`.

For a periodic background the backward monodromy is the inverse of the forward one, and the spectrum
of an inverse is the inverse of the spectrum. Putting the two together:

`σ(M_{W(−·)}(T)) = σ(M_W(T))⁻¹`.

**Reversing time inverts the Floquet multipliers.** A mode that grows by a factor `k` per period in
one direction of time decays by exactly that factor in the other — the spectral form of the
reversibility of the equation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The flip is a unit -/

theorem kgFlip_mul_self : kgFlip E * kgFlip E = 1 :=
  ContinuousLinearMap.ext fun v => kgFlip_kgFlip v

variable (E) in
/-- The velocity flip, as a unit of the operator algebra. -/
def kgFlipUnit : (KGEnergy E →L[ℂ] KGEnergy E)ˣ :=
  ⟨kgFlip E, kgFlip E, kgFlip_mul_self, kgFlip_mul_self⟩

theorem kgFlipUnit_val : ((kgFlipUnit E : (KGEnergy E →L[ℂ] KGEnergy E)ˣ) :
    KGEnergy E →L[ℂ] KGEnergy E) = kgFlip E := rfl

theorem kgFlipUnit_inv_val : (((kgFlipUnit E)⁻¹ : (KGEnergy E →L[ℂ] KGEnergy E)ˣ) :
    KGEnergy E →L[ℂ] KGEnergy E) = kgFlip E := rfl

/-! ## The spectrum under time reversal -/

section Reversal

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The backward monodromy is a flip conjugate**, as an identity of operators. -/
theorem kgMonodromy_neg_eq_conj (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    kgMonodromy W b hb0 hWb hWs (-T)
      = kgFlip E * kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T * kgFlip E :=
  ContinuousLinearMap.ext fun v => kgMonodromy_neg_apply hb0 hWb hWs v

/-- **Conjugating by the flip does not move the spectrum.** -/
theorem spectrum_kgMonodromy_neg_eq (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    spectrum ℂ (kgMonodromy W b hb0 hWb hWs (-T))
      = spectrum ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T) := by
  rw [kgMonodromy_neg_eq_conj hb0 hWb hWs]
  have hconj := spectrum.units_conjugate (R := ℂ)
    (a := kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
      (continuous_neg_background_apply hWs) T) (u := kgFlipUnit E)
  rw [kgFlipUnit_val, kgFlipUnit_inv_val] at hconj
  exact hconj

/-- **Time reversal inverts the Floquet multipliers.** -/
theorem spectrum_kgMonodromy_reflected (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) :
    spectrum ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
        (continuous_neg_background_apply hWs) T)
      = (spectrum ℂ (kgMonodromy W b hb0 hWb hWs T))⁻¹ := by
  have hab : kgMonodromy W b hb0 hWb hWs T * kgMonodromy W b hb0 hWb hWs (-T) = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_right_inverse hb0 hWb hWs hper v
  have hba : kgMonodromy W b hb0 hWb hWs (-T) * kgMonodromy W b hb0 hWb hWs T = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_left_inverse hb0 hWb hWs hper v
  set u : (KGEnergy E →L[ℂ] KGEnergy E)ˣ :=
    ⟨kgMonodromy W b hb0 hWb hWs T, kgMonodromy W b hb0 hWb hWs (-T), hab, hba⟩ with hudef
  have hval : ((u : (KGEnergy E →L[ℂ] KGEnergy E)ˣ) : KGEnergy E →L[ℂ] KGEnergy E)
      = kgMonodromy W b hb0 hWb hWs T := rfl
  have hvalinv : (((u⁻¹ : (KGEnergy E →L[ℂ] KGEnergy E)ˣ)) : KGEnergy E →L[ℂ] KGEnergy E)
      = kgMonodromy W b hb0 hWb hWs (-T) := rfl
  have hmap := spectrum.map_inv (𝕜 := ℂ) u
  rw [hval, hvalinv] at hmap
  rw [← spectrum_kgMonodromy_neg_eq hb0 hWb hWs, ← hmap]

/-- **The multipliers of the reflected clock are the reciprocals of the original's.** -/
theorem mem_spectrum_reflected_iff (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (k : ℂ) :
    k ∈ spectrum ℂ (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
        (continuous_neg_background_apply hWs) T)
      ↔ k⁻¹ ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T) := by
  rw [spectrum_kgMonodromy_reflected hb0 hWb hWs hper, Set.mem_inv]

end Reversal

end GaloisForLFunctions.HTGeometry
