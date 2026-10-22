import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandMonodromy
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# The Floquet multipliers

The spectrum of the monodromy is the set of **Floquet multipliers** of a periodically driven field.
Two facts about it follow from the estimate and from the criterion of statement 310, by the single
inequality `‖k‖ⁿ = ‖kⁿ‖ ≤ ‖Mⁿ‖‖1‖` for a spectral value `k`:

* every multiplier lies in the disc `|k| ≤ e^{b|T|}` set by the energy estimate over one period;
* if the clock is stable, every multiplier lies in the **closed unit disc**; contrapositively, a
  multiplier of modulus greater than one produces a datum whose state is unbounded in time.

The second is the Floquet instability criterion: one point of the spectrum outside the unit circle is
enough to break the clock.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Multipliers

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- The identity of the energy space has norm at most one. -/
theorem norm_one_kgEnergy_le :
    ‖(1 : KGEnergy E →L[ℂ] KGEnergy E)‖ ≤ 1 :=
  ContinuousLinearMap.norm_id_le

/-- **The Floquet multipliers lie in the disc set by the energy estimate.** -/
theorem norm_le_of_mem_spectrum_kgMonodromy (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) :
    ‖k‖ ≤ Real.exp (b * |T|) := by
  have hle := spectrum.norm_le_norm_mul_of_mem hk
  have hone := norm_one_kgEnergy_le (E := E)
  have hM := norm_kgMonodromy_le (W := W) (T := T) hb0 hWb hWs
  have hM0 : (0 : ℝ) ≤ ‖kgMonodromy W b hb0 hWb hWs T‖ := norm_nonneg _
  have hstep : ‖kgMonodromy W b hb0 hWb hWs T‖ * ‖(1 : KGEnergy E →L[ℂ] KGEnergy E)‖
      ≤ Real.exp (b * |T|) * 1 :=
    mul_le_mul hM hone (norm_nonneg _) (Real.exp_pos _).le
  rw [mul_one] at hstep
  exact hle.trans hstep

/-- **A power bound confines the multipliers to the closed unit disc.** -/
theorem norm_le_one_of_mem_spectrum_of_pow_bound (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) {C : ℝ}
    (hC : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) : ‖k‖ ≤ 1 := by
  have hpow : ∀ n : ℕ, ‖k‖ ^ n ≤ C := by
    intro n
    have hmem : k ^ n ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T ^ n) :=
      spectrum.pow_mem_pow _ n hk
    have hle := spectrum.norm_le_norm_mul_of_mem hmem
    have hone := norm_one_kgEnergy_le (E := E)
    have hstep : ‖kgMonodromy W b hb0 hWb hWs T ^ n‖
        * ‖(1 : KGEnergy E →L[ℂ] KGEnergy E)‖ ≤ C * 1 :=
      mul_le_mul (hC n) hone (norm_nonneg _) (le_trans (norm_nonneg _) (hC n))
    rw [mul_one] at hstep
    rw [← norm_pow]
    exact hle.trans hstep
  by_contra hlt
  push Not at hlt
  have hdiv : Tendsto (fun n : ℕ => ‖k‖ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlt
  obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop C).exists
  exact absurd (hpow n) (not_le.mpr hn)

/-- A multiplier of modulus greater than one forbids any bound on the powers. -/
theorem not_pow_bounded_of_one_lt_norm_spectrum (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) (hk1 : 1 < ‖k‖) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C := by
  rintro ⟨C, hC⟩
  exact absurd (norm_le_one_of_mem_spectrum_of_pow_bound hb0 hWb hWs hC hk) (not_le.mpr hk1)

/-- **The Floquet instability criterion.** One multiplier outside the closed unit disc produces a
Cauchy datum whose state is unbounded in time: the clock does not keep running. -/
theorem exists_unbounded_of_one_lt_norm_spectrum (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {k : ℂ}
    (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) (hk1 : 1 < ‖k‖) :
    ∃ g h : Lp ℂ 2 (volume : Measure E), ∀ C : ℝ, ∃ t : ℝ,
      0 ≤ t ∧ C < ‖kgFieldStateT W g h t‖ := by
  have hno := not_pow_bounded_of_one_lt_norm_spectrum hb0 hWb hWs hk hk1
  have hiff := kgFloquet_stable_iff hb0 hWb hWs hper hT
  have hneg : ¬ ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖kgFieldStateT W g h t‖ ≤ C := fun hall => hno (hiff.mpr hall)
  push Not at hneg
  obtain ⟨g, h, hgh⟩ := hneg
  exact ⟨g, h, hgh⟩

end Multipliers

end GaloisForLFunctions.HTGeometry
