import GaloisForLFunctions.HTGeometry.KleinGordonStateReflection

/-!
# Deciding oscillation on a band

Statement 324 transfers a bound on the powers of the band monodromies to the true one, but only
forwards in time: the state estimate it rests on is proved for `t ≥ 0`. The oscillatory criterion of
statement 349 needs both directions.

The reflection of statements 352–355 supplies the other one, and in a sharp form: the monodromy over
`−T` is the **flip conjugate** of the monodromy of the reflected background over `+T`,

`M_W(−T) = F ∘ M_{W(−·)}(T) ∘ F`,   `F` the velocity flip,

so its powers have exactly the same norms, and the forward transfer applied to `W(−·)` bounds them.
With both bounds statement 349 applies:

**a clock whose band models are power bounded in both directions, uniformly in the cut-off, has all of
its Floquet multipliers on the unit circle** — oscillation, like stability, can be decided on the band
models.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Backward

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The backward monodromy is the flip conjugate of the reflected forward one.** -/
theorem kgMonodromy_neg_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (v : KGEnergy E) :
    kgMonodromy W b hb0 hWb hWs (-T) v
      = kgFlip E (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T (kgFlip E v)) := by
  have hstate := kgFieldStateT_neg hb0 hWb hWs v.fst v.snd T
  have hfst : (kgFlip E v).fst = v.fst := rfl
  have hsnd : (kgFlip E v).snd = -v.snd := rfl
  show kgFieldStateT W v.fst v.snd (-T)
    = kgFlip E (kgFieldStateT (fun r : ℝ => W (-r)) (kgFlip E v).fst (kgFlip E v).snd T)
  rw [hfst, hsnd, hstate]

/-- Every power of the backward monodromy is the flip conjugate of the corresponding power. -/
theorem kgMonodromy_neg_pow_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (n : ℕ) (v : KGEnergy E) :
    (kgMonodromy W b hb0 hWb hWs (-T) ^ n) v
      = kgFlip E ((kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T ^ n) (kgFlip E v)) := by
  induction n generalizing v with
  | zero =>
      have h1 : (kgMonodromy W b hb0 hWb hWs (-T) ^ (0 : ℕ)) v = v := by
        rw [pow_zero]
        rfl
      have h2 : ((kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T) ^ (0 : ℕ)) (kgFlip E v) = kgFlip E v := by
        rw [pow_zero]
        rfl
      rw [h1, h2, kgFlip_kgFlip]
  | succ n ih =>
      have hstepA : (kgMonodromy W b hb0 hWb hWs (-T) ^ (n + 1)) v
          = (kgMonodromy W b hb0 hWb hWs (-T) ^ n)
            (kgMonodromy W b hb0 hWb hWs (-T) v) := by
        rw [pow_succ]
        rfl
      have hstepB : ∀ x : KGEnergy E,
          (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
              (continuous_neg_background_apply hWs) T ^ (n + 1)) x
            = (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
                (continuous_neg_background_apply hWs) T ^ n)
              (kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
                (continuous_neg_background_apply hWs) T x) := by
        intro x
        rw [pow_succ]
        rfl
      rw [hstepA, ih, kgMonodromy_neg_apply hb0 hWb hWs v, kgFlip_kgFlip, hstepB]

/-- **The backward powers have the same norms as the reflected forward ones.** -/
theorem norm_kgMonodromy_neg_pow_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (n : ℕ) :
    ‖kgMonodromy W b hb0 hWb hWs (-T) ^ n‖
      ≤ ‖kgMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
          (continuous_neg_background_apply hWs) T ^ n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [kgMonodromy_neg_pow_apply hb0 hWb hWs n v, norm_kgFlip_apply]
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  rw [norm_kgFlip_apply]

end Backward

/-! ## Oscillation from the band models -/

section BandOscillatory

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **The backward transfer.** A bound on the powers of the band monodromies of the reflected
background bounds the powers of the backward monodromy. -/
theorem norm_kgMonodromy_neg_pow_le_of_band_bound (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (hT : 0 ≤ T)
    {C : ℝ} (hC : ∀ R : ℝ, ∀ n : ℕ,
      ‖kgBandMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
        (continuous_neg_background_apply hWs) R T ^ n‖ ≤ C) (n : ℕ) :
    ‖kgMonodromy W b hb0 hWb hWs (-T) ^ n‖ ≤ C := by
  refine (norm_kgMonodromy_neg_pow_le hb0 hWb hWs n).trans ?_
  exact norm_kgMonodromy_pow_le_of_band_bound hb0 (norm_neg_background_le hWb)
    (continuous_neg_background_apply hWs) hT hC n

/-- **Oscillation can be decided on the band models.** If the band monodromies of the background and
of its reflection have powers bounded uniformly in the cut-off, every Floquet multiplier of the clock
lies on the unit circle. -/
theorem norm_eq_one_of_mem_spectrum_of_band_bounds (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 ≤ T) {C C' : ℝ}
    (hC : ∀ R : ℝ, ∀ n : ℕ, ‖kgBandMonodromy W b hb0 hWb hWs R T ^ n‖ ≤ C)
    (hC' : ∀ R : ℝ, ∀ n : ℕ,
      ‖kgBandMonodromy (fun r : ℝ => W (-r)) b hb0 (norm_neg_background_le hWb)
        (continuous_neg_background_apply hWs) R T ^ n‖ ≤ C')
    {k : ℂ} (hk : k ∈ spectrum ℂ (kgMonodromy W b hb0 hWb hWs T)) : ‖k‖ = 1 := by
  have hab : kgMonodromy W b hb0 hWb hWs T * kgMonodromy W b hb0 hWb hWs (-T) = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_right_inverse hb0 hWb hWs hper v
  have hba : kgMonodromy W b hb0 hWb hWs (-T) * kgMonodromy W b hb0 hWb hWs T = 1 := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_left_inverse hb0 hWb hWs hper v
  have hfwd : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C := fun n =>
    norm_kgMonodromy_pow_le_of_band_bound hb0 hWb hWs hT hC n
  have hbwd : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs (-T) ^ n‖ ≤ C' := fun n =>
    norm_kgMonodromy_neg_pow_le_of_band_bound hb0 hWb hWs hT hC' n
  exact norm_eq_one_of_mem_spectrum_of_inverse (le_of_eq norm_one_kgEnergy) hab hba hfwd hbwd hk

end BandOscillatory

end GaloisForLFunctions.HTGeometry
