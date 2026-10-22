import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonMonodromy
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# When is a periodically driven clock stable?

The monodromy is invertible: running the evolution over one period backwards is the evolution of the
same equation over the period `-T`, because a periodic background is periodic in both directions. So
the period map is a linear homeomorphism of the energy space, with both norms bounded by `e^{b|T|}`.

That makes the long-time question a question about the powers of one operator, and it is decided by
them:

* if `sup_n‖Mⁿ‖ < ∞` the state is bounded at *every* time, not only at the multiples of the period —
  the leftover piece of time is shorter than one period and costs at most one factor `e^{bT}`;
* conversely, if every solution's state stays bounded along the periods, the powers are uniformly
  bounded, by the uniform boundedness principle on the energy space.

So a periodically driven clock is stable exactly when its monodromy has bounded powers.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Invertible

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- A periodic background is periodic backwards as well. -/
theorem periodic_neg (hper : ∀ r : ℝ, W (r + T) = W r) (r : ℝ) : W (r + -T) = W r := by
  have h := hper (r + -T)
  rw [add_assoc, neg_add_cancel, add_zero] at h
  exact h.symm

/-- **Running one period backwards undoes it.** -/
theorem kgPeriodMap_left_inverse (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (v : KGEnergy E) :
    kgPeriodMap W (-T) (kgPeriodMap W T v) = v := by
  have hshift : (fun ρ : ℝ => W (ρ + T)) = W := funext hper
  have hrestart := kgFieldStateT_restart hb0 hWb hWs v.fst v.snd (-T) T
  rw [hshift, neg_add_cancel, kgFieldStateT_zero, kgPair_fst_snd] at hrestart
  exact hrestart.symm

/-- **Running one period forwards undoes running it backwards.** -/
theorem kgPeriodMap_right_inverse (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (v : KGEnergy E) :
    kgPeriodMap W T (kgPeriodMap W (-T) v) = v := by
  have hshift : (fun ρ : ℝ => W (ρ + -T)) = W := funext (periodic_neg hper)
  have hrestart := kgFieldStateT_restart hb0 hWb hWs v.fst v.snd T (-T)
  rw [hshift, add_neg_cancel, kgFieldStateT_zero, kgPair_fst_snd] at hrestart
  exact hrestart.symm

/-- **The monodromy is a linear homeomorphism of the energy space.** -/
def kgMonodromyEquiv (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (b : ℝ) (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) (T : ℝ)
    (hper : ∀ r : ℝ, W (r + T) = W r) : KGEnergy E ≃L[ℂ] KGEnergy E :=
  ContinuousLinearEquiv.equivOfInverse (kgMonodromy W b hb0 hWb hWs T)
    (kgMonodromy W b hb0 hWb hWs (-T)) (kgPeriodMap_left_inverse hb0 hWb hWs hper)
    (kgPeriodMap_right_inverse hb0 hWb hWs hper)

theorem kgMonodromyEquiv_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (v : KGEnergy E) :
    kgMonodromyEquiv W b hb0 hWb hWs T hper v = kgPeriodMap W T v := rfl

theorem kgMonodromyEquiv_symm_apply (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (v : KGEnergy E) :
    (kgMonodromyEquiv W b hb0 hWb hWs T hper).symm v = kgPeriodMap W (-T) v := rfl

/-- Both the monodromy and its inverse obey the sharp bound over one period. -/
theorem norm_kgMonodromy_neg_le (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x) :
    ‖kgMonodromy W b hb0 hWb hWs (-T)‖ ≤ Real.exp (b * |T|) := by
  have h := norm_kgMonodromy_le (W := W) (T := -T) hb0 hWb hWs
  rwa [abs_neg] at h

end Invertible

/-! ## Stability -/

section Stability

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b T : ℝ}

/-- **Bounded powers give stability at every time.** The leftover piece of time is shorter than one
period, so it costs at most one factor `e^{bT}` beyond the bound on the powers. -/
theorem norm_kgFieldStateT_le_of_pow_bound_all (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) {C : ℝ}
    (hC : ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C)
    (g h : Lp ℂ 2 (volume : Measure E)) {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldStateT W g h t‖ ≤ C * ‖kgPair E (g, h)‖ * Real.exp (b * T) := by
  set n : ℕ := ⌊t / T⌋₊ with hndef
  have hdiv0 : (0 : ℝ) ≤ t / T := div_nonneg ht hT.le
  have hnle : (n : ℝ) ≤ t / T := Nat.floor_le hdiv0
  have hnlt : t / T < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnT : (n : ℝ) * T ≤ t := by
    have := mul_le_mul_of_nonneg_right hnle hT.le
    rwa [div_mul_cancel₀ _ hT.ne'] at this
  have hltT : t < ((n : ℝ) + 1) * T := by
    have := mul_lt_mul_of_pos_right hnlt hT
    rwa [div_mul_cancel₀ _ hT.ne'] at this
  set r : ℝ := t - (n : ℝ) * T with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrT : r ≤ T := by rw [hrdef]; nlinarith
  have hsplit : t = r + (n : ℝ) * T := by rw [hrdef]; ring
  have hshift : (fun ρ : ℝ => W (ρ + (n : ℝ) * T)) = W :=
    funext (periodic_shift_nat hper n)
  have hrestart := kgFieldStateT_restart hb0 hWb hWs g h r ((n : ℝ) * T)
  rw [hshift] at hrestart
  have hstate : kgPair E (kgFieldGradT W g h ((n : ℝ) * T), kgFieldVelT W g h ((n : ℝ) * T))
      = kgFieldStateT W g h ((n : ℝ) * T) := rfl
  have hstep : ‖kgFieldStateT W (kgFieldGradT W g h ((n : ℝ) * T))
        (kgFieldVelT W g h ((n : ℝ) * T)) r‖
      ≤ ‖kgFieldStateT W g h ((n : ℝ) * T)‖ * Real.exp (b * |r|) := by
    rw [kgFieldStateT_eq_kgStateMildT hb0 hWb hWs, ← hstate]
    exact norm_kgStateMildT_le hb0 hWb hWs _ _ r
  have hper' : ‖kgFieldStateT W g h ((n : ℝ) * T)‖ ≤ C * ‖kgPair E (g, h)‖ :=
    norm_kgFieldStateT_le_of_pow_bound hb0 hWb hWs hper hC g h n
  have hexp : Real.exp (b * |r|) ≤ Real.exp (b * T) := by
    rw [abs_of_nonneg hr0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrT hb0)
  have hC0 : (0 : ℝ) ≤ C * ‖kgPair E (g, h)‖ :=
    le_trans (norm_nonneg _) hper'
  rw [hsplit, hrestart]
  refine hstep.trans ?_
  exact mul_le_mul hper' hexp (Real.exp_pos _).le hC0

/-- **Bounded orbits give bounded powers.** The uniform boundedness principle on the energy space,
which is complete. -/
theorem exists_pow_bound_of_orbits_bounded (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (horb : ∀ v : KGEnergy E, ∃ C : ℝ, ∀ n : ℕ,
      ‖(kgMonodromy W b hb0 hWb hWs T ^ n) v‖ ≤ C) :
    ∃ C : ℝ, ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C :=
  banach_steinhaus (g := fun n : ℕ => kgMonodromy W b hb0 hWb hWs T ^ n) horb

/-- **The stability criterion for a periodically driven clock.** The state stays bounded at every
time, for every datum, exactly when the powers of the monodromy are uniformly bounded. -/
theorem kgFloquet_stable_iff (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W r x)
    (hper : ∀ r : ℝ, W (r + T) = W r) (hT : 0 < T) :
    (∃ C : ℝ, ∀ n : ℕ, ‖kgMonodromy W b hb0 hWb hWs T ^ n‖ ≤ C)
      ↔ ∀ g h : Lp ℂ 2 (volume : Measure E), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
          ‖kgFieldStateT W g h t‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩ g h
    refine ⟨C * ‖kgPair E (g, h)‖ * Real.exp (b * T), fun t ht => ?_⟩
    exact norm_kgFieldStateT_le_of_pow_bound_all hb0 hWb hWs hper hT hC g h ht
  · intro hbdd
    refine exists_pow_bound_of_orbits_bounded hb0 hWb hWs fun v => ?_
    obtain ⟨C, hC⟩ := hbdd v.fst v.snd
    refine ⟨C, fun n => ?_⟩
    have hnT : (0 : ℝ) ≤ (n : ℝ) * T := by positivity
    have hval : (kgMonodromy W b hb0 hWb hWs T ^ n) v
        = kgFieldStateT W v.fst v.snd ((n : ℝ) * T) := by
      rw [kgFieldStateT_monodromy_pow hb0 hWb hWs hper v.fst v.snd n, kgPair_fst_snd]
    rw [hval]
    exact hC _ hnT

end Stability

end GaloisForLFunctions.HTGeometry
