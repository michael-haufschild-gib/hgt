import GaloisForLFunctions.RHTower.WindowRelation
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import GaloisForLFunctions.RHTower.HorizontalOddFiberCharging
import GaloisForLFunctions.RHTower.CensusProfile
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# The off-line first moment and the census: bridges for the single-input `(L)` constant

* `offLineMoment U = Σ_{box zeros, Im ≤ U} m_ρ (Re ρ − ½)` (monotone, nonnegative);
* `rightHalfOrderSum T = Σ_{strip zeros, 0 < Im ≤ T, Re ≥ ½} m_ρ` and the reflection identity
  `2·rightHalfOrderSum = N + N₀` (from `window_identity`);
* odd fibres are dominated by the critical count, `xiOddFiberCount ≤ xiPosCriticalZeroCount`;
* window comparisons with the ceiling's zero finset `Z` (ζ-zeros in `[½,15/2] × [T₁,T₂]`):
  `rightHalfOrderSum T₂ − rightHalfOrderSum T₁ ≤ Σ_Z m_ρ` and
  `offLineMoment T₂ ≤ offLineMoment T₁ + Σ_Z m_ρ (Re ρ − ½)`.
-/

namespace RHTower

open Complex Finset Set

noncomputable section

/-- The off-line first moment up to height `U`. -/
def offLineMoment (U : ℝ) : ℝ :=
  ∑ z ∈ boxFinsetLe U, ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)

theorem offLineMoment_term_nonneg {U : ℝ} {z : ℂ} (hz : z ∈ boxFinsetLe U) :
    0 ≤ ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2) := by
  rw [mem_boxFinsetLe] at hz
  obtain ⟨h1, _, _, _, _⟩ := hz
  exact mul_nonneg (Nat.cast_nonneg _) (by linarith)

theorem offLineMoment_nonneg (U : ℝ) : 0 ≤ offLineMoment U :=
  Finset.sum_nonneg fun z hz => offLineMoment_term_nonneg hz

theorem offLineMoment_mono {U V : ℝ} (h : U ≤ V) : offLineMoment U ≤ offLineMoment V :=
  Finset.sum_le_sum_of_subset_of_nonneg (boxFinsetLe_mono h)
    (fun z hz _ => offLineMoment_term_nonneg hz)

/-- The right-half order sum including the line: strip zeros with `0 < Im ≤ T`, `Re ≥ ½`. -/
def rightHalfOrderSum (T : ℝ) : ℕ :=
  ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 ≤ z.re), (analyticOrderAt xi z).toNat

theorem lineReflect_mem_stripFinsetPos {T : ℝ} {z : ℂ} (hz : z ∈ stripFinsetPos T) :
    lineReflect z ∈ stripFinsetPos T := by
  rw [stripFinsetPos, Finset.mem_filter] at hz ⊢
  refine ⟨lineReflect_mem_stripFinsetLe hz.1, ?_⟩
  have him : (lineReflect z).im = z.im := by simp [lineReflect]
  rw [him]
  exact hz.2

/-- **`2·Right = N + N₀`.** -/
theorem two_mul_rightHalfOrderSum (T : ℝ) :
    2 * rightHalfOrderSum T = xiPosZeroCount T + xiPosCriticalZeroCount T := by
  classical
  have hid := window_identity (t := stripFinsetPos T)
    (m := fun z => (analyticOrderAt xi z).toNat)
    (fun z hz => lineReflect_mem_stripFinsetPos hz)
    (fun z _ => by simp only [xi_orderAt_lineReflect])
  have hsplit : rightHalfOrderSum T
      = (∑ z ∈ (stripFinsetPos T).filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat)
        + ∑ z ∈ (stripFinsetPos T).filter (fun z => 1 / 2 < z.re),
            (analyticOrderAt xi z).toNat := by
    unfold rightHalfOrderSum
    rw [← Finset.sum_filter_add_sum_filter_not
      ((stripFinsetPos T).filter (fun z => 1 / 2 ≤ z.re)) (fun z => z.re = 1 / 2)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hz, _⟩, heq⟩; exact ⟨hz, heq⟩
      · rintro ⟨hz, heq⟩; exact ⟨⟨hz, heq.symm.le⟩, heq⟩
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hz, hle⟩, hne⟩; exact ⟨hz, lt_of_le_of_ne hle (Ne.symm hne)⟩
      · rintro ⟨hz, hlt⟩; exact ⟨⟨hz, hlt.le⟩, ne_of_gt hlt⟩
  unfold xiPosZeroCount xiPosCriticalZeroCount
  rw [hsplit]
  rw [hid]
  ring

/-- Odd fibres are critical-line zeros counted at least once. -/
theorem xiOddFiberCount_le_xiPosCriticalZeroCount (T : ℝ) :
    xiOddFiberCount T ≤ xiPosCriticalZeroCount T := by
  classical
  unfold xiOddFiberCount xiPosCriticalZeroCount
  calc ((stripFinsetPos T).filter
          (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im))).card
      = ∑ _z ∈ (stripFinsetPos T).filter
          (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)), 1 := by
        rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ z ∈ (stripFinsetPos T).filter
          (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)),
          (analyticOrderAt xi z).toNat := by
        refine Finset.sum_le_sum fun z hz => ?_
        have hzero : xi z = 0 :=
          (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.2.2
        exact Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
    _ ≤ ∑ z ∈ (stripFinsetPos T).filter (fun z => z.re = 1 / 2),
          (analyticOrderAt xi z).toNat := by
        refine Finset.sum_le_sum_of_subset ?_
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2.1⟩

theorem stripFinsetPos_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : stripFinsetPos T₁ ⊆ stripFinsetPos T₂ := by
  intro z hz
  rw [mem_stripFinsetPos] at hz ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  exact ⟨h1, h2, h3, le_trans h4 h, h5⟩

/-- **Window comparison for the count.** Every strip zero with `T₁ < Im ≤ T₂` and `Re ≥ ½` lies in
the ceiling's zero set `Z`, with the same order. -/
theorem rightHalfOrderSum_sub_le_zetaZeroSum {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    (rightHalfOrderSum T₂ : ℝ) - rightHalfOrderSum T₁
      ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
  classical
  set A₁ := (stripFinsetPos T₁).filter (fun z => 1 / 2 ≤ z.re) with hA₁
  set A₂ := (stripFinsetPos T₂).filter (fun z => 1 / 2 ≤ z.re) with hA₂
  have hsub : A₁ ⊆ A₂ := by
    intro z hz
    rw [hA₁, Finset.mem_filter] at hz
    rw [hA₂, Finset.mem_filter]
    exact ⟨stripFinsetPos_mono hT hz.1, hz.2⟩
  have hdiff : (rightHalfOrderSum T₂ : ℝ) - rightHalfOrderSum T₁
      = ∑ z ∈ A₂ \ A₁, ((analyticOrderAt xi z).toNat : ℝ) := by
    unfold rightHalfOrderSum
    rw [← hA₁, ← hA₂]
    have h := Finset.sum_sdiff (f := fun z => ((analyticOrderAt xi z).toNat : ℝ)) hsub
    push_cast
    linarith [h]
  rw [hdiff]
  have hstrip : ∀ z ∈ A₂ \ A₁, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    have hz2 := (Finset.mem_sdiff.mp hz).1
    rw [hA₂, Finset.mem_filter, mem_stripFinsetPos] at hz2
    exact ⟨hz2.1.1, hz2.1.2.1⟩
  have hDZ : A₂ \ A₁ ⊆ Z := by
    intro z hz
    have hz2 := (Finset.mem_sdiff.mp hz).1
    have hz1 := (Finset.mem_sdiff.mp hz).2
    rw [hA₂, Finset.mem_filter, mem_stripFinsetPos] at hz2
    obtain ⟨⟨h1, h2, h3, h4, hxi⟩, hre⟩ := hz2
    have hgt : T₁ < z.im := by
      by_contra hle
      push_neg at hle
      apply hz1
      rw [hA₁, Finset.mem_filter, mem_stripFinsetPos]
      exact ⟨⟨h1, h2, h3, hle, hxi⟩, hre⟩
    rw [hZ]
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]
      exact ⟨hre, by linarith⟩
    · rw [uIcc_of_le hT]
      exact ⟨hgt.le, h4⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip h1 h2).mp hxi
  calc ∑ z ∈ A₂ \ A₁, ((analyticOrderAt xi z).toNat : ℝ)
      = ∑ z ∈ A₂ \ A₁, ((analyticOrderAt riemannZeta z).toNat : ℝ) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip (hstrip z hz)]
    _ ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hDZ (fun _ _ _ => Nat.cast_nonneg _)

/-- **Window comparison for the moment.** -/
theorem offLineMoment_le_add_zetaZeroMoment {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) :
    offLineMoment T₂ ≤ offLineMoment T₁
      + ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
  classical
  have hsub : boxFinsetLe T₁ ⊆ boxFinsetLe T₂ := boxFinsetLe_mono hT
  have hdiff := Finset.sum_sdiff
    (f := fun z => ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)) hsub
  unfold offLineMoment
  rw [← hdiff]
  have hDZ : boxFinsetLe T₂ \ boxFinsetLe T₁ ⊆ Z := by
    intro z hz
    have hz2 := (Finset.mem_sdiff.mp hz).1
    have hz1 := (Finset.mem_sdiff.mp hz).2
    rw [mem_boxFinsetLe] at hz2
    obtain ⟨h1, h2, h3, h4, hxi⟩ := hz2
    have hgt : T₁ < z.im := by
      by_contra hle
      push_neg at hle
      apply hz1
      rw [mem_boxFinsetLe]
      exact ⟨h1, h2, h3, hle, hxi⟩
    rw [hZ]
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)]
      exact ⟨h1.le, by linarith⟩
    · rw [uIcc_of_le hT]
      exact ⟨hgt.le, h4⟩
    · exact (xi_zero_iff_zeta_zero_of_mem_strip (by linarith) h2).mp hxi
  have hZnonneg : ∀ w ∈ Z, 0 ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hstrip : ∀ z ∈ boxFinsetLe T₂ \ boxFinsetLe T₁, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    have hz2 := (Finset.mem_sdiff.mp hz).1
    rw [mem_boxFinsetLe] at hz2
    exact ⟨by linarith [hz2.1], hz2.2.1⟩
  have hle : ∑ z ∈ boxFinsetLe T₂ \ boxFinsetLe T₁,
        ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)
      ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    calc ∑ z ∈ boxFinsetLe T₂ \ boxFinsetLe T₁,
          ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)
        = ∑ z ∈ boxFinsetLe T₂ \ boxFinsetLe T₁,
            ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - 1 / 2) := by
          refine Finset.sum_congr rfl fun z hz => ?_
          rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip (hstrip z hz)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hDZ (fun w hw _ => hZnonneg w hw)
  linarith

end

end RHTower
