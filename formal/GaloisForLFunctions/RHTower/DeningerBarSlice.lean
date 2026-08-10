import GaloisForLFunctions.RHTower.DeningerBarInsert

/-!
# Length slices of the entire word-height bar source

A weighted word series splits along word length, and unit insertion at a fixed position compares
one length slice with the next: it preserves the product of the letter heights, multiplies the
length weight by `R`, and is injective.  This is the only analytic mechanism the bar faces and
the extra degeneracy need.

* `deningerBarWeightR`, `deningerBarSliceR` : the two-parameter weight and its length slices.
* `deningerBarSeminormR_eq_tsum_slice` : the series splits along length.
* `deningerBarInsert_slice_le` : **unit insertion costs one factor `R`.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The two-parameter word weight `R^{|w|} h(w)^k`. -/
def deningerBarWeightR (k : ℕ) (R : ℝ) (w : DeningerBarWord) : ℝ :=
  R ^ deningerBarLength w * deningerBarHeight w ^ k

theorem deningerBarWeightR_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (w : DeningerBarWord) :
    0 ≤ deningerBarWeightR k R w :=
  mul_nonneg (pow_nonneg hR _) (pow_nonneg (deningerBarHeight_pos w).le _)

theorem deningerBarSeminormR_eq (k : ℕ) (R : ℝ) (c : DeningerBarKothe) :
    deningerBarSeminormR k R c
      = ∑' w, deningerBarWeightR k R w * ‖(c : DeningerBarWord → ℂ) w‖ := rfl

theorem deningerBarWeightR_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    Summable fun w => deningerBarWeightR k R w * ‖(c : DeningerBarWord → ℂ) w‖ :=
  deningerBarSeminormR_summable hR c

/-- Unit insertion multiplies the two-parameter weight by `R`. -/
theorem deningerBarWeightR_insert (k : ℕ) (R : ℝ) {r : ℕ} (t : Fin (r + 2))
    (f : Fin (r + 1) → DeningerPrimeLattice) :
    deningerBarWeightR k R (deningerInsertUnitWord t f)
      = R * deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) := by
  rw [deningerBarWeightR, deningerBarWeightR, deningerInsertUnitWord_height,
    deningerInsertUnitWord_length, pow_succ]
  ring

/-- The length-`r` slice of a weighted word series. -/
def deningerBarSliceR (k : ℕ) (R : ℝ) (c : DeningerBarWord → ℂ) (r : ℕ) : ℝ :=
  ∑' f : Fin (r + 1) → DeningerPrimeLattice,
    deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) * ‖c (⟨r, f⟩ : DeningerBarWord)‖

theorem deningerBarSlice_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe)
    (r : ℕ) :
    Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖(c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖ :=
  ((summable_sigma_of_nonneg
    (fun w => mul_nonneg (deningerBarWeightR_nonneg k (by linarith) w) (norm_nonneg _))).mp
      (deningerBarWeightR_summable hR c)).1 r

theorem deningerBarSliceR_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    Summable (deningerBarSliceR k R (c : DeningerBarWord → ℂ)) :=
  ((summable_sigma_of_nonneg
    (fun w => mul_nonneg (deningerBarWeightR_nonneg k (by linarith) w) (norm_nonneg _))).mp
      (deningerBarWeightR_summable hR c)).2

theorem deningerBarSliceR_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) (c : DeningerBarWord → ℂ)
    (r : ℕ) : 0 ≤ deningerBarSliceR k R c r :=
  tsum_nonneg fun _ => mul_nonneg (deningerBarWeightR_nonneg k hR _) (norm_nonneg _)

theorem deningerBarSeminormR_eq_tsum_slice {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerBarKothe) :
    deningerBarSeminormR k R c
      = ∑' r, deningerBarSliceR k R (c : DeningerBarWord → ℂ) r :=
  (deningerBarWeightR_summable hR c).tsum_sigma

/-- **Unit insertion costs one factor `R`.**  Weighting the source length and pulling back along
the insertion at a fixed position is bounded by the next length slice divided by `R`. -/
theorem deningerBarInsert_slice_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe)
    (r : ℕ) (t : Fin (r + 2)) :
    (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖)
      ≤ R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hcomp : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (deningerInsertUnitWord t f) *
        ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖ :=
    (deningerBarSlice_summable hR c (r + 1)).comp_injective
      (deningerInsertUnit_injective t)
  have hsum : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖ := by
    refine (hcomp.mul_left R⁻¹).congr fun f => ?_
    rw [deningerBarWeightR_insert]
    field_simp
  have hle : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (deningerInsertUnitWord t f) *
          ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖)
      ≤ deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1) := by
    refine Summable.tsum_le_tsum_of_inj
      (deningerInsertUnit (r := r) t) (deningerInsertUnit_injective t) ?_ ?_ hcomp
      (deningerBarSlice_summable hR c (r + 1))
    · intro g _
      exact mul_nonneg (deningerBarWeightR_nonneg k hRpos.le _) (norm_nonneg _)
    · intro f
      exact le_of_eq rfl
  have hrewrite : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖)
      = R⁻¹ * ∑' f : Fin (r + 1) → DeningerPrimeLattice,
          deningerBarWeightR k R (deningerInsertUnitWord t f) *
            ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖ := by
    rw [← Summable.tsum_mul_left _ hcomp]
    refine tsum_congr fun f => ?_
    rw [deningerBarWeightR_insert]
    field_simp
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end RHTower
