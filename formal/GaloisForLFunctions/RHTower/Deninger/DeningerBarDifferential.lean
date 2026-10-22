import GaloisForLFunctions.RHTower.Deninger.DeningerBarSlice

/-!
# The bar differential of the entire word-height source

The two-term Milnor algebra has the zero letter as its unit and kills the product of two nonunit
letters, so the fibre of the `j`-th bar face over a word consists of the two unit insertions at
positions `j` and `j+1` — one word when the merged letter is itself the unit.  Summing the fibres
with the simplicial signs gives the bar differential on coefficients.

Every face decreases the length by one and preserves the product of the letter heights, so a word
of length `r` receives at most `r - 1` faces; the elementary bound `2(r+1)R^{r+1} ≤ (2R)^{r+2}`
absorbs that growth into a doubling of the exponential length weight:

`P_{k,R}(bc) ≤ P_{k,2R}(c)`.

* `deningerBarDiffCoe` : the differential on coefficients.
* `deningerBarDiff` : the differential as a linear map of the source.
* `deningerBarSeminormR_diff_le` : **the doubling estimate.**
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-! ## The differential -/

/-- The fibre of the `j`-th bar face: the two unit insertions, which coincide exactly when the
merged letter is the unit. -/
def deningerBarFibreSum (c : DeningerBarWord → ℂ) {s : ℕ}
    (f : Fin (s + 1) → DeningerPrimeLattice) (j : Fin (s + 1)) : ℂ :=
  if f j = 0 then c (deningerInsertUnitWord j.castSucc f)
  else c (deningerInsertUnitWord j.castSucc f) + c (deningerInsertUnitWord j.succ f)

/-- **The bar differential on coefficients.** -/
def deningerBarDiffCoe (c : DeningerBarWord → ℂ) : DeningerBarWord → ℂ :=
  fun w => ∑ j : Fin (w.1 + 1), (-1 : ℂ) ^ (j : ℕ) * deningerBarFibreSum c w.2 j

theorem deningerBarFibreSum_norm_le (c : DeningerBarWord → ℂ) {s : ℕ}
    (f : Fin (s + 1) → DeningerPrimeLattice) (j : Fin (s + 1)) :
    ‖deningerBarFibreSum c f j‖
      ≤ ‖c (deningerInsertUnitWord j.castSucc f)‖ +
        ‖c (deningerInsertUnitWord j.succ f)‖ := by
  rw [deningerBarFibreSum]
  by_cases h : f j = 0
  · rw [if_pos h]
    have := norm_nonneg (c (deningerInsertUnitWord j.succ f))
    linarith
  · rw [if_neg h]
    exact norm_add_le _ _

theorem deningerBarDiffCoe_norm_le (c : DeningerBarWord → ℂ) (w : DeningerBarWord) :
    ‖deningerBarDiffCoe c w‖
      ≤ ∑ j : Fin (w.1 + 1),
          (‖c (deningerInsertUnitWord j.castSucc w.2)‖ +
            ‖c (deningerInsertUnitWord j.succ w.2)‖) := by
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact deningerBarFibreSum_norm_le c w.2 j

/-! ## The doubling estimate -/

private theorem deningerBar_face_growth {R : ℝ} (hR : 1 ≤ R) (r : ℕ) :
    2 * ((r : ℝ) + 1) * R ^ (r + 1) ≤ (2 * R) ^ (r + 2) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hpow : R ^ (r + 1) ≤ R ^ (r + 2) := pow_le_pow_right₀ hR (Nat.le_succ _)
  have hcount : ((r : ℝ) + 1) ≤ 2 ^ (r + 1) := by
    have hnat : r + 1 ≤ 2 ^ (r + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    linarith
  have hposR : (0 : ℝ) ≤ R ^ (r + 1) := by positivity
  calc 2 * ((r : ℝ) + 1) * R ^ (r + 1)
      ≤ 2 * (2 ^ (r + 1) : ℝ) * R ^ (r + 1) := by nlinarith
    _ = (2 : ℝ) ^ (r + 2) * R ^ (r + 1) := by ring
    _ ≤ (2 : ℝ) ^ (r + 2) * R ^ (r + 2) := by
        refine mul_le_mul_of_nonneg_left hpow ?_
        positivity
    _ = (2 * R) ^ (r + 2) := by rw [mul_pow]

private theorem deningerBarDiff_slice_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerBarKothe) (r : ℕ) :
    (Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖) ∧
      (∑' f : Fin (r + 1) → DeningerPrimeLattice,
          deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
            ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
        ≤ deningerBarSliceR k (2 * R) (c : DeningerBarWord → ℂ) (r + 1) := by
  classical
  have hRpos : (0 : ℝ) < R := by linarith
  have h2R : (1 : ℝ) ≤ 2 * R := by linarith
  -- the two families of insertions
  have hins : ∀ t : Fin (r + 2), Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖ := by
    intro t
    have hcomp : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
        deningerBarWeightR k R (deningerInsertUnitWord t f) *
          ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord t f)‖ :=
      (deningerBarSlice_summable hR c (r + 1)).comp_injective
        (deningerInsertUnit_injective t)
    refine (hcomp.mul_left R⁻¹).congr fun f => ?_
    rw [deningerBarWeightR_insert]
    field_simp
  -- the majorant
  set G : Fin (r + 1) → (Fin (r + 1) → DeningerPrimeLattice) → ℝ := fun j f =>
    deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
      (‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.castSucc f)‖ +
        ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.succ f)‖) with hG
  have hGsummable : ∀ j : Fin (r + 1), Summable (G j) := by
    intro j
    refine ((hins j.castSucc).add (hins j.succ)).congr fun f => ?_
    rw [hG]
    ring
  have hmaj : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      ∑ j : Fin (r + 1), G j f :=
    summable_sum fun j _ => hGsummable j
  have hpointwise : ∀ f : Fin (r + 1) → DeningerPrimeLattice,
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖
        ≤ ∑ j : Fin (r + 1), G j f := by
    intro f
    have hb := deningerBarDiffCoe_norm_le (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)
    have hwnn : 0 ≤ deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) :=
      deningerBarWeightR_nonneg k hRpos.le _
    calc deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖
        ≤ deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
            ∑ j : Fin (r + 1),
              (‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.castSucc f)‖ +
                ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.succ f)‖) :=
          mul_le_mul_of_nonneg_left hb hwnn
      _ = ∑ j : Fin (r + 1), G j f := by
          rw [Finset.mul_sum]
  have hsummable : Summable fun f : Fin (r + 1) → DeningerPrimeLattice =>
      deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
        ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖ :=
    Summable.of_nonneg_of_le
      (fun f => mul_nonneg (deningerBarWeightR_nonneg k hRpos.le _) (norm_nonneg _))
      hpointwise hmaj
  refine ⟨hsummable, ?_⟩
  have hstep1 : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
      ≤ ∑' f : Fin (r + 1) → DeningerPrimeLattice, ∑ j : Fin (r + 1), G j f :=
    Summable.tsum_le_tsum hpointwise hsummable hmaj
  have hswap : (∑' f : Fin (r + 1) → DeningerPrimeLattice, ∑ j : Fin (r + 1), G j f)
      = ∑ j : Fin (r + 1), ∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f :=
    Summable.tsum_finsetSum fun j _ => hGsummable j
  have hslicebound : ∀ j : Fin (r + 1),
      (∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f)
        ≤ 2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1)) := by
    intro j
    have hsplit : (∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f)
        = (∑' f : Fin (r + 1) → DeningerPrimeLattice,
            deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
              ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.castSucc f)‖)
          + ∑' f : Fin (r + 1) → DeningerPrimeLattice,
            deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
              ‖(c : DeningerBarWord → ℂ) (deningerInsertUnitWord j.succ f)‖ := by
      rw [← Summable.tsum_add (hins j.castSucc) (hins j.succ)]
      refine tsum_congr fun f => ?_
      rw [hG]
      ring
    rw [hsplit]
    have h1 := deningerBarInsert_slice_le (k := k) hR c r j.castSucc
    have h2 := deningerBarInsert_slice_le (k := k) hR c r j.succ
    linarith
  have hfinal : (∑ j : Fin (r + 1), ∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f)
      ≤ ((r : ℝ) + 1) * (2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1))) := by
    have hcard : (Finset.univ : Finset (Fin (r + 1))).card = r + 1 := by simp
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (r + 1)))
      (fun j => ∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f)
      (2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1)))
      (fun j _ => hslicebound j)
    rw [hcard, nsmul_eq_mul] at this
    push_cast at this
    linarith
  have hgrow : ((r : ℝ) + 1) * (2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1)))
      ≤ deningerBarSliceR k (2 * R) (c : DeningerBarWord → ℂ) (r + 1) := by
    have hHnn : ∀ g : Fin (r + 2) → DeningerPrimeLattice,
        (0 : ℝ) ≤ deningerBarHeight (⟨r + 1, g⟩ : DeningerBarWord) ^ k :=
      fun g => pow_nonneg (deningerBarHeight_pos _).le _
    have hMle : ∀ g : Fin (r + 2) → DeningerPrimeLattice,
        (2 * ((r : ℝ) + 1) * R ^ (r + 1) *
            deningerBarHeight (⟨r + 1, g⟩ : DeningerBarWord) ^ k) *
              ‖(c : DeningerBarWord → ℂ) (⟨r + 1, g⟩ : DeningerBarWord)‖
          ≤ deningerBarWeightR k (2 * R) (⟨r + 1, g⟩ : DeningerBarWord) *
              ‖(c : DeningerBarWord → ℂ) (⟨r + 1, g⟩ : DeningerBarWord)‖ := by
      intro g
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hlen : deningerBarLength (⟨r + 1, g⟩ : DeningerBarWord) = r + 2 := rfl
      rw [deningerBarWeightR, hlen]
      exact mul_le_mul_of_nonneg_right (deningerBar_face_growth hR r) (hHnn g)
    have hMnn : ∀ g : Fin (r + 2) → DeningerPrimeLattice,
        (0 : ℝ) ≤ (2 * ((r : ℝ) + 1) * R ^ (r + 1) *
            deningerBarHeight (⟨r + 1, g⟩ : DeningerBarWord) ^ k) *
              ‖(c : DeningerBarWord → ℂ) (⟨r + 1, g⟩ : DeningerBarWord)‖ := by
      intro g
      refine mul_nonneg (mul_nonneg ?_ (hHnn g)) (norm_nonneg _)
      have h1 : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) := by positivity
      exact mul_nonneg h1 (pow_nonneg hRpos.le _)
    have hMsummable : Summable fun g : Fin (r + 2) → DeningerPrimeLattice =>
        (2 * ((r : ℝ) + 1) * R ^ (r + 1) *
            deningerBarHeight (⟨r + 1, g⟩ : DeningerBarWord) ^ k) *
              ‖(c : DeningerBarWord → ℂ) (⟨r + 1, g⟩ : DeningerBarWord)‖ :=
      Summable.of_nonneg_of_le hMnn hMle (deningerBarSlice_summable h2R c (r + 1))
    have hcong : ((r : ℝ) + 1) *
          (2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1)))
        = ∑' g : Fin (r + 2) → DeningerPrimeLattice,
            (2 * ((r : ℝ) + 1) * R ^ (r + 1) *
              deningerBarHeight (⟨r + 1, g⟩ : DeningerBarWord) ^ k) *
                ‖(c : DeningerBarWord → ℂ) (⟨r + 1, g⟩ : DeningerBarWord)‖ := by
      have hA : ((r : ℝ) + 1) *
            (2 * (R⁻¹ * deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1)))
          = (((r : ℝ) + 1) * 2 * R⁻¹) *
              deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1) := by ring
      rw [hA, deningerBarSliceR,
        ← Summable.tsum_mul_left _ (deningerBarSlice_summable hR c (r + 1))]
      refine tsum_congr fun g => ?_
      have hlen : deningerBarLength (⟨r + 1, g⟩ : DeningerBarWord) = r + 2 := rfl
      rw [deningerBarWeightR, hlen]
      have hRne : R ≠ 0 := ne_of_gt hRpos
      field_simp
      ring
    rw [hcong, deningerBarSliceR]
    exact Summable.tsum_le_tsum hMle hMsummable (deningerBarSlice_summable h2R c (r + 1))
  calc (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarWeightR k R (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
      ≤ ∑' f : Fin (r + 1) → DeningerPrimeLattice, ∑ j : Fin (r + 1), G j f := hstep1
    _ = ∑ j : Fin (r + 1), ∑' f : Fin (r + 1) → DeningerPrimeLattice, G j f := hswap
    _ ≤ ((r : ℝ) + 1) * (2 * (R⁻¹ *
          deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1))) := hfinal
    _ ≤ deningerBarSliceR k (2 * R) (c : DeningerBarWord → ℂ) (r + 1) := hgrow

/-! ## The differential as an operator of the source -/

theorem deningerBarKotheData_eq_weightR (k : ℕ) (w : DeningerBarWord) :
    deningerBarKotheData.w k w = deningerBarWeightR k ((k : ℝ) + 1) w := by
  rw [deningerBarKotheData_w, deningerBarWeightR]
  ring

private theorem deningerBarSliceR_succ_summable {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerBarKothe) :
    Summable fun r : ℕ => deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1) :=
  (deningerBarSliceR_summable hR c).comp_injective (fun a b h => by simpa using h)

private theorem deningerBarSliceR_succ_tsum_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (c : DeningerBarKothe) :
    (∑' r : ℕ, deningerBarSliceR k R (c : DeningerBarWord → ℂ) (r + 1))
      ≤ deningerBarSeminormR k R c := by
  rw [deningerBarSeminormR_eq_tsum_slice hR c]
  refine Summable.tsum_le_tsum_of_inj (fun r : ℕ => r + 1) (fun a b h => by simpa using h)
    (fun r _ => deningerBarSliceR_nonneg k (by linarith) _ r)
    (fun r => le_rfl) (deningerBarSliceR_succ_summable hR c)
    (deningerBarSliceR_summable hR c)

theorem deningerBarDiffCoe_mem (c : DeningerBarKothe) :
    deningerBarDiffCoe (c : DeningerBarWord → ℂ) ∈ DeningerBarKothe := by
  intro k
  have hR : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2R : (1 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by linarith
  have hnn : ∀ w : DeningerBarWord,
      0 ≤ deningerBarKotheData.w k w *
        ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) w‖ := fun w =>
    mul_nonneg (deningerBarKotheData.pos k w).le (norm_nonneg _)
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun r => ?_, ?_⟩
  · refine ((deningerBarDiff_slice_le (k := k) hR c r).1).congr fun f => ?_
    rw [deningerBarKotheData_eq_weightR]
  · refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun f => hnn _) (fun r => ?_)
      (deningerBarSliceR_succ_summable (k := k) h2R c)
    have hcongr : (∑' f : Fin (r + 1) → DeningerPrimeLattice,
        deningerBarKotheData.w k (⟨r, f⟩ : DeningerBarWord) *
          ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖)
        = ∑' f : Fin (r + 1) → DeningerPrimeLattice,
            deningerBarWeightR k ((k : ℝ) + 1) (⟨r, f⟩ : DeningerBarWord) *
              ‖deningerBarDiffCoe (c : DeningerBarWord → ℂ) (⟨r, f⟩ : DeningerBarWord)‖ := by
      refine tsum_congr fun f => ?_
      rw [deningerBarKotheData_eq_weightR]
    rw [hcongr]
    exact (deningerBarDiff_slice_le (k := k) hR c r).2


theorem deningerBarFibreSum_add (a b : DeningerBarWord → ℂ) {s : ℕ}
    (f : Fin (s + 1) → DeningerPrimeLattice) (j : Fin (s + 1)) :
    deningerBarFibreSum (a + b) f j
      = deningerBarFibreSum a f j + deningerBarFibreSum b f j := by
  rw [deningerBarFibreSum, deningerBarFibreSum, deningerBarFibreSum]
  by_cases h : f j = 0
  · rw [if_pos h, if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h, if_neg h]
    show (a _ + b _) + (a _ + b _) = (a _ + a _) + (b _ + b _)
    ring

theorem deningerBarFibreSum_smul (t : ℂ) (a : DeningerBarWord → ℂ) {s : ℕ}
    (f : Fin (s + 1) → DeningerPrimeLattice) (j : Fin (s + 1)) :
    deningerBarFibreSum (t • a) f j = t * deningerBarFibreSum a f j := by
  rw [deningerBarFibreSum, deningerBarFibreSum]
  by_cases h : f j = 0
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    show t * a _ + t * a _ = t * (a _ + a _)
    ring

theorem deningerBarDiffCoe_add (a b : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (a + b) = deningerBarDiffCoe a + deningerBarDiffCoe b := by
  funext w
  show (∑ j : Fin (w.1 + 1), (-1 : ℂ) ^ (j : ℕ) * deningerBarFibreSum (a + b) w.2 j)
      = deningerBarDiffCoe a w + deningerBarDiffCoe b w
  rw [deningerBarDiffCoe, deningerBarDiffCoe, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerBarFibreSum_add]
  ring

theorem deningerBarDiffCoe_smul (t : ℂ) (a : DeningerBarWord → ℂ) :
    deningerBarDiffCoe (t • a) = t • deningerBarDiffCoe a := by
  funext w
  show (∑ j : Fin (w.1 + 1), (-1 : ℂ) ^ (j : ℕ) * deningerBarFibreSum (t • a) w.2 j)
      = t * deningerBarDiffCoe a w
  rw [deningerBarDiffCoe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerBarFibreSum_smul]
  ring

/-- **The bar differential** of the entire word-height source. -/
def deningerBarDiff : DeningerBarKothe →ₗ[ℂ] DeningerBarKothe where
  toFun c := ⟨deningerBarDiffCoe (c : DeningerBarWord → ℂ), deningerBarDiffCoe_mem c⟩
  map_add' a b := by
    ext w
    show deningerBarDiffCoe ((a + b : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((⟨deningerBarDiffCoe (a : DeningerBarWord → ℂ), deningerBarDiffCoe_mem a⟩ +
            ⟨deningerBarDiffCoe (b : DeningerBarWord → ℂ), deningerBarDiffCoe_mem b⟩ :
              DeningerBarKothe) : DeningerBarWord → ℂ) w
    rw [Submodule.coe_add, deningerBarDiffCoe_add, Submodule.coe_add, Pi.add_apply]
  map_smul' t a := by
    ext w
    show deningerBarDiffCoe ((t • a : DeningerBarKothe) : DeningerBarWord → ℂ) w
        = ((t • (⟨deningerBarDiffCoe (a : DeningerBarWord → ℂ),
            deningerBarDiffCoe_mem a⟩ : DeningerBarKothe)) : DeningerBarWord → ℂ) w
    rw [Submodule.coe_smul, deningerBarDiffCoe_smul]

@[simp]
theorem deningerBarDiff_coe (c : DeningerBarKothe) (w : DeningerBarWord) :
    ((deningerBarDiff c : DeningerBarKothe) : DeningerBarWord → ℂ) w
      = deningerBarDiffCoe (c : DeningerBarWord → ℂ) w := rfl

/-- **The doubling estimate for the bar differential**: `P_{k,R}(bc) ≤ P_{k,2R}(c)`. -/
theorem deningerBarSeminormR_diff_le {k : ℕ} {R : ℝ} (hR : 1 ≤ R) (c : DeningerBarKothe) :
    deningerBarSeminormR k R (deningerBarDiff c) ≤ deningerBarSeminormR k (2 * R) c := by
  have h2R : (1 : ℝ) ≤ 2 * R := by linarith
  have hsplit := deningerBarSeminormR_eq_tsum_slice (k := k) hR (deningerBarDiff c)
  have hslice : ∀ r : ℕ,
      deningerBarSliceR k R ((deningerBarDiff c : DeningerBarKothe) : DeningerBarWord → ℂ) r
        ≤ deningerBarSliceR k (2 * R) (c : DeningerBarWord → ℂ) (r + 1) := fun r =>
    (deningerBarDiff_slice_le (k := k) hR c r).2
  calc deningerBarSeminormR k R (deningerBarDiff c)
      = ∑' r, deningerBarSliceR k R
          ((deningerBarDiff c : DeningerBarKothe) : DeningerBarWord → ℂ) r := hsplit
    _ ≤ ∑' r, deningerBarSliceR k (2 * R) (c : DeningerBarWord → ℂ) (r + 1) := by
        refine Summable.tsum_le_tsum hslice
          (deningerBarSliceR_summable (k := k) hR (deningerBarDiff c))
          (deningerBarSliceR_succ_summable (k := k) h2R c)
    _ ≤ deningerBarSeminormR k (2 * R) c := deningerBarSliceR_succ_tsum_le h2R c

end

end RHTower
