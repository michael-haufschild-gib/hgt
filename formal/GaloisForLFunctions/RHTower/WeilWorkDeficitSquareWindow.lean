import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMoment
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision

/-!
# Squared horizontal displacement on admissible zero windows

The corpus's weighted zeta tail estimate transfers to actual Xi multiplicity copies. Line
conjugation handles the left tail without requiring the finite copy set to be symmetric.
-/

open Complex Set Filter
open scoped Topology

noncomputable section

namespace RHTower.WeilSpectral

private theorem sum_copies_le_order_sum (F : Finset XiZeroCopy) (Z : Finset ℂ)
    (f : ℂ → ℝ) (hf : ∀ z, 0 ≤ f z) (hF : ∀ q ∈ F, (q.1 : ℂ) ∈ Z) :
    ∑ q ∈ F, f (q.1 : ℂ) ≤
      ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) * f z := by
  classical
  let S : Finset XiDivisorSupport := F.image Sigma.fst
  let G : Finset XiZeroCopy := S.sigma (fun _ => Finset.univ)
  have hFG : F ⊆ G := by
    intro q hq
    exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_univ _⟩
  have hG : (∑ q ∈ G, f (q.1 : ℂ)) =
      ∑ ρ ∈ S, ((analyticOrderAt riemannZeta (ρ : ℂ)).toNat : ℝ) * f ρ := by
    dsimp only [G]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (xiSupportMultiplicity ρ : ℝ) * f ρ = _
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat,
      xi_analyticOrderAt_eq_riemannZeta_of_mem_strip (xi_divisor_support_re_mem_open_unit ρ)]
  have hSZ : S.image (fun ρ : XiDivisorSupport => (ρ : ℂ)) ⊆ Z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨ρ, hρ, rfl⟩
    rcases Finset.mem_image.mp hρ with ⟨q, hq, rfl⟩
    exact hF q hq
  calc
    ∑ q ∈ F, f (q.1 : ℂ) ≤ ∑ q ∈ G, f (q.1 : ℂ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hFG (fun q _ _ => hf _)
    _ = ∑ ρ ∈ S, ((analyticOrderAt riemannZeta (ρ : ℂ)).toNat : ℝ) * f ρ := hG
    _ = ∑ z ∈ S.image (fun ρ : XiDivisorSupport => (ρ : ℂ)),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * f z := by
      rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    _ ≤ ∑ z ∈ Z, ((analyticOrderAt riemannZeta z).toNat : ℝ) * f z :=
      Finset.sum_le_sum_of_subset_of_nonneg hSZ (fun z _ _ => mul_nonneg (Nat.cast_nonneg _) (hf z))

private theorem copy_mem_windowZeros {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (q : XiZeroCopy) (hq : a ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b)
    (hβ : 1 / 2 ≤ (q.1 : ℂ).re) : (q.1 : ℂ) ∈ windowZeros a b := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  apply (mem_windowZeros_iff ha hab _).mpr
  constructor
  · apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2), uIcc_of_le hab]
    exact ⟨⟨hβ, by linarith [hstrip.2]⟩, hq⟩
  · exact (xi_zero_iff_zeta_zero_of_mem_strip hstrip.1 hstrip.2).mp
      (xi_eq_zero_of_mem_divisor_support q.1)

private theorem lineConj_re (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
  rw [xiZero_lineConj_eq]
  simp

private theorem lineConj_im (q : XiZeroCopy) :
    ((xiZeroCopyLineConjEquiv q).1 : ℂ).im = (q.1 : ℂ).im := by
  rw [xiZero_lineConj_eq]
  simp

private theorem square_le_near_add_tails {δ v : ℝ} (hδ0 : -(1 / 2) < δ)
    (hδ1 : δ < 1 / 2) (hv : 0 < v) :
    δ ^ 2 ≤ v ^ 2 + (1 / 2) * (if v ≤ δ then δ else 0) +
      (1 / 2) * (if v ≤ -δ then -δ else 0) := by
  by_cases hr : v ≤ δ
  · rw [if_pos hr]
    have hd : 0 ≤ δ := by linarith
    have hleft : 0 ≤ (if v ≤ -δ then -δ else 0) := by
      split_ifs with h <;> linarith
    nlinarith [mul_nonneg hd (le_of_lt (sub_pos.mpr hδ1)), sq_nonneg v]
  · rw [if_neg hr]
    by_cases hl : v ≤ -δ
    · rw [if_pos hl]
      have hd : 0 ≤ -δ := by linarith
      nlinarith [mul_nonneg hd (show 0 ≤ 1 / 2 + δ by linarith), sq_nonneg v]
    · rw [if_neg hl]
      nlinarith [mul_nonneg (show 0 ≤ v - δ by linarith) (show 0 ≤ v + δ by linarith)]

/-- Uniform square-displacement bound for every finite set of actual copies in one admissible
window. No symmetry or closure property is imposed on the finite set. -/
theorem exists_deficit_square_window_bound :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ c : ℝ, 2 ≤ c → ∀ F : Finset XiZeroCopy,
          (∀ q ∈ F, T₁ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T₂) →
          ∑ q ∈ F, ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤
            (c / Real.log U) ^ 2 * F.card +
              D / c * (T₂ - T₁) + K * Real.log U ^ 2 := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (16 : ℝ)] with U hU hU16
  obtain ⟨T₁, hT₁, T₂, hT₂, ht⟩ := hU
  have hT₁pos : 0 < T₁ := by linarith [hT₁.1]
  have hT12 : T₁ ≤ T₂ := by linarith [hT₁.2, hT₂.1]
  refine ⟨T₁, hT₁, T₂, hT₂, fun c hc F hF => ?_⟩
  let v : ℝ := c / Real.log U
  let B : ℝ := D / c * (T₂ - T₁) + K * Real.log U ^ 2
  have hv : 0 < v := div_pos (by linarith) (Real.log_pos (by linarith))
  have hz := ht (windowZeros T₁ T₂) (mem_windowZeros_iff hT₁pos hT12) c hc
  have hright (G : Finset XiZeroCopy)
      (hG : ∀ q ∈ G, T₁ ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T₂)
      (hβ : ∀ q ∈ G, v ≤ (q.1 : ℂ).re - 1 / 2) :
      ∑ q ∈ G, ((q.1 : ℂ).re - 1 / 2) ≤ B := by
    have htrans := sum_copies_le_order_sum G
      ((windowZeros T₁ T₂).filter (fun z => 1 / 2 + v ≤ z.re))
      (fun z => max (z.re - 1 / 2) 0) (fun _ => le_max_right _ _) (fun q hq =>
        Finset.mem_filter.mpr ⟨copy_mem_windowZeros hT₁pos hT12 q (hG q hq)
          (by linarith [hβ q hq]), by linarith [hβ q hq]⟩)
    have heqL : (∑ q ∈ G, max ((q.1 : ℂ).re - 1 / 2) 0) =
        ∑ q ∈ G, ((q.1 : ℂ).re - 1 / 2) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact max_eq_left (by linarith [hβ q hq])
    have heqR : (∑ z ∈ (windowZeros T₁ T₂).filter (fun z => 1 / 2 + v ≤ z.re),
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * max (z.re - 1 / 2) 0) =
        ∑ z ∈ (windowZeros T₁ T₂).filter (fun z => 1 / 2 + v ≤ z.re),
          ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - 1 / 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [max_eq_left (by linarith [(Finset.mem_filter.mp hz).2])]
    rw [heqL, heqR] at htrans
    exact htrans.trans hz
  have hR : (∑ q ∈ F, if v ≤ (q.1 : ℂ).re - 1 / 2 then (q.1 : ℂ).re - 1 / 2 else 0) ≤ B := by
    rw [← Finset.sum_filter]
    exact hright _ (fun q hq => hF q (Finset.mem_filter.mp hq).1)
      (fun _ hq => (Finset.mem_filter.mp hq).2)
  let FL := F.filter (fun q => v ≤ -((q.1 : ℂ).re - 1 / 2))
  have hLimage := hright (FL.image xiZeroCopyLineConjEquiv) (by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
      rw [lineConj_im]
      exact hF r (Finset.mem_filter.mp hr).1) (by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
      rw [lineConj_re]
      have := (Finset.mem_filter.mp hr).2
      linarith)
  rw [Finset.sum_image (fun _ _ _ _ h => xiZeroCopyLineConjEquiv.injective h)] at hLimage
  have hL : (∑ q ∈ F, if v ≤ -((q.1 : ℂ).re - 1 / 2) then -((q.1 : ℂ).re - 1 / 2) else 0) ≤ B := by
    rw [← Finset.sum_filter]
    have heq : (∑ q ∈ FL, -((q.1 : ℂ).re - 1 / 2)) =
        ∑ q ∈ FL, (((xiZeroCopyLineConjEquiv q).1 : ℂ).re - 1 / 2) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [lineConj_re]
      ring
    exact heq.trans_le hLimage
  have hs := Finset.sum_le_sum (s := F) (fun q _ =>
    square_le_near_add_tails
      (show -(1 / 2) < (q.1 : ℂ).re - 1 / 2 by linarith [(xi_divisor_support_re_mem_open_unit q.1).1])
      (show (q.1 : ℂ).re - 1 / 2 < 1 / 2 by linarith [(xi_divisor_support_re_mem_open_unit q.1).2]) hv)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hs
  change _ ≤ v ^ 2 * F.card + D / c * (T₂ - T₁) + K * Real.log U ^ 2
  dsimp only [B] at hR hL
  nlinarith

end RHTower.WeilSpectral

end
