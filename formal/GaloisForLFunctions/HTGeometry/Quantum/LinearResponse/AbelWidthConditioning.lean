import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelBohrSampling

/-!
# Conditioning in physical width coordinates

The extrapolation weights are real rational functions of the widths.
The modulus of the Bohr denominator separates into one explicit
positive factor per supported gap.
-/

open Matrix Polynomial Set
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem abelWidthNode_eq_neg_I_mul_inv (ε : Ioi (0 : ℝ)) :
    abelWidthNode ε = -Complex.I * (((ε : ℝ) : ℂ)⁻¹) := by
  have hz : hamiltonianAbelShift ε = ((ε : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hamiltonianAbelShift, Complex.mul_re, Complex.mul_im]
  rw [abelWidthNode, hz, _root_.mul_inv_rev, Complex.inv_I]

private theorem abelWidthLagrangeFactor_zero (ε η : Ioi (0 : ℝ)) (h : ε ≠ η) :
    (abelWidthNode ε - abelWidthNode η)⁻¹ * (0 - abelWidthNode η) =
      (((ε : ℝ) / ((ε : ℝ) - (η : ℝ)) : ℝ) : ℂ) := by
  have hn : abelWidthNode ε - abelWidthNode η ≠ 0 :=
    sub_ne_zero.mpr (fun he => h (abelWidthNode_injective he))
  have he : (((ε : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (show 0 < (ε : ℝ) from ε.2).ne'
  have hη : (((η : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (show 0 < (η : ℝ) from η.2).ne'
  have hd : ((ε : ℝ) : ℂ) - ((η : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact sub_ne_zero.mpr (fun h' => h (Subtype.ext h'))
  apply mul_right_cancel₀ hn
  rw [mul_right_comm (abelWidthNode ε - abelWidthNode η)⁻¹,
    inv_mul_cancel₀ hn, one_mul, Complex.ofReal_div, Complex.ofReal_sub]
  simp only [abelWidthNode_eq_neg_I_mul_inv]
  field_simp [he, hη, hd]
  ring

/-- The Lagrange weights at inverse shift zero are real and depend on
ordinary width differences. -/
theorem abelWidthLagrangeWeight_zero_eq_real {n : ℕ} (widths : Fin n → Ioi (0 : ℝ))
    (hw : Function.Injective widths) (k : Fin n) :
    abelWidthLagrangeWeight widths k 0 =
      ((∏ l ∈ Finset.univ.erase k, (widths k : ℝ) / ((widths k : ℝ) - (widths l : ℝ)) : ℝ) : ℂ) := by
  unfold abelWidthLagrangeWeight
  change _ = Complex.ofRealHom _
  rw [map_prod]
  refine Finset.prod_congr rfl fun l hl => ?_
  exact abelWidthLagrangeFactor_zero (widths k) (widths l)
    (fun he => (Finset.mem_erase.mp hl).1 (hw he).symm)

theorem norm_abelWidthLagrangeWeight_zero {n : ℕ} (widths : Fin n → Ioi (0 : ℝ))
    (hw : Function.Injective widths) (k : Fin n) :
    ‖abelWidthLagrangeWeight widths k 0‖ =
      ∏ l ∈ Finset.univ.erase k, (widths k : ℝ) / |(widths k : ℝ) - (widths l : ℝ)| := by
  rw [abelWidthLagrangeWeight_zero_eq_real widths hw, Complex.norm_real, norm_prod]
  refine Finset.prod_congr rfl fun _ _ => ?_
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < (widths k : ℝ) from (widths k).2)]

/-- Width separation controls the largest possible extrapolation gain. -/
theorem norm_abelWidthLagrangeWeight_zero_le_of_separated {n : ℕ}
    (widths : Fin n → Ioi (0 : ℝ)) (hw : Function.Injective widths) (k : Fin n) (R ρ : ℝ)
    (hρ : 0 < ρ) (hR : ∀ i, (widths i : ℝ) ≤ R)
    (hsep : ∀ i j, i ≠ j → ρ ≤ |(widths i : ℝ) - (widths j : ℝ)|) :
    ‖abelWidthLagrangeWeight widths k 0‖ ≤ (R / ρ) ^ (n - 1) := by
  rw [norm_abelWidthLagrangeWeight_zero widths hw]
  have hk : 0 ≤ (widths k : ℝ) := (show 0 < (widths k : ℝ) from (widths k).2).le
  calc
    _ ≤ ∏ _l ∈ Finset.univ.erase k, R / ρ := by
      apply Finset.prod_le_prod
      · intro l _
        exact div_nonneg hk (abs_nonneg _)
      · intro l hl
        have hkl : k ≠ l := Ne.symm (Finset.mem_erase.mp hl).1
        exact (div_le_div_of_nonneg_right (hR k) (abs_nonneg _)).trans
          (div_le_div_of_nonneg_left (hk.trans (hR k)) hρ (hsep k l hkl))
    _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin]

theorem eval_abelGapFactor_width (ε : Ioi (0 : ℝ)) (g : ℝ) :
    (abelGapFactor g).eval (abelWidthNode ε) =
      1 + Complex.I * (((g / (ε : ℝ)) : ℝ) : ℂ) := by
  rw [eval_abelGapFactor, abelWidthNode_eq_neg_I_mul_inv, Complex.ofReal_div, div_eq_mul_inv]
  ring

theorem norm_sq_abelGapFactor_width (ε : Ioi (0 : ℝ)) (g : ℝ) :
    ‖(abelGapFactor g).eval (abelWidthNode ε)‖ ^ 2 = 1 + (g / (ε : ℝ)) ^ 2 := by
  rw [eval_abelGapFactor_width, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_sub, neg_zero, add_zero,
    zero_add, pow_two]

/-- Gap sizes and width determine the exact gain of clearing the denominator. -/
theorem norm_sq_abelBohrDenominator_width {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (X : Matrix ι ι ℂ) (ε : Ioi (0 : ℝ)) :
    ‖(abelBohrDenominator hH X).eval (abelWidthNode ε)‖ ^ 2 =
      ∏ g ∈ abelProbeBohrGaps hH X, (1 + (g / (ε : ℝ)) ^ 2) := by
  rw [abelBohrDenominator, Polynomial.eval_prod, norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun g _ => norm_sq_abelGapFactor_width ε g

/-- Swapping the two energy indices negates the gap and preserves support. -/
theorem neg_mem_abelProbeBohrGaps_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H X : Matrix ι ι ℂ} (hH : H.IsHermitian) (hX : X.IsHermitian) (g : ℝ) :
    -g ∈ abelProbeBohrGaps hH X ↔ g ∈ abelProbeBohrGaps hH X := by
  let E := hamiltonianEnergyCoordinates hH
  have hE : (E X)ᴴ = E X := by
    calc
      (E X)ᴴ = star (E X) := (Matrix.star_eq_conjTranspose _).symm
      _ = E (star X) := (map_star E X).symm
      _ = E X := congrArg E ((Matrix.star_eq_conjTranspose X).trans hX)
  have hneg (a : ℝ) (ha : a ∈ abelProbeBohrGaps hH X) : -a ∈ abelProbeBohrGaps hH X := by
    obtain ⟨h0, i, j, hg, hi⟩ := (mem_abelProbeBohrGaps hH X a).mp ha
    refine (mem_abelProbeBohrGaps hH X (-a)).mpr ⟨neg_ne_zero.mpr h0, j, i, ?_, ?_⟩
    · rw [← hg, hamiltonianGap, hamiltonianGap, neg_sub]
    · change E X j i ≠ 0
      intro hz
      have he := congrArg (fun A : Matrix ι ι ℂ => A i j) hE
      rw [Matrix.conjTranspose_apply, hz, star_zero] at he
      exact hi he.symm
  exact ⟨fun hg => by simpa only [neg_neg] using hneg (-g) hg, hneg g⟩

private theorem abelProbeBohrGaps_pair_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H X : Matrix ι ι ℂ} (hH : H.IsHermitian) (hX : X.IsHermitian) :
    let s := abelProbeBohrGaps hH X
    let p := s.filter fun g => 0 < g
    s = p ∪ p.image (fun g => -g) ∧ Disjoint p (p.image fun g => -g) := by
  classical
  let s := abelProbeBohrGaps hH X
  let p := s.filter fun g => 0 < g
  change s = p ∪ p.image (fun g => -g) ∧ Disjoint p (p.image fun g => -g)
  constructor
  · ext g
    constructor
    · intro hg
      rcases lt_or_gt_of_ne ((mem_abelProbeBohrGaps hH X g).mp hg).1 with hn | hp
      · exact Finset.mem_union.mpr (.inr (Finset.mem_image.mpr ⟨-g,
          Finset.mem_filter.mpr ⟨(neg_mem_abelProbeBohrGaps_iff hH hX g).mpr hg, neg_pos.mpr hn⟩,
          neg_neg g⟩))
      · exact Finset.mem_union.mpr (.inl (Finset.mem_filter.mpr ⟨hg, hp⟩))
    · intro hg
      rcases Finset.mem_union.mp hg with hp | hn
      · exact (Finset.mem_filter.mp hp).1
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
        exact (neg_mem_abelProbeBohrGaps_iff hH hX a).mpr (Finset.mem_filter.mp ha).1
  · refine Finset.disjoint_left.mpr fun g hg hn => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact (not_lt_of_ge (neg_nonpos.mpr (Finset.mem_filter.mp ha).2.le))
      (Finset.mem_filter.mp hg).2

theorem card_abelProbeBohrGaps_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H X : Matrix ι ι ℂ} (hH : H.IsHermitian) (hX : X.IsHermitian) :
    (abelProbeBohrGaps hH X).card =
      2 * ((abelProbeBohrGaps hH X).filter fun g => 0 < g).card := by
  classical
  let s := abelProbeBohrGaps hH X
  let p := s.filter fun g => 0 < g
  obtain ⟨hp, hd⟩ := abelProbeBohrGaps_pair_partition hH hX
  change s = p ∪ p.image (fun g => -g) at hp
  change Disjoint p (p.image fun g => -g) at hd
  change s.card = 2 * p.card
  rw [hp, Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ neg_injective,
    two_mul]

/-- For a Hermitian probe, opposite frequencies give a positive real
product with one term per supported positive gap. -/
theorem eval_abelBohrDenominator_width_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H X : Matrix ι ι ℂ} (hH : H.IsHermitian) (hX : X.IsHermitian) (ε : Ioi (0 : ℝ)) :
    (abelBohrDenominator hH X).eval (abelWidthNode ε) =
      ((∏ g ∈ (abelProbeBohrGaps hH X).filter (fun g => 0 < g),
        (1 + (g / (ε : ℝ)) ^ 2) : ℝ) : ℂ) := by
  classical
  let s := abelProbeBohrGaps hH X
  let p := s.filter fun g => 0 < g
  obtain ⟨hp, hd⟩ := abelProbeBohrGaps_pair_partition hH hX
  change s = p ∪ p.image (fun g => -g) at hp
  change Disjoint p (p.image fun g => -g) at hd
  change Polynomial.eval _ (∏ g ∈ s, abelGapFactor g) = Complex.ofRealHom (∏ g ∈ p, _)
  rw [Polynomial.eval_prod, hp, Finset.prod_union hd,
    Finset.prod_image (fun a _ b _ he => neg_injective he), ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [eval_abelGapFactor_width, eval_abelGapFactor_width, neg_div, Complex.ofReal_neg]
  let a : ℂ := ((g / (ε : ℝ) : ℝ) : ℂ)
  change (1 + Complex.I * a) * (1 + Complex.I * -a) =
    Complex.ofRealHom (1 + (g / (ε : ℝ)) ^ 2)
  calc
    _ = 1 - Complex.I ^ 2 * a ^ 2 := by ring
    _ = _ := by
      change 1 - Complex.I ^ 2 * (((g / (ε : ℝ)) : ℝ) : ℂ) ^ 2 =
        (((1 + (g / (ε : ℝ)) ^ 2) : ℝ) : ℂ)
      rw [Complex.I_sq, neg_one_mul, sub_neg_eq_add, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_pow]

/-- A gap bound and a lower width bound control the denominator gain
without using the individual locations of the supported gaps. -/
theorem norm_abelBohrDenominator_width_le_of_gap_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (ε : Ioi (0 : ℝ)) (a G : ℝ) (ha : 0 < a) (hε : a ≤ (ε : ℝ)) (hG : 0 ≤ G)
    (hg : ∀ g ∈ abelProbeBohrGaps hH X, |g| ≤ G) :
    ‖(abelBohrDenominator hH X).eval (abelWidthNode ε)‖ ≤
      √((1 + (G / a) ^ 2) ^ (abelProbeBohrGaps hH X).card) := by
  have hε0 : 0 < (ε : ℝ) := ha.trans_le hε
  have hsq : ‖(abelBohrDenominator hH X).eval (abelWidthNode ε)‖ ^ 2 ≤
      (1 + (G / a) ^ 2) ^ (abelProbeBohrGaps hH X).card := by
    rw [norm_sq_abelBohrDenominator_width]
    calc
      _ ≤ ∏ _g ∈ abelProbeBohrGaps hH X, (1 + (G / a) ^ 2) := by
        apply Finset.prod_le_prod
        · intro g _
          exact add_nonneg zero_le_one (sq_nonneg _)
        · intro g hgs
          have hb : |g / (ε : ℝ)| ≤ G / a := by
            rw [abs_div, abs_of_pos hε0]
            exact (div_le_div_of_nonneg_right (hg g hgs) hε0.le).trans
              (div_le_div_of_nonneg_left hG ha hε)
          apply add_le_add le_rfl
          rw [← sq_abs (g / (ε : ℝ))]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := Finset.prod_const _
  have he := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at he

#print axioms abelWidthLagrangeWeight_zero_eq_real
#print axioms norm_abelWidthLagrangeWeight_zero_le_of_separated
#print axioms norm_sq_abelBohrDenominator_width
#print axioms eval_abelBohrDenominator_width_of_isHermitian
#print axioms norm_abelBohrDenominator_width_le_of_gap_bound

end

end GaloisForLFunctions.HTGeometry
