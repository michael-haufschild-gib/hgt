import GaloisForLFunctions.RHTower.ConstrainedProlateFullDistanceCCM
import GaloisForLFunctions.RHTower.ConstrainedProlateLeakageStructure
import GaloisForLFunctions.RHTower.ConstrainedProlateParityDistanceCCM

/-!
# Quantitative normalized distance for constrained-prolate secular vectors

This module proves the paper's full `O(λ⁻⁷)` sign-optimized eigenvector law.  It retains the
literal infinite secular vector and literal two-mode seed in `lp 2`.  A pointwise combination of
the head Lagrange defect and infinite-tail mass bound controls the full normalized alignment; the
step-four Fuchs quotient then supplies the exact seventh-power rate.  Positive and negative Fourier
sectors are both discharged under the same Bessel and fixed-coordinate inputs used by their exact
secular-root theorems.
-/

open Filter Asymptotics

namespace GaloisForLFunctions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem min_norm_sub_normalize_le_of_inner_sq
    {u w : H} (hu : u ≠ 0) (hw : w ≠ 0) {s r : ℝ} (hs : 0 ≤ s)
    (h : 1 - s * r ^ 2 ≤
      inner ℝ u w ^ 2 / (‖u‖ ^ 2 * ‖w‖ ^ 2)) :
    min ‖(‖u‖)⁻¹ • u - (‖w‖)⁻¹ • w‖
        ‖(‖u‖)⁻¹ • u + (‖w‖)⁻¹ • w‖
      ≤ (1 + s) * |r| := by
  let x := ‖(‖u‖)⁻¹ • u - (‖w‖)⁻¹ • w‖
  let y := ‖(‖u‖)⁻¹ • u + (‖w‖)⁻¹ • w‖
  let a := |inner ℝ u w| / (‖u‖ * ‖w‖)
  have hden : 0 < ‖u‖ * ‖w‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hw)
  have ha0 : 0 ≤ a := div_nonneg (abs_nonneg _) hden.le
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (abs_real_inner_le_norm u w)
  have ha2 : a ^ 2 = inner ℝ u w ^ 2 / (‖u‖ ^ 2 * ‖w‖ ^ 2) := by
    dsimp [a]
    rw [div_pow, sq_abs]
    ring
  have hminsq : min (x ^ 2) (y ^ 2) = 2 - 2 * a := by
    dsimp [x, y, a]
    exact min_norm_sub_sq_normalize hu hw
  have hsq : min (x ^ 2) (y ^ 2) ≤ 2 * s * r ^ 2 := by
    rw [hminsq]
    rw [← ha2] at h
    have haa : a ^ 2 ≤ a := by nlinarith
    nlinarith
  have hminsquare : (min x y) ^ 2 = min (x ^ 2) (y ^ 2) := by
    rcases le_total x y with hxy | hyx
    · have hxy2 : x ^ 2 ≤ y ^ 2 := by
        have hx0 : 0 ≤ x := by dsimp [x]; positivity
        have hy0 : 0 ≤ y := by dsimp [y]; positivity
        nlinarith
      simp only [min_eq_left hxy, min_eq_left hxy2]
    · have hyx2 : y ^ 2 ≤ x ^ 2 := by
        have hx0 : 0 ≤ x := by dsimp [x]; positivity
        have hy0 : 0 ≤ y := by dsimp [y]; positivity
        nlinarith
      simp only [min_eq_right hyx, min_eq_right hyx2]
  have hm0 : 0 ≤ min x y := le_min (by dsimp [x]; positivity) (by dsimp [y]; positivity)
  have hR0 : 0 ≤ (1 + s) * |r| := mul_nonneg (by linarith) (abs_nonneg _)
  have hcoeff : 2 * s ≤ (1 + s) ^ 2 := by nlinarith [sq_nonneg s]
  have hsquare : (min x y) ^ 2 ≤ ((1 + s) * |r|) ^ 2 := by
    rw [hminsquare]
    calc min (x ^ 2) (y ^ 2)
        ≤ 2 * s * r ^ 2 := hsq
      _ ≤ (1 + s) ^ 2 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg r)
      _ = ((1 + s) * |r|) ^ 2 := by rw [mul_pow, sq_abs]
  dsimp [x, y] at hm0 hR0 hsquare ⊢
  nlinarith

end GaloisForLFunctions

open GaloisForLFunctions

noncomputable section

namespace RHTower

theorem full_normalized_alignment_ge
    {V G : lp (fun _ : ℕ => ℝ) 2} {d ℓ : ℕ → ℝ} {μ E F : ℝ}
    (hV : ((V : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = secularVector d ℓ μ)
    (hG : ((G : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = twoModeSeedFun ℓ)
    (hsum : Summable fun j => secularVector d ℓ μ j ^ 2)
    (hv0 : secularVector d ℓ μ 0 ≠ 0) (hℓ0 : ℓ 0 ≠ 0)
    (hdefect :
      (ℓ 0 * secularVector d ℓ μ 0 + ℓ 1 * secularVector d ℓ μ 1) ^ 2 /
          ((secularVector d ℓ μ 0 ^ 2 + secularVector d ℓ μ 1 ^ 2) *
            (ℓ 0 ^ 2 + ℓ 1 ^ 2)) ≤ E)
    (htail :
      (∑' j : ℕ, secularVector d ℓ μ (j + 2) ^ 2) /
          secularVector d ℓ μ 0 ^ 2 ≤ F) :
    1 - (E + F) ≤ inner ℝ V G ^ 2 / (‖V‖ ^ 2 * ‖G‖ ^ 2) := by
  let H := ‖secularHead d ℓ μ‖ ^ 2
  let T := ∑' j : ℕ, secularVector d ℓ μ (j + 2) ^ 2
  let q := inner ℝ (secularHead d ℓ μ) (twoModeSeed ℓ) ^ 2 /
    (‖secularHead d ℓ μ‖ ^ 2 * ‖twoModeSeed ℓ‖ ^ 2)
  let defect := inner ℝ (secularHead d ℓ μ) (constraintNormal ℓ) ^ 2 /
    (‖secularHead d ℓ μ‖ ^ 2 * ‖constraintNormal ℓ‖ ^ 2)
  have hHpos : 0 < H := by
    dsimp [H]
    exact pow_pos (norm_pos_iff.mpr (secularHead_ne_zero d ℓ μ hv0)) 2
  have hTnn : 0 ≤ T := by dsimp [T]; exact tsum_nonneg fun j => sq_nonneg _
  have hv0sq : 0 < secularVector d ℓ μ 0 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv0))
  have hGpos : 0 < ‖twoModeSeed ℓ‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (twoModeSeed_ne_zero ℓ hℓ0)) 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hdef0 : 0 ≤ defect := by
    dsimp [defect]
    positivity
  have hqdef : q = 1 - defect := by
    dsimp [q, defect]
    exact align_eq_one_sub_defect d ℓ μ hv0 hℓ0
  have hq1 : q ≤ 1 := by nlinarith
  have htailH : T / H ≤ T / secularVector d ℓ μ 0 ^ 2 := by
    have hv0H : secularVector d ℓ μ 0 ^ 2 ≤ H := by
      dsimp [H]
      rw [norm_sq_secularHead]
      nlinarith [sq_nonneg (secularVector d ℓ μ 1)]
    exact div_le_div_of_nonneg_left hTnn hv0sq hv0H
  have hmassden : 0 < H + T := add_pos_of_pos_of_nonneg hHpos hTnn
  have hmassdef : 1 - H / (H + T) = T / (H + T) := by
    field_simp
    ring
  have hmassdef0 : 0 ≤ 1 - H / (H + T) := by
    rw [hmassdef]
    positivity
  have hmassdef_le : 1 - H / (H + T) ≤ T / H := by
    rw [hmassdef]
    exact div_le_div_of_nonneg_left hTnn hHpos (by linarith)
  have hqmass : 1 - q * (H / (H + T)) ≤ defect + T / H := by
    calc
      1 - q * (H / (H + T))
          = (1 - q) + q * (1 - H / (H + T)) := by ring
      _ = defect + q * (1 - H / (H + T)) := by rw [hqdef]; ring
      _ ≤ defect + 1 * (1 - H / (H + T)) := by
        gcongr
      _ ≤ defect + T / H := by linarith
  have hdefect' : defect ≤ E := by
    dsimp [defect]
    rw [← defect_eq_inner_sq_div d ℓ μ]
    exact hdefect
  have htail' : T / secularVector d ℓ μ 0 ^ 2 ≤ F := by
    exact htail
  have hlower : 1 - (E + F) ≤ q * (H / (H + T)) := by
    have herror : 1 - q * (H / (H + T)) ≤ E + F :=
      le_trans hqmass (by linarith [htailH])
    linarith
  have hfactor : inner ℝ V G ^ 2 / (‖V‖ ^ 2 * ‖G‖ ^ 2) =
      q * (H / (H + T)) := by
    dsimp [q, H, T]
    rw [lp_inner_twoModeSeed V G hG, hV,
      lp_norm_sq_split V hV hsum, lp_norm_sq_twoModeSeed G hG,
      inner_secularHead_twoModeSeed, norm_sq_twoModeSeed]
    have hHne : ‖secularHead d ℓ μ‖ ^ 2 ≠ 0 := ne_of_gt hHpos
    rw [norm_sq_secularHead] at hHne ⊢
    field_simp
  rwa [hfactor]

theorem secular_defect_tail_bounds
    {d ℓ : ℕ → ℝ} {a0 lam : ℝ} (ha0 : a0 ≠ 0)
    (hstruct : (0 ≤ d 0 ∧ d 0 < d 1 ∧ d 1 < d 2) ∧ ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2)
    (hbessel : (∑' j : ℕ, ℓ j ^ 2) ≤ 2 * lam)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0)
    (hℓ0big : a0 ^ 2 / 2 ≤ ℓ 0 ^ 2) (hlam : 1 ≤ lam) :
    (ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
        + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1) ^ 2 /
      ((secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
          + secularVector d ℓ (infiniteSecularRoot d ℓ) 1 ^ 2) *
        (ℓ 0 ^ 2 + ℓ 1 ^ 2))
      ≤ 16 / a0 ^ 4 * (lam * d 1 / (d 2 - d 1)) ^ 2 ∧
    (∑' j : ℕ, secularVector d ℓ (infiniteSecularRoot d ℓ) (j + 2) ^ 2) /
        secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
      ≤ 4 / a0 ^ 2 * (lam * d 1 / (d 2 - d 1)) ^ 2 := by
  have ha0sq : (0 : ℝ) < a0 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha0))
  obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hstruct
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hd1pos : 0 < d 1 := lt_of_le_of_lt hd0 h01
  have hd21 : 0 < d 2 - d 1 := by linarith
  have hT0 : 0 ≤ ∑' j : ℕ, ℓ (j + 2) ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hT2 : (∑' j : ℕ, ℓ (j + 2) ^ 2) ≤ 2 * lam := by
    have hfull := hsum.sum_add_tsum_nat_add 2
    have hfin : 0 ≤ ∑ i ∈ Finset.range 2, ℓ i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hheadfloor : 0 < a0 ^ 2 / 2 / d 1 ^ 2 :=
    div_pos (half_pos ha0sq) (pow_pos hd1pos 2)
  have hhead_ge : a0 ^ 2 / 2 / d 1 ^ 2
      ≤ secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2 := by
    have h1' := secularVector_head_sq_ge (ℓ := ℓ) hd0 hrmem
    have h2' : a0 ^ 2 / 2 / d 1 ^ 2 ≤ ℓ 0 ^ 2 / d 1 ^ 2 :=
      div_le_div_of_le_of_pos hℓ0big (pow_pos hd1pos 2)
    exact le_trans h2' h1'
  constructor
  · have hnum : (ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
          + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1) ^ 2
        ≤ (2 * lam / (d 2 - d 1)) ^ 2 := by
      have habs := abs_secularVector_head_seed_pairing_le h01 h12 hd2 hsum hℓ0 hℓ1
      have hstep : |ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
            + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1|
          ≤ 2 * lam / (d 2 - d 1) :=
        le_trans habs (div_le_div_of_le_of_pos hT2 hd21)
      calc
        (ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
            + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1) ^ 2
            = |ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
                + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1| ^ 2 :=
              (sq_abs _).symm
        _ ≤ (2 * lam / (d 2 - d 1)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hstep 2
    have hDfloor : 0 < a0 ^ 2 / 2 / d 1 ^ 2 * (a0 ^ 2 / 2) :=
      mul_pos hheadfloor (half_pos ha0sq)
    have hD_ge : a0 ^ 2 / 2 / d 1 ^ 2 * (a0 ^ 2 / 2)
        ≤ (secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
            + secularVector d ℓ (infiniteSecularRoot d ℓ) 1 ^ 2) *
          (ℓ 0 ^ 2 + ℓ 1 ^ 2) := by
      have hv : a0 ^ 2 / 2 / d 1 ^ 2
          ≤ secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
            + secularVector d ℓ (infiniteSecularRoot d ℓ) 1 ^ 2 := by
        nlinarith [hhead_ge, sq_nonneg (secularVector d ℓ (infiniteSecularRoot d ℓ) 1)]
      have hℓ : a0 ^ 2 / 2 ≤ ℓ 0 ^ 2 + ℓ 1 ^ 2 := by
        nlinarith [hℓ0big, sq_nonneg (ℓ 1)]
      exact mul_le_mul hv hℓ (half_pos ha0sq).le (le_trans hheadfloor.le hv)
    have heq : (2 * lam / (d 2 - d 1)) ^ 2 /
          (a0 ^ 2 / 2 / d 1 ^ 2 * (a0 ^ 2 / 2))
        = 16 / a0 ^ 4 * (lam * d 1 / (d 2 - d 1)) ^ 2 := by
      field_simp
      ring
    calc
      (ℓ 0 * secularVector d ℓ (infiniteSecularRoot d ℓ) 0
            + ℓ 1 * secularVector d ℓ (infiniteSecularRoot d ℓ) 1) ^ 2 /
          ((secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
              + secularVector d ℓ (infiniteSecularRoot d ℓ) 1 ^ 2) *
            (ℓ 0 ^ 2 + ℓ 1 ^ 2))
          ≤ (2 * lam / (d 2 - d 1)) ^ 2 /
            ((secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
                + secularVector d ℓ (infiniteSecularRoot d ℓ) 1 ^ 2) *
              (ℓ 0 ^ 2 + ℓ 1 ^ 2)) :=
        div_le_div_of_le_of_pos hnum (lt_of_lt_of_le hDfloor hD_ge)
      _ ≤ (2 * lam / (d 2 - d 1)) ^ 2 /
          (a0 ^ 2 / 2 / d 1 ^ 2 * (a0 ^ 2 / 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hDfloor hD_ge
      _ = 16 / a0 ^ 4 * (lam * d 1 / (d 2 - d 1)) ^ 2 := heq
  · have htail_le : (∑' j : ℕ,
          secularVector d ℓ (infiniteSecularRoot d ℓ) (j + 2) ^ 2)
        ≤ 2 * lam / (d 2 - d 1) ^ 2 := by
      have h1' := secularVector_sq_tail_le hd2 hsum
        (μ := infiniteSecularRoot d ℓ) (by linarith [hrmem.2])
      have h2' : (∑' j : ℕ, ℓ (j + 2) ^ 2) /
            (d 2 - infiniteSecularRoot d ℓ) ^ 2
          ≤ (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - d 1) ^ 2 :=
        div_le_div_of_nonneg_left hT0 (pow_pos hd21 2)
          (pow_le_pow_left₀ hd21.le (by linarith [hrmem.2]) 2)
      have h3' : (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - d 1) ^ 2
          ≤ 2 * lam / (d 2 - d 1) ^ 2 :=
        div_le_div_of_le_of_pos hT2 (pow_pos hd21 2)
      exact le_trans h1' (le_trans h2' h3')
    have hheadpos : 0 < secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2 :=
      lt_of_lt_of_le hheadfloor hhead_ge
    have hnn : 0 ≤ 2 * lam / (d 2 - d 1) ^ 2 :=
      div_nonneg (by linarith) (sq_nonneg _)
    have heqA : 2 * lam / (d 2 - d 1) ^ 2 / (a0 ^ 2 / 2 / d 1 ^ 2)
        = 4 * lam * d 1 ^ 2 / (a0 ^ 2 * (d 2 - d 1) ^ 2) := by
      field_simp
      ring
    have heqB : 4 / a0 ^ 2 * (lam * d 1 / (d 2 - d 1)) ^ 2
        = 4 * lam ^ 2 * d 1 ^ 2 / (a0 ^ 2 * (d 2 - d 1) ^ 2) := by
      field_simp
    calc
      (∑' j : ℕ, secularVector d ℓ (infiniteSecularRoot d ℓ) (j + 2) ^ 2) /
            secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2
          ≤ (2 * lam / (d 2 - d 1) ^ 2) /
            secularVector d ℓ (infiniteSecularRoot d ℓ) 0 ^ 2 :=
        div_le_div_of_le_of_pos htail_le hheadpos
      _ ≤ (2 * lam / (d 2 - d 1) ^ 2) / (a0 ^ 2 / 2 / d 1 ^ 2) :=
        div_le_div_of_nonneg_left hnn hheadfloor hhead_ge
      _ = 4 * lam * d 1 ^ 2 / (a0 ^ 2 * (d 2 - d 1) ^ 2) := heqA
      _ ≤ 4 * lam ^ 2 * d 1 ^ 2 / (a0 ^ 2 * (d 2 - d 1) ^ 2) := by
        refine div_le_div_of_le_of_pos ?_ (mul_pos ha0sq (pow_pos hd21 2))
        have hle : 4 * lam ≤ 4 * lam ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = 4 / a0 ^ 2 * (lam * d 1 / (d 2 - d 1)) ^ 2 := heqB.symm

theorem fuchsRate_step4_tail_ratio_eventually_le
    {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (n : ℕ) :
    ∀ᶠ lam : ℝ in atTop,
      |lam * fuchsRate A₁ n lam /
          (fuchsRate A₂ (n + 4) lam - fuchsRate A₁ n lam)|
        ≤ 2 * (A₁ / A₂) * (lam ^ 7)⁻¹ := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num : (8 : ℕ) ≠ 0)).eventually_ge_atTop
      (2 * A₁ / A₂)] with lam hlam hpow
  have hF1pos : 0 < fuchsRate A₁ n lam := fuchsRate_pos hA₁ n hlam
  have hF2pos : 0 < fuchsRate A₂ (n + 4) lam := fuchsRate_pos hA₂ (n + 4) hlam
  have hhalf : fuchsRate A₁ n lam ≤ fuchsRate A₂ (n + 4) lam / 2 :=
    fuchsRate_le_half_step4 hA₂ hlam n hpow
  have hdenpos : 0 < fuchsRate A₂ (n + 4) lam - fuchsRate A₁ n lam := by linarith
  rw [abs_of_pos (div_pos (mul_pos hlam hF1pos) hdenpos)]
  calc
    lam * fuchsRate A₁ n lam /
          (fuchsRate A₂ (n + 4) lam - fuchsRate A₁ n lam)
        ≤ lam * fuchsRate A₁ n lam / (fuchsRate A₂ (n + 4) lam / 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hlam.le hF1pos.le) (half_pos hF2pos)
        (by linarith)
    _ = 2 * (A₁ / A₂) * (lam ^ 7)⁻¹ :=
      fuchsRate_tail_bound_eq hA₂.ne' hlam n

theorem min_norm_lp_normalize_sub_twoModeSeed_eventually_le
    {D L : ℝ → ℕ → ℝ} {a0 K : ℝ} (ha0 : a0 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ D lam 0 ∧ D lam 0 < D lam 1 ∧ D lam 1 < D lam 2) ∧
        ∀ j, D lam 2 ≤ D lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => L lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, L lam j ^ 2) ≤ 2 * lam)
    (hL0 : ∀ᶠ lam in atTop, L lam 0 ≠ 0)
    (hL1 : ∀ᶠ lam in atTop, L lam 1 ≠ 0)
    (hL0big : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ L lam 0 ^ 2)
    (hrate : ∀ᶠ lam in atTop,
      |lam * D lam 1 / (D lam 2 - D lam 1)| ≤ K * (lam ^ 7)⁻¹) :
    ∀ᶠ lam in atTop,
      min
          ‖(‖secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))‖)⁻¹ •
              secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))
            - (‖twoModeSeedLp (L lam)‖)⁻¹ • twoModeSeedLp (L lam)‖
          ‖(‖secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))‖)⁻¹ •
              secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))
            + (‖twoModeSeedLp (L lam)‖)⁻¹ • twoModeSeedLp (L lam)‖
        ≤ (1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) * K * (lam ^ 7)⁻¹ := by
  filter_upwards [hstruct, hsum, hbessel, hL0, hL1, hL0big, hrate,
    eventually_ge_atTop (1 : ℝ)] with lam hst hsm hbes h0 h1 hbig hrate' hlam
  obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
  have hmem : Memℓp (secularVector (D lam) (L lam)
      (infiniteSecularRoot (D lam) (L lam))) 2 :=
    memℓp_secularVector h01 h12 hd2 hsm h0 h1
  have hsecularsum : Summable fun j => secularVector (D lam) (L lam)
      (infiniteSecularRoot (D lam) (L lam)) j ^ 2 := by
    exact (summable_nat_add_iff
      (f := fun j => secularVector (D lam) (L lam)
        (infiniteSecularRoot (D lam) (L lam)) j ^ 2) 2).mp
      (summable_secularVector_sq_tail hd2 hsm (by linarith [hrmem.2]))
  have hv0 : secularVector (D lam) (L lam)
      (infiniteSecularRoot (D lam) (L lam)) 0 ≠ 0 := by
    rw [secularVector]
    exact div_ne_zero h0 (by linarith [hrmem.1])
  have hb := secular_defect_tail_bounds ha0
    ⟨⟨hd0, h01, h12⟩, hd2⟩ hsm hbes h0 h1 hbig hlam
  have halign := full_normalized_alignment_ge
    (V := secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam)))
    (G := twoModeSeedLp (L lam))
    (E := 16 / a0 ^ 4 * (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2)
    (F := 4 / a0 ^ 2 * (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2)
    (secularLp_coeFn hmem) (twoModeSeedLp_coeFn (L lam)) hsecularsum hv0 h0 hb.1 hb.2
  have hs : 0 ≤ 16 / a0 ^ 4 + 4 / a0 ^ 2 := by positivity
  have halign' : 1 - (16 / a0 ^ 4 + 4 / a0 ^ 2) *
        (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2
      ≤ inner ℝ
          (secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam)))
          (twoModeSeedLp (L lam)) ^ 2 /
        (‖secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))‖ ^ 2 *
          ‖twoModeSeedLp (L lam)‖ ^ 2) := by
    have hEF :
        16 / a0 ^ 4 * (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2 +
            4 / a0 ^ 2 * (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2
          = (16 / a0 ^ 4 + 4 / a0 ^ 2) *
            (lam * D lam 1 / (D lam 2 - D lam 1)) ^ 2 := by ring
    rw [hEF] at halign
    exact halign
  have hgeom := min_norm_sub_normalize_le_of_inner_sq
    (u := secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam)))
    (w := twoModeSeedLp (L lam))
    (s := 16 / a0 ^ 4 + 4 / a0 ^ 2)
    (r := lam * D lam 1 / (D lam 2 - D lam 1))
    (by
      intro hz
      apply hv0
      have hz0 : (((secularLp (D lam) (L lam)
          (infiniteSecularRoot (D lam) (L lam)) : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 0) = 0 := by
        rw [hz]
        rfl
      rw [secularLp_coeFn hmem] at hz0
      exact hz0)
    (by
      intro hz
      apply h0
      have hz1 : (((twoModeSeedLp (L lam) : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 1) = 0 := by
        rw [hz]
        rfl
      rw [twoModeSeedLp_coeFn, twoModeSeedFun_one] at hz1
      exact hz1)
    hs halign'
  calc
    min
          ‖(‖secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))‖)⁻¹ •
              secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))
            - (‖twoModeSeedLp (L lam)‖)⁻¹ • twoModeSeedLp (L lam)‖
          ‖(‖secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))‖)⁻¹ •
              secularLp (D lam) (L lam) (infiniteSecularRoot (D lam) (L lam))
            + (‖twoModeSeedLp (L lam)‖)⁻¹ • twoModeSeedLp (L lam)‖
        ≤ (1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) *
          |lam * D lam 1 / (D lam 2 - D lam 1)| := hgeom
    _ ≤ (1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) * (K * (lam ^ 7)⁻¹) :=
      mul_le_mul_of_nonneg_left hrate' (by linarith)
    _ = (1 + (16 / a0 ^ 4 + 4 / a0 ^ 2)) * K * (lam ^ 7)⁻¹ := by ring

theorem ccm_normalized_ground_distance_eventually_le
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      min
          ‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹ •
              secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
            - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
          ‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹ •
              secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
            + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
        ≤ (1 + (16 / ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 +
              4 / ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2)) *
            (2 * (A 1 / A 2)) * (lam ^ 7)⁻¹ := by
  let a0 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)
  have ha0 : a0 ≠ 0 := by dsimp [a0]; positivity
  have hbig : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by
      dsimp [a0]
      have : (0 : ℝ) < ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by positivity
      linarith))).mono fun _ hx => hx.le
  have hrate : ∀ᶠ lam in atTop,
      |lam * ccmFuchsScale A lam 1 /
          (ccmFuchsScale A lam 2 - ccmFuchsScale A lam 1)|
        ≤ 2 * (A 1 / A 2) * (lam ^ 7)⁻¹ := by
    simpa only [ccmFuchsScale, Nat.reduceMul, Nat.reduceAdd] using
      fuchsRate_step4_tail_ratio_eventually_le (hA 1) (hA 2) 4
  simpa only [ccmFuchsRoot, a0] using
    min_norm_lp_normalize_sub_twoModeSeed_eventually_le
      (D := fun lam => ccmFuchsScale A lam) (L := ℓ)
      ha0
      (ccm_struct hA hC hgrow) hsum hbessel (ccm_l0_ne_zero hl0)
      (ccm_l1_ne_zero hl1) hbig hrate

theorem isBigO_inv_pow_seven_of_eventually_le
    {f : ℝ → ℝ} {K : ℝ} (hf : ∀ lam, 0 ≤ f lam)
    (h : ∀ᶠ lam in atTop, f lam ≤ K * (lam ^ 7)⁻¹) :
    f =O[atTop] fun lam : ℝ => (lam ^ 7)⁻¹ := by
  refine IsBigO.of_bound K ?_
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with lam hle hlam
  rw [Real.norm_eq_abs, abs_of_nonneg (hf lam), Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hlam 7))]
  exact hle

theorem ccm_normalized_ground_distance_isBigO
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    (fun lam => min
        ‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹ •
            secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
        ‖(‖secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)‖)⁻¹ •
            secularLp (ccmFuchsScale A lam) (ℓ lam) (ccmFuchsRoot A ℓ lam)
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖)
      =O[atTop] fun lam : ℝ => (lam ^ 7)⁻¹ := by
  exact isBigO_inv_pow_seven_of_eventually_le
    (fun lam => le_min (norm_nonneg _) (norm_nonneg _))
    (ccm_normalized_ground_distance_eventually_le hA hC hgrow hsum hbessel hl0 hl1)

theorem ccmNegative_normalized_ground_distance_eventually_le
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    ∀ᶠ lam in atTop,
      min
          ‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
                (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
              secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
                (ccmNegativeFuchsRoot M ℓ lam)
            - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
          ‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
                (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
              secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
                (ccmNegativeFuchsRoot M ℓ lam)
            + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
        ≤ (1 + (16 / ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 4 +
              4 / ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2)) *
            (2 * (M 1 / M 2)) * (lam ^ 7)⁻¹ := by
  let a0 : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 4)
  have ha0 : a0 ≠ 0 := by dsimp [a0]; positivity
  have hbig : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by
      dsimp [a0]
      have : (0 : ℝ) < ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 := by positivity
      linarith))).mono fun _ hx => hx.le
  have hrate : ∀ᶠ lam in atTop,
      |lam * ccmNegativeFuchsScale M lam 1 /
          (ccmNegativeFuchsScale M lam 2 - ccmNegativeFuchsScale M lam 1)|
        ≤ 2 * (M 1 / M 2) * (lam ^ 7)⁻¹ := by
    simpa only [ccmNegativeFuchsScale, Nat.reduceMul, Nat.reduceAdd] using
      fuchsRate_step4_tail_ratio_eventually_le (hM 1) (hM 2) 6
  simpa only [ccmNegativeFuchsRoot, a0] using
    min_norm_lp_normalize_sub_twoModeSeed_eventually_le
      (D := fun lam => ccmNegativeFuchsScale M lam) (L := ℓ)
      ha0
      (ccmNegative_struct hM hC hgrow) hsum hbessel (ccmNegative_l0_ne_zero hl0)
      (ccmNegative_l1_ne_zero hl1) hbig hrate

theorem ccmNegative_normalized_ground_distance_isBigO
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop
      (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    (fun lam => min
        ‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
            secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)
          - (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖
        ‖(‖secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)‖)⁻¹ •
            secularLp (ccmNegativeFuchsScale M lam) (ℓ lam)
              (ccmNegativeFuchsRoot M ℓ lam)
          + (‖twoModeSeedLp (ℓ lam)‖)⁻¹ • twoModeSeedLp (ℓ lam)‖)
      =O[atTop] fun lam : ℝ => (lam ^ 7)⁻¹ := by
  exact isBigO_inv_pow_seven_of_eventually_le
    (fun lam => le_min (norm_nonneg _) (norm_nonneg _))
    (ccmNegative_normalized_ground_distance_eventually_le
      hM hC hgrow hsum hbessel hl0 hl1)

end RHTower

