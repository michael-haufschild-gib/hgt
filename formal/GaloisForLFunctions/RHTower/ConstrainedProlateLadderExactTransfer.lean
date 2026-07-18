import GaloisForLFunctions.RHTower.ConstrainedProlateDepthSecular
import GaloisForLFunctions.RHTower.ConstrainedProlateParityExactTransfer

/-!
# The exact Fuchs-model ladder: every depth, and the `λ⁸` adjacent separation

The radial Fuchs family `d_λ(j) = A_j·λ^(8j+1)·e^(−4πλ²)` satisfies the depth-`k` transfer
hypotheses of the flattening sandwich at every fixed depth: the head is ordered below `d_k` once
`λ⁸` clears the finitely many head constant ratios, the two gap inequalities hold once it clears
the two adjacent ones, the floor above `d_{k+2}` follows from tempered growth of the Fuchs
constants, and the collapse and tail rates are the usual `λ⁻⁸` and `λ⁻⁷` cancellations of the
Gaussian clock.

Consequently the exact constrained root in the `k`-th spectral gap of the Fuchs model obeys the
Hermite ladder law `μ_k(λ)/d_{k+1}(λ) → θ_k` for every `k`, and dividing two consecutive exact
roots exposes the rigid scale separation of the ladder:

```text
(μ_{k+1}(λ)/μ_k(λ)) / λ⁸ → (θ_{k+1}/θ_k) · A_{k+2}/A_{k+1}.
```

Only the constraint-coordinate inputs (Bessel bound and prolate-to-Hermite limits) remain as
hypotheses; the entire leakage side is discharged.
-/

open Filter

namespace RHTower

/-- The radial Fuchs family satisfies the depth-`k` ordered-head structural hypothesis for all
sufficiently large apertures. -/
theorem fuchsRate_radial_depth_struct {A : ℕ → ℝ} (hA : ∀ j, 0 < A j)
    {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hgrow : ∀ j, A (k + 2) ≤ C ^ j * A (j + (k + 2))) :
    ∀ᶠ lam : ℝ in atTop,
      ((∀ j, j ≤ k → 0 ≤ fuchsRate (A j) (4 * j) lam ∧
          fuchsRate (A j) (4 * j) lam ≤ fuchsRate (A k) (4 * k) lam) ∧
        fuchsRate (A k) (4 * k) lam < fuchsRate (A (k + 1)) (4 * (k + 1)) lam ∧
        fuchsRate (A (k + 1)) (4 * (k + 1)) lam < fuchsRate (A (k + 2)) (4 * (k + 2)) lam) ∧
      ∀ j, fuchsRate (A (k + 2)) (4 * (k + 2)) lam
        ≤ fuchsRate (A (j + (k + 2))) (4 * (j + (k + 2))) lam := by
  have hhead_ev : ∀ᶠ lam : ℝ in atTop,
      ∀ j ∈ Finset.range (k + 1), A j / A k ≤ lam ^ 8 :=
    (eventually_all_finset (Finset.range (k + 1))).2 fun j _ =>
      (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop C, hhead_ev,
    (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A k / A (k + 1)),
    (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A (k + 1) / A (k + 2))]
    with lam hl1 hlC hall hpk hpk1
  have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
  have hE : (0 : ℝ) < Real.exp (-(4 * Real.pi * lam ^ 2)) := Real.exp_pos _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- the ordered head
    intro j hjk
    refine ⟨(fuchsRate_pos (hA j) _ hlam).le, ?_⟩
    rcases eq_or_lt_of_le hjk with heq | hlt
    · rw [heq]
    · have h2 : A j / A k ≤ lam ^ 8 := hall j (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))
      have h3 : A j / A k ≤ lam ^ (8 * (k - j)) :=
        le_trans h2 (pow_le_pow_right₀ hl1 (by omega))
      have h1' : A j ≤ lam ^ (8 * (k - j)) * A k := (div_le_iff₀ (hA k)).mp h3
      have hkey : A j * lam ^ (2 * (4 * j) + 1) ≤ A k * lam ^ (2 * (4 * k) + 1) := by
        rw [show 2 * (4 * j) + 1 = 8 * j + 1 from by ring,
          show 2 * (4 * k) + 1 = 8 * k + 1 from by ring]
        calc A j * lam ^ (8 * j + 1)
            ≤ lam ^ (8 * (k - j)) * A k * lam ^ (8 * j + 1) :=
              mul_le_mul_of_nonneg_right h1' (pow_nonneg hlam.le _)
          _ = A k * (lam ^ (8 * (k - j)) * lam ^ (8 * j + 1)) := by ring
          _ = A k * lam ^ (8 * (k - j) + (8 * j + 1)) := by rw [← pow_add]
          _ = A k * lam ^ (8 * k + 1) := by
              rw [show 8 * (k - j) + (8 * j + 1) = 8 * k + 1 from by omega]
      exact mul_le_mul_of_nonneg_right hkey hE.le
  · -- `d_k < d_{k+1}`
    have hAlt : A k < lam ^ 8 * A (k + 1) := (div_lt_iff₀ (hA (k + 1))).mp hpk
    have hkey : A k * lam ^ (2 * (4 * k) + 1) < A (k + 1) * lam ^ (2 * (4 * (k + 1)) + 1) := by
      rw [show 2 * (4 * k) + 1 = 8 * k + 1 from by ring,
        show 2 * (4 * (k + 1)) + 1 = 8 + (8 * k + 1) from by ring]
      calc A k * lam ^ (8 * k + 1)
          < lam ^ 8 * A (k + 1) * lam ^ (8 * k + 1) :=
            mul_lt_mul_of_pos_right hAlt (pow_pos hlam _)
        _ = A (k + 1) * (lam ^ 8 * lam ^ (8 * k + 1)) := by ring
        _ = A (k + 1) * lam ^ (8 + (8 * k + 1)) := by rw [← pow_add]
    exact mul_lt_mul_of_pos_right hkey hE
  · -- `d_{k+1} < d_{k+2}`
    have hAlt : A (k + 1) < lam ^ 8 * A (k + 2) := (div_lt_iff₀ (hA (k + 2))).mp hpk1
    have hkey : A (k + 1) * lam ^ (2 * (4 * (k + 1)) + 1)
        < A (k + 2) * lam ^ (2 * (4 * (k + 2)) + 1) := by
      rw [show 2 * (4 * (k + 1)) + 1 = 8 * k + 9 from by ring,
        show 2 * (4 * (k + 2)) + 1 = 8 + (8 * k + 9) from by ring]
      calc A (k + 1) * lam ^ (8 * k + 9)
          < lam ^ 8 * A (k + 2) * lam ^ (8 * k + 9) :=
            mul_lt_mul_of_pos_right hAlt (pow_pos hlam _)
        _ = A (k + 2) * (lam ^ 8 * lam ^ (8 * k + 9)) := by ring
        _ = A (k + 2) * lam ^ (8 + (8 * k + 9)) := by rw [← pow_add]
    exact mul_lt_mul_of_pos_right hkey hE
  · -- the floor above `d_{k+2}`
    intro j
    have hCj : C ^ j ≤ lam ^ (8 * j) := by
      calc C ^ j ≤ lam ^ j := pow_le_pow_left₀ (le_trans zero_le_one hC) hlC j
        _ ≤ lam ^ (8 * j) := pow_le_pow_right₀ hl1 (by omega)
    have hA2le : A (k + 2) ≤ A (j + (k + 2)) * lam ^ (8 * j) := by
      calc A (k + 2) ≤ C ^ j * A (j + (k + 2)) := hgrow j
        _ ≤ lam ^ (8 * j) * A (j + (k + 2)) :=
          mul_le_mul_of_nonneg_right hCj (hA _).le
        _ = A (j + (k + 2)) * lam ^ (8 * j) := mul_comm _ _
    have hkey : A (k + 2) * lam ^ (2 * (4 * (k + 2)) + 1)
        ≤ A (j + (k + 2)) * lam ^ (2 * (4 * (j + (k + 2))) + 1) := by
      rw [show 2 * (4 * (k + 2)) + 1 = 8 * k + 17 from by ring,
        show 2 * (4 * (j + (k + 2))) + 1 = 8 * j + (8 * k + 17) from by ring]
      calc A (k + 2) * lam ^ (8 * k + 17)
          ≤ A (j + (k + 2)) * lam ^ (8 * j) * lam ^ (8 * k + 17) :=
            mul_le_mul_of_nonneg_right hA2le (pow_nonneg hlam.le _)
        _ = A (j + (k + 2)) * (lam ^ (8 * j) * lam ^ (8 * k + 17)) := by ring
        _ = A (j + (k + 2)) * lam ^ (8 * j + (8 * k + 17)) := by rw [← pow_add]
    exact mul_le_mul_of_nonneg_right hkey hE.le

/-- **The exact CCM ladder law in the Fuchs model, at every depth.**  With the Hermite
coordinate limits, the exact constrained root in the `k`-th gap of the radial Fuchs family
obeys `μ_k(λ)/d_{k+1}(λ) → θ_k = Q_k/Q_{k+1}`. -/
theorem ccm_fuchsModel_depthSecularRoot_ratio_tendsto
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hgrow : ∀ j, A (k + 2) ≤ C ^ j * A (j + (k + 2)))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 1 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam =>
      depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) k /
        fuchsRate (A (k + 1)) (4 * (k + 1)) lam) atTop
      (nhds (constrainedProlateHermiteTheta k)) :=
  ccm_depthSecularRoot_ratio_tendsto
    (d := fun lam j => fuchsRate (A j) (4 * j) lam)
    (fuchsRate_radial_depth_struct hA hC k hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hA (k + 1)) (hA k) (4 * k) (k := 4) (by norm_num))
    (fuchsRate_step4_tail_ratio_tendsto_zero (hA (k + 1)) (hA (k + 2)) (4 * (k + 1)))
    hl

/-- **The exact-root `λ⁸` adjacent scale separation.**  Two consecutive exact constrained roots
of the Fuchs-model ladder separate by exactly the eighth power of the aperture, with the
explicit Hermite-Fuchs coefficient `(θ_{k+1}/θ_k)·A_{k+2}/A_{k+1}` — the card's adjacent-gap
law for the true infinite-dimensional constrained spectrum. -/
theorem ccm_fuchsModel_ladder_adjacent_scaled_ratio_tendsto
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C) (k : ℕ)
    (hgrow2 : ∀ j, A (k + 2) ≤ C ^ j * A (j + (k + 2)))
    (hgrow3 : ∀ j, A (k + 3) ≤ C ^ j * A (j + (k + 3)))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl : ∀ j, j ≤ k + 2 → Tendsto (fun lam => ℓ lam j) atTop
      (nhds (constrainedProlateHermiteCoordinate j))) :
    Tendsto (fun lam =>
      (depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) (k + 1) /
        depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) k) / lam ^ 8)
      atTop (nhds ((constrainedProlateHermiteTheta (k + 1) /
        constrainedProlateHermiteTheta k) * (A (k + 2) / A (k + 1)))) := by
  have hθk := constrainedProlateHermiteTheta_mem_Ioo k
  have hθk1 := constrainedProlateHermiteTheta_mem_Ioo (k + 1)
  have hk := ccm_fuchsModel_depthSecularRoot_ratio_tendsto hA hC k hgrow2 hsum hbessel
    fun j hj => hl j (le_trans hj (Nat.le_succ _))
  have hk1 := ccm_fuchsModel_depthSecularRoot_ratio_tendsto hA hC (k + 1) hgrow3 hsum hbessel hl
  -- the scale bridge is eventually constant
  have hbridge : Tendsto (fun lam : ℝ =>
      fuchsRate (A (k + 2)) (4 * (k + 2)) lam /
        (lam ^ 8 * fuchsRate (A (k + 1)) (4 * (k + 1)) lam)) atTop
      (nhds (A (k + 2) / A (k + 1))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    unfold fuchsRate
    have hE : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
    rw [show 2 * (4 * (k + 2)) + 1 = 8 + (2 * (4 * (k + 1)) + 1) from by ring, pow_add]
    field_simp
  -- eventual positivity of the two exact roots
  have hd1pos : ∀ᶠ lam : ℝ in atTop, 0 < fuchsRate (A (k + 1)) (4 * (k + 1)) lam := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    exact fuchsRate_pos (hA (k + 1)) _ hlam
  have hd2pos : ∀ᶠ lam : ℝ in atTop, 0 < fuchsRate (A (k + 2)) (4 * (k + 2)) lam := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    exact fuchsRate_pos (hA (k + 2)) _ hlam
  have hrkpos : ∀ᶠ lam : ℝ in atTop,
      0 < depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) k := by
    have h1 := hk.eventually (eventually_gt_nhds (half_lt_self hθk.1))
    filter_upwards [h1, hd1pos] with lam hgt hd1
    have hfrac : 0 < depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) k /
        fuchsRate (A (k + 1)) (4 * (k + 1)) lam :=
      lt_trans (half_pos hθk.1) hgt
    by_contra hle
    push Not at hle
    exact absurd (div_nonpos_of_nonpos_of_nonneg hle hd1.le) (not_le.mpr hfrac)
  have hrk1pos : ∀ᶠ lam : ℝ in atTop,
      0 < depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) (k + 1) := by
    have h1 := hk1.eventually (eventually_gt_nhds (half_lt_self hθk1.1))
    filter_upwards [h1, hd2pos] with lam hgt hd2
    have hfrac : 0 < depthSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) (k + 1) /
        fuchsRate (A (k + 2)) (4 * (k + 2)) lam :=
      lt_trans (half_pos hθk1.1) hgt
    by_contra hle
    push Not at hle
    exact absurd (div_nonpos_of_nonpos_of_nonneg hle hd2.le) (not_le.mpr hfrac)
  -- assemble the limit
  have hkinv := hk.inv₀ hθk.1.ne'
  have h1 := (hk1.mul hbridge).mul hkinv
  have hval : constrainedProlateHermiteTheta (k + 1) * (A (k + 2) / A (k + 1)) *
      (constrainedProlateHermiteTheta k)⁻¹
      = (constrainedProlateHermiteTheta (k + 1) / constrainedProlateHermiteTheta k) *
        (A (k + 2) / A (k + 1)) := by
    field_simp
  rw [hval] at h1
  refine h1.congr' ?_
  filter_upwards [hd1pos, hd2pos, hrkpos, hrk1pos, eventually_gt_atTop (0 : ℝ)]
    with lam hd1 hd2 hrk hrk1 hlam
  have hlam8 : lam ^ 8 ≠ 0 := pow_ne_zero _ hlam.ne'
  field_simp

end RHTower
