import GaloisForLFunctions.RHTower.ConstrainedProlateHeadDistance
import GaloisForLFunctions.RHTower.ConstrainedProlateOperatorIdentification

/-!
# The constrained ground vector in metric form

The head of the exact constrained eigenvector converges to the two-mode seed direction; the rest
of the eigenvector carries vanishing mass.  Together these say that the *whole* `ℓ²` eigenvector,
normalized, converges to the normalized seed up to a sign.

Two factors carry the statement.  Writing `H` for the head, `T` for the squared tail mass and `G`
for the seed — which is supported on the first two coordinates — the seed sees only the head, so

```text
⟪V, G⟫² / (‖V‖²‖G‖²) = [⟪H, G⟫² / (‖H‖²‖G‖²)] · [‖H‖² / (‖H‖² + T)].
```

The first bracket tends to one because the head–constraint defect collapses; the second because
the tail fraction does, `‖H‖² ≥ v₀²` giving `T/‖H‖² ≤ T/v₀²`.  A product of two quantities tending
to one tends to one, and the sign-choice lemma converts that into the vanishing of the
sign-optimized distance.
-/

open Filter GaloisForLFunctions
open scoped Real

noncomputable section

namespace RHTower

/-! ## The seed as an `ℓ²` vector -/

/-- The two-mode seed as a sequence: supported on the first two coordinates. -/
def twoModeSeedFun (ℓ : ℕ → ℝ) : ℕ → ℝ := fun j =>
  if j = 0 then -(ℓ 1) else if j = 1 then ℓ 0 else 0

theorem twoModeSeedFun_eq_zero {ℓ : ℕ → ℝ} {j : ℕ} (hj : j ∉ ({0, 1} : Finset ℕ)) :
    twoModeSeedFun ℓ j = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  rw [twoModeSeedFun]
  simp [hj.1, hj.2]

@[simp] theorem twoModeSeedFun_zero (ℓ : ℕ → ℝ) : twoModeSeedFun ℓ 0 = -(ℓ 1) := rfl

@[simp] theorem twoModeSeedFun_one (ℓ : ℕ → ℝ) : twoModeSeedFun ℓ 1 = ℓ 0 := by
  rw [twoModeSeedFun]
  norm_num

/-- A sequence vanishing off the first two coordinates has its series equal to the two-term sum. -/
theorem tsum_of_support_le_two {f : ℕ → ℝ} (hf : ∀ j ∉ ({0, 1} : Finset ℕ), f j = 0) :
    ∑' j : ℕ, f j = f 0 + f 1 := by
  rw [tsum_eq_sum hf]
  simp [Finset.sum_insert, Finset.mem_singleton]

/-! ## Coordinates of the `ℓ²` quantities -/

variable {D L : ℝ → ℕ → ℝ} {M : ℝ → ℝ}

/-- The squared norm of an `ℓ²` vector is the sum of its squared coordinates. -/
theorem lp_norm_sq_eq_tsum (f : lp (fun _ : ℕ => ℝ) 2) :
    ‖f‖ ^ (2 : ℕ) = ∑' j : ℕ, (f : ℕ → ℝ) j ^ (2 : ℕ) := by
  rw [← real_inner_self_eq_norm_sq, lp_inner_eq_tsum_mul]
  exact tsum_congr fun j => (sq _).symm

/-- The pairing of a vector with the seed sees only the head coordinates. -/
theorem lp_inner_twoModeSeed (V G : lp (fun _ : ℕ => ℝ) 2) {ℓ : ℕ → ℝ}
    (hG : (G : ℕ → ℝ) = twoModeSeedFun ℓ) :
    inner ℝ V G = -((V : ℕ → ℝ) 0 * ℓ 1) + (V : ℕ → ℝ) 1 * ℓ 0 := by
  rw [lp_inner_eq_tsum_mul]
  rw [tsum_of_support_le_two (f := fun j => (V : ℕ → ℝ) j * (G : ℕ → ℝ) j) ?_]
  · rw [hG, twoModeSeedFun_zero, twoModeSeedFun_one]
    ring
  · intro j hj
    simp only [hG, twoModeSeedFun_eq_zero hj, mul_zero]

/-- The squared norm of the seed. -/
theorem lp_norm_sq_twoModeSeed (G : lp (fun _ : ℕ => ℝ) 2) {ℓ : ℕ → ℝ}
    (hG : (G : ℕ → ℝ) = twoModeSeedFun ℓ) :
    ‖G‖ ^ (2 : ℕ) = ℓ 0 ^ (2 : ℕ) + ℓ 1 ^ (2 : ℕ) := by
  rw [lp_norm_sq_eq_tsum]
  rw [tsum_of_support_le_two (f := fun j => (G : ℕ → ℝ) j ^ (2 : ℕ)) ?_]
  · rw [hG, twoModeSeedFun_zero, twoModeSeedFun_one]
    ring
  · intro j hj
    simp [hG, twoModeSeedFun_eq_zero hj]

/-! ## The mass ratio -/

/-- A relative remainder tending to zero makes the retained fraction tend to one. -/
theorem tendsto_ratio_one_of_tendsto_zero {T Hd : ℝ → ℝ}
    (hH : ∀ᶠ lam in atTop, 0 < Hd lam) (hT : ∀ᶠ lam in atTop, 0 ≤ T lam)
    (h : Tendsto (fun lam => T lam / Hd lam) atTop (nhds 0)) :
    Tendsto (fun lam => Hd lam / (Hd lam + T lam)) atTop (nhds 1) := by
  have h1 : Tendsto (fun lam => 1 + T lam / Hd lam) atTop (nhds (1 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds h
  rw [add_zero] at h1
  have h2 : Tendsto (fun lam => (1 + T lam / Hd lam)⁻¹) atTop (nhds ((1 : ℝ))⁻¹) :=
    h1.inv₀ one_ne_zero
  rw [inv_one] at h2
  refine h2.congr' ?_
  filter_upwards [hH, hT] with lam hpos hTnn
  have hne : Hd lam ≠ 0 := ne_of_gt hpos
  have hrw : (1 : ℝ) + T lam / Hd lam = (Hd lam + T lam) / Hd lam := by field_simp
  rw [hrw, inv_div]

/-! ## Head/tail splitting -/

/-- The squared norm of the full eigenvector splits into head and tail mass. -/
theorem lp_norm_sq_split (V : lp (fun _ : ℕ => ℝ) 2) {d ℓ : ℕ → ℝ} {μ : ℝ}
    (hV : (V : ℕ → ℝ) = secularVector d ℓ μ)
    (hsum : Summable fun j => secularVector d ℓ μ j ^ (2 : ℕ)) :
    ‖V‖ ^ (2 : ℕ) = ‖secularHead d ℓ μ‖ ^ (2 : ℕ) + ∑' j : ℕ, secularVector d ℓ μ (j + 2) ^ (2 : ℕ) := by
  rw [lp_norm_sq_eq_tsum, hV, norm_sq_secularHead, ← Summable.sum_add_tsum_nat_add 2 hsum]
  congr 1
  simp [Finset.sum_range_succ]

/-! ## The metric form for the full vector -/

/-- **The exact constrained ground vector converges to the two-mode seed, in `ℓ²`.**  The
normalized full eigenvector approaches the normalized seed up to a sign.

The two hypotheses `hdefect` and `htailfrac` are verbatim the conclusions of
`secularVector_head_seed_defect_tendsto_zero` and `secularVector_tail_fraction_tendsto_zero`. -/
theorem tendsto_min_norm_lp_normalize_sub_twoModeSeed
    {V G : ℝ → lp (fun _ : ℕ => ℝ) 2} {D L : ℝ → ℕ → ℝ} {M : ℝ → ℝ}
    (hV : ∀ᶠ lam in atTop, ((V lam : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ)
      = secularVector (D lam) (L lam) (M lam))
    (hG : ∀ᶠ lam in atTop, ((G lam : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) = twoModeSeedFun (L lam))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => secularVector (D lam) (L lam) (M lam) j ^ (2 : ℕ))
    (hv0 : ∀ᶠ lam in atTop, secularVector (D lam) (L lam) (M lam) 0 ≠ 0)
    (hL0 : ∀ᶠ lam in atTop, L lam 0 ≠ 0)
    (hdefect : Tendsto (fun lam =>
      (L lam 0 * secularVector (D lam) (L lam) (M lam) 0
          + L lam 1 * secularVector (D lam) (L lam) (M lam) 1) ^ (2 : ℕ)
        / ((secularVector (D lam) (L lam) (M lam) 0 ^ (2 : ℕ)
              + secularVector (D lam) (L lam) (M lam) 1 ^ (2 : ℕ))
            * (L lam 0 ^ (2 : ℕ) + L lam 1 ^ (2 : ℕ)))) atTop (nhds 0))
    (htailfrac : Tendsto (fun lam =>
      (∑' j : ℕ, secularVector (D lam) (L lam) (M lam) (j + 2) ^ (2 : ℕ))
        / secularVector (D lam) (L lam) (M lam) 0 ^ (2 : ℕ)) atTop (nhds 0)) :
    Tendsto (fun lam => min
        (‖(‖V lam‖)⁻¹ • V lam - (‖G lam‖)⁻¹ • G lam‖ ^ (2 : ℕ))
        (‖(‖V lam‖)⁻¹ • V lam + (‖G lam‖)⁻¹ • G lam‖ ^ (2 : ℕ))) atTop (nhds 0) := by
  have hHpos : ∀ᶠ lam in atTop, 0 < ‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ) := by
    filter_upwards [hv0] with lam h0
    exact pow_pos (norm_pos_iff.mpr (secularHead_ne_zero _ _ _ h0)) 2
  have hTnn : ∀ᶠ lam in atTop,
      0 ≤ ∑' j : ℕ, secularVector (D lam) (L lam) (M lam) (j + 2) ^ (2 : ℕ) :=
    Eventually.of_forall fun lam => tsum_nonneg fun j => sq_nonneg _
  -- the tail is small relative to the head mass
  have hratio : Tendsto (fun lam =>
      (∑' j : ℕ, secularVector (D lam) (L lam) (M lam) (j + 2) ^ (2 : ℕ))
        / ‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ)) atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun lam =>
      div_nonneg (tsum_nonneg fun j => sq_nonneg _) (sq_nonneg _)) ?_ htailfrac
    filter_upwards [hv0] with lam h0
    rw [norm_sq_secularHead]
    have hv0sq : 0 < secularVector (D lam) (L lam) (M lam) 0 ^ (2 : ℕ) :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
    exact div_le_div_of_nonneg_left (tsum_nonneg fun j => sq_nonneg _) hv0sq
      (by nlinarith [sq_nonneg (secularVector (D lam) (L lam) (M lam) 1)])
  have hmass := tendsto_ratio_one_of_tendsto_zero hHpos hTnn hratio
  -- the head alignment tends to one
  have halign : Tendsto (fun lam =>
      inner ℝ (secularHead (D lam) (L lam) (M lam)) (twoModeSeed (L lam)) ^ (2 : ℕ)
        / (‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ) * ‖twoModeSeed (L lam)‖ ^ (2 : ℕ)))
      atTop (nhds 1) := by
    have h1 : Tendsto (fun lam => 1 -
        (L lam 0 * secularVector (D lam) (L lam) (M lam) 0
            + L lam 1 * secularVector (D lam) (L lam) (M lam) 1) ^ (2 : ℕ)
          / ((secularVector (D lam) (L lam) (M lam) 0 ^ (2 : ℕ)
                + secularVector (D lam) (L lam) (M lam) 1 ^ (2 : ℕ))
              * (L lam 0 ^ (2 : ℕ) + L lam 1 ^ (2 : ℕ)))) atTop (nhds (1 - 0)) :=
      Filter.Tendsto.sub tendsto_const_nhds hdefect
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [hv0, hL0] with lam h0 h1'
    rw [defect_eq_inner_sq_div]
    exact (align_eq_one_sub_defect (D lam) (L lam) (M lam) h0 h1').symm
  have hprod : Tendsto (fun lam =>
      (inner ℝ (secularHead (D lam) (L lam) (M lam)) (twoModeSeed (L lam)) ^ (2 : ℕ)
        / (‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ) * ‖twoModeSeed (L lam)‖ ^ (2 : ℕ)))
      * (‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ)
          / (‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ)
            + ∑' j : ℕ, secularVector (D lam) (L lam) (M lam) (j + 2) ^ (2 : ℕ))))
      atTop (nhds (1 * 1)) := halign.mul hmass
  rw [one_mul] at hprod
  refine tendsto_min_norm_sub_sq_normalize_of_inner_sq ?_ ?_ ?_
  · filter_upwards [hv0, hV] with lam h0 hVl
    intro hz
    apply h0
    have hc : ((V lam : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 0
        = ((0 : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 0 := by rw [hz]
    rw [hVl] at hc
    simpa using hc
  · filter_upwards [hL0, hG] with lam h0 hGl
    intro hz
    apply h0
    have hc : ((G lam : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 1
        = ((0 : lp (fun _ : ℕ => ℝ) 2) : ℕ → ℝ) 1 := by rw [hz]
    rw [hGl, twoModeSeedFun_one] at hc
    simpa using hc
  · refine hprod.congr' ?_
    filter_upwards [hsum, hv0, hL0, hV, hG] with lam hsm h0 h1' hVl hGl
    rw [lp_inner_twoModeSeed (V lam) (G lam) hGl, hVl,
      lp_norm_sq_split (V lam) hVl hsm, lp_norm_sq_twoModeSeed (G lam) hGl,
      inner_secularHead_twoModeSeed, norm_sq_twoModeSeed]
    have hHne : ‖secularHead (D lam) (L lam) (M lam)‖ ^ (2 : ℕ) ≠ 0 :=
      ne_of_gt (pow_pos (norm_pos_iff.mpr (secularHead_ne_zero _ _ _ h0)) 2)
    rw [norm_sq_secularHead] at hHne ⊢
    field_simp

end RHTower

end
