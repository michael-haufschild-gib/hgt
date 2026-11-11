import GaloisForLFunctions.ShortIntervalPrimesInProgressions.ZeroDensityForACharacter
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LittlewoodZeroFreeRegion
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterSumsInShortWindows

/-!
# The weighted zero sum vanishes

For a primitive nonprincipal character `χ` and `0 < u < u₁/4`, `u₁ = 1/(14·10⁷ + 12)`,

`Σ_ρ x^{β−1} min(1, c x^{2u}/(|ρ||1 − ρ|)) → 0`   (`x → ∞`)

(`tendsto_tsum_zeroShortWeight`).  With `P_ρ = |ρ||1 − ρ|` and `T₁ = x^{u₁}`:

* zeros with `β ≤ 3/4` contribute at most `x^{−1/4} (c x^{2u})^{3/4} Σ P^{−3/4}`;
* zeros with `|γ| > T₁` contribute at most `c x^{2u} T₁^{−1/2} Σ P^{−3/4}`;
* the remaining zeros, `β > 3/4` and `|γ| ≤ T₁`, are cut into slabs `σ_k ≤ β < σ_k + 1/log x`; the
  density estimate bounds a slab by `D (1 + log T₁)^{11} T₁^{12(1 − σ_k)}`, and Littlewood's region
  gives `1 − σ_k ≥ w₁ = c₀ log log T₁/log T₁`, so the slab sum is
  `≪ (log x)^{12} x^{−(1 − 12u₁) w₁} = (log x)^{12} (u₁ log x)^{−14}`.

`Σ P^{−3/4} < ∞` comes from the convergence exponent `1` of the zeros (`summable_rpow_three_quarters`).
-/

open Complex Filter Topology Finset

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- `Σ_ρ (|ρ||1 − ρ|)^{−3/4} < ∞`. -/
theorem summable_rpow_three_quarters (hχ : χ ≠ 1) :
    Summable (fun r : LZero χ => (‖r.point‖ * ‖1 - r.point‖) ^ (-(3 / 4 : ℝ))) := by
  have hev := RHTower.eventually_norm_ge_of_summable_inv_sq (zeroCopyPoint_ne_zero' hχ)
    (summable_inv_sq hχ) (S := 4) (by norm_num)
  refine Summable.of_norm_bounded_eventually
    (g := fun r => 3 * ‖EntireZeroDivisor.zeroCopyPoint (shiftedL χ) r‖ ^ (-(3 / 2 : ℝ)))
    ((summable_norm_rpow_neg hχ (by norm_num : (1 : ℝ) < 3 / 2)).mul_left _) ?_
  filter_upwards [hev] with r hr
  set w := EntireZeroDivisor.zeroCopyPoint (shiftedL χ) r
  have hpt : r.point = w + 2 := rfl
  have hw0 : 0 < ‖w‖ := by linarith
  have hρ : ‖w‖ / 2 ≤ ‖r.point‖ := by
    rw [hpt]
    have := norm_sub_norm_le w (-(2 : ℂ))
    rw [sub_neg_eq_add, norm_neg] at this
    norm_num at this
    linarith
  have hρ1 : 3 * ‖w‖ / 4 ≤ ‖1 - r.point‖ := by
    rw [hpt, show 1 - (w + 2) = -(w - (-1)) by ring, norm_neg]
    have := norm_sub_norm_le w (-1 : ℂ)
    rw [norm_neg, norm_one] at this
    linarith
  have hP : 3 / 8 * ‖w‖ ^ 2 ≤ ‖r.point‖ * ‖1 - r.point‖ := by
    calc 3 / 8 * ‖w‖ ^ 2 = (‖w‖ / 2) * (3 * ‖w‖ / 4) := by ring
      _ ≤ _ := mul_le_mul hρ hρ1 (by positivity) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (‖r.point‖ * ‖1 - r.point‖) ^ (-(3 / 4 : ℝ)) ≤ (3 / 8 * ‖w‖ ^ 2) ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hP (by norm_num)
    _ = (3 / 8 : ℝ) ^ (-(3 / 4 : ℝ)) * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul hw0.le]
        norm_num
    _ ≤ 3 * ‖w‖ ^ (-(3 / 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hw0.le _)
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
        calc (3 / 8 : ℝ)⁻¹ ^ (3 / 4 : ℝ) ≤ (3 / 8 : ℝ)⁻¹ ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ ≤ 3 := by norm_num

/-- `min(1, z) ≤ z^{3/4}` for `z ≥ 0`. -/
theorem min_one_le_rpow_three_quarters {z : ℝ} (hz : 0 ≤ z) : min 1 z ≤ z ^ (3 / 4 : ℝ) := by
  rcases le_total z 1 with h | h
  · rw [min_eq_right h]
    rcases hz.eq_or_lt with h0 | hpos
    · rw [← h0]; exact Real.rpow_nonneg le_rfl _
    calc z = z ^ (1 : ℝ) := (Real.rpow_one z).symm
      _ ≤ z ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hpos h (by norm_num)
  · rw [min_eq_left h]
    exact Real.one_le_rpow h (by norm_num)

/-- **The pointwise split of the weight.**  Away from the near zeros (`β > 3/4`, `|γ| ≤ T₁`) the
weight is at most `(x^{−1/4} Y^{3/4} + Y T₁^{−1/2}) P^{−3/4}`. -/
theorem zeroShortWeight_le_split (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {x Y T₁ : ℝ} (hx : 1 ≤ x)
    (hY : 0 ≤ Y) (hT₁ : 0 < T₁) (r : LZero χ) :
    RHTower.zeroShortWeight x Y r.point ≤
      (x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))) *
          (‖r.point‖ * ‖1 - r.point‖) ^ (-(3 / 4 : ℝ)) +
        (if 3 / 4 < r.point.re ∧ |r.point.im| ≤ T₁ then x ^ (r.point.re - 1) else 0) := by
  have hρ0 : 0 < ‖r.point‖ := norm_pos_iff.mpr (point_ne_zero hχ hprim r)
  have hρ1 : 0 < ‖1 - r.point‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (point_ne_one hχ hprim r).symm)
  set P := ‖r.point‖ * ‖1 - r.point‖ with hPdef
  have hP0 : 0 < P := mul_pos hρ0 hρ1
  have hx0 : 0 < x := by linarith
  have hβ1 : r.point.re < 1 := (zero_re_mem hχ hprim r).2
  have hxβ : x ^ (r.point.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hmin0 : 0 ≤ min 1 (Y / P) := le_min zero_le_one (by positivity)
  have hPpow : 0 ≤ P ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hP0.le _
  have hfirst0 : 0 ≤ (x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))) *
      P ^ (-(3 / 4 : ℝ)) := by positivity
  unfold RHTower.zeroShortWeight
  by_cases hnear : 3 / 4 < r.point.re ∧ |r.point.im| ≤ T₁
  · rw [if_pos hnear]
    have : x ^ (r.point.re - 1) * min 1 (Y / P) ≤ x ^ (r.point.re - 1) :=
      mul_le_of_le_one_right (Real.rpow_nonneg hx0.le _) (min_le_left _ _)
    linarith
  · rw [if_neg hnear, add_zero]
    rcases le_or_gt r.point.re (3 / 4) with hlow | hhigh
    · -- `β ≤ 3/4`
      have h1 : x ^ (r.point.re - 1) ≤ x ^ (-(1 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have h2 : min 1 (Y / P) ≤ Y ^ (3 / 4 : ℝ) * P ^ (-(3 / 4 : ℝ)) := by
        refine (min_one_le_rpow_three_quarters (by positivity)).trans (le_of_eq ?_)
        rw [Real.div_rpow hY hP0.le, Real.rpow_neg hP0.le, div_eq_mul_inv]
      calc x ^ (r.point.re - 1) * min 1 (Y / P)
          ≤ x ^ (-(1 / 4 : ℝ)) * (Y ^ (3 / 4 : ℝ) * P ^ (-(3 / 4 : ℝ))) :=
            mul_le_mul h1 h2 hmin0 (Real.rpow_nonneg hx0.le _)
        _ ≤ (x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))) *
              P ^ (-(3 / 4 : ℝ)) := by
            have : 0 ≤ Y * T₁ ^ (-(1 / 2 : ℝ)) * P ^ (-(3 / 4 : ℝ)) := by positivity
            nlinarith
    · -- `|γ| > T₁`
      have hfar : T₁ < |r.point.im| := by
        by_contra h
        exact hnear ⟨hhigh, not_lt.mp h⟩
      have hPγ : T₁ ^ 2 ≤ P := by
        have h1 : |r.point.im| ≤ ‖r.point‖ := Complex.abs_im_le_norm _
        have h2 : |r.point.im| ≤ ‖1 - r.point‖ := by
          have := Complex.abs_im_le_norm (1 - r.point)
          rwa [sub_im, one_im, zero_sub, abs_neg] at this
        nlinarith [abs_nonneg r.point.im]
      have hP14 : P ^ (-(1 / 4 : ℝ)) ≤ T₁ ^ (-(1 / 2 : ℝ)) := by
        calc P ^ (-(1 / 4 : ℝ)) ≤ (T₁ ^ 2) ^ (-(1 / 4 : ℝ)) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hPγ (by norm_num)
          _ = T₁ ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hT₁.le]; norm_num
      have hYP : Y / P = Y * (P ^ (-(1 / 4 : ℝ)) * P ^ (-(3 / 4 : ℝ))) := by
        rw [← Real.rpow_add hP0, show -(1 / 4 : ℝ) + -(3 / 4) = -1 by norm_num,
          Real.rpow_neg_one, div_eq_mul_inv]
      calc x ^ (r.point.re - 1) * min 1 (Y / P) ≤ 1 * (Y / P) :=
            mul_le_mul hxβ (min_le_right _ _) hmin0 zero_le_one
        _ = Y * (P ^ (-(1 / 4 : ℝ)) * P ^ (-(3 / 4 : ℝ))) := by rw [one_mul, hYP]
        _ ≤ Y * (T₁ ^ (-(1 / 2 : ℝ)) * P ^ (-(3 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP14 hPpow) hY
        _ ≤ (x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))) *
              P ^ (-(3 / 4 : ℝ)) := by
            have : 0 ≤ x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) * P ^ (-(3 / 4 : ℝ)) := by positivity
            nlinarith

/-- The near zeros (`β > 3/4`, `|γ| ≤ T₁`) are finitely many. -/
theorem finite_nearZeros (hχ : χ ≠ 1) (T₁ : ℝ) :
    {r : LZero χ | 3 / 4 < r.point.re ∧ |r.point.im| ≤ T₁}.Finite := by
  refine (EntireZeroDivisor.locallyFinite_zeroCopyPoint (analyticOnNhd_shiftedL hχ)
    (|T₁| + 3)).subset fun (r : LZero χ) hr => ?_
  obtain ⟨hre, him⟩ := hr
  have hlt := point_re_lt_one hχ r
  simp only [Set.mem_setOf_eq]
  have hz : EntireZeroDivisor.zeroCopyPoint (shiftedL χ) r = r.point - 2 := by
    simp [LZero.point]
  rw [hz]
  calc ‖r.point - 2‖ ≤ |(r.point - 2).re| + |(r.point - 2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 + |T₁| := by
        simp only [sub_re, sub_im, Complex.re_ofNat, Complex.im_ofNat, sub_zero]
        have : |r.point.re - 2| ≤ 2 := by rw [abs_le]; constructor <;> linarith
        linarith [le_abs_self T₁]
    _ ≤ |T₁| + 3 := by linarith

/-- **The zero sum against the near zeros.** -/
theorem tsum_zeroShortWeight_le (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {x Y T₁ : ℝ} (hx : 1 ≤ x)
    (hY : 0 ≤ Y) (hT₁ : 0 < T₁) :
    ∑' r : LZero χ, RHTower.zeroShortWeight x Y r.point ≤
      (x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))) *
          ∑' r : LZero χ, (‖r.point‖ * ‖1 - r.point‖) ^ (-(3 / 4 : ℝ)) +
        ∑ r ∈ (finite_nearZeros hχ T₁).toFinset, x ^ (r.point.re - 1) := by
  classical
  set F := (finite_nearZeros hχ T₁).toFinset
  have hS := summable_rpow_three_quarters hχ
  have hind : Summable (fun r : LZero χ =>
      if 3 / 4 < r.point.re ∧ |r.point.im| ≤ T₁ then x ^ (r.point.re - 1) else 0) := by
    refine summable_of_ne_finset_zero (s := F) fun r hr => ?_
    rw [Set.Finite.mem_toFinset] at hr
    exact if_neg hr
  have htsum_ind : ∑' r : LZero χ,
      (if 3 / 4 < r.point.re ∧ |r.point.im| ≤ T₁ then x ^ (r.point.re - 1) else 0)
        = ∑ r ∈ F, x ^ (r.point.re - 1) := by
    rw [tsum_eq_sum (s := F) fun r hr => by
      rw [Set.Finite.mem_toFinset] at hr; exact if_neg hr]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Set.Finite.mem_toFinset] at hr
    exact if_pos hr
  rw [← htsum_ind, ← tsum_mul_left, ← (hS.mul_left _).tsum_add hind]
  exact (summable_zeroShortWeight hχ hprim hx hY).tsum_le_tsum
    (fun r => zeroShortWeight_le_split hχ hprim hx hY hT₁ r) ((hS.mul_left _).add hind)

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
