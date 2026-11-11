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

/-! ### The near zeros, slab by slab -/

/-- **The slab sum.**  If the zeros of a finite set have `3/4 < β ≤ 1 − w` and `|γ| ≤ x^{u₁}`, the
density estimate gives `Σ x^{β−1} ≤ (⌊log x/4⌋ + 1) e D (1 + log x^{u₁})^{11} x^{−(1 − 12u₁) w}`. -/
theorem sum_slab_le {D : ℝ} (hD : 0 ≤ D)
    (hdens : ∀ T σ : ℝ, 2050 * (q : ℝ) ^ 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
      {r : LZero χ | σ ≤ r.point.re ∧ |r.point.im| ≤ T}.Finite ∧
      ({r : LZero χ | σ ≤ r.point.re ∧ |r.point.im| ≤ T}.ncard : ℝ) ≤
        D * (1 + Real.log T) ^ 11 * T ^ (12 * (1 - σ)))
    {x u₁ w : ℝ} (hx : 1 < x) (hu₁ : 0 < u₁) (hu₁12 : 12 * u₁ ≤ 1)
    (hT : 2050 * (q : ℝ) ^ 2 ≤ x ^ u₁) (hw : 0 ≤ w) (Z : Finset (LZero χ))
    (hZ : ∀ r ∈ Z, 3 / 4 < r.point.re ∧ r.point.re ≤ 1 - w ∧ |r.point.im| ≤ x ^ u₁) :
    ∑ r ∈ Z, x ^ (r.point.re - 1) ≤
      (⌊Real.log x / 4⌋₊ + 1 : ℕ) *
        (Real.exp 1 * D * (1 + Real.log (x ^ u₁)) ^ 11 * x ^ (-((1 - 12 * u₁) * w))) := by
  classical
  set L := Real.log x with hL
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos hx
  set T₁ := x ^ u₁ with hT₁
  set B := Real.exp 1 * D * (1 + Real.log T₁) ^ 11 * x ^ (-((1 - 12 * u₁) * w)) with hB
  have hlogT₁ : 0 ≤ Real.log T₁ := by
    rw [hT₁, Real.log_rpow hx0]; positivity
  have hB0 : 0 ≤ B := by positivity
  set k : LZero χ → ℕ := fun r => ⌊(r.point.re - 3 / 4) * L⌋₊ with hk
  have hmaps : ∀ r ∈ Z, k r ∈ Finset.range (⌊L / 4⌋₊ + 1) := by
    intro r hr
    obtain ⟨h1, h2, _⟩ := hZ r hr
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.floor_le_floor ?_
    have h3 : r.point.re - 3 / 4 ≤ 1 / 4 := by linarith
    calc (r.point.re - 3 / 4) * L ≤ 1 / 4 * L := mul_le_mul_of_nonneg_right h3 hL0.le
      _ = L / 4 := by ring
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [show ((⌊L / 4⌋₊ + 1 : ℕ) : ℝ) * B = ∑ _j ∈ Finset.range (⌊L / 4⌋₊ + 1), B by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
  refine Finset.sum_le_sum fun j _ => ?_
  set σj : ℝ := 3 / 4 + j / L with hσj
  by_cases hne : (Z.filter (fun r => k r = j)).Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    rw [Finset.mem_filter] at hr₀
    -- the slab lies left of `1 − w`
    have hslab : ∀ r ∈ Z.filter (fun r => k r = j), σj ≤ r.point.re ∧
        r.point.re < σj + 1 / L := by
      intro r hr
      rw [Finset.mem_filter] at hr
      have h1 := (hZ r hr.1).1
      have hfl := Nat.floor_le (mul_nonneg (show 0 ≤ r.point.re - 3 / 4 by linarith) hL0.le)
      have hlt := Nat.lt_floor_add_one ((r.point.re - 3 / 4) * L)
      rw [show ⌊(r.point.re - 3 / 4) * L⌋₊ = j from hr.2] at hfl hlt
      constructor
      · rw [hσj]
        have : (j : ℝ) / L ≤ r.point.re - 3 / 4 := by rw [div_le_iff₀ hL0]; linarith
        linarith
      · rw [hσj]
        have : r.point.re - 3 / 4 < ((j : ℝ) + 1) / L := by rw [lt_div_iff₀ hL0]; linarith
        rw [add_div] at this
        linarith
    have hσj1 : σj ≤ 1 - w := ((hslab r₀ (Finset.mem_filter.mpr hr₀)).1).trans (hZ r₀ hr₀.1).2.1
    have hσj34 : 3 / 4 ≤ σj := by
      have : 0 ≤ (j : ℝ) / L := by positivity
      rw [hσj]; linarith
    -- the count of the slab
    obtain ⟨hfin, hcount⟩ := hdens T₁ σj hT (by linarith) (by linarith)
    have hcard : ((Z.filter (fun r => k r = j)).card : ℝ) ≤
        D * (1 + Real.log T₁) ^ 11 * T₁ ^ (12 * (1 - σj)) := by
      refine le_trans ?_ hcount
      have hsub : (((Z.filter (fun r => k r = j)) : Finset (LZero χ)) : Set (LZero χ)) ⊆
          {r : LZero χ | σj ≤ r.point.re ∧ |r.point.im| ≤ T₁} := by
        intro r hr
        have hr' := hr
        rw [Finset.mem_coe] at hr'
        exact ⟨(hslab r hr').1, (hZ r (Finset.mem_filter.mp hr').1).2.2⟩
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    -- the size of each term
    have hterm : ∀ r ∈ Z.filter (fun r => k r = j),
        x ^ (r.point.re - 1) ≤ Real.exp 1 * x ^ (σj - 1) := by
      intro r hr
      have h := (hslab r hr).2
      calc x ^ (r.point.re - 1) ≤ x ^ (σj - 1 + 1 / L) :=
            Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
        _ = x ^ (1 / L) * x ^ (σj - 1) := by rw [Real.rpow_add hx0]; ring
        _ = Real.exp 1 * x ^ (σj - 1) := by
            rw [Real.rpow_def_of_pos hx0, ← hL, mul_one_div_cancel hL0.ne']
    have hpow : T₁ ^ (12 * (1 - σj)) * x ^ (σj - 1) ≤ x ^ (-((1 - 12 * u₁) * w)) := by
      rw [hT₁, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      refine Real.rpow_le_rpow_of_exponent_le hx.le ?_
      have h1 : w ≤ 1 - σj := by linarith
      have h2 : 0 ≤ 1 - 12 * u₁ := by linarith
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      linarith
    calc ∑ r ∈ Z.filter (fun r => k r = j), x ^ (r.point.re - 1)
        ≤ ∑ _r ∈ Z.filter (fun r => k r = j), Real.exp 1 * x ^ (σj - 1) :=
          Finset.sum_le_sum hterm
      _ = ((Z.filter (fun r => k r = j)).card : ℝ) * (Real.exp 1 * x ^ (σj - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D * (1 + Real.log T₁) ^ 11 * T₁ ^ (12 * (1 - σj))) * (Real.exp 1 * x ^ (σj - 1)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = Real.exp 1 * D * (1 + Real.log T₁) ^ 11 * (T₁ ^ (12 * (1 - σj)) * x ^ (σj - 1)) := by
          ring
      _ ≤ B := by
          rw [hB]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact hB0

/-- `log log t / log t` is antitone for `log t ≥ e`. -/
theorem loglog_div_log_antitone {s t : ℝ} (hs0 : 0 < s) (hs : Real.exp 1 ≤ Real.log s)
    (hst : s ≤ t) :
    Real.log (Real.log t) / Real.log t ≤ Real.log (Real.log s) / Real.log s := by
  have hlog : Real.log s ≤ Real.log t := Real.log_le_log hs0 hst
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hlog)) hlog

/-! ### The limit -/

/-- The height exponent `u₁ = 1/(14·10⁷ + 12)` of the near zeros: `(1 − 12u₁)/(10⁷ u₁) = 14`. -/
def nearExponent : ℝ := 1 / (14 * 10 ^ 7 + 12)

theorem nearExponent_pos : 0 < nearExponent := by unfold nearExponent; positivity

theorem nearExponent_identity : (1 - 12 * nearExponent) / (10 ^ 7 * nearExponent) = 14 := by
  unfold nearExponent; field_simp; ring

/-- The slab bound in the variable `L = log x`. -/
theorem slab_bound_le {D L : ℝ} (hD : 0 ≤ D) (hL4 : 4 ≤ L) (hL1 : 1 ≤ nearExponent * L) :
    ((⌊L / 4⌋₊ + 1 : ℕ) : ℝ) * (Real.exp 1 * D * (1 + nearExponent * L) ^ 11 *
        (1 / (nearExponent * L) ^ 14))
      ≤ Real.exp 1 * D * 2 ^ 11 / nearExponent ^ 3 * (1 / L ^ 2) := by
  have hu := nearExponent_pos
  set u := nearExponent
  have hL0 : 0 < L := by linarith
  have hfl : ((⌊L / 4⌋₊ + 1 : ℕ) : ℝ) ≤ L := by
    push_cast
    have := Nat.floor_le (show 0 ≤ L / 4 by positivity)
    linarith
  have h1 : (1 + u * L) ^ 11 ≤ (2 * (u * L)) ^ 11 := pow_le_pow_left₀ (by positivity) (by linarith) 11
  have hE : 0 ≤ Real.exp 1 * D := by positivity
  calc ((⌊L / 4⌋₊ + 1 : ℕ) : ℝ) * (Real.exp 1 * D * (1 + u * L) ^ 11 * (1 / (u * L) ^ 14))
      ≤ L * (Real.exp 1 * D * (2 * (u * L)) ^ 11 * (1 / (u * L) ^ 14)) := by
        refine mul_le_mul hfl ?_ (by positivity) hL0.le
        gcongr
    _ = Real.exp 1 * D * 2 ^ 11 / u ^ 3 * (1 / L ^ 2) := by
        field_simp

/-- **The weighted zero sum vanishes.**  For a primitive nonprincipal `χ`, `0 < u < u₁/4` and
`c ≥ 0`, `Σ_ρ x^{β−1} min(1, c x^{2u}/(|ρ||1 − ρ|)) → 0`. -/
theorem tendsto_tsum_zeroShortWeight (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {u c : ℝ}
    (hu : 0 < u) (hu1 : u < nearExponent / 4) (hc : 0 ≤ c) :
    Tendsto (fun x : ℝ => ∑' r : LZero χ, RHTower.zeroShortWeight x (c * x ^ (2 * u)) r.point)
      atTop (𝓝 0) := by
  classical
  obtain ⟨D, hD, hdens⟩ := exists_zeroDensity_character hχ
  obtain ⟨TLW, hTLW, hreg⟩ := exists_littlewood_zero_free_region_character q
  set u₁ := nearExponent with hu₁def
  have hu₁ : 0 < u₁ := nearExponent_pos
  have hu₁small : u₁ < 1 / 24 := by rw [hu₁def, nearExponent]; norm_num
  set S := ∑' r : LZero χ, (‖r.point‖ * ‖1 - r.point‖) ^ (-(3 / 4 : ℝ)) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun r => Real.rpow_nonneg (by positivity) _
  set T₂ := max TLW (Real.exp (Real.exp 1)) with hT₂
  set Flow := (finite_nearZeros hχ T₂).toFinset with hFlow
  -- the upper bound
  set U : ℝ → ℝ := fun x =>
    (c ^ (3 / 4 : ℝ) * x ^ (3 / 2 * u - 1 / 4) + c * x ^ (2 * u - u₁ / 2)) * S +
      ∑ r ∈ Flow, x ^ (r.point.re - 1) +
      Real.exp 1 * D * 2 ^ 11 / u₁ ^ 3 * (1 / Real.log x ^ 2) with hU
  have hUlim : Tendsto U atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (3 / 2 * u - 1 / 4)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1 / 4 - 3 / 2 * u) (by linarith)
      simpa [neg_sub] using this
    have h2 : Tendsto (fun x : ℝ => x ^ (2 * u - u₁ / 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := u₁ / 2 - 2 * u) (by linarith)
      simpa [neg_sub] using this
    have h3 : Tendsto (fun x : ℝ => ∑ r ∈ Flow, x ^ (r.point.re - 1)) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ _r ∈ Flow, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ fun r _ => ?_
      have hβ := point_re_lt_one hχ r
      have := tendsto_rpow_neg_atTop (y := 1 - r.point.re) (by linarith)
      simpa [neg_sub] using this
    have h4 : Tendsto (fun x : ℝ => 1 / Real.log x ^ 2) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop (two_ne_zero)).comp Real.tendsto_log_atTop).inv_tendsto_atTop
      exact this.congr fun x => by simp [Function.comp, one_div]
    have := ((((h1.const_mul (c ^ (3 / 4 : ℝ))).add (h2.const_mul c)).mul_const S).add h3).add
      (h4.const_mul (Real.exp 1 * D * 2 ^ 11 / u₁ ^ 3))
    simpa [hU] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact tsum_nonneg fun r => RHTower.zeroShortWeight_nonneg (by linarith) (by positivity) _
  have hT₁big : ∀ᶠ x : ℝ in atTop, max T₂ (2050 * (q : ℝ) ^ 2) ≤ x ^ u₁ :=
    (tendsto_rpow_atTop hu₁).eventually_ge_atTop _
  have hlogbig : ∀ᶠ x : ℝ in atTop, max 4 (1 / u₁) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [hT₁big, hlogbig, eventually_ge_atTop 2] with x hT₁x hlogx hx2
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  set L := Real.log x with hL
  have hL4 : 4 ≤ L := le_trans (le_max_left _ _) hlogx
  have hL1 : 1 ≤ u₁ * L := by
    have h := le_trans (le_max_right _ _) hlogx
    rw [div_le_iff₀ hu₁] at h
    linarith
  set T₁ := x ^ u₁ with hT₁
  have hT₁T₂ : T₂ ≤ T₁ := le_trans (le_max_left _ _) hT₁x
  have hT₁q : 2050 * (q : ℝ) ^ 2 ≤ T₁ := le_trans (le_max_right _ _) hT₁x
  have hee : Real.exp 1 ≤ Real.log T₂ := by
    rw [Real.le_log_iff_exp_le (by positivity)]; exact le_max_right _ _
  have hT₂0 : 0 < T₂ := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  have hT₁0 : 0 < T₁ := by positivity
  have hlogT₁ : Real.log T₁ = u₁ * L := by rw [hT₁, Real.log_rpow hx0]
  set Y := c * x ^ (2 * u) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hmain := tsum_zeroShortWeight_le hχ hprim (x := x) (Y := Y) (T₁ := T₁) hx1.le hY0 hT₁0
  -- the first factor
  have hA : x ^ (-(1 / 4 : ℝ)) * Y ^ (3 / 4 : ℝ) + Y * T₁ ^ (-(1 / 2 : ℝ))
      = c ^ (3 / 4 : ℝ) * x ^ (3 / 2 * u - 1 / 4) + c * x ^ (2 * u - u₁ / 2) := by
    have e1 : (x ^ (2 * u)) ^ (3 / 4 : ℝ) = x ^ (3 / 2 * u) := by
      rw [← Real.rpow_mul hx0.le]; ring_nf
    have e2 : T₁ ^ (-(1 / 2 : ℝ)) = x ^ (-(u₁ / 2)) := by
      rw [hT₁, ← Real.rpow_mul hx0.le]; ring_nf
    have e3 : x ^ (-(1 / 4 : ℝ)) * x ^ (3 / 2 * u) = x ^ (3 / 2 * u - 1 / 4) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have e4 : x ^ (2 * u) * x ^ (-(u₁ / 2)) = x ^ (2 * u - u₁ / 2) := by
      rw [← Real.rpow_add hx0]; ring_nf
    rw [hY, Real.mul_rpow hc (by positivity), e1, e2, ← e3, ← e4]
    ring
  -- the near zeros
  set Near := (finite_nearZeros hχ T₁).toFinset with hNear
  have hf0 : ∀ r : LZero χ, 0 ≤ x ^ (r.point.re - 1) := fun r => Real.rpow_nonneg hx0.le _
  have hlow : ∑ r ∈ Near.filter (fun r => |r.point.im| ≤ T₂), x ^ (r.point.re - 1)
      ≤ ∑ r ∈ Flow, x ^ (r.point.re - 1) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) fun r _ _ => hf0 r
    rw [Finset.mem_filter, hNear, Set.Finite.mem_toFinset] at hr
    rw [hFlow, Set.Finite.mem_toFinset]
    exact ⟨hr.1.1, hr.2⟩
  set w₁ := Real.log (Real.log T₁) / (10 ^ 7 * Real.log T₁) with hw₁
  have hlogT₁e : Real.exp 1 ≤ Real.log T₁ :=
    hee.trans (Real.log_le_log hT₂0 hT₁T₂)
  have hw₁0 : 0 ≤ w₁ := by
    have h1 : 0 < Real.log T₁ := lt_of_lt_of_le (Real.exp_pos 1) hlogT₁e
    have h2 : 0 ≤ Real.log (Real.log T₁) := Real.log_nonneg (by
      linarith [Real.add_one_le_exp (1 : ℝ)])
    positivity
  have hhigh : ∀ r ∈ Near.filter (fun r => ¬ |r.point.im| ≤ T₂),
      3 / 4 < r.point.re ∧ r.point.re ≤ 1 - w₁ ∧ |r.point.im| ≤ T₁ := by
    intro r hr
    rw [Finset.mem_filter, hNear, Set.Finite.mem_toFinset] at hr
    obtain ⟨⟨h34, hT⟩, hfar⟩ := hr
    have hfar' : T₂ < |r.point.im| := not_le.mp hfar
    refine ⟨h34, ?_, hT⟩
    have hz : DirichletCharacter.LFunction χ ((r.point.re : ℂ) + (r.point.im : ℂ) * I) = 0 := by
      rw [Complex.re_add_im]; exact LFunction_point_eq_zero hχ r (by linarith)
    have hreg' := hreg χ hχ r.point.re r.point.im
      (le_trans (le_max_left _ _) hfar'.le) hz
    have hanti := loglog_div_log_antitone (lt_trans hT₂0 hfar')
      (hee.trans (Real.log_le_log hT₂0 hfar'.le)) hT
    have hw : w₁ ≤ Real.log (Real.log |r.point.im|) / (10 ^ 7 * Real.log |r.point.im|) := by
      have e1 : w₁ = Real.log (Real.log T₁) / Real.log T₁ / 10 ^ 7 := by
        rw [hw₁, div_div, mul_comm]
      have e2 : Real.log (Real.log |r.point.im|) / (10 ^ 7 * Real.log |r.point.im|)
          = Real.log (Real.log |r.point.im|) / Real.log |r.point.im| / 10 ^ 7 := by
        rw [div_div, mul_comm]
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hanti (by norm_num)
    linarith
  have hslab := sum_slab_le hD hdens hx1 hu₁ (by linarith) hT₁q hw₁0 _ hhigh
  have hpow : x ^ (-((1 - 12 * u₁) * w₁)) = 1 / (u₁ * L) ^ 14 := by
    have hul : 0 < u₁ * L := by linarith
    have hid : (1 - 12 * u₁) / (10 ^ 7 * u₁) = 14 := nearExponent_identity
    have hexp : Real.log x * -((1 - 12 * u₁) * w₁) = -Real.log ((u₁ * L) ^ 14) := by
      rw [Real.log_pow, hw₁, hlogT₁, ← hL]
      push_cast
      rw [← hid]
      field_simp
    rw [Real.rpow_def_of_pos hx0, hexp, Real.exp_neg, Real.exp_log (by positivity), one_div]
  rw [hlogT₁, hpow] at hslab
  have hslab2 := slab_bound_le hD hL4 hL1
  have hsplit := Finset.sum_filter_add_sum_filter_not Near (fun r => |r.point.im| ≤ T₂)
    (fun r => x ^ (r.point.re - 1))
  rw [hA] at hmain
  simp only [hU]
  linarith

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
