import GaloisForLFunctions.RHTower.PositiveOperatorDiagonalResidue
import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds
import GaloisForLFunctions.HTGeometry.ShiftSpectrumSpacing

/-!
# The singular-value logarithmic mean from a diagonal logarithmic mean

For a positive compact operator with a Hilbert basis indexed by `ℤ`, the logarithmic mean of the
diagonal over the symmetric bands determines the logarithmic mean of the singular values, provided
the columns decay faster than any power `|n|^(-1+δ)`.

The lower half is Ky Fan majorization.  The upper half is the finite compression comparison
`sum_singVal_le_diagonal_add_tail` at the shifted scale `M = ceil (N^(1+u))`, whose Hilbert-Schmidt
remainder is `O(N^(-u/4))` and whose diagonal contributes `(1+u)` times the diagonal mean.  Letting
`u` tend to zero gives the exact value.
-/

namespace ContinuousLinearMap

open Filter Topology Finset GaloisForLFunctions
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Hilbert–Schmidt tail of a power-decaying column family -/

/-- A column family decaying like `|n|^(-1+δ)` has band tails of size `M^(-1+4δ)`. -/
theorem tsum_tail_le_of_norm_apply_le (b : HilbertBasis ℤ ℂ H) {T : H →L[ℂ] H} {C δ : ℝ}
    (hC : 0 ≤ C) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    (hb : ∀ n : ℤ, n ≠ 0 → ‖T (b n)‖ ≤ C * ((n.natAbs : ℝ)) ^ (-1 + δ))
    (M : ℕ) (hM : 1 ≤ M) :
    ∑' j : ℤ, (if j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) then 0
        else ENNReal.ofReal (‖T (b j)‖ ^ 2))
      ≤ ENNReal.ofReal (4 * C ^ 2 * (∑' j : ℤ, intPowWeight (1 + 2 * δ) j).toReal
          * (M : ℝ) ^ (-1 + 4 * δ)) := by
  classical
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hs : (1 : ℝ) < 1 + 2 * δ := by linarith
  set W : ℝ≥0∞ := ∑' j : ℤ, intPowWeight (1 + 2 * δ) j with hW
  have hWne : W ≠ ⊤ := tsum_intPowWeight_ne_top hs
  -- pointwise bound
  have hpt : ∀ j : ℤ, (if j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) then 0
      else ENNReal.ofReal (‖T (b j)‖ ^ 2))
      ≤ ENNReal.ofReal (4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ)) * intPowWeight (1 + 2 * δ) j := by
    intro j
    by_cases hj : j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)
    · rw [if_pos hj]
      exact _root_.zero_le
    rw [if_neg hj]
    -- `|j| > M`
    have hjabs : (M : ℝ) < (j.natAbs : ℝ) := by
      rcases lt_or_ge j 0 with h | h
      · have : j < -(M : ℤ) := by
          by_contra hcon
          exact hj (Finset.mem_Icc.mpr ⟨not_lt.mp hcon, by omega⟩)
        have : (M : ℤ) < j.natAbs := by omega
        exact_mod_cast this
      · have : (M : ℤ) < j := by
          by_contra hcon
          exact hj (Finset.mem_Icc.mpr ⟨by omega, not_lt.mp hcon⟩)
        have : (M : ℤ) < j.natAbs := by omega
        exact_mod_cast this
    have hj0 : j ≠ 0 := by
      intro h
      rw [h] at hjabs
      simp at hjabs
      linarith
    have hjge : (1 : ℝ) ≤ (j.natAbs : ℝ) := le_trans hMR hjabs.le
    have hjpos : (0 : ℝ) < (j.natAbs : ℝ) := by linarith
    have hnb := hb j hj0
    have hsq : ‖T (b j)‖ ^ 2 ≤ C ^ 2 * ((j.natAbs : ℝ)) ^ (-2 + 2 * δ) := by
      have hx : ((j.natAbs : ℝ)) ^ (-2 + 2 * δ) = (((j.natAbs : ℝ)) ^ (-1 + δ)) ^ 2 := by
        rw [← Real.rpow_natCast (((j.natAbs : ℝ)) ^ (-1 + δ)) 2, ← Real.rpow_mul hjpos.le]
        congr 1
        push_cast
        ring
      rw [hx, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hnb 2
    -- split the power
    have hsplit : ((j.natAbs : ℝ)) ^ (-2 + 2 * δ)
        ≤ 4 * (M : ℝ) ^ (-1 + 4 * δ) * (1 / (1 + |(j : ℝ)|) ^ (1 + 2 * δ)) := by
      have habs : |(j : ℝ)| = (j.natAbs : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      rw [habs]
      have hfac : ((j.natAbs : ℝ)) ^ (-2 + 2 * δ)
          = ((j.natAbs : ℝ)) ^ (-1 - 2 * δ) * ((j.natAbs : ℝ)) ^ (-1 + 4 * δ) := by
        rw [← Real.rpow_add hjpos]
        ring_nf
      rw [hfac]
      have hA : ((j.natAbs : ℝ)) ^ (-1 + 4 * δ) ≤ (M : ℝ) ^ (-1 + 4 * δ) := by
        have h1 : (M : ℝ) ^ (1 - 4 * δ) ≤ ((j.natAbs : ℝ)) ^ (1 - 4 * δ) :=
          Real.rpow_le_rpow hMpos.le hjabs.le (by linarith)
        rw [show (-1 + 4 * δ) = -(1 - 4 * δ) by ring, Real.rpow_neg hjpos.le,
          Real.rpow_neg hMpos.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hMpos _) h1
      have hB : ((j.natAbs : ℝ)) ^ (-1 - 2 * δ)
          ≤ 4 * (1 / (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ)) := by
        have h2j : (1 : ℝ) + (j.natAbs : ℝ) ≤ 2 * (j.natAbs : ℝ) := by linarith
        have hp : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by linarith
        have hmono : (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ)
            ≤ (2 * (j.natAbs : ℝ)) ^ (1 + 2 * δ) :=
          Real.rpow_le_rpow hp.le h2j (by linarith)
        have hexp : (2 * (j.natAbs : ℝ)) ^ (1 + 2 * δ)
            = 2 ^ (1 + 2 * δ) * ((j.natAbs : ℝ)) ^ (1 + 2 * δ) :=
          Real.mul_rpow (by norm_num) hjpos.le
        have h2b : (2 : ℝ) ^ (1 + 2 * δ) ≤ 4 := by
          have hle := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
            (by linarith : 1 + 2 * δ ≤ 2)
          calc (2 : ℝ) ^ (1 + 2 * δ) ≤ (2 : ℝ) ^ (2 : ℝ) := hle
            _ = 4 := by norm_num
        have hinv : ((j.natAbs : ℝ)) ^ (-1 - 2 * δ)
            = 1 / ((j.natAbs : ℝ)) ^ (1 + 2 * δ) := by
          rw [show (-1 - 2 * δ) = -(1 + 2 * δ) by ring, Real.rpow_neg hjpos.le]
          rw [one_div]
        rw [hinv]
        have hjp : (0 : ℝ) < ((j.natAbs : ℝ)) ^ (1 + 2 * δ) := Real.rpow_pos_of_pos hjpos _
        have hpp : (0 : ℝ) < (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ) := Real.rpow_pos_of_pos hp _
        have key : (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ)
            ≤ 4 * ((j.natAbs : ℝ)) ^ (1 + 2 * δ) := by
          calc (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ)
              ≤ (2 * (j.natAbs : ℝ)) ^ (1 + 2 * δ) := hmono
            _ = 2 ^ (1 + 2 * δ) * ((j.natAbs : ℝ)) ^ (1 + 2 * δ) := hexp
            _ ≤ 4 * ((j.natAbs : ℝ)) ^ (1 + 2 * δ) :=
                mul_le_mul_of_nonneg_right h2b hjp.le
        rw [mul_one_div, div_le_div_iff₀ hjp hpp]
        linarith [key]
      have hApos : (0 : ℝ) < ((j.natAbs : ℝ)) ^ (-1 + 4 * δ) := Real.rpow_pos_of_pos hjpos _
      have hBpos : (0 : ℝ) ≤ ((j.natAbs : ℝ)) ^ (-1 - 2 * δ) := (Real.rpow_pos_of_pos hjpos _).le
      have hMp : (0 : ℝ) < (M : ℝ) ^ (-1 + 4 * δ) := Real.rpow_pos_of_pos hMpos _
      calc ((j.natAbs : ℝ)) ^ (-1 - 2 * δ) * ((j.natAbs : ℝ)) ^ (-1 + 4 * δ)
          ≤ (4 * (1 / (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ))) * ((j.natAbs : ℝ)) ^ (-1 + 4 * δ) :=
            mul_le_mul_of_nonneg_right hB hApos.le
        _ ≤ (4 * (1 / (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ))) * (M : ℝ) ^ (-1 + 4 * δ) := by
            refine mul_le_mul_of_nonneg_left hA ?_
            positivity
        _ = 4 * (M : ℝ) ^ (-1 + 4 * δ) * (1 / (1 + (j.natAbs : ℝ)) ^ (1 + 2 * δ)) := by ring
    have hfinal : ‖T (b j)‖ ^ 2
        ≤ 4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ) * (1 / (1 + |(j : ℝ)|) ^ (1 + 2 * δ)) := by
      have hC2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
      calc ‖T (b j)‖ ^ 2 ≤ C ^ 2 * ((j.natAbs : ℝ)) ^ (-2 + 2 * δ) := hsq
        _ ≤ C ^ 2 * (4 * (M : ℝ) ^ (-1 + 4 * δ) * (1 / (1 + |(j : ℝ)|) ^ (1 + 2 * δ))) :=
            mul_le_mul_of_nonneg_left hsplit hC2
        _ = 4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ) * (1 / (1 + |(j : ℝ)|) ^ (1 + 2 * δ)) := by ring
    rw [intPowWeight, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hfinal
  calc ∑' j : ℤ, (if j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) then 0
        else ENNReal.ofReal (‖T (b j)‖ ^ 2))
      ≤ ∑' j : ℤ, ENNReal.ofReal (4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ))
          * intPowWeight (1 + 2 * δ) j := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ)) * W := by
        rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (4 * C ^ 2 * (M : ℝ) ^ (-1 + 4 * δ)) * ENNReal.ofReal W.toReal := by
        rw [ENNReal.ofReal_toReal hWne]
    _ = ENNReal.ofReal (4 * C ^ 2 * (∑' j : ℤ, intPowWeight (1 + 2 * δ) j).toReal
          * (M : ℝ) ^ (-1 + 4 * δ)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hW]
        ring

/-! ## Elementary logarithmic ratios -/

theorem tendsto_log_natCast_atTop' :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_const_div_log_natCast (β : ℝ) :
    Tendsto (fun N : ℕ => β / Real.log (N : ℝ)) atTop (nhds 0) :=
  tendsto_log_natCast_atTop'.const_div_atTop β

/-- A scale comparison in the logarithm passes to the ratio of logarithms. -/
theorem tendsto_log_div_log_of_bounds {f : ℕ → ℕ} {α β : ℝ}
    (hlow : ∀ᶠ N : ℕ in atTop, α * Real.log (N : ℝ) - β ≤ Real.log ((f N : ℕ) : ℝ))
    (hhigh : ∀ᶠ N : ℕ in atTop, Real.log ((f N : ℕ) : ℝ) ≤ α * Real.log (N : ℝ) + β) :
    Tendsto (fun N : ℕ => Real.log ((f N : ℕ) : ℝ) / Real.log (N : ℝ)) atTop (nhds α) := by
  have hlim1 : Tendsto (fun N : ℕ => α - β / Real.log (N : ℝ)) atTop (nhds α) := by
    have := (tendsto_const_div_log_natCast β).const_sub α
    simpa using this
  have hlim2 : Tendsto (fun N : ℕ => α + β / Real.log (N : ℝ)) atTop (nhds α) := by
    have := (tendsto_const_div_log_natCast β).const_add α
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim1 hlim2 ?_ ?_
  · filter_upwards [hlow, eventually_gt_atTop 1] with N hN hN1
    have hlog : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      exact_mod_cast hN1
    rw [le_div_iff₀ hlog, sub_mul, div_mul_cancel₀ _ hlog.ne']
    linarith
  · filter_upwards [hhigh, eventually_gt_atTop 1] with N hN hN1
    have hlog : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      exact_mod_cast hN1
    rw [div_le_iff₀ hlog, add_mul, div_mul_cancel₀ _ hlog.ne']
    linarith

/-! ## The band majorization -/

theorem card_Icc_neg_symm (M : ℕ) : (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
  rw [Int.card_Icc]
  omega

theorem sum_band_re_inner_le_sum_singVal (b : HilbertBasis ℤ ℂ H) {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (hT : 0 ≤ T) (M N : ℕ) (hMN : 2 * M + 1 ≤ N) :
    ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), RCLike.re (inner ℂ (b j) (T (b j)) : ℂ)
      ≤ ∑ n ∈ Finset.range N, singVal T n := by
  refine sum_re_inner_le_sum_singVal hcpt hT (fun j : ℤ => b j)
    (fun i => Or.inr (b.orthonormal.1 i)) (fun i j hij => b.orthonormal.2 hij)
    (Finset.Icc (-(M : ℤ)) (M : ℤ)) ?_
  rw [card_Icc_neg_symm]
  exact hMN

/-! ## The two-sided logarithmic comparison -/

set_option maxHeartbeats 2000000 in
/-- **From the diagonal logarithmic mean to the singular-value logarithmic mean.**  A positive
compact operator whose columns in a `ℤ`-indexed Hilbert basis decay faster than `|n|^(-1+δ)` for
every `δ > 0` has singular-value logarithmic mean equal to the logarithmic mean of its symmetric
band diagonals. -/
theorem tendsto_sum_singVal_div_log_of_diagonal (b : HilbertBasis ℤ ℂ H) {T : H →L[ℂ] H}
    (hcpt : IsCompactOperator T) (hT : 0 ≤ T) {L : ℝ}
    (hdiag : Tendsto (fun M : ℕ =>
        (∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), RCLike.re (inner ℂ (b j) (T (b j)) : ℂ))
          / Real.log (M : ℝ)) atTop (nhds L))
    (htail : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, n ≠ 0 →
        ‖T (b n)‖ ≤ C * ((n.natAbs : ℝ)) ^ (-1 + δ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, singVal T n) / Real.log (N : ℝ))
      atTop (nhds L) := by
  classical
  set D : ℕ → ℝ := fun M =>
    ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), RCLike.re (inner ℂ (b j) (T (b j)) : ℂ) with hD
  have hTpos : T.IsPositive := by
    rw [ContinuousLinearMap.le_def, sub_zero] at hT
    exact hT
  have hDnn : ∀ M : ℕ, 0 ≤ D M := fun M =>
    Finset.sum_nonneg fun j _ => hTpos.re_inner_nonneg_right (b j)
  have hL0 : 0 ≤ L := by
    refine ge_of_tendsto hdiag ?_
    filter_upwards [eventually_gt_atTop 1] with M hM
    have hlog : (0 : ℝ) < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
    exact div_nonneg (hDnn M) hlog.le
  refine tendsto_order.2 ⟨?_, ?_⟩
  · -- lower half: Ky Fan majorization on the band of cardinality `2M+1`
    intro a ha
    set MM : ℕ → ℕ := fun N => (N - 1) / 2 with hMM
    have hMMtop : Tendsto MM atTop atTop := by
      refine tendsto_atTop_atTop.2 fun d => ⟨2 * d + 1, fun N hN => ?_⟩
      simp only [hMM]
      omega
    have h1 : Tendsto (fun N : ℕ => D (MM N) / Real.log ((MM N : ℕ) : ℝ)) atTop (nhds L) :=
      hdiag.comp hMMtop
    have h2 : Tendsto (fun N : ℕ => Real.log ((MM N : ℕ) : ℝ) / Real.log (N : ℝ))
        atTop (nhds 1) := by
      refine tendsto_log_div_log_of_bounds (α := 1) (β := Real.log 3) ?_ ?_
      · filter_upwards [eventually_ge_atTop 5] with N hN
        have hMMpos : 0 < MM N := by simp only [hMM]; omega
        have hNle : (N : ℝ) ≤ 3 * ((MM N : ℕ) : ℝ) := by
          have h : N ≤ 3 * MM N := by simp only [hMM]; omega
          exact_mod_cast h
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hMR : ((MM N : ℕ) : ℝ) ≠ 0 := by
          have : (0 : ℝ) < ((MM N : ℕ) : ℝ) := by exact_mod_cast hMMpos
          exact this.ne'
        have h := Real.log_le_log hNpos hNle
        rw [Real.log_mul (by norm_num) hMR] at h
        linarith
      · filter_upwards [eventually_ge_atTop 5] with N hN
        have hMMpos : 0 < MM N := by simp only [hMM]; omega
        have hle : ((MM N : ℕ) : ℝ) ≤ (N : ℝ) := by
          have h : MM N ≤ N := by simp only [hMM]; omega
          exact_mod_cast h
        have hMpos : (0 : ℝ) < ((MM N : ℕ) : ℝ) := by exact_mod_cast hMMpos
        have h := Real.log_le_log hMpos hle
        have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        linarith
    have hprod := h1.mul h2
    rw [mul_one] at hprod
    filter_upwards [(tendsto_order.1 hprod).1 a ha, eventually_ge_atTop 5] with N hNa hN5
    have hMM2 : 2 ≤ MM N := by simp only [hMM]; omega
    have hlogM : (0 : ℝ) < Real.log ((MM N : ℕ) : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ ((MM N : ℕ) : ℝ) := by exact_mod_cast hMM2
      linarith
    have hlogN : (0 : ℝ) < Real.log (N : ℝ) := by
      refine Real.log_pos ?_
      have : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN5
      linarith
    have hid : D (MM N) / Real.log ((MM N : ℕ) : ℝ)
        * (Real.log ((MM N : ℕ) : ℝ) / Real.log (N : ℝ))
        = D (MM N) / Real.log (N : ℝ) := by
      field_simp
    rw [hid] at hNa
    have hband : D (MM N) ≤ ∑ n ∈ Finset.range N, singVal T n :=
      sum_band_re_inner_le_sum_singVal b hcpt hT (MM N) N (by simp only [hMM]; omega)
    calc a < D (MM N) / Real.log (N : ℝ) := hNa
      _ ≤ (∑ n ∈ Finset.range N, singVal T n) / Real.log (N : ℝ) := by gcongr
  · -- upper half: the finite compression at the shifted scale
    intro c hc
    obtain ⟨u, hu0, hu2, hLu⟩ : ∃ u : ℝ, 0 < u ∧ u ≤ 1 / 2 ∧ L * (1 + u) < c := by
      refine ⟨min (1 / 2) ((c - L) / (2 * (L + 1))), ?_, min_le_left _ _, ?_⟩
      · refine lt_min (by norm_num) ?_
        have : (0 : ℝ) < c - L := by linarith
        positivity
      · have hmin : min (1 / 2) ((c - L) / (2 * (L + 1))) ≤ (c - L) / (2 * (L + 1)) :=
          min_le_right _ _
        have hLL : L / (L + 1) ≤ 1 := by
          rw [div_le_one (by linarith)]
          linarith
        have h1 : L * min (1 / 2) ((c - L) / (2 * (L + 1)))
            ≤ L * ((c - L) / (2 * (L + 1))) := mul_le_mul_of_nonneg_left hmin hL0
        have hrw : L * ((c - L) / (2 * (L + 1))) = (L / (L + 1)) * ((c - L) / 2) := by
          field_simp
        have h2 : (L / (L + 1)) * ((c - L) / 2) ≤ 1 * ((c - L) / 2) := by
          refine mul_le_mul_of_nonneg_right hLL ?_
          linarith
        rw [hrw] at h1
        nlinarith [h1, h2]
    set δ : ℝ := u / 16 with hδdef
    have hδ0 : 0 < δ := by simp only [hδdef]; linarith
    have hδ1 : δ < 1 / 4 := by simp only [hδdef]; linarith
    obtain ⟨C, hC0, hCb⟩ := htail δ hδ0
    set K : ℝ := 4 * C ^ 2 * (∑' j : ℤ, intPowWeight (1 + 2 * δ) j).toReal with hKdef
    have hK0 : 0 ≤ K := by
      refine mul_nonneg (by positivity) ENNReal.toReal_nonneg
    set MM : ℕ → ℕ := fun N => ⌈(N : ℝ) ^ (1 + u)⌉₊ with hMM
    have hMMge : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ ((MM N : ℕ) : ℝ) := by
      intro N hN
      have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hstep : (N : ℝ) ≤ (N : ℝ) ^ (1 + u) := by
        calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (N : ℝ) ^ (1 + u) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      exact le_trans hstep (Nat.le_ceil _)
    have hMMtop : Tendsto MM atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ (tendsto_id (α := ℕ))
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact_mod_cast hMMge N hN
    have h1 : Tendsto (fun N : ℕ => D (MM N) / Real.log ((MM N : ℕ) : ℝ)) atTop (nhds L) :=
      hdiag.comp hMMtop
    have h2 : Tendsto (fun N : ℕ => Real.log ((MM N : ℕ) : ℝ) / Real.log (N : ℝ))
        atTop (nhds (1 + u)) := by
      refine tendsto_log_div_log_of_bounds (α := 1 + u) (β := Real.log 2) ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hlow : (N : ℝ) ^ (1 + u) ≤ ((MM N : ℕ) : ℝ) := Nat.le_ceil _
        have h := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hlow
        rw [Real.log_rpow (by linarith)] at h
        have h2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hpos : (0 : ℝ) < (N : ℝ) ^ (1 + u) := Real.rpow_pos_of_pos (by linarith) _
        have hge1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 + u) := by
          have h := Real.rpow_le_rpow_of_exponent_le hNR.le (by linarith : (0 : ℝ) ≤ 1 + u)
          rwa [Real.rpow_zero] at h
        have hup : ((MM N : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 + u) := by
          have hc1 : ((MM N : ℕ) : ℝ) < (N : ℝ) ^ (1 + u) + 1 := Nat.ceil_lt_add_one hpos.le
          linarith
        have h := Real.log_le_log (by positivity) hup
        rw [Real.log_mul (by norm_num) (ne_of_gt hpos), Real.log_rpow (by linarith)] at h
        linarith
    have h3 : Tendsto (fun N : ℕ => Real.sqrt (2 * (N : ℝ))
        * Real.sqrt (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ)) / Real.log (N : ℝ))
        atTop (nhds 0) := by
      have hpow : Tendsto (fun N : ℕ => (2 * K) * ((N : ℝ) ^ (-(5 * u / 8)))) atTop (nhds 0) := by
        have hbase := (GaloisForLFunctions.HTGeometry.tendsto_rpow_neg_nhds_zero (by linarith : -(5 * u / 8) < 0)).comp
          tendsto_natCast_atTop_atTop
        have := hbase.const_mul (2 * K)
        simpa using this
      have hsq : Tendsto (fun N : ℕ => Real.sqrt ((2 * K) * ((N : ℝ) ^ (-(5 * u / 8)))))
          atTop (nhds 0) := by
        have := hpow.sqrt
        simpa using this
      have hzero : Tendsto (fun N : ℕ =>
          Real.sqrt ((2 * K) * ((N : ℝ) ^ (-(5 * u / 8)))) / Real.log 2) atTop (nhds 0) := by
        have := hsq.div_const (Real.log 2)
        simpa using this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hlogN : (0 : ℝ) < Real.log (N : ℝ) := by
          refine Real.log_pos ?_
          have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          linarith
        positivity
      · filter_upwards [eventually_ge_atTop 2] with N hN
        have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
        have hMpos : (0 : ℝ) < ((MM N : ℕ) : ℝ) := by
          have := hMMge N (by omega)
          linarith
        have hlogle : Real.log 2 ≤ Real.log (N : ℝ) := by
          refine Real.log_le_log (by norm_num) ?_
          exact_mod_cast hN
        have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hlogNpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
        -- the product of square roots is the square root of the product
        have hprodsq : Real.sqrt (2 * (N : ℝ))
            * Real.sqrt (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ))
            = Real.sqrt ((2 * (N : ℝ)) * (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ))) :=
          (Real.sqrt_mul (by positivity) _).symm
        -- the argument is dominated
        have hMle : ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ) ≤ ((N : ℝ) ^ (1 + u)) ^ (-1 + 4 * δ) := by
          have hbase : (N : ℝ) ^ (1 + u) ≤ ((MM N : ℕ) : ℝ) := Nat.le_ceil _
          have hposb : (0 : ℝ) < (N : ℝ) ^ (1 + u) := Real.rpow_pos_of_pos hNpos _
          have h1' : ((N : ℝ) ^ (1 + u)) ^ (1 - 4 * δ) ≤ ((MM N : ℕ) : ℝ) ^ (1 - 4 * δ) :=
            Real.rpow_le_rpow hposb.le hbase (by linarith)
          rw [show (-1 + 4 * δ) = -(1 - 4 * δ) by ring, Real.rpow_neg hMpos.le,
            Real.rpow_neg hposb.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hposb _) h1'
        have hcollapse : ((N : ℝ) ^ (1 + u)) ^ (-1 + 4 * δ)
            = (N : ℝ) ^ ((1 + u) * (-1 + 4 * δ)) := (Real.rpow_mul hNpos.le _ _).symm
        have hexp : (1 : ℝ) + (1 + u) * (-1 + 4 * δ) ≤ -(5 * u / 8) := by
          simp only [hδdef]
          nlinarith [hu0, hu2]
        have harg : (2 * (N : ℝ)) * (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ))
            ≤ (2 * K) * ((N : ℝ) ^ (-(5 * u / 8))) := by
          have hstep1 : (2 * (N : ℝ)) * (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ))
              ≤ (2 * (N : ℝ)) * (K * (N : ℝ) ^ ((1 + u) * (-1 + 4 * δ))) := by
            rw [← hcollapse]
            have : K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ)
                ≤ K * ((N : ℝ) ^ (1 + u)) ^ (-1 + 4 * δ) :=
              mul_le_mul_of_nonneg_left hMle hK0
            nlinarith [this, hNpos]
          have hstep2 : (2 * (N : ℝ)) * (K * (N : ℝ) ^ ((1 + u) * (-1 + 4 * δ)))
              = (2 * K) * (N : ℝ) ^ (1 + (1 + u) * (-1 + 4 * δ)) := by
            rw [Real.rpow_add hNpos, Real.rpow_one]
            ring
          have hstep3 : (N : ℝ) ^ (1 + (1 + u) * (-1 + 4 * δ))
              ≤ (N : ℝ) ^ (-(5 * u / 8)) :=
            Real.rpow_le_rpow_of_exponent_le hNR.le hexp
          have hstep4 : (2 * K) * (N : ℝ) ^ (1 + (1 + u) * (-1 + 4 * δ))
              ≤ (2 * K) * (N : ℝ) ^ (-(5 * u / 8)) :=
            mul_le_mul_of_nonneg_left hstep3 (by linarith)
          linarith [hstep1, hstep2.le, hstep2.ge, hstep4]
        rw [hprodsq]
        have hsqle : Real.sqrt ((2 * (N : ℝ)) * (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ)))
            ≤ Real.sqrt ((2 * K) * ((N : ℝ) ^ (-(5 * u / 8)))) := Real.sqrt_le_sqrt harg
        have hnn : (0 : ℝ) ≤ Real.sqrt ((2 * (N : ℝ)) * (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ))) :=
          Real.sqrt_nonneg _
        rw [div_le_div_iff₀ hlogNpos hlog2]
        nlinarith [hsqle, hnn, hlogle, hlog2,
          Real.sqrt_nonneg ((2 * K) * ((N : ℝ) ^ (-(5 * u / 8))))]
    have hmain := (h1.mul h2).add h3
    rw [add_zero] at hmain
    filter_upwards [(tendsto_order.1 hmain).2 c hLu, eventually_ge_atTop 2] with N hNc hN2
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
    have hlogN : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNR
    have hMM1 : 1 ≤ MM N := by
      have := hMMge N (by omega)
      have h2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      have : (1 : ℝ) ≤ ((MM N : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hMpos : (0 : ℝ) < ((MM N : ℕ) : ℝ) := by exact_mod_cast hMM1
    have hlogM : (0 : ℝ) < Real.log ((MM N : ℕ) : ℝ) := by
      refine Real.log_pos ?_
      have h2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      have := hMMge N (by omega)
      -- `MM N ≥ N ≥ 2 > 1`
      linarith
    set E : ℝ := Real.sqrt (K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ)) with hEdef
    have hE0 : 0 ≤ E := Real.sqrt_nonneg _
    have hEsq : E ^ 2 = K * ((MM N : ℕ) : ℝ) ^ (-1 + 4 * δ) := by
      rw [hEdef, Real.sq_sqrt (by positivity)]
    have hEtail : ∑' j : ℤ, (if j ∈ Finset.Icc (-((MM N : ℕ) : ℤ)) ((MM N : ℕ) : ℤ) then 0
        else ENNReal.ofReal (‖T (b j)‖ ^ 2)) ≤ ENNReal.ofReal (E ^ 2) := by
      rw [hEsq, hKdef]
      exact tsum_tail_le_of_norm_apply_le b hC0 hδ0 hδ1 hCb (MM N) hMM1
    have hcomp := sum_singVal_le_diagonal_add_tail b
      (Finset.Icc (-((MM N : ℕ) : ℤ)) ((MM N : ℕ) : ℤ)) hcpt hT N E hE0 hEtail
    have hid : D (MM N) / Real.log ((MM N : ℕ) : ℝ)
        * (Real.log ((MM N : ℕ) : ℝ) / Real.log (N : ℝ))
        + Real.sqrt (2 * (N : ℝ)) * E / Real.log (N : ℝ)
        = (D (MM N) + Real.sqrt (2 * (N : ℝ)) * E) / Real.log (N : ℝ) := by
      field_simp
    rw [hid] at hNc
    calc (∑ n ∈ Finset.range N, singVal T n) / Real.log (N : ℝ)
        ≤ (D (MM N) + Real.sqrt (2 * (N : ℝ)) * E) / Real.log (N : ℝ) := by gcongr
      _ < c := hNc

end ContinuousLinearMap
