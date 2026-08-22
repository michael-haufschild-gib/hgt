import GaloisForLFunctions.RHTower.ConnesCutoffTailDecay

/-!
# §VII (47), two-sided

§VII (47) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∫_{X_Λ} |x_v|^{-α} Sup_{|ε| ≤ 1} |η(x+ε)| dx = O(Λ^{-N})`.

`ConnesCutoffTailDecay` proved this over the *positive* tail `(Λ,∞)`.  The commutator of (46) lives
on the whole thickened tail `X_Λ = {|x| ≥ Λ}`, so the negative half is needed too.  It is not a
formal consequence of the positive half — the reflected function `η(−·)` would have to be produced
as a Schwartz map — but no reflection is required: the thickened Schwartz bound
`connesUnitSup_schwartz_le` is stated in terms of `|x|` and therefore applies verbatim at `−x`.

The negative half is then transported to `Ioi R` by `integral_comp_neg_Ioi`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§VII (47), the reflected half.**  The tail integral of the reflected thickened supremum
decays faster than every power of the cutoff. -/
theorem connes_cutoff_tail_neg_rapidDecay (η : SchwartzMap ℝ ℂ) {α : ℝ} (hα0 : 0 < α) (N : ℕ) :
    Tendsto (fun L : ℝ => L ^ N *
        ∫ x in Ioi L, x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x))
      atTop (𝓝 0) := by
  set m : ℕ := N + 2 with hm
  set S : ℝ := (SchwartzMap.seminorm ℂ m 0) η with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ η
  set p : ℝ := α + (m : ℝ) with hp
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hp1 : 1 < p := by
    rw [hp, hm]
    push_cast
    linarith
  set K : ℝ := 2 ^ m * S / (p - 1) with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) < p - 1 := by linarith
    positivity
  have htail : ∀ L : ℝ, 0 < L → (∫ x in Ioi L, x ^ (-p)) = L ^ (1 - p) / (p - 1) := by
    intro L hL
    have hlt : (-p : ℝ) < -1 := by linarith
    rw [integral_Ioi_rpow_of_lt hlt hL]
    have h1 : (-p + 1 : ℝ) = -(p - 1) := by ring
    rw [h1, div_neg, neg_div, neg_neg, show -(p - 1) = 1 - p by ring]
  have hbound : ∀ L : ℝ, 2 ≤ L →
      (∫ x in Ioi L, x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x))
        ≤ K * L ^ (1 - p) := by
    intro L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    have hmajint : IntegrableOn (fun x : ℝ => 2 ^ m * S * x ^ (-p)) (Ioi L) volume := by
      have hint : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioi L) volume :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hL0
      exact hint.const_mul _
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi L)]
        fun x : ℝ => x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans hL0 hx
      exact mul_nonneg (Real.rpow_nonneg hx0.le _) (connesUnitSup_nonneg _ _)
    have hle : (fun x : ℝ => x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x))
        ≤ᵐ[volume.restrict (Ioi L)] fun x : ℝ => 2 ^ m * S * x ^ (-p) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxL : L < x := hx
      have hx0 : (0 : ℝ) < x := lt_trans hL0 hxL
      have hxabs : |(-x)| = x := by rw [abs_neg, abs_of_pos hx0]
      have hx2 : 2 ≤ |(-x)| := by rw [hxabs]; linarith
      have hsup := connesUnitSup_schwartz_le η m hx2
      rw [hxabs] at hsup
      have h1 : (0 : ℝ) ≤ x ^ (-α) := Real.rpow_nonneg hx0.le _
      have hstep : x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x)
          ≤ x ^ (-α) * (2 ^ m * S / x ^ m) := mul_le_mul_of_nonneg_left hsup h1
      refine le_trans hstep (le_of_eq ?_)
      have hxm : (x : ℝ) ^ m = x ^ ((m : ℝ)) := (Real.rpow_natCast x m).symm
      have hxa : (x : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hx0 α).ne'
      have hxmm : (x : ℝ) ^ ((m : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
      rw [hxm, hp, Real.rpow_neg hx0.le α, Real.rpow_neg hx0.le (α + (m : ℝ)),
        Real.rpow_add hx0 α ((m : ℝ))]
      field_simp
    refine le_trans (integral_mono_of_nonneg hnn hmajint hle) (le_of_eq ?_)
    rw [integral_const_mul, htail L hL0, hK]
    field_simp
  have hlim : Tendsto (fun L : ℝ => K * (L ^ N * L ^ (1 - p))) atTop (𝓝 0) := by
    have hexp : ∀ L : ℝ, 0 < L →
        L ^ N * L ^ (1 - p) = L ^ (-(p - (N : ℝ) - 1)) := by
      intro L hL
      rw [← Real.rpow_natCast L N, ← Real.rpow_add hL]
      congr 1
      ring
    have hmcast : ((m : ℕ) : ℝ) = (N : ℝ) + 2 := by rw [hm]; push_cast; ring
    have hq : (0 : ℝ) < p - (N : ℝ) - 1 := by
      rw [hp, hmcast]
      linarith
    have h0 : Tendsto (fun L : ℝ => L ^ (-(p - (N : ℝ) - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hq
    have h1 : Tendsto (fun L : ℝ => L ^ N * L ^ (1 - p)) atTop (𝓝 0) := by
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact (hexp L hL).symm
    simpa using h1.const_mul K
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_trans hL0 hx
    exact mul_nonneg (Real.rpow_nonneg hx0.le _) (connesUnitSup_nonneg _ _)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    have hb := hbound L hL
    calc L ^ N * ∫ x in Ioi L, x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x)
        ≤ L ^ N * (K * L ^ (1 - p)) := by
          refine mul_le_mul_of_nonneg_left hb (by positivity)
      _ = K * (L ^ N * L ^ (1 - p)) := by ring

/-- The negative half of the thickened tail, transported to `Ioi L`. -/
theorem connes_tail_Iic_eq {α : ℝ} (η : SchwartzMap ℝ ℂ) {L : ℝ} (hL : 0 < L) :
    (∫ x in Iic (-L), |x| ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) x)
      = ∫ x in Ioi L, x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x) := by
  have hcomp := integral_comp_neg_Ioi (E := ℝ) L
    (fun x : ℝ => |x| ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) x)
  rw [← hcomp]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans hL hx
  show |(-x)| ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x)
    = x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x)
  rw [abs_neg, abs_of_pos hx0]

/-- **§VII (47), two-sided.**  The whole thickened tail contributes `O(Λ^{-N})`. -/
theorem connes_cutoff_tail_twoSided_rapidDecay (η : SchwartzMap ℝ ℂ) {α : ℝ} (hα0 : 0 < α)
    (N : ℕ) :
    Tendsto (fun L : ℝ => L ^ N *
        ((∫ x in Ioi L, x ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) x)
          + ∫ x in Iic (-L), |x| ^ (-α) * connesUnitSup ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) x))
      atTop (𝓝 0) := by
  have h1 := connes_cutoff_tail_rapidDecay η hα0 N
  have h2 := connes_cutoff_tail_neg_rapidDecay η hα0 N
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  rw [connes_tail_Iic_eq η hL]
  ring

end

end GaloisForLFunctions.RHTower
