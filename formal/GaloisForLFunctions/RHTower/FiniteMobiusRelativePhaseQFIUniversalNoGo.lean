import GaloisForLFunctions.RHTower.FiniteMobiusRelativePhaseQFI

/-!
# Relative-phase overflow QFI is universal on the strict-left strip

Every open-strip point strictly left of the critical line admits a cofinal
subsequence on which Möbius overflow escapes, correction–recovery interaction
is asymptotically opposite to that overflow, and their relative-phase QFI tends
to `4`.  Hence this leading information-geometric circle cannot select zeros.
-/

open Complex Filter Set
open scoped Topology BigOperators

namespace RHTower.DeletionMixedRefinement

noncomputable section

/-- Any open-strip point strictly left of the critical line. -/
abbrev StrictLeftOpenStripPoint :=
  {s : FiniteCutoffOpenStripPoint // (s.1 : ℂ).re < (1 : ℝ) / 2}

theorem tendsto_nat_cpow_mul_finiteCutoffNormalizer_zero_at_strictLeftPoint
    (s : StrictLeftOpenStripPoint) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ (s.1 : ℂ) * finiteCutoffNormalizer s.1 N)
      atTop (nhds 0) := by
  have hexponent : (((s.1 : ℂ) + ((s.1 : ℂ) - 1))).re < 0 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re]
    linarith [s.2]
  have hpow : Tendsto (fun N : ℕ =>
      (N : ℂ) ^ ((s.1 : ℂ) + ((s.1 : ℂ) - 1))) atTop (nhds 0) :=
    tendsto_nat_cpow_zero hexponent
  have hscaled :=
    (tendsto_const_nhds (x := (1 - (s.1 : ℂ)))).mul hpow
  simpa only [mul_zero] using hscaled.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    change (1 - (s.1 : ℂ)) *
        (N : ℂ) ^ ((s.1 : ℂ) + ((s.1 : ℂ) - 1)) =
      (N : ℂ) ^ (s.1 : ℂ) *
        ((1 - (s.1 : ℂ)) * (N : ℂ) ^ ((s.1 : ℂ) - 1))
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [Complex.cpow_add _ _ hN0]
    ring)

theorem tendsto_nat_cpow_mul_finiteMobiusRecoveryHead_zero_of_bounded_product_at_strictLeftPoint
    (s : StrictLeftOpenStripPoint)
    (hbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun N : ℕ =>
      finiteZetaFormationHead N (s.1 : ℂ) *
        finiteMobiusRecoveryHead N (s.1 : ℂ))) :
    Tendsto (fun N : ℕ =>
      (N : ℂ) ^ (s.1 : ℂ) * finiteMobiusRecoveryHead N (s.1 : ℂ))
      atTop (nhds 0) := by
  have hscale :=
    tendsto_nat_cpow_mul_finiteCutoffNormalizer_zero_at_strictLeftPoint s
  have hzero : Tendsto (fun N : ℕ =>
      ((N : ℂ) ^ (s.1 : ℂ) * finiteCutoffNormalizer s.1 N) *
        (finiteZetaFormationHead N (s.1 : ℂ) *
          finiteMobiusRecoveryHead N (s.1 : ℂ))) atTop (nhds 0) :=
    hscale.zero_mul_isBoundedUnder_le hbounded
  have hnormalized := tendsto_normalized_finiteZetaFormationHead s.1
  have hinverse := hnormalized.inv₀ one_ne_zero
  have hproduct := hzero.mul hinverse
  simpa only [zero_mul] using hproduct.congr' (by
    filter_upwards [hnormalized.eventually_ne one_ne_zero] with N hne
    have hcancel :
        (finiteCutoffNormalizer s.1 N * finiteZetaFormationHead N (s.1 : ℂ)) *
          (finiteCutoffNormalizer s.1 N *
            finiteZetaFormationHead N (s.1 : ℂ))⁻¹ = 1 :=
      mul_inv_cancel₀ hne
    calc
      ((N : ℂ) ^ (s.1 : ℂ) * finiteCutoffNormalizer s.1 N) *
            (finiteZetaFormationHead N (s.1 : ℂ) *
              finiteMobiusRecoveryHead N (s.1 : ℂ)) *
          (finiteCutoffNormalizer s.1 N *
            finiteZetaFormationHead N (s.1 : ℂ))⁻¹ =
        ((N : ℂ) ^ (s.1 : ℂ) *
          finiteMobiusRecoveryHead N (s.1 : ℂ)) *
          ((finiteCutoffNormalizer s.1 N *
            finiteZetaFormationHead N (s.1 : ℂ)) *
              (finiteCutoffNormalizer s.1 N *
                finiteZetaFormationHead N (s.1 : ℂ))⁻¹) := by ring
      _ = _ := by rw [hcancel, mul_one])

theorem finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftPoint
    (s : StrictLeftOpenStripPoint) :
    ¬ IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => finiteMobiusOverflow N (s.1 : ℂ)) := by
  intro hbounded
  have hproduct :=
    bounded_finiteMobiusOverflow_implies_bounded_head_product (s.1 : ℂ) hbounded
  have hcurrent :=
    tendsto_nat_cpow_mul_finiteMobiusRecoveryHead_zero_of_bounded_product_at_strictLeftPoint
      s hproduct
  have hprevious :=
    tendsto_natSucc_cpow_mul_finiteMobiusRecoveryHead_zero (s.1 : ℂ) hcurrent
  exact finiteMobiusRecoveryHead_scaled_pair_not_both_zero
    (s.1 : ℂ) hcurrent hprevious

theorem exists_finiteMobiusOverflow_norm_gt_after_at_strictLeftPoint
    (s : StrictLeftOpenStripPoint) (R : ℝ) (N0 : ℕ) :
    ∃ N, N0 ≤ N ∧ R < ‖finiteMobiusOverflow N (s.1 : ℂ)‖ := by
  by_contra h
  push Not at h
  apply finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftPoint s
  apply isBoundedUnder_of_eventually_le (a := R)
  filter_upwards [eventually_ge_atTop N0] with N hN
  simpa only [Function.comp_apply] using h N hN

noncomputable def leftOverflowChoice
    (s : StrictLeftOpenStripPoint) (N : ℕ) : ℕ :=
  Classical.choose
    (exists_finiteMobiusOverflow_norm_gt_after_at_strictLeftPoint s (N : ℝ) N)

theorem leftOverflowChoice_spec
    (s : StrictLeftOpenStripPoint) (N : ℕ) :
    N ≤ leftOverflowChoice s N ∧
      (N : ℝ) < ‖finiteMobiusOverflow (leftOverflowChoice s N) (s.1 : ℂ)‖ :=
  Classical.choose_spec
    (exists_finiteMobiusOverflow_norm_gt_after_at_strictLeftPoint s (N : ℝ) N)

theorem strictLeftPoint_exists_overflowRecoveryRelativePhaseQFI_balanced
    (s : StrictLeftOpenStripPoint) :
    ∃ k : ℕ → ℕ,
      StrictMono k ∧
      Tendsto (fun N => ‖finiteMobiusOverflow (k N) (s.1 : ℂ)‖) atTop atTop ∧
      Tendsto (fun N =>
        finiteCorrectionRecoveryInteraction (k N) (s.1 : ℂ) *
          (finiteMobiusOverflow (k N) (s.1 : ℂ))⁻¹) atTop (nhds (-1)) ∧
      Tendsto (fun N => compensatedPairRelativePhaseQFI
        (finiteMobiusOverflow (k N) (s.1 : ℂ))
        (finiteCorrectionRecoveryInteraction (k N) (s.1 : ℂ))) atTop (nhds 4) := by
  obtain ⟨phi, hphi, hk⟩ :=
    Filter.strictMono_subseq_of_id_le (fun N => (leftOverflowChoice_spec s N).1)
  let k := leftOverflowChoice s ∘ phi
  have hk' : StrictMono k := hk
  have hphiTop : Tendsto phi atTop atTop := hphi.tendsto_atTop
  have hphiReal : Tendsto (fun N => (phi N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hphiTop
  have hO : Tendsto (fun N => ‖finiteMobiusOverflow (k N) (s.1 : ℂ)‖)
      atTop atTop := by
    refine tendsto_atTop.2 (fun R => ?_)
    filter_upwards [hphiReal.eventually (eventually_gt_atTop R)] with N hN
    simpa [k] using (hN.trans (leftOverflowChoice_spec s (phi N)).2).le
  have hOInv : Tendsto (fun N => (finiteMobiusOverflow (k N) (s.1 : ℂ))⁻¹)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun N => ‖(finiteMobiusOverflow (k N) (s.1 : ℂ))⁻¹‖) =
      (fun r : ℝ => r⁻¹) ∘ fun N => ‖finiteMobiusOverflow (k N) (s.1 : ℂ)‖ by
        funext N
        simp]
    exact tendsto_inv_atTop_zero.comp hO
  have hH : Tendsto (fun N => ‖finiteZetaFormationHead (k N) (s.1 : ℂ)‖)
      atTop atTop :=
    (tendsto_norm_finiteZetaFormationHead_atTop s.1).comp hk'.tendsto_atTop
  have hHInv : Tendsto (fun N => (finiteZetaFormationHead (k N) (s.1 : ℂ))⁻¹)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun N => ‖(finiteZetaFormationHead (k N) (s.1 : ℂ))⁻¹‖) =
      (fun r : ℝ => r⁻¹) ∘ fun N => ‖finiteZetaFormationHead (k N) (s.1 : ℂ)‖ by
        funext N
        simp]
    exact tendsto_inv_atTop_zero.comp hH
  have hF : Tendsto (fun N => finiteCutoffZeta (k N) (s.1 : ℂ)) atTop
      (nhds (riemannZeta (s.1 : ℂ))) :=
    (tendsto_finiteCutoffZeta_at_openStrip s.1).comp hk'.tendsto_atTop
  have hCoverH : Tendsto (fun N =>
      finiteCutoffContinuationCorrection (k N) (s.1 : ℂ) *
        (finiteZetaFormationHead (k N) (s.1 : ℂ))⁻¹) atTop (nhds (-1)) := by
    have hmain := (hF.mul hHInv).sub (tendsto_const_nhds (x := (1 : ℂ)))
    have hHnz : ∀ᶠ N in atTop, finiteZetaFormationHead (k N) (s.1 : ℂ) ≠ 0 :=
      eventually_ne_of_tendsto_norm_atTop hH 0
    simpa only [mul_zero, zero_sub] using hmain.congr' (hHnz.mono fun N hN => by
      rw [show finiteCutoffContinuationCorrection (k N) (s.1 : ℂ) =
          finiteCutoffZeta (k N) (s.1 : ℂ) -
            finiteZetaFormationHead (k N) (s.1 : ℂ) by
        linear_combination
          finiteZetaFormationHead_add_continuationCorrection (k N) (s.1 : ℂ)]
      rw [sub_mul, mul_inv_cancel₀ hN])
  have hHBoverO : Tendsto (fun N =>
      (finiteZetaFormationHead (k N) (s.1 : ℂ) *
        finiteMobiusRecoveryHead (k N) (s.1 : ℂ)) *
          (finiteMobiusOverflow (k N) (s.1 : ℂ))⁻¹) atTop (nhds 1) := by
    have hmain := (tendsto_const_nhds (x := (1 : ℂ))).add hOInv
    have hevent : ∀ᶠ N in atTop, 1 ≤ k N :=
      (hk'.tendsto_atTop.eventually (eventually_ge_atTop 1))
    have hOnz : ∀ᶠ N in atTop, finiteMobiusOverflow (k N) (s.1 : ℂ) ≠ 0 :=
      eventually_ne_of_tendsto_norm_atTop hO 0
    simpa only [add_zero] using hmain.congr' ((hevent.and hOnz).mono fun N hN => by
      rw [finiteZetaFormationHead_mul_finiteMobiusRecoveryHead_eq_one_add_overflow
        (k N) hN.1, add_mul, mul_inv_cancel₀ hN.2]
      ring)
  have hratio : Tendsto (fun N =>
      finiteCorrectionRecoveryInteraction (k N) (s.1 : ℂ) *
        (finiteMobiusOverflow (k N) (s.1 : ℂ))⁻¹) atTop (nhds (-1)) := by
    have hproduct := hCoverH.mul hHBoverO
    have hHnz : ∀ᶠ N in atTop, finiteZetaFormationHead (k N) (s.1 : ℂ) ≠ 0 :=
      eventually_ne_of_tendsto_norm_atTop hH 0
    simpa only [mul_one] using hproduct.congr' (hHnz.mono fun N hN => by
      rw [finiteCorrectionRecoveryInteraction]
      field_simp)
  refine ⟨k, hk', hO, hratio, ?_⟩
  exact tendsto_compensatedPairRelativePhaseQFI_of_ratio
    (fun N => finiteMobiusOverflow (k N) (s.1 : ℂ))
    (fun N => finiteCorrectionRecoveryInteraction (k N) (s.1 : ℂ)) hO hratio

end
end RHTower.DeletionMixedRefinement
