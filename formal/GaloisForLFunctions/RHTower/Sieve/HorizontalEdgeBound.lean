import GaloisForLFunctions.HTGeometry.SmoothWeightMellin

/-!
# The horizontal edges of the truncated contour

In the untruncated shift the horizontal edges vanish in the limit and never appear as terms.  For
`1/ζ` the contour must be truncated at a finite height, so the edges are explicit terms and must be
estimated.

The estimate is carried entirely by the cutoff: `exists_bound_mellin_smoothWeight` bounds
`‖s‖·∏_{i<j}‖s+1+i‖·‖W(s)‖` uniformly on `0 < Re s ≤ σmax`, and each of the `j+1` factors is at
least `|Im s|`, since adding a real number leaves the imaginary part alone.  So `W` decays in the
height faster than any fixed power, uniformly in the abscissa, and a horizontal segment of the
truncated rectangle contributes at most `M·C·T^{-(j+1)}·(d-c)` whenever the other factor is bounded
by `M` on that segment.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Set GaloisForLFunctions.HTGeometry

/-- **Decay of the cutoff's transform in the height, uniformly in the abscissa.**  Each of the
`j+1` norms in `exists_bound_mellin_smoothWeight` dominates `|Im s|`, because the shifts `1 + i` are
real. -/
theorem exists_bound_mellin_smoothWeight_im_pow {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight hN hH j σmax
  refine ⟨C, hC, fun s hs hsmax => ?_⟩
  have hbase := hbd s hs hsmax
  rw [← mellin_smoothWeight_eq s] at hbase
  have him : ∀ i : ℕ, |s.im| ≤ ‖s + 1 + (i : ℂ)‖ := by
    intro i
    have himeq : (s + 1 + (i : ℂ)).im = s.im := by simp
    calc |s.im| = |(s + 1 + (i : ℂ)).im| := by rw [himeq]
      _ ≤ ‖s + 1 + (i : ℂ)‖ := Complex.abs_im_le_norm _
  have hprod : |s.im| ^ j ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    calc |s.im| ^ j = ∏ _i ∈ Finset.range j, |s.im| := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => him i)
  have hs0 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hstep : |s.im| ^ (j + 1) ≤ ‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖ := by
    rw [pow_succ']
    exact mul_le_mul hs0 hprod (by positivity) (norm_nonneg _)
  calc |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖
      ≤ (‖s‖ * ∏ i ∈ Finset.range j, ‖s + 1 + (i : ℂ)‖) *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ ≤ C := hbase

/-- The transform's decay in the explicit divided form. -/
theorem norm_mellin_smoothWeight_le_div {N H : ℝ} (j : ℕ) {σmax C : ℝ}
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ σmax →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) (hsmax : s.re ≤ σmax) (hT : 0 < |s.im|) :
    ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C / |s.im| ^ (j + 1) := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hbd s hs hsmax

/-- **The horizontal edge of the truncated rectangle.**  With the second factor bounded by `M` on
the segment, the edge contributes at most `M·C·T^{-(j+1)}·(d-c)` — arbitrarily fast decay in the
truncation height, uniformly in the abscissa range. -/
theorem exists_horizontal_edge_bound {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : ℂ → ℂ) (c d T M : ℝ), 0 < c → c ≤ d → d ≤ σmax → T ≠ 0 → 0 ≤ M →
      (∀ x ∈ Set.Ioc c d, ‖F ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ M) →
      ‖∫ x : ℝ in c..d, F ((x : ℂ) + (T : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((x : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ M * C / |T| ^ (j + 1) * (d - c) := by
  obtain ⟨C, hC, hbd⟩ := exists_bound_mellin_smoothWeight_im_pow hN hH j σmax
  refine ⟨C, hC, fun F c d T M hc hcd hdmax hT hM hF => ?_⟩
  have hkey : ∀ x ∈ Set.uIoc c d,
      ‖F ((x : ℂ) + (T : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ M * C / |T| ^ (j + 1) := by
    intro x hx
    rw [Set.uIoc_of_le hcd] at hx
    have hre : ((x : ℂ) + (T : ℝ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (T : ℝ) * Complex.I).im = T := by simp
    have hTabs : (0 : ℝ) < |T| := abs_pos.2 hT
    have hW : ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((x : ℂ) + (T : ℝ) * Complex.I)‖ ≤ C / |T| ^ (j + 1) := by
      have h := norm_mellin_smoothWeight_le_div j hbd
        (s := (x : ℂ) + (T : ℝ) * Complex.I) (by rw [hre]; linarith [hx.1])
        (by rw [hre]; exact le_trans hx.2 hdmax) (by rw [him]; exact hTabs)
      rwa [him] at h
    rw [norm_mul]
    calc ‖F ((x : ℂ) + (T : ℝ) * Complex.I)‖ *
          ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((x : ℂ) + (T : ℝ) * Complex.I)‖
        ≤ M * (C / |T| ^ (j + 1)) :=
          mul_le_mul (hF x hx) hW (norm_nonneg _) hM
      _ = M * C / |T| ^ (j + 1) := by ring
  have hres := intervalIntegral.norm_integral_le_of_norm_le_const hkey
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ d - c)] at hres

end RHTower.Sieve
