import GaloisForLFunctions.WindowedLandauTheory.SizeWindowBrackets.RealSlopeBoundsSplit

namespace WindowedLandauTheory.LFunctionChainParameters.WeightedMeanLemmas

/-- Lower-bound the mean using the slope inequality and upper-bound the maximum
by discarding the nonnegative degree term. -/
theorem weighted_mean_lemma_ge (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaUge ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hslopes
  obtain ⟨hmax, hmin⟩ := hslopes
  have hpos := sum_rank_pos hd
  have hmean : wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u)
      ≤ sF d muN h := by
    have hcombine :
        wmean d (fun u => muM u - h u + Sg0 - (dr u + BE u)) =
          wmean d (fun u => muM u - h u) + Sg0 - wmean d (fun u => dr u + BE u) := by
      simp only [wmean, rankMean, mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
      rw [← Finset.sum_mul, sub_div, add_div, mul_div_cancel_left₀ _ hpos.ne']
    rw [← hcombine]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
        (by linarith only [hmin u]) (hd u).le) hpos.le
  have hupper : umax (fun u => muMaxN u - h u) ≤ umax (fun u => muMaxM u - h u) + Sg0 := by
    unfold umax
    apply Finset.sup'_le
    intro u _
    have hu := Finset.le_sup' (fun u => muMaxM u - h u) (Finset.mem_univ u)
    linarith only [hu, hmax u, hdr u]
  unfold uF rhsU
  linarith only [hmean, hupper]

/-- Compare the slope spread with the mean loss when the lower slope is given exactly. -/
theorem weighted_mean_claimU (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaU ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hslopes
  exact weighted_mean_lemma_ge ι d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr
    ⟨hslopes.1, fun u => (hslopes.2 u).symm.le⟩

end WindowedLandauTheory.LFunctionChainParameters.WeightedMeanLemmas
