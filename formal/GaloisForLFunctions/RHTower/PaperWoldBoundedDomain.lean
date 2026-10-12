import GaloisForLFunctions.RHTower.PaperWoldPrimeNormGrowth

/-! # Exact bounded-realization domain of the full arithmetic Wold kernel

The prime rectangles exclude every bounded realization at and above the half
power. Below it, the already constructed Hilbert–Schmidt realization is unique.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldRealization_not_nonempty (t : {t : ℝ // 1 / 2 ≤ t}) :
    ¬ Nonempty (PaperWoldRealization t) := by
  rintro ⟨T⟩
  have hg : Tendsto (fun N : ℕ => Real.log N / 8192) atTop atTop :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num)
  obtain ⟨N, hN, hlarge⟩ := ((paperWoldRealization_eventual_prime_norm_lower t T).and
    (hg.eventually (eventually_gt_atTop ‖T.val‖))).exists
  exact (not_lt_of_ge hN) hlarge

/-- The original full kernel has a bounded realization precisely in the strict-half domain. -/
theorem paperWold_exists_bounded_realization_iff (t : ℝ) :
    Nonempty (PaperWoldRealization t) ↔ t < 1 / 2 := by
  constructor
  · intro h
    by_contra ht
    exact paperWoldRealization_not_nonempty ⟨t, le_of_not_gt ht⟩ h
  · intro ht
    exact ⟨paperWoldStrictRealization ⟨t, ht⟩⟩

/-- For this exact arithmetic kernel, bounded admission already pays the full Hilbert–Schmidt budget. -/
theorem paperWold_bounded_realization_iff_isHS (t : ℝ) :
    Nonempty (PaperWoldRealization t) ↔ HilbertSchmidt.IsHS (paperWoldDirectedKernel t) :=
  (paperWold_exists_bounded_realization_iff t).trans (paperWoldDirectedKernel_isHS_iff t).symm

theorem paperWoldRealization_compact (t : ℝ) (T : PaperWoldRealization t) :
    IsCompactOperator T.val :=
  (paperWoldRealization_compact_iff t T).mpr ((paperWold_exists_bounded_realization_iff t).mp ⟨T⟩)

theorem paperWoldRealization_traceCost_zero (t : ℝ) (T : PaperWoldRealization t) :
    compactOperatorTraceCost PaperWoldHistory T.val = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldRealization_compact t T)

end
end RHTower
