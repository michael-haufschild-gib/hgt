import GaloisForLFunctions.RHTower.PaperWoldCompositeFamily
import GaloisForLFunctions.RHTower.PaperWoldPrimeNormGrowth

/-! # Power-law norm growth above the composite admission boundary

Two adjacent composite-index windows give a positive rectangle of the literal
matrix. Its characteristic vectors expose the exact supercritical obstruction.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators

theorem paperWoldCompositeEntry_rectangle_lower (t : {t : ℝ // 1 / 2 < t})
    (N : ℕ) (hN : 1 ≤ N) (n : ℕ) (hn : n ∈ Finset.Ico N (2 * N))
    (j : ℕ) (hj : j ∈ Finset.Ico (2 * N) (3 * N)) :
    (N : ℝ) ^ (2 * (t : ℝ)) / (48 * (N : ℝ) ^ 2) ≤
      (paperWoldCompositeEntry t n j).re := by
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hn
  obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnhi' : (n : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hnhi
  have hjhi' : (j : ℝ) + 1 ≤ 3 * N := by exact_mod_cast hjhi
  have hnlo' : (N : ℝ) ≤ n := by exact_mod_cast hnlo
  have hncell : 1 / (6 * (N : ℝ)) ≤ -xiHeatCassiniWoldNatIncrement (2 * n + 2) :=
    (one_div_le_one_div_of_le (by positivity) (by linarith :
      2 * (n : ℝ) + 4 ≤ 6 * N)).trans (paperWold_even_composite_increment_lower n)
  have hjcell : 1 / (8 * (N : ℝ)) ≤ -xiHeatCassiniWoldNatIncrement (2 * j + 2) :=
    (one_div_le_one_div_of_le (by positivity) (by linarith :
      2 * (j : ℝ) + 4 ≤ 8 * N)).trans (paperWold_even_composite_increment_lower j)
  have hw : (N : ℝ) ^ (2 * (t : ℝ)) ≤ (2 * (n : ℝ) + 3) ^ (2 * (t : ℝ)) :=
    Real.rpow_le_rpow hNp.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
      (by linarith [t.property])
  rw [paperWoldCompositeEntry_formula, if_pos (by omega : n < j), Complex.ofReal_re]
  calc
    _ = (N : ℝ) ^ (2 * (t : ℝ)) * (1 / (6 * (N : ℝ))) * (1 / (8 * (N : ℝ))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul hw hncell (by positivity)
        (Real.rpow_nonneg (by positivity) _)) hjcell (by positivity)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (neg_nonneg.mpr (paperWold_even_composite_increment_neg n).le))

/-- A finite positive composite rectangle already forces supercritical norm growth. -/
theorem paperWoldComposite_rectangle_norm_lower (t : {t : ℝ // 1 / 2 < t})
    (N : ℕ) (hN : 1 ≤ N) (A : PaperWoldHistory →L[ℂ] PaperWoldHistory)
    (he : ∀ n ∈ Finset.Ico N (2 * N), ∀ j ∈ Finset.Ico (2 * N) (3 * N),
      A (lp.single 2 j (1 : ℂ)) n = paperWoldCompositeEntry t n j) :
    (N : ℝ) ^ (2 * (t : ℝ) - 1) / 48 ≤ ‖A‖ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := paperWold_finite_rectangle_norm_lower A (Finset.Ico N (2 * N))
    (Finset.Ico (2 * N) (3 * N)) N
    ((N : ℝ) ^ (2 * (t : ℝ)) / (48 * (N : ℝ) ^ 2)) hNp (by positivity)
    (by simp only [Nat.card_Ico]; exact_mod_cast (show N ≤ 2 * N - N by omega))
    (by simp only [Nat.card_Ico]; exact_mod_cast (show N ≤ 3 * N - 2 * N by omega))
    (fun n hn j hj => by rw [he n hn j hj]; exact paperWoldCompositeEntry_rectangle_lower t N hN n hn j hj)
  have hc : ((N : ℝ) ^ (2 * (t : ℝ)) / (48 * (N : ℝ) ^ 2)) * N =
      (N : ℝ) ^ (2 * (t : ℝ) - 1) / 48 := by
    rw [Real.rpow_sub_one (ne_of_gt hNp)]
    field_simp
  rwa [hc] at h

theorem paperWoldCompositeEntry_finite_isHS (t : ℝ) (s : Finset ℕ) :
    HilbertSchmidt.IsHS (fun q : ℕ × ℕ =>
      if q.1 ∈ s ∧ q.2 ∈ s then paperWoldCompositeEntry t q.1 q.2 else 0) := by
  apply HilbertSchmidt.isHS_of_support_subset (s ×ˢ s)
  intro q hq
  exact if_neg (by simpa only [Finset.mem_product] using hq)

/-- Literal finite cutoffs exist at every real exponent. -/
def paperWoldCompositeFiniteCutoff (t : ℝ) (s : Finset ℕ) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  HilbertSchmidt.toOperator (paperWoldCompositeEntry_finite_isHS t s)

theorem paperWoldCompositeFiniteCutoff_single (t : ℝ) (s : Finset ℕ) (n j : ℕ) :
    paperWoldCompositeFiniteCutoff t s (lp.single 2 j (1 : ℂ)) n =
      if n ∈ s ∧ j ∈ s then paperWoldCompositeEntry t n j else 0 :=
  HilbertSchmidt.toOperator_single (paperWoldCompositeEntry_finite_isHS t s) n j

theorem paperWoldCompositeFiniteCutoff_compact (t : ℝ) (s : Finset ℕ) :
    IsCompactOperator (paperWoldCompositeFiniteCutoff t s) :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator (paperWoldCompositeEntry_finite_isHS t s)).isCompactOperator

theorem paperWoldCompositeFiniteCutoff_traceCost (t : ℝ) (s : Finset ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositeFiniteCutoff t s) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldCompositeFiniteCutoff_compact t s)

theorem paperWoldCompositeFiniteCutoff_norm_lower (t : {t : ℝ // 1 / 2 < t})
    (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (2 * (t : ℝ) - 1) / 48 ≤
      ‖paperWoldCompositeFiniteCutoff t (Finset.range (3 * N))‖ := by
  apply paperWoldComposite_rectangle_norm_lower t N hN
  intro n hn j hj
  rw [paperWoldCompositeFiniteCutoff_single, if_pos]
  have hn' := Finset.mem_Ico.mp hn
  have hj' := Finset.mem_Ico.mp hj
  exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hj'.2⟩

theorem paperWoldComposite_power_atTop (t : {t : ℝ // 1 / 2 < t}) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * (t : ℝ) - 1) / 48) atTop atTop :=
  ((tendsto_rpow_atTop (by linarith [t.property])).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).atTop_div_const (by norm_num)

/-- Unconditional divergence of the actual finite-cutoff operator norms. -/
theorem paperWoldCompositeFiniteCutoff_norm_atTop (t : {t : ℝ // 1 / 2 < t}) :
    Tendsto (fun N : ℕ => ‖paperWoldCompositeFiniteCutoff t (Finset.range (3 * N))‖)
      atTop atTop :=
  tendsto_atTop_mono' atTop
    ((eventually_ge_atTop 1).mono (fun N hN => paperWoldCompositeFiniteCutoff_norm_lower t N hN))
    (paperWoldComposite_power_atTop t)

end
end RHTower
