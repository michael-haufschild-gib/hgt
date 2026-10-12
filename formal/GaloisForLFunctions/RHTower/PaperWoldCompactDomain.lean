import GaloisForLFunctions.RHTower.PaperWoldCompositeMass
import GaloisForLFunctions.RHTower.PaperWoldCompositeFlat

/-! # Exact compact-realization domain of the literal full Wold kernel

The original arithmetic matrix admits a compact realization exactly below the
half power. Its composite probe floor also determines the ideal trace cost of
every bounded realization, whenever one exists.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators InnerProductSpace ENNReal

/-- An actual bounded operator retaining every entry of the original full kernel. -/
def PaperWoldRealization (t : ℝ) :=
  {T : PaperWoldHistory →L[ℂ] PaperWoldHistory //
    HasLpMatrix T (fun n j => paperWoldDirectedKernel t (n, j))}

theorem paperWoldRealization_single (t : ℝ) (T : PaperWoldRealization t) (n j : ℕ) :
    T.val (lp.single 2 j (1 : ℂ)) n = paperWoldDirectedKernel t (n, j) :=
  T.property n j

theorem paperWoldRealization_unique (t : ℝ) (T S : PaperWoldRealization t) : T = S :=
  Subtype.ext (HasLpMatrix.ext T.property S.property)

def paperWoldStrictRealization (t : {t : ℝ // t < 1 / 2}) : PaperWoldRealization t :=
  ⟨HilbertSchmidt.toOperator ((paperWoldDirectedKernel_isHS_iff t).mpr t.property),
    fun n j => HilbertSchmidt.toOperator_single _ n j⟩

theorem paperWoldStrictRealization_compact (t : {t : ℝ // t < 1 / 2}) :
    IsCompactOperator (paperWoldStrictRealization t).val :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator
    ((paperWoldDirectedKernel_isHS_iff t).mpr t.property)).isCompactOperator

theorem paperWoldRealization_composite_form (t : ℝ) (T : PaperWoldRealization t) (N : ℕ) :
    inner ℂ (paperWoldCompositeFlat N) (T.val (paperWoldCompositeFlat N)) =
      Complex.ofReal (((N : ℝ) + 1)⁻¹) * ∑ n ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), paperWoldCompositeEntry t n j := by
  rw [paperWoldCompositeFlat_quadratic]
  simp only [paperWoldRealization_single, paperWoldCompositeEntry]

theorem paperWoldRealization_composite_form_re (t : ℝ) (T : PaperWoldRealization t) (N : ℕ) :
    (inner ℂ (paperWoldCompositeFlat N) (T.val (paperWoldCompositeFlat N))).re =
      ((N : ℝ) + 1)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        ∑ j ∈ Finset.range (N + 1), (paperWoldCompositeEntry t n j).re := by
  rw [paperWoldRealization_composite_form]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]

theorem paperWoldRealization_composite_floor
    (t : {t : ℝ // 1 / 2 ≤ t}) (T : PaperWoldRealization t) (N : ℕ) :
    (1 / 24 : ℝ) ≤ (inner ℂ (paperWoldCompositeFlat (N + 1))
      (T.val (paperWoldCompositeFlat (N + 1)))).re := by
  rw [paperWoldRealization_composite_form_re]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show N + 1 + 1 = N + 2 by omega,
    show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
  exact paperWoldCompositeEntry_normalized_mass t N

/-- The compact-ideal admission boundary holds for every exact bounded realization. -/
theorem paperWoldRealization_compact_iff (t : ℝ) (T : PaperWoldRealization t) :
    IsCompactOperator T.val ↔ t < 1 / 2 := by
  constructor
  · intro hT
    by_contra hn
    have ht : 1 / 2 ≤ t := le_of_not_gt hn
    have hc := paperWoldCompositeFlat_compact_form_tendsto ⟨T.val, hT⟩
    have hr := (Complex.continuous_re.tendsto 0).comp hc
    simp only [Function.comp_def, Complex.zero_re] at hr
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr (1 / 24) (by norm_num)
    have hs := hN (N + 1) (by omega)
    rw [Real.dist_eq, sub_zero] at hs
    have hl := paperWoldRealization_composite_floor ⟨t, ht⟩ T N
    exact (not_lt_of_ge hl) ((le_abs_self _).trans_lt hs)
  · intro ht
    have he := paperWoldRealization_unique t T (paperWoldStrictRealization ⟨t, ht⟩)
    rw [he]
    exact paperWoldStrictRealization_compact ⟨t, ht⟩

/-- Unconditional existence classification, with no assumed realization or source sign. -/
theorem paperWold_exists_compact_realization_iff (t : ℝ) :
    (∃ T : PaperWoldRealization t, IsCompactOperator T.val) ↔ t < 1 / 2 := by
  constructor
  · rintro ⟨T, hT⟩
    exact (paperWoldRealization_compact_iff t T).mp hT
  · intro ht
    exact ⟨paperWoldStrictRealization ⟨t, ht⟩, paperWoldStrictRealization_compact ⟨t, ht⟩⟩

/-- The proven closed-ideal weight detects exactly the same native exponent boundary. -/
theorem paperWoldRealization_traceCost (t : ℝ) (T : PaperWoldRealization t) :
    compactOperatorTraceCost PaperWoldHistory T.val = if t < 1 / 2 then 0 else ∞ := by
  split_ifs with ht
  · exact (compactOperatorTraceCost_eq_zero_iff _).mpr ((paperWoldRealization_compact_iff t T).mpr ht)
  · exact (compactOperatorTraceCost_eq_top_iff _).mpr
      (fun h => ht ((paperWoldRealization_compact_iff t T).mp h))

end
end RHTower
