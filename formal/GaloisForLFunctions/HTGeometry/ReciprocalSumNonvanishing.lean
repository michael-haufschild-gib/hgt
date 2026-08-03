import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import GaloisForLFunctions.HTGeometry.BlockSplitEscape

/-!
# A nonzero weighting of shifted reciprocals never vanishes identically

Clearing denominators in `∑_z β_z / (a_z + t)` produces the polynomial
`∑_z β_z ∏_{w ≠ z} (X + a_w)`, whose value at `t = -a_{z₀}` is `β_{z₀} ∏_{w ≠ z₀} (a_w - a_{z₀})`.
For distinct shifts that value is nonzero as soon as `β_{z₀}` is, so the polynomial is nonzero and
the reciprocal sum is nonzero for all but finitely many shifts.

This is the gap-weight nondegeneracy behind a block-splitting escape: the reciprocal gaps of a
diagonal base can always be weighted so that a prescribed nonzero character survives.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Clearing denominators in a weighted sum of shifted reciprocals. -/
def reciprocalSumPolynomial (a β : ι → ℝ) : Polynomial ℝ :=
  ∑ z, Polynomial.C (β z) * ∏ w ∈ Finset.univ.erase z, (Polynomial.X + Polynomial.C (a w))

theorem eval_reciprocalSumPolynomial_neg (a β : ι → ℝ) (z₀ : ι) :
    (reciprocalSumPolynomial a β).eval (-a z₀)
      = β z₀ * ∏ w ∈ Finset.univ.erase z₀, (a w - a z₀) := by
  classical
  rw [reciprocalSumPolynomial, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single z₀]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · intro z _ hz
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hmem : z₀ ∈ Finset.univ.erase z := Finset.mem_erase.mpr ⟨Ne.symm hz, Finset.mem_univ _⟩
    have hzero : ∏ w ∈ Finset.univ.erase z,
        (Polynomial.X + Polynomial.C (a w)).eval (-a z₀) = 0 := by
      refine Finset.prod_eq_zero hmem ?_
      rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      ring
    rw [hzero, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ z₀) hcon

/-- **The clearing polynomial of a nonzero weighting is nonzero.** -/
theorem reciprocalSumPolynomial_ne_zero {a β : ι → ℝ} (hinj : Function.Injective a) {z₀ : ι}
    (hβ : β z₀ ≠ 0) : reciprocalSumPolynomial a β ≠ 0 := by
  classical
  intro hzero
  have hval := eval_reciprocalSumPolynomial_neg a β z₀
  rw [hzero, Polynomial.eval_zero] at hval
  have hprod : (∏ w ∈ Finset.univ.erase z₀, (a w - a z₀)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun w hw => ?_
    have hne : w ≠ z₀ := (Finset.mem_erase.mp hw).1
    exact sub_ne_zero.mpr fun hcon => hne (hinj hcon)
  exact hprod ((mul_eq_zero.mp hval.symm).resolve_left hβ)

/-- Away from the poles the reciprocal sum is the clearing polynomial over the product. -/
theorem reciprocalSum_eq_div {a β : ι → ℝ} {t : ℝ} (ht : ∀ z, a z + t ≠ 0) :
    (∑ z, β z / (a z + t))
      = (reciprocalSumPolynomial a β).eval t / ∏ z, (a z + t) := by
  classical
  have hprodne : (∏ z, (a z + t)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z _ => ht z
  rw [reciprocalSumPolynomial, Polynomial.eval_finsetSum, eq_div_iff hprodne, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hval : ∏ w ∈ Finset.univ.erase z, (Polynomial.X + Polynomial.C (a w)).eval t
      = ∏ w ∈ Finset.univ.erase z, (a w + t) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [hval, ← Finset.mul_prod_erase Finset.univ (fun w => a w + t) (Finset.mem_univ z),
    div_mul_eq_mul_div, mul_comm (a z + t)]
  rw [mul_div_assoc, mul_div_assoc]
  congr 1
  rw [div_self (ht z), mul_one]

/-- **Gap-weight nondegeneracy.**  For distinct shifts and a nonzero weight there are arbitrarily
large translates at which the weighted sum of reciprocals is nonzero and every shifted gap is
positive. -/
theorem exists_large_reciprocalSum_ne_zero {a β : ι → ℝ} (hinj : Function.Injective a) {z₀ : ι}
    (hβ : β z₀ ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ (∀ z, 0 < a z + t) ∧ (∑ z, β z / (a z + t)) ≠ 0 := by
  classical
  have hne : Nonempty ι := ⟨z₀⟩
  set S : ℝ := Finset.univ.sup' (Finset.univ_nonempty) (fun z => -a z) with hS
  have hpoly : reciprocalSumPolynomial a β ≠ 0 := reciprocalSumPolynomial_ne_zero hinj hβ
  have hroots : {t : ℝ | (reciprocalSumPolynomial a β).IsRoot t}.Finite :=
    Polynomial.finite_setOf_isRoot hpoly
  obtain ⟨M, hM⟩ := hroots.bddAbove
  refine ⟨max (max T S) M + 1, ?_, ?_, ?_⟩
  · have h1 : T ≤ max (max T S) M := le_trans (le_max_left T S) (le_max_left (max T S) M)
    linarith
  · intro z
    have hle : -a z ≤ S := Finset.le_sup' (fun z => -a z) (Finset.mem_univ z)
    have h1 : S ≤ max (max T S) M := le_trans (le_max_right T S) (le_max_left (max T S) M)
    linarith
  · have hpos : ∀ z, 0 < a z + (max (max T S) M + 1) := by
      intro z
      have hle : -a z ≤ S := Finset.le_sup' (fun z => -a z) (Finset.mem_univ z)
      have h1 : S ≤ max (max T S) M := le_trans (le_max_right T S) (le_max_left (max T S) M)
      linarith
    rw [reciprocalSum_eq_div (fun z => ne_of_gt (hpos z))]
    refine div_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun z _ => ne_of_gt (hpos z))
    intro hcon
    have hmem : (max (max T S) M + 1) ∈ {t : ℝ | (reciprocalSumPolynomial a β).IsRoot t} := hcon
    have hle := hM hmem
    have h2 : M ≤ max (max T S) M := le_max_right (max T S) M
    linarith


/-- **Escape by gap selection.**  For pairwise distinct base gaps and a nonzero block-difference
vector, some diagonal shift makes every gap positive and leaves a splitting parameter, arbitrarily
close to the unsplit point, at which the block-split relation is nonzero. -/
theorem exists_shift_and_split_ne_zero {a β : ι → ℝ} (hinj : Function.Injective a) {z₀ : ι}
    (hβ : β z₀ ≠ 0) (c T : ℝ) {V : Set ℝ} (hV : V ∈ nhds (0 : ℝ)) :
    ∃ t : ℝ, T < t ∧ (∀ z, 0 < a z + t) ∧
      ∃ u ∈ V, blockSplitRelation c β (fun z => a z + t) u ≠ 0 := by
  obtain ⟨t, htT, hpos, hsum⟩ := exists_large_reciprocalSum_ne_zero hinj hβ T
  refine ⟨t, htT, hpos, ?_⟩
  refine exists_ne_zero_blockSplitRelation c β (fun z => a z + t) (fun z => ne_of_gt (hpos z)) ?_ hV
  have hweight : (∑ z, β z * (1 / |a z + t|)) = ∑ z, β z / (a z + t) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [abs_of_pos (hpos z), mul_one_div]
  rw [hweight]
  exact hsum


/-- **Gap-weight nondegeneracy near the base.**  For pairwise distinct positive base gaps and a
nonzero weight, arbitrarily small shifts keep every gap positive and make the weighted sum of
reciprocals nonzero: the finitely many roots of the clearing polynomial cannot fill a neighbourhood
of the base. -/
theorem exists_small_reciprocalSum_ne_zero {a β : ι → ℝ} (hinj : Function.Injective a) {z₀ : ι}
    (hβ : β z₀ ≠ 0) (hpos : ∀ z, 0 < a z) {W : Set ℝ} (hW : W ∈ nhds (0 : ℝ)) :
    ∃ t ∈ W, (∀ z, 0 < a z + t) ∧ (∑ z, β z / (a z + t)) ≠ 0 := by
  classical
  have hne : Nonempty ι := ⟨z₀⟩
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨z₁, -, hz₁⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) a
  set A : ℝ := Finset.univ.inf' Finset.univ_nonempty a with hA
  have hApos : 0 < A := by rw [hz₁]; exact hpos z₁
  have hAle : ∀ z, A ≤ a z := fun z => Finset.inf'_le a (Finset.mem_univ z)
  set ε : ℝ := min ε₀ A with hεdef
  have hε : 0 < ε := lt_min hε₀ hApos
  have hroots : {t : ℝ | (reciprocalSumPolynomial a β).IsRoot t}.Finite :=
    Polynomial.finite_setOf_isRoot (reciprocalSumPolynomial_ne_zero hinj hβ)
  obtain ⟨t, ht⟩ :=
    ((Set.Ioo_infinite (show (-ε : ℝ) < ε by linarith)).sdiff hroots).nonempty
  have htIoo : t ∈ Set.Ioo (-ε) ε := ht.1
  have htroot : ¬ (reciprocalSumPolynomial a β).IsRoot t := ht.2
  have hεA : ε ≤ A := min_le_right _ _
  have hpos' : ∀ z, 0 < a z + t := by
    intro z
    have h1 : -ε < t := htIoo.1
    have h2 : A ≤ a z := hAle z
    linarith
  refine ⟨t, hball ?_, hpos', ?_⟩
  · have hεε₀ : ε ≤ ε₀ := min_le_left _ _
    have habs : |t| < ε₀ :=
      abs_lt.mpr ⟨by linarith [htIoo.1], by linarith [htIoo.2]⟩
    simpa [Real.dist_eq] using habs
  · rw [reciprocalSum_eq_div (fun z => ne_of_gt (hpos' z))]
    exact div_ne_zero htroot (Finset.prod_ne_zero_iff.mpr fun z _ => ne_of_gt (hpos' z))

end

end GaloisForLFunctions.HTGeometry
