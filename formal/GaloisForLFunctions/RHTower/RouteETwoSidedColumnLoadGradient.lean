import GaloisForLFunctions.RHTower.RouteEDegreeNormalizedGibbsBoundaryVariation

/-!
# Route E two-sided column-load gradient laws

For a recurrence kernel with complete outgoing rows, the symmetrized inverse degree is
`2 / (1 + columnLoad)`.  This removes the empty-column denominator and reduces its Dirichlet
energy to ordinary column-load roughness with sharp factor four.  The file also proves the exact
two-cell parity energy and a weighted hydrodynamic decomposition retaining the recurrence edge
budget.
-/

namespace RHTower

open scoped BigOperators
open GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

noncomputable section

/-- Full-row inverse load. -/
def routeETwoSidedInverseLoad (l : ℝ) : ℝ := 2 / (1 + l)

theorem routeETwoSidedInverseLoad_sub (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    routeETwoSidedInverseLoad a - routeETwoSidedInverseLoad b =
      2 * (b - a) / ((1 + a) * (1 + b)) := by
  have ha0 : 1 + a ≠ 0 := by linarith
  have hb0 : 1 + b ≠ 0 := by linarith
  unfold routeETwoSidedInverseLoad
  field_simp
  ring

/-- Sharp scalar Lipschitz law behind the factor-four energy reduction. -/
theorem routeETwoSidedInverseLoad_sub_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (routeETwoSidedInverseLoad a - routeETwoSidedInverseLoad b) ^ 2 ≤
      4 * (a - b) ^ 2 := by
  rw [routeETwoSidedInverseLoad_sub a b ha hb]
  let d := (1 + a) * (1 + b)
  have hd : 1 ≤ d := by
    dsimp [d]
    nlinarith [mul_nonneg ha hb]
  have hdpos : 0 < d := lt_of_lt_of_le zero_lt_one hd
  calc
    (2 * (b - a) / d) ^ 2 = 4 * (a - b) ^ 2 / d ^ 2 := by
      field_simp
      ring
    _ ≤ 4 * (a - b) ^ 2 / 1 := by
      gcongr
      nlinarith
    _ = 4 * (a - b) ^ 2 := by ring

namespace RouteERecurrenceKernel

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Ordinary column-load edge energy, retaining symmetric recurrence and co-moving Gibbs weights. -/
def columnLoadDirichletEnergy (K : RouteERecurrenceKernel ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 *
      (K.columnLoad p.1 - K.columnLoad p.2) ^ 2

theorem columnLoadDirichletEnergy_nonneg (K : RouteERecurrenceKernel ι) :
    0 ≤ K.columnLoadDirichletEnergy :=
  Finset.sum_nonneg fun p _hp =>
    mul_nonneg
      (mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
        (K.toWeightedGibbsGraph.weight_nonneg p.2)) (sq_nonneg _)

theorem inverseDegree_eq_twoSidedInverseLoad
    (K : RouteERecurrenceKernel ι) (hrow : ∀ i, K.rowMass i = 1) (i : ι) :
    K.toWeightedGibbsGraph.inverseDegree i =
      routeETwoSidedInverseLoad (K.columnLoad i) := by
  rw [K.toWeightedGibbsGraph_inverseDegree, hrow]
  have hnonneg := K.columnLoad_nonneg i
  rw [if_neg (by linarith : 1 + K.columnLoad i ≠ 0)]
  rfl

theorem isolatedResidual_eq_zero_of_fullRow
    (K : RouteERecurrenceKernel ι) (hrow : ∀ i, K.rowMass i = 1) (i : ι) :
    K.toWeightedGibbsGraph.isolatedResidual i = 0 := by
  rw [RouteEWeightedGibbsGraph.isolatedResidual, if_neg]
  rw [K.toWeightedGibbsGraph_degree, hrow]
  linarith [K.columnLoad_nonneg i]

/-- **Ordinary column-load gradient reduction.** -/
theorem inverseDegreeDirichletEnergy_le_four_columnLoadDirichletEnergy
    (K : RouteERecurrenceKernel ι) (hrow : ∀ i, K.rowMass i = 1) :
    K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy ≤
      4 * K.columnLoadDirichletEnergy := by
  unfold RouteEWeightedGibbsGraph.inverseDegreeDirichletEnergy columnLoadDirichletEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _hp
  rw [K.inverseDegree_eq_twoSidedInverseLoad hrow,
    K.inverseDegree_eq_twoSidedInverseLoad hrow]
  have hweight :
      0 ≤ K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 :=
    mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
      (K.toWeightedGibbsGraph.weight_nonneg p.2)
  calc
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 *
        (routeETwoSidedInverseLoad (K.columnLoad p.1) -
          routeETwoSidedInverseLoad (K.columnLoad p.2)) ^ 2 ≤
        K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 *
          (4 * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (routeETwoSidedInverseLoad_sub_sq_le _ _
          (K.columnLoad_nonneg p.1) (K.columnLoad_nonneg p.2)) hweight
    _ = 4 * (K.toWeightedGibbsGraph.base p.1 p.2 *
          K.toWeightedGibbsGraph.weight p.2 *
            (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) := by ring

/-- Full two-sided rows turn the recurrence Dirichlet bridge into an ordinary column-load
gradient bound, with no isolated term and no hidden denominator. -/
theorem abs_signedCurrent_le_columnLoadDirichletBridge
    (K : RouteERecurrenceKernel ι) (hrow : ∀ i, K.rowMass i = 1) :
    |K.toWeightedGibbsGraph.signedCurrent| ≤
      K.laplace * K.displacement * K.toWeightedGibbsGraph.totalWeight +
        Real.sqrt
          ((1 + Real.exp (K.laplace * K.displacement)) *
            K.toWeightedGibbsGraph.totalWeight * K.columnLoadDirichletEnergy) := by
  have hbridge := K.abs_signedCurrent_le_recurrenceDirichletBridge
  have hisolated : ∑ i, K.toWeightedGibbsGraph.isolatedResidual i = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact K.isolatedResidual_eq_zero_of_fullRow hrow i
  rw [hisolated, zero_add] at hbridge
  let A := (1 + Real.exp (K.laplace * K.displacement)) *
    K.toWeightedGibbsGraph.totalWeight
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le)
      (Finset.sum_nonneg fun i _hi => K.toWeightedGibbsGraph.weight_nonneg i)
  have hE := K.inverseDegreeDirichletEnergy_le_four_columnLoadDirichletEnergy hrow
  have hcol := K.columnLoadDirichletEnergy_nonneg
  have hmul : A * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy ≤
      4 * (A * K.columnLoadDirichletEnergy) := by
    have := mul_le_mul_of_nonneg_left hE hA
    nlinarith
  have harg : 0 ≤ A * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy :=
    mul_nonneg hA K.inverseDegreeDirichletEnergy_nonneg
  have hcolarg : 0 ≤ A * K.columnLoadDirichletEnergy := mul_nonneg hA hcol
  have hsqrt : (1 / 2 : ℝ) *
      Real.sqrt (A * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy) ≤
        Real.sqrt (A * K.columnLoadDirichletEnergy) := by
    have hleft : 0 ≤ (1 / 2 : ℝ) *
        Real.sqrt (A * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy) := by positivity
    have hright : 0 ≤ Real.sqrt (A * K.columnLoadDirichletEnergy) := Real.sqrt_nonneg _
    apply (sq_le_sq₀ hleft hright).mp
    rw [mul_pow, Real.sq_sqrt harg, Real.sq_sqrt hcolarg]
    nlinarith
  change |K.toWeightedGibbsGraph.signedCurrent| ≤
      K.laplace * K.displacement * K.toWeightedGibbsGraph.totalWeight +
        Real.sqrt (A * K.columnLoadDirichletEnergy)
  change |K.toWeightedGibbsGraph.signedCurrent| ≤
      K.laplace * K.displacement * K.toWeightedGibbsGraph.totalWeight +
        (1 / 2 : ℝ) *
          Real.sqrt (A * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy) at hbridge
  linarith

/-- Same-sector residual edge energy. -/
def sameSectorResidualEnergy
    {A : Type*} [DecidableEq A]
    (K : RouteERecurrenceKernel ι) (sector : ι → A) (residual : ι → ℝ) : ℝ :=
  ∑ p ∈ (strictPairs (Finset.univ : Finset ι)).filter
      (fun p => sector p.1 = sector p.2),
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 *
      (residual p.1 - residual p.2) ^ 2

/-- Cross-sector column-load energy, left untouched by hydrodynamic subtraction. -/
def crossSectorColumnLoadEnergy
    {A : Type*} [DecidableEq A]
    (K : RouteERecurrenceKernel ι) (sector : ι → A) : ℝ :=
  ∑ p ∈ (strictPairs (Finset.univ : Finset ι)).filter
      (fun p => sector p.1 ≠ sector p.2),
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2 *
      (K.columnLoad p.1 - K.columnLoad p.2) ^ 2

theorem sameSectorResidualEnergy_nonneg
    {A : Type*} [DecidableEq A]
    (K : RouteERecurrenceKernel ι) (sector : ι → A) (residual : ι → ℝ) :
    0 ≤ K.sameSectorResidualEnergy sector residual :=
  Finset.sum_nonneg fun p _hp =>
    mul_nonneg
      (mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
        (K.toWeightedGibbsGraph.weight_nonneg p.2)) (sq_nonneg _)

theorem crossSectorColumnLoadEnergy_nonneg
    {A : Type*} [DecidableEq A]
    (K : RouteERecurrenceKernel ι) (sector : ι → A) :
    0 ≤ K.crossSectorColumnLoadEnergy sector :=
  Finset.sum_nonneg fun p _hp =>
    mul_nonneg
      (mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
        (K.toWeightedGibbsGraph.weight_nonneg p.2)) (sq_nonneg _)

/-- **Weighted hydrodynamic split.**  Any same-sector macroscopic component whose edge increment
is at most `L*H/X` contributes only the recurrence edge budget. -/
theorem columnLoadDirichletEnergy_le_hydrodynamicSplit
    {A : Type*} [DecidableEq A]
    (K : RouteERecurrenceKernel ι) (sector : ι → A) (residual : ι → ℝ)
    (X L H : ℝ) (hX : 0 < X) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (htrend : ∀ p ∈ strictPairs (Finset.univ : Finset ι),
      sector p.1 = sector p.2 →
      |(K.columnLoad p.1 - residual p.1) -
        (K.columnLoad p.2 - residual p.2)| ≤ L * H / X) :
    K.columnLoadDirichletEnergy ≤
      2 * K.sameSectorResidualEnergy sector residual +
      K.crossSectorColumnLoadEnergy sector +
      (L ^ 2 * H ^ 2 / (2 * X ^ 2)) *
        (1 + Real.exp (K.laplace * K.displacement)) *
          K.toWeightedGibbsGraph.totalWeight := by
  classical
  let edges := strictPairs (Finset.univ : Finset ι)
  let same := edges.filter fun p => sector p.1 = sector p.2
  let cross := edges.filter fun p => sector p.1 ≠ sector p.2
  let ew : ι × ι → ℝ := fun p =>
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2
  have hew : ∀ p, 0 ≤ ew p := fun p =>
    mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
      (K.toWeightedGibbsGraph.weight_nonneg p.2)
  have hsplit : K.columnLoadDirichletEnergy =
      (∑ p ∈ same, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) +
      ∑ p ∈ cross, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2 := by
    simp only [columnLoadDirichletEnergy, same, cross, ew, edges]
    exact (Finset.sum_filter_add_sum_filter_not
      (strictPairs (Finset.univ : Finset ι))
      (fun p => sector p.1 = sector p.2)
      (fun p => K.toWeightedGibbsGraph.base p.1 p.2 *
        K.toWeightedGibbsGraph.weight p.2 *
          (K.columnLoad p.1 - K.columnLoad p.2) ^ 2)).symm
  have hsame :
      (∑ p ∈ same, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) ≤
        2 * K.sameSectorResidualEnergy sector residual +
          2 * (L * H / X) ^ 2 * K.edgeWeightBudget := by
    calc
      (∑ p ∈ same, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) ≤
          ∑ p ∈ same, ew p *
            (2 * (residual p.1 - residual p.2) ^ 2 +
              2 * (L * H / X) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpEdges : p ∈ edges := (Finset.mem_filter.mp hp).1
        have hpSame : sector p.1 = sector p.2 := (Finset.mem_filter.mp hp).2
        have ht := htrend p hpEdges hpSame
        have htSq :
            ((K.columnLoad p.1 - residual p.1) -
              (K.columnLoad p.2 - residual p.2)) ^ 2 ≤ (L * H / X) ^ 2 := by
          have htLower := (abs_le.mp ht).1
          have htUpper := (abs_le.mp ht).2
          nlinarith
        apply mul_le_mul_of_nonneg_left _ (hew p)
        nlinarith [sq_nonneg
          ((K.columnLoad p.1 - residual p.1) -
            (K.columnLoad p.2 - residual p.2) -
              (residual p.1 - residual p.2))]
      _ = 2 * K.sameSectorResidualEnergy sector residual +
          2 * (L * H / X) ^ 2 * ∑ p ∈ same, ew p := by
        change
          (∑ p ∈ same, ew p *
            (2 * (residual p.1 - residual p.2) ^ 2 + 2 * (L * H / X) ^ 2)) =
          2 * (∑ p ∈ same, ew p * (residual p.1 - residual p.2) ^ 2) +
            2 * (L * H / X) ^ 2 * ∑ p ∈ same, ew p
        calc
          (∑ p ∈ same, ew p *
              (2 * (residual p.1 - residual p.2) ^ 2 + 2 * (L * H / X) ^ 2)) =
              ∑ p ∈ same,
                (2 * (ew p * (residual p.1 - residual p.2) ^ 2) +
                  (2 * (L * H / X) ^ 2) * ew p) := by
            apply Finset.sum_congr rfl
            intro p _hp
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * K.sameSectorResidualEnergy sector residual +
          2 * (L * H / X) ^ 2 * K.edgeWeightBudget := by
        gcongr
        simp only [same, edgeWeightBudget, edges, ew]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _hp _hnot =>
            mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
              (K.toWeightedGibbsGraph.weight_nonneg p.2))
  rw [hsplit]
  have hcross :
      (∑ p ∈ cross, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) =
        K.crossSectorColumnLoadEnergy sector := by
    simp only [crossSectorColumnLoadEnergy, cross, edges, ew]
  have hbudget := K.edgeWeightBudget_le_quarter_one_add_exp_mul_totalWeight
  have hfactor : 0 ≤ 2 * (L * H / X) ^ 2 := by positivity
  calc
    (∑ p ∈ same, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2) +
        ∑ p ∈ cross, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2 ≤
      (2 * K.sameSectorResidualEnergy sector residual +
        2 * (L * H / X) ^ 2 * K.edgeWeightBudget) +
        K.crossSectorColumnLoadEnergy sector := by
      calc
        _ ≤ (2 * K.sameSectorResidualEnergy sector residual +
              2 * (L * H / X) ^ 2 * K.edgeWeightBudget) +
            ∑ p ∈ cross, ew p * (K.columnLoad p.1 - K.columnLoad p.2) ^ 2 :=
          add_le_add_left hsame _
        _ = _ := by rw [hcross]
    _ ≤ 2 * K.sameSectorResidualEnergy sector residual +
        K.crossSectorColumnLoadEnergy sector +
        (L ^ 2 * H ^ 2 / (2 * X ^ 2)) *
          (1 + Real.exp (K.laplace * K.displacement)) *
            K.toWeightedGibbsGraph.totalWeight := by
      have := mul_le_mul_of_nonneg_left hbudget hfactor
      calc
        (2 * K.sameSectorResidualEnergy sector residual +
            2 * (L * H / X) ^ 2 * K.edgeWeightBudget) +
              K.crossSectorColumnLoadEnergy sector =
            2 * K.sameSectorResidualEnergy sector residual +
              K.crossSectorColumnLoadEnergy sector +
                2 * (L * H / X) ^ 2 * K.edgeWeightBudget := by ring
        _ ≤ 2 * K.sameSectorResidualEnergy sector residual +
              K.crossSectorColumnLoadEnergy sector +
                2 * (L * H / X) ^ 2 *
                  ((1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement)) *
                    K.toWeightedGibbsGraph.totalWeight) := by linarith
        _ = _ := by field_simp [ne_of_gt hX]; ring

end RouteERecurrenceKernel

/-! ## Exact two-cell parity energy -/

/-- Canonical inverse loads of opposite-parity masses `P,N`. -/
def routeEParityCellInverseLoadPlus (P N : ℝ) : ℝ := 2 * P / (P + N)
def routeEParityCellInverseLoadMinus (P N : ℝ) : ℝ := 2 * N / (P + N)

/-- Exact complete-bipartite / opposite-parity cell energy. -/
theorem routeEParityCellEnergy_eq (P N : ℝ) (hP : 0 ≤ P) (hN : 0 ≤ N)
    (hPN : P + N ≠ 0) :
    ((P + N) / 2) *
        (routeEParityCellInverseLoadPlus P N -
          routeEParityCellInverseLoadMinus P N) ^ 2 =
      2 * (P - N) ^ 2 / (P + N) := by
  unfold routeEParityCellInverseLoadPlus routeEParityCellInverseLoadMinus
  field_simp

/-- The hostile `2:1` block has linear parity energy. -/
theorem routeEParityCellEnergy_two_one (h : ℝ) (hh : 0 < h) :
    ((2 * h + h) / 2) *
        (routeEParityCellInverseLoadPlus (2 * h) h -
          routeEParityCellInverseLoadMinus (2 * h) h) ^ 2 =
      2 * h / 3 := by
  rw [routeEParityCellEnergy_eq (2 * h) h (by positivity) hh.le (by linarith)]
  field_simp
  ring

end

end RHTower
