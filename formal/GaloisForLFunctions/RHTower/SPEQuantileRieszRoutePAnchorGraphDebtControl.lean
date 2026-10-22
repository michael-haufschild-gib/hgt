import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileBaseEdgeDissipationLower
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePArithmeticVarianceNull

/-!
# Uniform anchored graph control of Route-P's first square debt

The physical Lorentz graph dissipation has a one-dimensional common-displacement
radical. The base-prime edge charges every late displacement relative to prime
`2` with a lever at least the atom index. A von Mangoldt `3/2`-weight is
summable, so finite Cauchy gives a cutoff-independent bound for the anchored
displacement first moment. Finitely many early atoms contribute one fixed
constant.

The exact first square-debt argument is the terminal mass-offset channel minus
this anchored first moment. Consequently that full debt, at physical ratio
one, is bounded by the terminal channel and graph dissipation with fixed
coefficients. This is a genuine decomposition/control of one coupled debt,
not payment by the signed source credit: the terminal scalar, graph energy,
second mass-mismatch debt, and ordered meromorphic intertwiner remain open.
-/

open scoped BigOperators
open scoped Chebyshev

namespace RHTower

noncomputable section

def routePAnchorTail (K : ℕ) : Finset ℕ := Finset.Icc 7 K

def routePAnchorDisplacement (n : ℕ) : ℝ :=
  ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
    ccmActualHeadMatchedQuantilePolarDisplacement 2

def routePAnchorWeight (n : ℕ) : ℝ :=
  criticalMellinAtomWeight (n + 2)

private theorem routePAnchorTail_subset (K : ℕ) :
    routePAnchorTail K ⊆ (Finset.range (K + 1)).erase 0 := by
  intro n hn
  have hn' : 7 ≤ n ∧ n ≤ K := Finset.mem_Icc.mp hn
  exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩

theorem routeP_anchorTail_energy_le_graph (K : ℕ) :
    (∑ n ∈ routePAnchorTail K,
      (criticalMellinAtomWeight 2 * routePAnchorWeight n) / 2 *
        ((n + 2 : ℕ) : ℝ) * (routePAnchorDisplacement n) ^ (2 : ℕ)) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  have hlocal : ∀ n ∈ routePAnchorTail K,
      (criticalMellinAtomWeight 2 * routePAnchorWeight n) / 2 *
          ((n + 2 : ℕ) : ℝ) * (routePAnchorDisplacement n) ^ (2 : ℕ) ≤
        ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n := by
    intro n hn
    have hn7 : 7 ≤ n := (Finset.mem_Icc.mp hn).1
    exact ccmActualHeadMatchedQuantile_baseEdgeDissipation_ge_weightedDisplacement hn7
  calc
    (∑ n ∈ routePAnchorTail K,
        (criticalMellinAtomWeight 2 * routePAnchorWeight n) / 2 *
          ((n + 2 : ℕ) : ℝ) * (routePAnchorDisplacement n) ^ (2 : ℕ)) ≤
      ∑ n ∈ routePAnchorTail K,
        ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n := by
          exact Finset.sum_le_sum hlocal
    _ ≤ ∑ n ∈ (Finset.range (K + 1)).erase 0,
        ccmActualHeadMatchedQuantileLorentzEdgeDissipation 0 n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (routePAnchorTail_subset K)
          intro n hn _
          exact ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg 0 n
    _ ≤ ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
          rw [← ccmActualHeadMatchedQuantileLorentzEdgeDissipation_sum_eq_graphDissipation]
          unfold ccmActualHeadMatchedQuantileLorentzEdgeSet
          rw [Finset.sum_sigma]
          have hzero : 0 ∈ Finset.range (K + 1) :=
            Finset.mem_range.mpr (by omega)
          exact Finset.single_le_sum (s := Finset.range (K + 1))
            (f := fun m => ∑ n ∈ (Finset.range (K + 1)).erase m,
              ccmActualHeadMatchedQuantileLorentzEdgeDissipation m n)
            (fun m hm => Finset.sum_nonneg fun n hn =>
              ccmActualHeadMatchedQuantileLorentzEdgeDissipation_nonneg m n) hzero

def routePAnchorTailMoment (K : ℕ) : ℝ :=
  ∑ n ∈ routePAnchorTail K, routePAnchorWeight n * routePAnchorDisplacement n

def routePAnchorTailReciprocalMass (K : ℕ) : ℝ :=
  ∑ n ∈ routePAnchorTail K,
    2 * routePAnchorWeight n /
      (criticalMellinAtomWeight 2 * ((n + 2 : ℕ) : ℝ))

theorem routeP_anchorTailMoment_sq_le_graph_mul_reciprocalMass (K : ℕ) :
    routePAnchorTailMoment K ^ (2 : ℕ) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K *
        routePAnchorTailReciprocalMass K := by
  let s := routePAnchorTail K
  let a : ℕ → ℝ := fun n => routePAnchorWeight n * routePAnchorDisplacement n
  let f : ℕ → ℝ := fun n =>
    (criticalMellinAtomWeight 2 * routePAnchorWeight n) / 2 *
      ((n + 2 : ℕ) : ℝ) * routePAnchorDisplacement n ^ (2 : ℕ)
  let g : ℕ → ℝ := fun n =>
    2 * routePAnchorWeight n /
      (criticalMellinAtomWeight 2 * ((n + 2 : ℕ) : ℝ))
  have hw2 : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hfg : ∀ n ∈ s, a n ^ (2 : ℕ) ≤ f n * g n := by
    intro n hn
    have hn0 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    dsimp [a, f, g]
    apply le_of_eq
    field_simp [hw2.ne', hn0.ne']
  have hf : ∀ n ∈ s, 0 ≤ f n := by
    intro n hn
    dsimp [f]
    have hwn : 0 ≤ routePAnchorWeight n :=
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    positivity
  have hg : ∀ n ∈ s, 0 ≤ g n := by
    intro n hn
    dsimp [g]
    have hwn : 0 ≤ routePAnchorWeight n :=
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    positivity
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := a) (f := f) (g := g) hf hg hfg
  change routePAnchorTailMoment K ^ (2 : ℕ) ≤
    (∑ n ∈ s, f n) * (∑ n ∈ s, g n) at hCS
  change routePAnchorTailMoment K ^ (2 : ℕ) ≤
    ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K *
      (∑ n ∈ s, g n)
  have hF : (∑ n ∈ s, f n) ≤
      ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K :=
    routeP_anchorTail_energy_le_graph K
  have hG : 0 ≤ ∑ n ∈ s, g n := Finset.sum_nonneg hg
  exact hCS.trans (mul_le_mul_of_nonneg_right hF hG)

private theorem routePAnchorWeight_div_index_eq_vonMangoldt (n : ℕ) :
    routePAnchorWeight n / ((n + 2 : ℕ) : ℝ) =
      (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) *
        (((n + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  let x : ℝ := ((n + 2 : ℕ) : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hp : x ^ (3 / 2 : ℝ) = Real.sqrt x * x := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
      Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold routePAnchorWeight
  rw [criticalMellinAtomWeight_eq_div_sqrt]
  change (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) / Real.sqrt x / x =
    (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) * x ^ (-(3 / 2 : ℝ))
  rw [Real.rpow_neg hx.le, hp]
  field_simp [hx.ne', hroot.ne']

private theorem summable_routePAnchorWeight_div_index :
    Summable (fun n : ℕ => routePAnchorWeight n / ((n + 2 : ℕ) : ℝ)) := by
  have hbase := RHTower.summable_vonMangoldt_rpow
    (σ := (3 / 2 : ℝ)) (by norm_num)
  have hshift : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt (n + 2) : ℝ) *
        (((n + 2 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))) :=
    hbase.comp_injective (fun a b h => Nat.add_right_cancel h)
  exact hshift.congr (fun n => (routePAnchorWeight_div_index_eq_vonMangoldt n).symm)

theorem exists_routeP_anchorTail_reciprocalMass_uniform_bound :
    ∃ C : ℝ, ∀ K : ℕ, routePAnchorTailReciprocalMass K ≤ C := by
  have hw2 : 0 < criticalMellinAtomWeight 2 :=
    criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  let g : ℕ → ℝ := fun n =>
    2 * routePAnchorWeight n /
      (criticalMellinAtomWeight 2 * ((n + 2 : ℕ) : ℝ))
  have hsum : Summable g := by
    have h := summable_routePAnchorWeight_div_index.mul_left
      (2 / criticalMellinAtomWeight 2)
    apply h.congr
    intro n
    dsimp [g]
    ring
  let C : ℝ := ∑' n, g n
  refine ⟨C, fun K => ?_⟩
  change (∑ n ∈ routePAnchorTail K, g n) ≤ ∑' n, g n
  apply hsum.sum_le_tsum
  intro n hn
  dsimp [g]
  have hwn : 0 ≤ routePAnchorWeight n :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  positivity

theorem exists_routeP_anchorTailMoment_uniform_graph_bound :
    ∃ C : ℝ, ∀ K : ℕ,
      routePAnchorTailMoment K ^ (2 : ℕ) ≤
        C * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  obtain ⟨C, hC⟩ := exists_routeP_anchorTail_reciprocalMass_uniform_bound
  refine ⟨C, fun K => ?_⟩
  have hD := ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_nonneg K
  calc
    routePAnchorTailMoment K ^ (2 : ℕ) ≤
        ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K *
          routePAnchorTailReciprocalMass K :=
      routeP_anchorTailMoment_sq_le_graph_mul_reciprocalMass K
    _ ≤ C * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
      nlinarith only [hC K, hD]

def routePAnchorFullMoment (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    criticalMellinAtomWeight (n + 2) *
      (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
        ccmActualHeadMatchedQuantilePolarDisplacement 2)

private theorem routeP_quantile_weighted_centroid_sum (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadQuantilePolarCentroid (n + 2)) =
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 +
        2 * ccmActualHeadParabolicMass K := by
  rw [← ccmActualHeadQuantileParabolicAggregate_one_eq_mass_sq_div_two_add_two_mul_mass]
  unfold ccmActualHeadQuantileParabolicAggregate
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change criticalMellinAtomWeight (n + 2) *
      ((ccmActualHeadQuantilePolarCoordinate (n + 2) +
        ccmActualHeadQuantilePolarCoordinate (n + 3)) / 2) =
      (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
        ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) / 2
  rw [← ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
  ring

private theorem routeP_fullAnchorMoment_eq_arithmetic (K : ℕ) :
    routePAnchorFullMoment K =
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 +
        2 * ccmActualHeadParabolicMass K -
        (2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
          ccmActualHeadMatchedCentroidChebyshevExcess K) -
        ccmActualHeadParabolicMass K *
          ccmActualHeadMatchedQuantilePolarDisplacement 2 := by
  unfold routePAnchorFullMoment
  have hsplit :
      (∑ n ∈ Finset.range (K + 1),
        criticalMellinAtomWeight (n + 2) *
          (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement 2)) =
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) *
            ccmActualHeadQuantilePolarCentroid (n + 2)) -
        (∑ n ∈ Finset.range (K + 1),
          criticalMellinAtomWeight (n + 2) *
            ccmActualHeadMatchedPolarCentroid (n + 2)) -
        ccmActualHeadParabolicMass K *
          ccmActualHeadMatchedQuantilePolarDisplacement 2 := by
    rw [← Finset.sum_sub_distrib]
    unfold ccmActualHeadParabolicMass
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement]
    ring
  rw [hsplit, routeP_quantile_weighted_centroid_sum]
  unfold ccmActualHeadMatchedCentroidChebyshevExcess
  ring

theorem routeP_squareDebtArgument_eq_anchorTerminal_sub_moment (K : ℕ) :
    let x : ℝ := ((K + 2 : ℕ) : ℝ)
    let r := Real.sqrt x
    let m := ccmActualHeadParabolicMass K
    2 * (Chebyshev.psi x - x) +
        ccmActualHeadMatchedCentroidChebyshevExcess K - r * (m - 2 * r) =
      m * (2 + m / 2 - r -
        ccmActualHeadMatchedQuantilePolarDisplacement 2) -
        routePAnchorFullMoment K := by
  dsimp only
  have hr : Real.sqrt (((K + 2 : ℕ) : ℝ)) ^ (2 : ℕ) =
      ((K + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [routeP_fullAnchorMoment_eq_arithmetic]
  nlinarith only [hr]

private theorem routeP_fullAnchorMoment_eq_early_add_tail
    {K : ℕ} (hK : 7 ≤ K) :
    routePAnchorFullMoment K =
      routePAnchorFullMoment 6 + routePAnchorTailMoment K := by
  let f : ℕ → ℝ := fun n =>
    criticalMellinAtomWeight (n + 2) *
      (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) -
        ccmActualHeadMatchedQuantilePolarDisplacement 2)
  have hsplit := Finset.sum_range_add_sum_Ico f (show 7 ≤ K + 1 by omega)
  have htailSet : Finset.Ico 7 (K + 1) = routePAnchorTail K := by
    ext n
    simp only [Finset.mem_Ico, routePAnchorTail, Finset.mem_Icc]
    omega
  rw [htailSet] at hsplit
  simpa only [routePAnchorFullMoment, routePAnchorTailMoment,
    routePAnchorTail, routePAnchorWeight, routePAnchorDisplacement, f] using hsplit.symm

theorem exists_routeP_fullAnchorMoment_uniform_graph_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ K : ℕ,
      routePAnchorFullMoment K ^ (2 : ℕ) ≤
        A + B * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  obtain ⟨C, hC⟩ := exists_routeP_anchorTail_reciprocalMass_uniform_bound
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp [routePAnchorTailReciprocalMass, routePAnchorTail] at h
    exact h
  let E : ℝ := routePAnchorFullMoment 6
  let A : ℝ := 2 * E ^ (2 : ℕ) +
    ∑ j ∈ Finset.range 7, routePAnchorFullMoment j ^ (2 : ℕ)
  let B : ℝ := 2 * C
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; linarith
  refine ⟨A, B, hA, hB, fun K => ?_⟩
  by_cases hK : 7 ≤ K
  · have hsplit := routeP_fullAnchorMoment_eq_early_add_tail hK
    have htail := routeP_anchorTailMoment_sq_le_graph_mul_reciprocalMass K
    have hD := ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_nonneg K
    have htail' : routePAnchorTailMoment K ^ (2 : ℕ) ≤
        C * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
      nlinarith only [htail, hC K, hD]
    have hsum0 : 0 ≤
        ∑ j ∈ Finset.range 7, routePAnchorFullMoment j ^ (2 : ℕ) := by
      exact Finset.sum_nonneg fun j hj => sq_nonneg _
    dsimp only [A, B, E]
    rw [hsplit]
    nlinarith only [htail', hsum0,
      sq_nonneg (routePAnchorFullMoment 6 - routePAnchorTailMoment K)]
  · have hK7 : K < 7 := by omega
    have hsingle : routePAnchorFullMoment K ^ (2 : ℕ) ≤
        ∑ j ∈ Finset.range 7, routePAnchorFullMoment j ^ (2 : ℕ) := by
      exact Finset.single_le_sum
        (fun j hj => sq_nonneg (routePAnchorFullMoment j))
        (Finset.mem_range.mpr hK7)
    have hD := ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_nonneg K
    dsimp only [A, B, E]
    nlinarith only [hsingle, hC0, hD, sq_nonneg (routePAnchorFullMoment 6)]

def routePFirstSquareDebtArgument (K : ℕ) : ℝ :=
  let x : ℝ := ((K + 2 : ℕ) : ℝ)
  let r := Real.sqrt x
  let m := ccmActualHeadParabolicMass K
  2 * (Chebyshev.psi x - x) +
    ccmActualHeadMatchedCentroidChebyshevExcess K - r * (m - 2 * r)

def routePAnchorTerminalDebt (K : ℕ) : ℝ :=
  let x : ℝ := ((K + 2 : ℕ) : ℝ)
  let r := Real.sqrt x
  let m := ccmActualHeadParabolicMass K
  m * (2 + m / 2 - r -
    ccmActualHeadMatchedQuantilePolarDisplacement 2)

theorem routeP_firstSquareDebtArgument_eq_terminal_sub_graphMoment (K : ℕ) :
    routePFirstSquareDebtArgument K =
      routePAnchorTerminalDebt K - routePAnchorFullMoment K := by
  exact routeP_squareDebtArgument_eq_anchorTerminal_sub_moment K

theorem exists_routeP_firstSquareDebt_uniform_terminal_graph_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ K : ℕ,
      routePFirstSquareDebtArgument K ^ (2 : ℕ) ≤
        2 * routePAnchorTerminalDebt K ^ (2 : ℕ) +
          A + B * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K := by
  obtain ⟨A, B, hA, hB, hM⟩ :=
    exists_routeP_fullAnchorMoment_uniform_graph_bound
  refine ⟨2 * A, 2 * B, by positivity, by positivity, fun K => ?_⟩
  rw [routeP_firstSquareDebtArgument_eq_terminal_sub_graphMoment]
  have hMK := hM K
  nlinarith only [hMK,
    sq_nonneg (routePAnchorTerminalDebt K + routePAnchorFullMoment K)]

theorem exists_routeP_firstSquareDebt_ratio_one_graph_bound :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ K : ℕ,
      routePFirstSquareDebtArgument K ^ (2 : ℕ) /
          ccmActualHeadParabolicMass K ≤
        (2 * routePAnchorTerminalDebt K ^ (2 : ℕ) + A +
          B * ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K) /
            ccmActualHeadParabolicMass K := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    exists_routeP_firstSquareDebt_uniform_terminal_graph_bound
  refine ⟨A, B, hA, hB, fun K => ?_⟩
  exact div_le_div_of_nonneg_right (hbound K)
    (ccmActualHeadParabolicMass_pos K).le

end

end RHTower
