import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport
import GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

/-!
# Route E degree-normalized Gibbs boundary-variation law

Exact finite formalization of
`route-e-degree-normalized-gibbs-boundary-variation-law.md`.  The carrier is a finite ordered
physical aperture.  A symmetric nonnegative base incidence flips the sign and moves physical
coordinate by at most `H`.  Its canonical minimum-endpoint conductance converts signed Gibbs
current into isolated mass, the sharp co-moving exponential cost, and reciprocal-degree edge
variation.  The recurrence-kernel specialization and its Dirichlet bridge appear below.
-/

namespace RHTower

open scoped BigOperators
open GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

noncomputable section

/-- Finite physical weighted graph used by the Gibbs boundary-variation law.  Strict monotonicity
of `coordinate` makes the type order the physical order, without identifying vertices after a
quotient. -/
structure RouteEWeightedGibbsGraph (ι : Type*) [Fintype ι] [LinearOrder ι] where
  coordinate : ι → ℝ
  sign : ι → ℝ
  base : ι → ι → ℝ
  laplace : ℝ
  displacement : ℝ
  coordinate_strictMono : StrictMono coordinate
  sign_abs_one : ∀ i, |sign i| = 1
  base_nonneg : ∀ i j, 0 ≤ base i j
  base_symm : ∀ i j, base i j = base j i
  base_diag : ∀ i, base i i = 0
  base_flip : ∀ i j, base i j ≠ 0 → sign i + sign j = 0
  base_displacement : ∀ i j, base i j ≠ 0 → |coordinate i - coordinate j| ≤ displacement
  laplace_nonneg : 0 ≤ laplace
  displacement_nonneg : 0 ≤ displacement

namespace RouteEWeightedGibbsGraph

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Gibbs weight at a physical vertex. -/
def weight (G : RouteEWeightedGibbsGraph ι) (i : ι) : ℝ :=
  Real.exp (-(G.coordinate i * G.laplace))

/-- Total Gibbs mass. -/
def totalWeight (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ i, G.weight i

/-- Signed Gibbs current. -/
def signedCurrent (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ i, G.sign i * G.weight i

/-- Weighted incidence degree. -/
def degree (G : RouteEWeightedGibbsGraph ι) (i : ι) : ℝ :=
  ∑ j, G.base i j

/-- Reciprocal weighted degree, zero exactly on weighted-isolated vertices. -/
def inverseDegree (G : RouteEWeightedGibbsGraph ι) (i : ι) : ℝ :=
  if G.degree i = 0 then 0 else (G.degree i)⁻¹

/-- Degree-normalized Gibbs density. -/
def normalizedWeight (G : RouteEWeightedGibbsGraph ι) (i : ι) : ℝ :=
  G.weight i * G.inverseDegree i

/-- Explicit Gibbs residual at weighted-isolated vertices. -/
def isolatedResidual (G : RouteEWeightedGibbsGraph ι) (i : ι) : ℝ :=
  if G.degree i = 0 then G.weight i else 0

/-- Canonical symmetric minimum-endpoint conductance. -/
def conductance (G : RouteEWeightedGibbsGraph ι) (i j : ι) : ℝ :=
  G.base i j * min (G.normalizedWeight i) (G.normalizedWeight j)

/-- Positive reciprocal-degree edge variation, with the larger physical endpoint carrying the
Gibbs weight. -/
def inverseDegreeVariation (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    G.base p.1 p.2 * G.weight p.2 * |G.inverseDegree p.1 - G.inverseDegree p.2|

/-- Edge Dirichlet energy of inverse weighted degree. -/
def inverseDegreeDirichletEnergy (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    G.base p.1 p.2 * G.weight p.2 *
      (G.inverseDegree p.1 - G.inverseDegree p.2) ^ 2

theorem weight_pos (G : RouteEWeightedGibbsGraph ι) (i : ι) : 0 < G.weight i :=
  Real.exp_pos _

theorem weight_nonneg (G : RouteEWeightedGibbsGraph ι) (i : ι) : 0 ≤ G.weight i :=
  (G.weight_pos i).le

theorem degree_nonneg (G : RouteEWeightedGibbsGraph ι) (i : ι) : 0 ≤ G.degree i :=
  Finset.sum_nonneg fun j _hj => G.base_nonneg i j

theorem degree_pos_of_base_ne_zero (G : RouteEWeightedGibbsGraph ι) {i j : ι}
    (hij : G.base i j ≠ 0) : 0 < G.degree i := by
  have hbij : 0 < G.base i j := lt_of_le_of_ne (G.base_nonneg i j) (Ne.symm hij)
  have hle : G.base i j ≤ ∑ k, G.base i k := by
    exact Finset.single_le_sum (fun k _hk => G.base_nonneg i k) (Finset.mem_univ j)
  exact lt_of_lt_of_le hbij hle

theorem inverseDegree_nonneg (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    0 ≤ G.inverseDegree i := by
  rw [inverseDegree]
  split_ifs with hi
  · exact le_rfl
  · exact inv_nonneg.mpr (G.degree_nonneg i)

theorem normalizedWeight_nonneg (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    0 ≤ G.normalizedWeight i :=
  mul_nonneg (G.weight_nonneg i) (G.inverseDegree_nonneg i)

theorem isolatedResidual_nonneg (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    0 ≤ G.isolatedResidual i := by
  rw [isolatedResidual]
  split_ifs
  · exact G.weight_nonneg i
  · exact le_rfl

theorem degree_mul_inverseDegree (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    G.degree i * G.inverseDegree i = if G.degree i = 0 then 0 else 1 := by
  rw [inverseDegree]
  split_ifs with hi
  · simp [hi]
  · exact mul_inv_cancel₀ hi

theorem degree_mul_inverseDegree_le_one (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    G.degree i * G.inverseDegree i ≤ 1 := by
  rw [G.degree_mul_inverseDegree]
  split_ifs <;> norm_num

theorem weight_eq_isolatedResidual_add_degree_mul_normalizedWeight
    (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    G.weight i = G.isolatedResidual i + G.degree i * G.normalizedWeight i := by
  rw [isolatedResidual, normalizedWeight, inverseDegree]
  split_ifs with hi
  · simp [hi]
  · field_simp
    ring

theorem conductance_nonneg (G : RouteEWeightedGibbsGraph ι) (i j : ι) :
    0 ≤ G.conductance i j :=
  mul_nonneg (G.base_nonneg i j)
    (le_min (G.normalizedWeight_nonneg i) (G.normalizedWeight_nonneg j))

theorem conductance_symm (G : RouteEWeightedGibbsGraph ι) (i j : ι) :
    G.conductance i j = G.conductance j i := by
  simp only [conductance, G.base_symm i j, min_comm]

theorem conductance_flip (G : RouteEWeightedGibbsGraph ι) (i j : ι)
    (hij : G.conductance i j ≠ 0) : G.sign i + G.sign j = 0 := by
  apply G.base_flip i j
  intro hb
  exact hij (by simp [conductance, hb])

theorem sum_conductance_le_weight (G : RouteEWeightedGibbsGraph ι) (i : ι) :
    ∑ j, G.conductance i j ≤ G.weight i := by
  calc
    ∑ j, G.conductance i j ≤ ∑ j, G.base i j * G.normalizedWeight i :=
      Finset.sum_le_sum fun j _hj =>
        mul_le_mul_of_nonneg_left (min_le_left _ _) (G.base_nonneg i j)
    _ = G.degree i * G.normalizedWeight i := by rw [degree, Finset.sum_mul]
    _ ≤ G.isolatedResidual i + G.degree i * G.normalizedWeight i := by
      linarith [G.isolatedResidual_nonneg i]
    _ = G.weight i := (G.weight_eq_isolatedResidual_add_degree_mul_normalizedWeight i).symm

private theorem real_sum_product_eq_two_mul_sum_strictPairs
    (F : ι × ι → ℝ) (hsymm : ∀ p, F p.swap = F p)
    (hdiag : ∀ p, p.1 = p.2 → F p = 0) :
    ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p =
      2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
  have h := sum_product_eq_two_mul_sum_strictPairs (Finset.univ : Finset ι)
    (fun p => (F p : ℂ))
    (fun p => by exact_mod_cast hsymm p)
    (fun p hp => by rw [hdiag p hp]; simp)
  exact_mod_cast h

private theorem pair_directedDefect
    (G : RouteEWeightedGibbsGraph ι) (i j : ι) :
    G.base i j *
          (G.normalizedWeight i - min (G.normalizedWeight i) (G.normalizedWeight j)) +
        G.base j i *
          (G.normalizedWeight j - min (G.normalizedWeight j) (G.normalizedWeight i)) =
      G.base i j * |G.normalizedWeight i - G.normalizedWeight j| := by
  rw [G.base_symm j i, min_comm (G.normalizedWeight j) (G.normalizedWeight i)]
  rcases le_total (G.normalizedWeight i) (G.normalizedWeight j) with hij | hji
  · rw [min_eq_left hij, abs_of_nonpos (sub_nonpos.mpr hij)]
    ring
  · rw [min_eq_right hji, abs_of_nonneg (sub_nonneg.mpr hji)]
    ring

/-- Exact weighted analogue of pairing two orientations of every edge: total unused canonical
conductance is isolated Gibbs mass plus unordered normalized-weight total variation. -/
theorem sum_unusedConductance_eq_isolated_add_edgeVariation
    (G : RouteEWeightedGibbsGraph ι) :
    (∑ i, (G.weight i - ∑ j, G.conductance i j)) =
      (∑ i, G.isolatedResidual i) +
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          G.base p.1 p.2 * |G.normalizedWeight p.1 - G.normalizedWeight p.2| := by
  classical
  let D : ι → ι → ℝ := fun i j =>
    G.base i j *
      (G.normalizedWeight i - min (G.normalizedWeight i) (G.normalizedWeight j))
  have hdirected :
      (∑ i, (G.weight i - ∑ j, G.conductance i j)) =
        (∑ i, G.isolatedResidual i) + ∑ i, ∑ j, D i j := by
    calc
      (∑ i, (G.weight i - ∑ j, G.conductance i j)) =
          ∑ i, (G.isolatedResidual i + ∑ j, D i j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [G.weight_eq_isolatedResidual_add_degree_mul_normalizedWeight i]
        simp only [conductance, D, degree]
        rw [show (∑ x, G.base i x *
              (G.normalizedWeight i - min (G.normalizedWeight i) (G.normalizedWeight x))) =
            (∑ x, G.base i x) * G.normalizedWeight i -
              ∑ x, G.base i x * min (G.normalizedWeight i) (G.normalizedWeight x) by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, Finset.sum_mul]]
        ring
      _ = (∑ i, G.isolatedResidual i) + ∑ i, ∑ j, D i j := by
        rw [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, D j i) = ∑ i, ∑ j, D i j := Finset.sum_comm
  let F : ι × ι → ℝ := fun p =>
    G.base p.1 p.2 * |G.normalizedWeight p.1 - G.normalizedWeight p.2|
  have hfullF : (∑ i, ∑ j, F (i, j)) = 2 * ∑ i, ∑ j, D i j := by
    calc
      (∑ i, ∑ j, F (i, j)) = ∑ i, ∑ j, (D i j + D j i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        exact (G.pair_directedDefect i j).symm
      _ = (∑ i, ∑ j, D i j) + ∑ i, ∑ j, D j i := by
        simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ i, ∑ j, D i j := by rw [hswap]; ring
  have hstrictF :
      (∑ i, ∑ j, F (i, j)) =
        2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
    rw [← Finset.sum_product]
    apply real_sum_product_eq_two_mul_sum_strictPairs
    · intro p
      rcases p with ⟨i, j⟩
      simp only [F, Prod.swap_prod_mk]
      rw [G.base_symm j i, abs_sub_comm]
    · intro p hp
      simp [F, hp]
  rw [hdirected]
  congr 1
  linarith

/-- Canonical weighted total-variation consumer before the Gibbs/co-moving split. -/
theorem abs_signedCurrent_le_isolated_add_edgeVariation
    (G : RouteEWeightedGibbsGraph ι) :
    |G.signedCurrent| ≤
      (∑ i, G.isolatedResidual i) +
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          G.base p.1 p.2 * |G.normalizedWeight p.1 - G.normalizedWeight p.2| := by
  classical
  have h := abs_sum_sign_weight_le_unusedConductance
    G.sign G.weight G.conductance G.sign_abs_one G.conductance_symm
      G.conductance_flip G.sum_conductance_le_weight
  rw [G.sum_unusedConductance_eq_isolated_add_edgeVariation] at h
  exact h

theorem coordinate_lt_of_mem_strictPairs (G : RouteEWeightedGibbsGraph ι)
    {p : ι × ι} (hp : p ∈ strictPairs (Finset.univ : Finset ι)) :
    G.coordinate p.1 < G.coordinate p.2 :=
  G.coordinate_strictMono (mem_strictPairs.mp hp).2.2

theorem weight_anti_of_le (G : RouteEWeightedGibbsGraph ι) {i j : ι} (hij : i ≤ j) :
    G.weight j ≤ G.weight i := by
  rw [weight, weight]
  apply Real.exp_le_exp.mpr
  have hc := G.coordinate_strictMono.monotone hij
  nlinarith [G.laplace_nonneg]

private theorem normalizedWeight_pair_fracture
    (G : RouteEWeightedGibbsGraph ι) {i j : ι} (hij : i ≤ j) :
    |G.normalizedWeight i - G.normalizedWeight j| ≤
      (G.weight i - G.weight j) * G.inverseDegree i +
        G.weight j * |G.inverseDegree i - G.inverseDegree j| := by
  have hw : G.weight j ≤ G.weight i := G.weight_anti_of_le hij
  have hfirst : 0 ≤ (G.weight i - G.weight j) * G.inverseDegree i :=
    mul_nonneg (sub_nonneg.mpr hw) (G.inverseDegree_nonneg i)
  calc
    |G.normalizedWeight i - G.normalizedWeight j| =
        |(G.weight i - G.weight j) * G.inverseDegree i +
          G.weight j * (G.inverseDegree i - G.inverseDegree j)| := by
            congr 1
            simp only [normalizedWeight]
            ring
    _ ≤ |(G.weight i - G.weight j) * G.inverseDegree i| +
          |G.weight j * (G.inverseDegree i - G.inverseDegree j)| := abs_add_le _ _
    _ = (G.weight i - G.weight j) * G.inverseDegree i +
          G.weight j * |G.inverseDegree i - G.inverseDegree j| := by
            rw [abs_of_nonneg hfirst, abs_mul, abs_of_nonneg (G.weight_nonneg j)]

private theorem coMoving_pair_le
    (G : RouteEWeightedGibbsGraph ι) {p : ι × ι}
    (hp : p ∈ strictPairs (Finset.univ : Finset ι)) :
    G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1 ≤
      G.laplace * G.displacement *
        (G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1) := by
  by_cases hb : G.base p.1 p.2 = 0
  · simp [hb]
  · have hc : G.coordinate p.1 < G.coordinate p.2 := G.coordinate_lt_of_mem_strictPairs hp
    have hw : G.weight p.2 ≤ G.weight p.1 := G.weight_anti_of_le (le_of_lt (mem_strictPairs.mp hp).2.2)
    have htransport := abs_exp_neg_mul_sub_exp_neg_mul_le_transportCost
      (u := G.coordinate p.1) (v := G.coordinate p.2) G.laplace_nonneg
    have hspan := G.base_displacement p.1 p.2 hb
    have hdiff : G.weight p.1 - G.weight p.2 ≤
        G.laplace * G.displacement * G.weight p.1 := by
      have habsCoord : |G.coordinate p.1 - G.coordinate p.2| =
          G.coordinate p.2 - G.coordinate p.1 :=
        by
          rw [abs_of_nonpos (sub_nonpos.mpr hc.le)]
          ring
      have hmin : min (G.coordinate p.1) (G.coordinate p.2) = G.coordinate p.1 :=
        min_eq_left hc.le
      rw [habsCoord, hmin] at htransport
      rw [habsCoord] at hspan
      change |G.weight p.1 - G.weight p.2| ≤
        G.laplace * (G.coordinate p.2 - G.coordinate p.1) * G.weight p.1 at htransport
      rw [abs_of_nonneg (sub_nonneg.mpr hw)] at htransport
      simp only [weight]
      have hxspan :
          G.laplace * (G.coordinate p.2 - G.coordinate p.1) *
              Real.exp (-(G.coordinate p.1 * G.laplace)) ≤
            G.laplace * G.displacement *
              Real.exp (-(G.coordinate p.1 * G.laplace)) := by
        gcongr
        exact G.laplace_nonneg
      exact le_trans htransport hxspan
    have hfactor : 0 ≤ G.base p.1 p.2 * G.inverseDegree p.1 :=
      mul_nonneg (G.base_nonneg p.1 p.2) (G.inverseDegree_nonneg p.1)
    have := mul_le_mul_of_nonneg_right hdiff hfactor
    nlinarith

private theorem strict_incidence_le_totalWeight (G : RouteEWeightedGibbsGraph ι) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
        G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1) ≤ G.totalWeight := by
  classical
  calc
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
        G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1) ≤
        ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ,
          G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p _hp _hnot
      exact mul_nonneg
        (mul_nonneg (G.base_nonneg p.1 p.2) (G.weight_nonneg p.1))
        (G.inverseDegree_nonneg p.1)
    _ = ∑ i, G.degree i * (G.weight i * G.inverseDegree i) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [degree]
      calc
        (∑ y, G.base i y * G.weight i * G.inverseDegree i) =
            ∑ y, G.base i y * (G.weight i * G.inverseDegree i) := by
          apply Finset.sum_congr rfl
          intro j _hj
          ring
        _ = (∑ y, G.base i y) * (G.weight i * G.inverseDegree i) :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ i, G.weight i := by
      apply Finset.sum_le_sum
      intro i _hi
      have hq := G.degree_mul_inverseDegree_le_one i
      have hmul := mul_le_mul_of_nonneg_left hq (G.weight_nonneg i)
      nlinarith
    _ = G.totalWeight := rfl

private theorem coMovingVariation_le (G : RouteEWeightedGibbsGraph ι) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1) ≤
        G.laplace * G.displacement * G.totalWeight := by
  calc
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1) ≤
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          G.laplace * G.displacement *
            (G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1) :=
      Finset.sum_le_sum fun p hp => G.coMoving_pair_le hp
    _ = G.laplace * G.displacement *
          ∑ p ∈ strictPairs (Finset.univ : Finset ι),
            G.base p.1 p.2 * G.weight p.1 * G.inverseDegree p.1 := by
      rw [Finset.mul_sum]
    _ ≤ G.laplace * G.displacement * G.totalWeight :=
      mul_le_mul_of_nonneg_left G.strict_incidence_le_totalWeight
        (mul_nonneg G.laplace_nonneg G.displacement_nonneg)

private theorem normalizedEdgeVariation_le_coMoving_add_inverseDegreeVariation
    (G : RouteEWeightedGibbsGraph ι) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 * |G.normalizedWeight p.1 - G.normalizedWeight p.2|) ≤
      (∑ p ∈ strictPairs (Finset.univ : Finset ι),
        G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1) +
        G.inverseDegreeVariation := by
  rw [inverseDegreeVariation, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpair := G.normalizedWeight_pair_fracture
    (le_of_lt (mem_strictPairs.mp hp).2.2)
  have hb := G.base_nonneg p.1 p.2
  have := mul_le_mul_of_nonneg_left hpair hb
  nlinarith

/-- **Weighted Gibbs fracture.** Signed current is bounded by weighted-isolated Gibbs mass, sharp
co-moving displacement, and reciprocal weighted-degree variation.  This is Theorem D of the
paper; the simple-degree law is its unit-base specialization. -/
theorem abs_signedCurrent_le_isolated_add_coMoving_add_inverseDegreeVariation
    (G : RouteEWeightedGibbsGraph ι) :
    |G.signedCurrent| ≤
      (∑ i, G.isolatedResidual i) +
        G.laplace * G.displacement * G.totalWeight + G.inverseDegreeVariation := by
  calc
    |G.signedCurrent| ≤
        (∑ i, G.isolatedResidual i) +
          ∑ p ∈ strictPairs (Finset.univ : Finset ι),
            G.base p.1 p.2 * |G.normalizedWeight p.1 - G.normalizedWeight p.2| :=
      G.abs_signedCurrent_le_isolated_add_edgeVariation
    _ ≤ (∑ i, G.isolatedResidual i) +
          ((∑ p ∈ strictPairs (Finset.univ : Finset ι),
            G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1) +
              G.inverseDegreeVariation) := by
        gcongr
        exact G.normalizedEdgeVariation_le_coMoving_add_inverseDegreeVariation
    _ ≤ (∑ i, G.isolatedResidual i) +
          G.laplace * G.displacement * G.totalWeight + G.inverseDegreeVariation := by
        linarith [G.coMovingVariation_le]

end RouteEWeightedGibbsGraph

/-! ## Recurrence-weighted specialization -/

/-- Source-predeclared substochastic opposite-sign recurrence kernel on one finite physical
aperture. -/
structure RouteERecurrenceKernel (ι : Type*) [Fintype ι] [LinearOrder ι] where
  coordinate : ι → ℝ
  sign : ι → ℝ
  transition : ι → ι → ℝ
  laplace : ℝ
  displacement : ℝ
  coordinate_strictMono : StrictMono coordinate
  sign_abs_one : ∀ i, |sign i| = 1
  transition_nonneg : ∀ i j, 0 ≤ transition i j
  row_substochastic : ∀ i, ∑ j, transition i j ≤ 1
  parity_reversing : ∀ i j, transition i j ≠ 0 → sign i + sign j = 0
  transition_displacement :
    ∀ i j, transition i j ≠ 0 → |coordinate i - coordinate j| ≤ displacement
  laplace_nonneg : 0 ≤ laplace
  displacement_nonneg : 0 ≤ displacement

namespace RouteERecurrenceKernel

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Outgoing row mass. -/
def rowMass (K : RouteERecurrenceKernel ι) (i : ι) : ℝ :=
  ∑ j, K.transition i j

/-- Incoming column load. -/
def columnLoad (K : RouteERecurrenceKernel ι) (i : ι) : ℝ :=
  ∑ j, K.transition j i

/-- Symmetrized recurrence incidence. -/
def symmetricBase (K : RouteERecurrenceKernel ι) (i j : ι) : ℝ :=
  (K.transition i j + K.transition j i) / 2

theorem rowMass_nonneg (K : RouteERecurrenceKernel ι) (i : ι) : 0 ≤ K.rowMass i :=
  Finset.sum_nonneg fun j _hj => K.transition_nonneg i j

theorem columnLoad_nonneg (K : RouteERecurrenceKernel ι) (i : ι) : 0 ≤ K.columnLoad i :=
  Finset.sum_nonneg fun j _hj => K.transition_nonneg j i

theorem transition_diag (K : RouteERecurrenceKernel ι) (i : ι) : K.transition i i = 0 := by
  by_contra hii
  have hflip := K.parity_reversing i i hii
  have hsign : K.sign i = 0 := by linarith
  have habs := K.sign_abs_one i
  rw [hsign, abs_zero] at habs
  norm_num at habs

theorem symmetricBase_nonneg (K : RouteERecurrenceKernel ι) (i j : ι) :
    0 ≤ K.symmetricBase i j := by
  exact div_nonneg
    (add_nonneg (K.transition_nonneg i j) (K.transition_nonneg j i)) (by norm_num)

theorem symmetricBase_symm (K : RouteERecurrenceKernel ι) (i j : ι) :
    K.symmetricBase i j = K.symmetricBase j i := by
  simp only [symmetricBase]
  ring

theorem symmetricBase_diag (K : RouteERecurrenceKernel ι) (i : ι) :
    K.symmetricBase i i = 0 := by
  simp [symmetricBase, K.transition_diag i]

private theorem transition_ne_zero_of_symmetricBase_ne_zero
    (K : RouteERecurrenceKernel ι) {i j : ι} (hij : K.symmetricBase i j ≠ 0) :
    K.transition i j ≠ 0 ∨ K.transition j i ≠ 0 := by
  by_contra h
  push Not at h
  exact hij (by simp [symmetricBase, h.1, h.2])

theorem symmetricBase_flip (K : RouteERecurrenceKernel ι) (i j : ι)
    (hij : K.symmetricBase i j ≠ 0) : K.sign i + K.sign j = 0 := by
  rcases K.transition_ne_zero_of_symmetricBase_ne_zero hij with h | h
  · exact K.parity_reversing i j h
  · nlinarith [K.parity_reversing j i h]

theorem symmetricBase_displacement (K : RouteERecurrenceKernel ι) (i j : ι)
    (hij : K.symmetricBase i j ≠ 0) :
    |K.coordinate i - K.coordinate j| ≤ K.displacement := by
  rcases K.transition_ne_zero_of_symmetricBase_ne_zero hij with h | h
  · exact K.transition_displacement i j h
  · simpa [abs_sub_comm] using K.transition_displacement j i h

/-- Symmetric weighted graph canonically associated to a directed recurrence kernel. -/
def toWeightedGibbsGraph (K : RouteERecurrenceKernel ι) : RouteEWeightedGibbsGraph ι where
  coordinate := K.coordinate
  sign := K.sign
  base := K.symmetricBase
  laplace := K.laplace
  displacement := K.displacement
  coordinate_strictMono := K.coordinate_strictMono
  sign_abs_one := K.sign_abs_one
  base_nonneg := K.symmetricBase_nonneg
  base_symm := K.symmetricBase_symm
  base_diag := K.symmetricBase_diag
  base_flip := K.symmetricBase_flip
  base_displacement := K.symmetricBase_displacement
  laplace_nonneg := K.laplace_nonneg
  displacement_nonneg := K.displacement_nonneg

@[simp]
theorem toWeightedGibbsGraph_weight (K : RouteERecurrenceKernel ι) (i : ι) :
    K.toWeightedGibbsGraph.weight i = Real.exp (-(K.coordinate i * K.laplace)) := rfl

@[simp]
theorem toWeightedGibbsGraph_laplace (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.laplace = K.laplace := rfl

@[simp]
theorem toWeightedGibbsGraph_displacement (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.displacement = K.displacement := rfl

@[simp]
theorem toWeightedGibbsGraph_totalWeight (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.totalWeight =
      ∑ i, Real.exp (-(K.coordinate i * K.laplace)) := rfl

@[simp]
theorem toWeightedGibbsGraph_signedCurrent (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.signedCurrent =
      ∑ i, K.sign i * Real.exp (-(K.coordinate i * K.laplace)) := rfl

/-- Symmetric weighted degree is exactly half of outgoing plus incoming recurrence load. -/
theorem toWeightedGibbsGraph_degree (K : RouteERecurrenceKernel ι) (i : ι) :
    K.toWeightedGibbsGraph.degree i = (K.rowMass i + K.columnLoad i) / 2 := by
  simp only [RouteEWeightedGibbsGraph.degree, toWeightedGibbsGraph, symmetricBase,
    rowMass, columnLoad]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- The paper's inverse incidence load `q=2/(row+column)` is exactly reciprocal symmetric degree,
including the zero-incidence convention. -/
theorem toWeightedGibbsGraph_inverseDegree (K : RouteERecurrenceKernel ι) (i : ι) :
    K.toWeightedGibbsGraph.inverseDegree i =
      if K.rowMass i + K.columnLoad i = 0 then 0 else 2 / (K.rowMass i + K.columnLoad i) := by
  rw [RouteEWeightedGibbsGraph.inverseDegree, K.toWeightedGibbsGraph_degree]
  by_cases h : K.rowMass i + K.columnLoad i = 0
  · simp [h]
  · simp [h]

/-- Smaller-endpoint edge mass used by the Dirichlet Cauchy bridge. -/
def edgeWeightBudget (K : RouteERecurrenceKernel ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2

theorem edgeWeightBudget_nonneg (K : RouteERecurrenceKernel ι) :
    0 ≤ K.edgeWeightBudget :=
  Finset.sum_nonneg fun p _hp => mul_nonneg
    (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
    (K.toWeightedGibbsGraph.weight_nonneg p.2)

theorem inverseDegreeDirichletEnergy_nonneg (K : RouteERecurrenceKernel ι) :
    0 ≤ K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy :=
  Finset.sum_nonneg fun p _hp => by
    exact mul_nonneg
      (mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
        (K.toWeightedGibbsGraph.weight_nonneg p.2)) (sq_nonneg _)

/-- Exact finite Cauchy--Schwarz bridge from reciprocal-degree BV to inverse-load Dirichlet
energy. -/
theorem inverseDegreeVariation_sq_le_budget_mul_dirichletEnergy
    (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.inverseDegreeVariation ^ 2 ≤
      K.edgeWeightBudget * K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy := by
  let s := strictPairs (Finset.univ : Finset ι)
  let e : ι × ι → ℝ := fun p =>
    K.toWeightedGibbsGraph.base p.1 p.2 * K.toWeightedGibbsGraph.weight p.2
  let d : ι × ι → ℝ := fun p =>
    |K.toWeightedGibbsGraph.inverseDegree p.1 -
      K.toWeightedGibbsGraph.inverseDegree p.2|
  have he : ∀ p, 0 ≤ e p := fun p => mul_nonneg
    (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
    (K.toWeightedGibbsGraph.weight_nonneg p.2)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun p => Real.sqrt (e p)) (fun p => d p * Real.sqrt (e p))
  have hprod : ∀ p, Real.sqrt (e p) * (d p * Real.sqrt (e p)) = e p * d p := by
    intro p
    have hsqrt := Real.mul_self_sqrt (he p)
    calc
      Real.sqrt (e p) * (d p * Real.sqrt (e p)) =
          d p * (Real.sqrt (e p) * Real.sqrt (e p)) := by ring
      _ = e p * d p := by rw [hsqrt]; ring
  have hsq1 : ∀ p, Real.sqrt (e p) ^ 2 = e p := fun p => Real.sq_sqrt (he p)
  have hsq2 : ∀ p, (d p * Real.sqrt (e p)) ^ 2 =
      e p * (K.toWeightedGibbsGraph.inverseDegree p.1 -
        K.toWeightedGibbsGraph.inverseDegree p.2) ^ 2 := by
    intro p
    rw [mul_pow, hsq1]
    simp only [d, sq_abs]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hprod p),
    Finset.sum_congr rfl (fun p _ => hsq1 p),
    Finset.sum_congr rfl (fun p _ => hsq2 p)] at hcs
  simpa [s, e, d, edgeWeightBudget,
    RouteEWeightedGibbsGraph.inverseDegreeVariation,
    RouteEWeightedGibbsGraph.inverseDegreeDirichletEnergy, mul_assoc, mul_left_comm,
    mul_comm] using hcs

private theorem strict_symmetricWeight_eq_sum_weight_mul_degree
    (K : RouteERecurrenceKernel ι) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      K.toWeightedGibbsGraph.base p.1 p.2 *
        (K.toWeightedGibbsGraph.weight p.1 + K.toWeightedGibbsGraph.weight p.2)) =
      ∑ i, K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i := by
  let G := K.toWeightedGibbsGraph
  let F : ι × ι → ℝ := fun p => G.base p.1 p.2 * (G.weight p.1 + G.weight p.2)
  have hstrict :
      (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p) =
        2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
    apply RouteEWeightedGibbsGraph.real_sum_product_eq_two_mul_sum_strictPairs
    · intro p
      rcases p with ⟨i, j⟩
      simp only [F, Prod.swap_prod_mk]
      rw [G.base_symm j i]
      ring
    · intro p hp
      simp [F, hp, G.base_diag]
  have hfull :
      (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p) =
        2 * ∑ i, G.weight i * G.degree i := by
    rw [Finset.sum_product]
    simp only [F]
    have hfirst : (∑ i, ∑ j, G.base i j * G.weight i) =
        ∑ i, G.weight i * G.degree i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [RouteEWeightedGibbsGraph.degree]
      calc
        (∑ j, G.base i j * G.weight i) = (∑ j, G.base i j) * G.weight i :=
          (Finset.sum_mul _ _ _).symm
        _ = G.weight i * ∑ j, G.base i j := by ring
    have hsecond : (∑ i, ∑ j, G.base i j * G.weight j) =
        ∑ i, G.weight i * G.degree i := by
      calc
        (∑ i, ∑ j, G.base i j * G.weight j) =
            ∑ j, ∑ i, G.base i j * G.weight j := Finset.sum_comm
        _ = ∑ j, G.weight j * G.degree j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [RouteEWeightedGibbsGraph.degree]
          calc
            (∑ i, G.base i j * G.weight j) = (∑ i, G.base i j) * G.weight j :=
              (Finset.sum_mul _ _ _).symm
            _ = G.weight j * ∑ i, G.base j i := by
              rw [show (∑ i, G.base i j) = ∑ i, G.base j i by
                apply Finset.sum_congr rfl
                intro i _hi
                exact G.base_symm i j]
              ring
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  simp only [G, F] at hstrict hfull ⊢
  linarith

theorem edgeWeightBudget_le_half_sum_weight_mul_degree (K : RouteERecurrenceKernel ι) :
    K.edgeWeightBudget ≤
      (1 / 2 : ℝ) * ∑ i,
        K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i := by
  calc
    K.edgeWeightBudget ≤
        (1 / 2 : ℝ) *
          ∑ p ∈ strictPairs (Finset.univ : Finset ι),
            K.toWeightedGibbsGraph.base p.1 p.2 *
              (K.toWeightedGibbsGraph.weight p.1 + K.toWeightedGibbsGraph.weight p.2) := by
      rw [edgeWeightBudget, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hw := K.toWeightedGibbsGraph.weight_anti_of_le
        (le_of_lt (mem_strictPairs.mp hp).2.2)
      have hb := K.toWeightedGibbsGraph.base_nonneg p.1 p.2
      nlinarith
    _ = (1 / 2 : ℝ) * ∑ i,
          K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i := by
      rw [K.strict_symmetricWeight_eq_sum_weight_mul_degree]

private theorem transition_weight_le_exp_displacement_mul
    (K : RouteERecurrenceKernel ι) (i j : ι) :
    K.toWeightedGibbsGraph.weight j * K.transition i j ≤
      Real.exp (K.laplace * K.displacement) *
        K.toWeightedGibbsGraph.weight i * K.transition i j := by
  by_cases hij : K.transition i j = 0
  · simp [hij]
  · have hspan := K.transition_displacement i j hij
    have hd : K.coordinate i - K.coordinate j ≤ K.displacement :=
      le_trans (le_abs_self _) hspan
    have hmul := mul_le_mul_of_nonneg_left hd K.laplace_nonneg
    have hweight : K.toWeightedGibbsGraph.weight j ≤
        Real.exp (K.laplace * K.displacement) * K.toWeightedGibbsGraph.weight i := by
      simp only [toWeightedGibbsGraph_weight]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    exact mul_le_mul_of_nonneg_right hweight (K.transition_nonneg i j)

theorem weightedColumnLoad_le_exp_displacement_mul_weightedRowMass
    (K : RouteERecurrenceKernel ι) :
    (∑ i, K.toWeightedGibbsGraph.weight i * K.columnLoad i) ≤
      Real.exp (K.laplace * K.displacement) *
        ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i := by
  calc
    (∑ i, K.toWeightedGibbsGraph.weight i * K.columnLoad i) =
        ∑ i, ∑ j, K.toWeightedGibbsGraph.weight i * K.transition j i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [columnLoad, Finset.mul_sum]
    _ =
        ∑ j, ∑ i, K.toWeightedGibbsGraph.weight i * K.transition j i := Finset.sum_comm
    _ ≤ ∑ j, ∑ i, Real.exp (K.laplace * K.displacement) *
          K.toWeightedGibbsGraph.weight j * K.transition j i :=
      Finset.sum_le_sum fun j _hj =>
        Finset.sum_le_sum fun i _hi => K.transition_weight_le_exp_displacement_mul j i
    _ = Real.exp (K.laplace * K.displacement) *
          ∑ j, K.toWeightedGibbsGraph.weight j * K.rowMass j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      calc
        (∑ i, Real.exp (K.laplace * K.displacement) *
            K.toWeightedGibbsGraph.weight j * K.transition j i) =
            ∑ i, Real.exp (K.laplace * K.displacement) *
              (K.toWeightedGibbsGraph.weight j * K.transition j i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = Real.exp (K.laplace * K.displacement) *
            ∑ i, K.toWeightedGibbsGraph.weight j * K.transition j i :=
          (Finset.mul_sum _ _ _).symm
        _ = Real.exp (K.laplace * K.displacement) *
            (K.toWeightedGibbsGraph.weight j * K.rowMass j) := by
          rw [rowMass]
          congr 1
          rw [Finset.mul_sum]

theorem weightedRowMass_le_totalWeight (K : RouteERecurrenceKernel ι) :
    (∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) ≤
      K.toWeightedGibbsGraph.totalWeight := by
  rw [RouteEWeightedGibbsGraph.totalWeight]
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_of_le_one_right (K.toWeightedGibbsGraph.weight_nonneg i)
    (K.row_substochastic i)

/-- The exact edge-mass budget responsible for the factor `1/2` in the recurrence-weighted
Dirichlet bridge. -/
theorem edgeWeightBudget_le_quarter_one_add_exp_mul_totalWeight
    (K : RouteERecurrenceKernel ι) :
    K.edgeWeightBudget ≤
      (1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement)) *
        K.toWeightedGibbsGraph.totalWeight := by
  have hdegree :
      (∑ i, K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i) =
        (1 / 2 : ℝ) *
          ((∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) +
            ∑ i, K.toWeightedGibbsGraph.weight i * K.columnLoad i) := by
    calc
      (∑ i, K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i) =
          ∑ i, ((1 / 2 : ℝ) *
            (K.toWeightedGibbsGraph.weight i * K.rowMass i) +
            (1 / 2 : ℝ) *
              (K.toWeightedGibbsGraph.weight i * K.columnLoad i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [K.toWeightedGibbsGraph_degree]
        ring
      _ = (1 / 2 : ℝ) *
          ((∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) +
            ∑ i, K.toWeightedGibbsGraph.weight i * K.columnLoad i) := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hcolumn := K.weightedColumnLoad_le_exp_displacement_mul_weightedRowMass
  have hrow := K.weightedRowMass_le_totalWeight
  have hexp : 0 ≤ Real.exp (K.laplace * K.displacement) := (Real.exp_pos _).le
  calc
    K.edgeWeightBudget ≤
        (1 / 2 : ℝ) * ∑ i,
          K.toWeightedGibbsGraph.weight i * K.toWeightedGibbsGraph.degree i :=
      K.edgeWeightBudget_le_half_sum_weight_mul_degree
    _ = (1 / 4 : ℝ) *
          ((∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) +
            ∑ i, K.toWeightedGibbsGraph.weight i * K.columnLoad i) := by
      rw [hdegree]
      ring
    _ ≤ (1 / 4 : ℝ) *
          ((∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) +
            Real.exp (K.laplace * K.displacement) *
              ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) := by
      gcongr
    _ ≤ (1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement)) *
          K.toWeightedGibbsGraph.totalWeight := by
      have hfactor :
          (∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) +
              Real.exp (K.laplace * K.displacement) *
                ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i =
            (1 + Real.exp (K.laplace * K.displacement)) *
              ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i := by ring
      rw [hfactor]
      calc
        (1 / 4 : ℝ) *
            ((1 + Real.exp (K.laplace * K.displacement)) *
              ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i) =
            ((1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement))) *
              ∑ i, K.toWeightedGibbsGraph.weight i * K.rowMass i := by ring
        _ ≤ ((1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement))) *
              K.toWeightedGibbsGraph.totalWeight :=
          mul_le_mul_of_nonneg_left hrow
            (mul_nonneg (by norm_num) (add_nonneg zero_le_one hexp))
        _ = (1 / 4 : ℝ) * (1 + Real.exp (K.laplace * K.displacement)) *
              K.toWeightedGibbsGraph.totalWeight := by ring

/-- BV-to-Dirichlet estimate with the sharp paper constant. -/
theorem inverseDegreeVariation_le_half_sqrt_dirichletBudget
    (K : RouteERecurrenceKernel ι) :
    K.toWeightedGibbsGraph.inverseDegreeVariation ≤
      (1 / 2 : ℝ) * Real.sqrt
        ((1 + Real.exp (K.laplace * K.displacement)) *
          K.toWeightedGibbsGraph.totalWeight *
            K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy) := by
  have hsq := K.inverseDegreeVariation_sq_le_budget_mul_dirichletEnergy
  have hbudget := K.edgeWeightBudget_le_quarter_one_add_exp_mul_totalWeight
  have henergy := K.inverseDegreeDirichletEnergy_nonneg
  have hmul := mul_le_mul_of_nonneg_right hbudget henergy
  have hchain := le_trans hsq hmul
  have hvar : 0 ≤ K.toWeightedGibbsGraph.inverseDegreeVariation :=
    Finset.sum_nonneg fun p _hp => by
      exact mul_nonneg
        (mul_nonneg (K.toWeightedGibbsGraph.base_nonneg p.1 p.2)
          (K.toWeightedGibbsGraph.weight_nonneg p.2)) (abs_nonneg _)
  have harg : 0 ≤
      (1 + Real.exp (K.laplace * K.displacement)) *
        K.toWeightedGibbsGraph.totalWeight *
          K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy := by
    exact mul_nonneg
      (mul_nonneg (add_nonneg zero_le_one (Real.exp_pos _).le)
        (Finset.sum_nonneg fun i _ => K.toWeightedGibbsGraph.weight_nonneg i)) henergy
  have hsqrt := Real.sq_sqrt harg
  have hsqrtnn := Real.sqrt_nonneg
    ((1 + Real.exp (K.laplace * K.displacement)) *
      K.toWeightedGibbsGraph.totalWeight *
        K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy)
  nlinarith

/-- **Recurrence-weighted Dirichlet bridge.** This is Theorem E and inequality (20) of the paper,
with the actual substochastic recurrence weights, finite signs, Gibbs factors, and physical
displacement retained. -/
theorem abs_signedCurrent_le_recurrenceDirichletBridge
    (K : RouteERecurrenceKernel ι) :
    |K.toWeightedGibbsGraph.signedCurrent| ≤
      (∑ i, K.toWeightedGibbsGraph.isolatedResidual i) +
        K.laplace * K.displacement * K.toWeightedGibbsGraph.totalWeight +
          (1 / 2 : ℝ) * Real.sqrt
            ((1 + Real.exp (K.laplace * K.displacement)) *
              K.toWeightedGibbsGraph.totalWeight *
                K.toWeightedGibbsGraph.inverseDegreeDirichletEnergy) := by
  have hmain :=
    K.toWeightedGibbsGraph.abs_signedCurrent_le_isolated_add_coMoving_add_inverseDegreeVariation
  have hvariation := K.inverseDegreeVariation_le_half_sqrt_dirichletBudget
  exact le_trans hmain (by
    simpa [add_assoc, add_comm, add_left_comm] using
      add_le_add_left hvariation
        ((∑ i, K.toWeightedGibbsGraph.isolatedResidual i) +
          K.laplace * K.displacement * K.toWeightedGibbsGraph.totalWeight))

end RouteERecurrenceKernel

/-! ## Sharpness and the one-sign firewall -/

/-- Complete-bipartite saturation of reciprocal-degree variation.  With unit vertex weights,
every left degree is `|β|`, every right degree is `|α|`, and edge BV is exactly signed cardinal
imbalance. -/
theorem completeBipartite_reciprocalDegreeVariation_eq_signedImbalance
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (∑ _i : α, ∑ _j : β,
      |(1 : ℝ) / Fintype.card β - (1 : ℝ) / Fintype.card α|) =
        |(Fintype.card α : ℝ) - Fintype.card β| := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by positivity
  have hα0 : 0 ≤ (Fintype.card α : ℝ) := Nat.cast_nonneg _
  have hβ0 : 0 ≤ (Fintype.card β : ℝ) := Nat.cast_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (Fintype.card α : ℝ) *
          ((Fintype.card β : ℝ) *
            |(1 : ℝ) / Fintype.card β - (1 : ℝ) / Fintype.card α|) =
        |(Fintype.card α : ℝ)| *
          (|(Fintype.card β : ℝ)| *
            |(1 : ℝ) / Fintype.card β - (1 : ℝ) / Fintype.card α|) := by
      rw [abs_of_nonneg hα0, abs_of_nonneg hβ0]
    _ = |(Fintype.card α : ℝ) *
          ((Fintype.card β : ℝ) *
            ((1 : ℝ) / Fintype.card β - (1 : ℝ) / Fintype.card α))| := by
      rw [abs_mul, abs_mul]
    _ = |(Fintype.card α : ℝ) - Fintype.card β| := by
      congr 1
      field_simp

/-- One-sign source-to-target recurrence data. -/
structure RouteEOneSidedKernel (S T : Type*) [Fintype S] [Fintype T] where
  sourceCoordinate : S → ℝ
  targetCoordinate : T → ℝ
  transition : S → T → ℝ
  laplace : ℝ
  displacement : ℝ
  transition_nonneg : ∀ s t, 0 ≤ transition s t
  row_stochastic : ∀ s, ∑ t, transition s t = 1
  transition_displacement : ∀ s t, transition s t ≠ 0 →
    |sourceCoordinate s - targetCoordinate t| ≤ displacement
  laplace_nonneg : 0 ≤ laplace
  displacement_nonneg : 0 ≤ displacement

namespace RouteEOneSidedKernel

variable {S T : Type*} [Fintype S] [Fintype T]

def columnLoad (K : RouteEOneSidedKernel S T) (t : T) : ℝ :=
  ∑ s, K.transition s t

def inverseColumnLoad (K : RouteEOneSidedKernel S T) (t : T) : ℝ :=
  if K.columnLoad t = 0 then 0 else (K.columnLoad t)⁻¹

def coMovingEdgeWeight (K : RouteEOneSidedKernel S T) (s : S) (t : T) : ℝ :=
  Real.exp (-(K.laplace * max (K.sourceCoordinate s) (K.targetCoordinate t)))

def weightedIncoming (K : RouteEOneSidedKernel S T) (t : T) : ℝ :=
  ∑ s, K.transition s t * K.coMovingEdgeWeight s t

/-- Co-moving target weight `ω_t`. -/
def coMovingTargetWeight (K : RouteEOneSidedKernel S T) (t : T) : ℝ :=
  if K.columnLoad t = 0 then 0 else K.weightedIncoming t / K.columnLoad t

/-- One-sign specialization of inverse-incidence Dirichlet energy. -/
def oneSidedDirichletEnergy (K : RouteEOneSidedKernel S T) : ℝ :=
  ∑ t, ∑ s,
    (K.transition s t / 2) * K.coMovingEdgeWeight s t *
      (2 - 2 * K.inverseColumnLoad t) ^ 2

theorem columnLoad_nonneg (K : RouteEOneSidedKernel S T) (t : T) :
    0 ≤ K.columnLoad t :=
  Finset.sum_nonneg fun s _hs => K.transition_nonneg s t

theorem transition_eq_zero_of_columnLoad_eq_zero
    (K : RouteEOneSidedKernel S T) {s : S} {t : T} (ht : K.columnLoad t = 0) :
    K.transition s t = 0 := by
  have hle : K.transition s t ≤ K.columnLoad t := by
    exact Finset.single_le_sum (fun u _hu => K.transition_nonneg u t) (Finset.mem_univ s)
  linarith [K.transition_nonneg s t]

/-- Exact co-moving reverse Pearson identity. -/
theorem oneSidedDirichletEnergy_eq_coMovingReverseChiSquare
    (K : RouteEOneSidedKernel S T) :
    K.oneSidedDirichletEnergy =
      2 * ∑ t,
        if K.columnLoad t = 0 then 0
        else K.coMovingTargetWeight t * (K.columnLoad t - 1) ^ 2 / K.columnLoad t := by
  rw [oneSidedDirichletEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases hload : K.columnLoad t = 0
  · simp only [hload, if_pos, inverseColumnLoad, coMovingTargetWeight]
    simp_rw [K.transition_eq_zero_of_columnLoad_eq_zero hload]
    simp
  · have hloadPos : 0 < K.columnLoad t :=
      lt_of_le_of_ne (K.columnLoad_nonneg t) (Ne.symm hload)
    simp only [hload, if_false, inverseColumnLoad, coMovingTargetWeight]
    rw [show (∑ s, K.transition s t / 2 * K.coMovingEdgeWeight s t *
          (2 - 2 * (K.columnLoad t)⁻¹) ^ 2) =
        ((2 - 2 * (K.columnLoad t)⁻¹) ^ 2 / 2) * K.weightedIncoming t by
      rw [weightedIncoming]
      calc
        (∑ s, K.transition s t / 2 * K.coMovingEdgeWeight s t *
            (2 - 2 * (K.columnLoad t)⁻¹) ^ 2) =
            ∑ s, ((2 - 2 * (K.columnLoad t)⁻¹) ^ 2 / 2) *
              (K.transition s t * K.coMovingEdgeWeight s t) := by
          apply Finset.sum_congr rfl
          intro s _hs
          ring
        _ = ((2 - 2 * (K.columnLoad t)⁻¹) ^ 2 / 2) *
            ∑ s, K.transition s t * K.coMovingEdgeWeight s t :=
          (Finset.mul_sum _ _ _).symm]
    field_simp

theorem coMovingTargetWeight_nonneg (K : RouteEOneSidedKernel S T) (t : T) :
    0 ≤ K.coMovingTargetWeight t := by
  rw [coMovingTargetWeight]
  split_ifs with ht
  · exact le_rfl
  · exact div_nonneg
      (Finset.sum_nonneg fun s _hs => mul_nonneg (K.transition_nonneg s t)
        (Real.exp_pos _).le) (K.columnLoad_nonneg t)

private theorem coMovingEdgeWeight_le_targetWeight
    (K : RouteEOneSidedKernel S T) (s : S) (t : T) :
    K.coMovingEdgeWeight s t ≤ Real.exp (-(K.laplace * K.targetCoordinate t)) := by
  rw [coMovingEdgeWeight]
  apply Real.exp_le_exp.mpr
  have hmax : K.targetCoordinate t ≤ max (K.sourceCoordinate s) (K.targetCoordinate t) :=
    le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hmax K.laplace_nonneg
  nlinarith

private theorem lowerTargetWeight_le_coMovingEdgeWeight_of_transition_ne_zero
    (K : RouteEOneSidedKernel S T) {s : S} {t : T} (hst : K.transition s t ≠ 0) :
    Real.exp (-(K.laplace * K.displacement)) *
        Real.exp (-(K.laplace * K.targetCoordinate t)) ≤ K.coMovingEdgeWeight s t := by
  have hspan := K.transition_displacement s t hst
  have hsource : K.sourceCoordinate s ≤ K.targetCoordinate t + K.displacement := by
    have := le_trans (le_abs_self (K.sourceCoordinate s - K.targetCoordinate t)) hspan
    linarith
  have hmax : max (K.sourceCoordinate s) (K.targetCoordinate t) ≤
      K.targetCoordinate t + K.displacement :=
    max_le hsource (by linarith [K.displacement_nonneg])
  rw [coMovingEdgeWeight, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hmax K.laplace_nonneg
  nlinarith

/-- Co-moving target weight differs from literal target Gibbs weight by at most the sharp
displacement factor. -/
theorem coMovingTargetWeight_bounds (K : RouteEOneSidedKernel S T) (t : T) :
    K.columnLoad t ≠ 0 →
      Real.exp (-(K.laplace * K.displacement)) *
          Real.exp (-(K.laplace * K.targetCoordinate t)) ≤ K.coMovingTargetWeight t ∧
        K.coMovingTargetWeight t ≤ Real.exp (-(K.laplace * K.targetCoordinate t)) := by
  intro hload
  have hloadPos : 0 < K.columnLoad t :=
    lt_of_le_of_ne (K.columnLoad_nonneg t) (Ne.symm hload)
  have hupper : K.weightedIncoming t ≤
      K.columnLoad t * Real.exp (-(K.laplace * K.targetCoordinate t)) := by
    rw [weightedIncoming, columnLoad, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _hs
    exact mul_le_mul_of_nonneg_left (K.coMovingEdgeWeight_le_targetWeight s t)
      (K.transition_nonneg s t)
  have hlower :
      K.columnLoad t *
          (Real.exp (-(K.laplace * K.displacement)) *
            Real.exp (-(K.laplace * K.targetCoordinate t))) ≤ K.weightedIncoming t := by
    rw [weightedIncoming, columnLoad, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro s _hs
    by_cases hst : K.transition s t = 0
    · simp [hst]
    · exact mul_le_mul_of_nonneg_left
        (K.lowerTargetWeight_le_coMovingEdgeWeight_of_transition_ne_zero hst)
        (K.transition_nonneg s t)
  rw [coMovingTargetWeight, if_neg hload]
  constructor
  · exact (le_div_iff₀ hloadPos).2 (by nlinarith)
  · exact (div_le_iff₀ hloadPos).2 (by simpa [mul_comm] using hupper)

end RouteEOneSidedKernel

end

end RHTower
