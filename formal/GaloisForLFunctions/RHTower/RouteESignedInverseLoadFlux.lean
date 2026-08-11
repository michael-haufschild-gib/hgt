import GaloisForLFunctions.RHTower.RouteEDegreeNormalizedGibbsBoundaryVariation

/-!
# Route E exact signed inverse-load flux

Pairing both orientations of every live parity-reversing edge splits the signed Gibbs current into
isolated mass, a co-moving Gibbs increment, and a signed inverse-load flux.  The last term is
therefore exactly circular: controlling it is equivalent to controlling the current after the two
explicit terms are removed.
-/

namespace RHTower

open scoped BigOperators
open GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

noncomputable section

private theorem routeERealSumProduct_eq_two_mul_sum_strictPairs
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι × ι → ℝ) (hsymm : ∀ p, F p.swap = F p)
    (hdiag : ∀ p, p.1 = p.2 → F p = 0) :
    ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p =
      2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
  have h := sum_product_eq_two_mul_sum_strictPairs (Finset.univ : Finset ι)
    (fun p => (F p : ℂ))
    (fun p => by exact_mod_cast hsymm p)
    (fun p hp => by rw [hdiag p hp]; simp)
  exact_mod_cast h

private theorem routeESumProduct_eq_sum_strictPairs_add_swap
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (F : ι × ι → ℝ) (hdiag : ∀ i, F (i, i) = 0) :
    ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p =
      ∑ p ∈ strictPairs (Finset.univ : Finset ι), (F p + F p.swap) := by
  let S : ι × ι → ℝ := fun p => F p + F p.swap
  have hsymm : ∀ p, S p.swap = S p := by
    rintro ⟨i, j⟩
    simp only [S, Prod.swap_prod_mk]
    ring
  have hdiagS : ∀ p, p.1 = p.2 → S p = 0 := by
    rintro ⟨i, j⟩ hij
    subst j
    simp [S, hdiag]
  have hstrict := routeERealSumProduct_eq_two_mul_sum_strictPairs S hsymm hdiagS
  have hfull :
      (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, S p) =
        2 * ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p := by
    rw [Finset.sum_product, Finset.sum_product]
    simp only [S]
    rw [Finset.sum_add_distrib]
    simp_rw [Finset.sum_add_distrib]
    have hswap : (∑ i : ι, ∑ j : ι, F (j, i)) = ∑ i : ι, ∑ j : ι, F (i, j) :=
      Finset.sum_comm
    rw [hswap]
    ring
  change (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p) =
    ∑ p ∈ strictPairs (Finset.univ : Finset ι), S p
  linarith

namespace RouteEWeightedGibbsGraph

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Signed Gibbs mass on weighted-isolated vertices. -/
def signedIsolatedCurrent (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ i, G.sign i * G.isolatedResidual i

/-- Signed co-moving Gibbs increment over physically oriented edges. -/
def signedCoMovingFlux (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    G.base p.1 p.2 * G.sign p.1 * (G.weight p.1 - G.weight p.2) *
      G.inverseDegree p.1

/-- Signed inverse-load edge flux over physically oriented edges. -/
def signedInverseLoadFlux (G : RouteEWeightedGibbsGraph ι) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    G.base p.1 p.2 * G.sign p.1 * G.weight p.2 *
      (G.inverseDegree p.1 - G.inverseDegree p.2)

private theorem signedNormalizedWeight_pair
    (G : RouteEWeightedGibbsGraph ι) (i j : ι) :
    G.sign i * G.base i j * G.normalizedWeight i +
        G.sign j * G.base j i * G.normalizedWeight j =
      G.base i j * G.sign i * (G.weight i - G.weight j) * G.inverseDegree i +
        G.base i j * G.sign i * G.weight j *
          (G.inverseDegree i - G.inverseDegree j) := by
  by_cases hij : G.base i j = 0
  · simp [hij, G.base_symm j i]
  · have hflip := G.base_flip i j hij
    have hsign : G.sign j = -G.sign i := by linarith
    rw [G.base_symm j i, hsign]
    unfold normalizedWeight
    ring

/-- **Exact signed inverse-load flux identity.** -/
theorem signedCurrent_eq_signedIsolated_add_signedCoMoving_add_signedInverseLoadFlux
    (G : RouteEWeightedGibbsGraph ι) :
    G.signedCurrent = G.signedIsolatedCurrent + G.signedCoMovingFlux +
      G.signedInverseLoadFlux := by
  classical
  let F : ι × ι → ℝ := fun p =>
    G.sign p.1 * G.base p.1 p.2 * G.normalizedWeight p.1
  have hpoint : ∀ i,
      G.sign i * G.weight i = G.sign i * G.isolatedResidual i + ∑ j, F (i, j) := by
    intro i
    rw [G.weight_eq_isolatedResidual_add_degree_mul_normalizedWeight i]
    unfold F RouteEWeightedGibbsGraph.degree
    rw [Finset.sum_mul, Finset.mul_sum]
    ring
  have hdiag : ∀ i, F (i, i) = 0 := by
    intro i
    simp [F, G.base_diag]
  have hpair := routeESumProduct_eq_sum_strictPairs_add_swap F hdiag
  unfold signedCurrent signedIsolatedCurrent signedCoMovingFlux signedInverseLoadFlux
  calc
    (∑ i, G.sign i * G.weight i) =
        ∑ i, (G.sign i * G.isolatedResidual i + ∑ j, F (i, j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hpoint i
    _ = (∑ i, G.sign i * G.isolatedResidual i) + ∑ i, ∑ j, F (i, j) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, G.sign i * G.isolatedResidual i) +
        ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p := by
      rw [Finset.sum_product]
    _ = (∑ i, G.sign i * G.isolatedResidual i) +
        ∑ p ∈ strictPairs (Finset.univ : Finset ι), (F p + F p.swap) := by
      rw [hpair]
    _ = (∑ i, G.sign i * G.isolatedResidual i) +
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          (G.base p.1 p.2 * G.sign p.1 * (G.weight p.1 - G.weight p.2) *
              G.inverseDegree p.1 +
            G.base p.1 p.2 * G.sign p.1 * G.weight p.2 *
              (G.inverseDegree p.1 - G.inverseDegree p.2)) := by
      apply congrArg (fun z => (∑ i, G.sign i * G.isolatedResidual i) + z)
      apply Finset.sum_congr rfl
      intro p _hp
      simpa [F, mul_comm, mul_left_comm, mul_assoc] using
        G.signedNormalizedWeight_pair p.1 p.2
    _ = (∑ i, G.sign i * G.isolatedResidual i) +
        (∑ p ∈ strictPairs (Finset.univ : Finset ι),
          G.base p.1 p.2 * G.sign p.1 * (G.weight p.1 - G.weight p.2) *
            G.inverseDegree p.1) +
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          G.base p.1 p.2 * G.sign p.1 * G.weight p.2 *
            (G.inverseDegree p.1 - G.inverseDegree p.2) := by
      rw [Finset.sum_add_distrib]
      ring

/-- Signed co-moving flux costs at most the sharp physical displacement budget. -/
theorem abs_signedCoMovingFlux_le_laplace_mul_displacement_mul_totalWeight
    (G : RouteEWeightedGibbsGraph ι) :
    |G.signedCoMovingFlux| ≤ G.laplace * G.displacement * G.totalWeight := by
  unfold signedCoMovingFlux
  calc
    |∑ p ∈ strictPairs (Finset.univ : Finset ι),
        G.base p.1 p.2 * G.sign p.1 * (G.weight p.1 - G.weight p.2) *
          G.inverseDegree p.1| ≤
      ∑ p ∈ strictPairs (Finset.univ : Finset ι),
        |G.base p.1 p.2 * G.sign p.1 * (G.weight p.1 - G.weight p.2) *
          G.inverseDegree p.1| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ strictPairs (Finset.univ : Finset ι),
        G.base p.1 p.2 * (G.weight p.1 - G.weight p.2) * G.inverseDegree p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hweight : 0 ≤ G.weight p.1 - G.weight p.2 := sub_nonneg.mpr <|
        G.weight_anti_of_le (le_of_lt (mem_strictPairs.mp hp).2.2)
      rw [abs_mul, abs_mul, abs_mul, G.sign_abs_one,
        abs_of_nonneg (G.base_nonneg p.1 p.2), abs_of_nonneg hweight,
        abs_of_nonneg (G.inverseDegree_nonneg p.1)]
      ring
    _ ≤ G.laplace * G.displacement * G.totalWeight := G.coMovingVariation_le

/-- **Circularity firewall.**  A bound on complete signed inverse-load flux is literally the same
bound on current after removing isolated and co-moving terms. -/
theorem abs_signedInverseLoadFlux_le_iff_current_remainder
    (G : RouteEWeightedGibbsGraph ι) (eta : ℝ) :
    |G.signedInverseLoadFlux| ≤ eta ↔
      |G.signedCurrent - G.signedIsolatedCurrent - G.signedCoMovingFlux| ≤ eta := by
  rw [G.signedCurrent_eq_signedIsolated_add_signedCoMoving_add_signedInverseLoadFlux]
  ring_nf

theorem signedCoMovingFlux_eq_zero_of_laplace_eq_zero
    (G : RouteEWeightedGibbsGraph ι) (h : G.laplace = 0) :
    G.signedCoMovingFlux = 0 := by
  classical
  unfold signedCoMovingFlux weight
  apply Finset.sum_eq_zero
  intro p _hp
  simp [h]

/-- At zero Gibbs parameter the signed inverse-load flux is exactly current minus isolated mass. -/
theorem signedInverseLoadFlux_eq_current_sub_isolated_of_laplace_eq_zero
    (G : RouteEWeightedGibbsGraph ι) (h : G.laplace = 0) :
    G.signedInverseLoadFlux = G.signedCurrent - G.signedIsolatedCurrent := by
  have hmain := G.signedCurrent_eq_signedIsolated_add_signedCoMoving_add_signedInverseLoadFlux
  rw [G.signedCoMovingFlux_eq_zero_of_laplace_eq_zero h] at hmain
  linarith

end RouteEWeightedGibbsGraph

end

end RHTower
