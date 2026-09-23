import GaloisForLFunctions.RHTower.RouteEDegreeNormalizedGibbsBoundaryVariation

/-!
# Entropy-complement degree-variance bridge

The symmetric physical-incidence route needs reciprocal-degree Dirichlet energy, while sieve and
short-interval inputs naturally estimate ordinary endpoint-count variance.  This file gives the
deterministic missing interface.  Any source-declared reciprocal-degree profile reduces edge
energy to its weighted vertex residual plus its own edge smoothness.  A positive degree profile
with a pointwise fractional lower bound then converts ordinary degree variance into that residual.

No arithmetic estimate, column-load premise, Möbius cancellation premise, or RH premise is used.
-/

namespace RHTower

open scoped BigOperators
open GaloisForLFunctions.RHTower.CoHighPacketGramCollapse

noncomputable section

namespace RouteEWeightedGibbsGraph

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Weighted vertex residual of reciprocal degree from a source-declared profile. -/
def inverseDegreeProfileResidualEnergy
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) : ℝ :=
  ∑ i, G.weight i * G.degree i * (G.inverseDegree i - a i) ^ (2 : ℕ)

/-- Edge Dirichlet energy paid by variation of the declared reciprocal-degree profile. -/
def inverseDegreeProfileDirichletEnergy
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) : ℝ :=
  ∑ p ∈ strictPairs (Finset.univ : Finset ι),
    G.base p.1 p.2 * G.weight p.2 * (a p.1 - a p.2) ^ (2 : ℕ)

theorem inverseDegreeProfileResidualEnergy_nonneg
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) :
    0 ≤ G.inverseDegreeProfileResidualEnergy a := by
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (G.weight_nonneg i) (G.degree_nonneg i)) (sq_nonneg _)

theorem inverseDegreeProfileDirichletEnergy_nonneg
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) :
    0 ≤ G.inverseDegreeProfileDirichletEnergy a := by
  apply Finset.sum_nonneg
  intro p _hp
  exact mul_nonneg
    (mul_nonneg (G.base_nonneg p.1 p.2) (G.weight_nonneg p.2)) (sq_nonneg _)

/-- Weighted vertex variance of reciprocal physical degree around a scalar reference. -/
def inverseDegreeCenteredEnergy (G : RouteEWeightedGibbsGraph ι) (a : ℝ) : ℝ :=
  ∑ i, G.weight i * G.degree i * (G.inverseDegree i - a) ^ (2 : ℕ)

theorem inverseDegreeCenteredEnergy_nonneg
    (G : RouteEWeightedGibbsGraph ι) (a : ℝ) :
    0 ≤ G.inverseDegreeCenteredEnergy a := by
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg
    (mul_nonneg (G.weight_nonneg i) (G.degree_nonneg i)) (sq_nonneg _)

/-- Weighted ordinary degree variance around a positive reference scale. -/
def degreeCenteredEnergy (G : RouteEWeightedGibbsGraph ι) (D : ℝ) : ℝ :=
  ∑ i, G.weight i * (G.degree i - D) ^ (2 : ℕ)

theorem degreeCenteredEnergy_nonneg
    (G : RouteEWeightedGibbsGraph ι) (D : ℝ) :
    0 ≤ G.degreeCenteredEnergy D := by
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (G.weight_nonneg i) (sq_nonneg _)

/-- Vertex variance budget normalized by the cubic degree scale forced by reciprocal degrees. -/
def degreeProfileRelativeVarianceBudget
    (G : RouteEWeightedGibbsGraph ι) (δ : ℝ) (D : ι → ℝ) : ℝ :=
  ∑ i, G.weight i * (G.degree i - D i) ^ (2 : ℕ) * (δ * (D i) ^ (3 : ℕ))⁻¹

private theorem real_sum_product_eq_two_mul_sum_strictPairs_centered
    (F : ι × ι → ℝ) (hsymm : ∀ p, F p.swap = F p)
    (hdiag : ∀ p, p.1 = p.2 → F p = 0) :
    ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p =
      2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
  have h := sum_product_eq_two_mul_sum_strictPairs (Finset.univ : Finset ι)
    (fun p => (F p : ℂ))
    (fun p => by exact_mod_cast hsymm p)
    (fun p hp => by rw [hdiag p hp]; simp)
  exact_mod_cast h

private theorem strict_profileResidualIncidence_eq
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 *
        (G.weight p.1 * (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) +
          G.weight p.2 * (G.inverseDegree p.2 - a p.2) ^ (2 : ℕ))) =
      G.inverseDegreeProfileResidualEnergy a := by
  let r : ι → ℝ := fun i => (G.inverseDegree i - a i) ^ (2 : ℕ)
  let F : ι × ι → ℝ := fun p =>
    G.base p.1 p.2 * (G.weight p.1 * r p.1 + G.weight p.2 * r p.2)
  have hstrict :
      (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p) =
        2 * ∑ p ∈ strictPairs (Finset.univ : Finset ι), F p := by
    apply real_sum_product_eq_two_mul_sum_strictPairs_centered
    · rintro ⟨i, j⟩
      simp only [F, Prod.swap_prod_mk]
      rw [G.base_symm j i]
      ring
    · rintro ⟨i, j⟩ hij
      change i = j at hij
      subst j
      simp [F, G.base_diag]
  have hfull :
      (∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.univ, F p) =
        2 * G.inverseDegreeProfileResidualEnergy a := by
    rw [Finset.sum_product]
    simp only [F, mul_add, Finset.sum_add_distrib]
    have hfirst :
        (∑ i, ∑ j, G.base i j * (G.weight i * r i)) =
          G.inverseDegreeProfileResidualEnergy a := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [degree]
      calc
        (∑ j, G.base i j * (G.weight i * r i)) =
            (∑ j, G.base i j) * (G.weight i * r i) :=
          (Finset.sum_mul _ _ _).symm
        _ = G.weight i * (∑ j, G.base i j) * r i := by ring
        _ = G.weight i * G.degree i * (G.inverseDegree i - a i) ^ (2 : ℕ) := by
          rfl
    have hsecond :
        (∑ i, ∑ j, G.base i j * (G.weight j * r j)) =
          G.inverseDegreeProfileResidualEnergy a := by
      calc
        (∑ i, ∑ j, G.base i j * (G.weight j * r j)) =
            ∑ j, ∑ i, G.base i j * (G.weight j * r j) := Finset.sum_comm
        _ = ∑ j, G.weight j * G.degree j * (G.inverseDegree j - a j) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [degree]
          calc
            (∑ i, G.base i j * (G.weight j * r j)) =
                (∑ i, G.base i j) * (G.weight j * r j) :=
              (Finset.sum_mul _ _ _).symm
            _ = G.weight j * (∑ i, G.base j i) * r j := by
              rw [show (∑ i, G.base i j) = ∑ i, G.base j i by
                apply Finset.sum_congr rfl
                intro i _hi
                exact G.base_symm i j]
              ring
            _ = G.weight j * G.degree j * (G.inverseDegree j - a j) ^ (2 : ℕ) := by
              rfl
        _ = G.inverseDegreeProfileResidualEnergy a := rfl
    rw [hfirst, hsecond]
    ring
  simp only [F, r] at hstrict hfull ⊢
  linarith

private theorem strict_centeredIncidence_eq
    (G : RouteEWeightedGibbsGraph ι) (a : ℝ) :
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 *
        (G.weight p.1 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) +
          G.weight p.2 * (G.inverseDegree p.2 - a) ^ (2 : ℕ))) =
      G.inverseDegreeCenteredEnergy a := by
  simpa [inverseDegreeProfileResidualEnergy, inverseDegreeCenteredEnergy] using
    G.strict_profileResidualIncidence_eq (fun _ => a)

/-- A source-declared reciprocal-degree profile reduces physical edge energy to vertex residual
plus the profile's own edge energy. -/
theorem inverseDegreeDirichletEnergy_le_profileResidual_add_profileEnergy
    (G : RouteEWeightedGibbsGraph ι) (a : ι → ℝ) :
    G.inverseDegreeDirichletEnergy ≤
      3 * G.inverseDegreeProfileResidualEnergy a +
        3 * G.inverseDegreeProfileDirichletEnergy a := by
  rw [inverseDegreeDirichletEnergy]
  calc
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 * G.weight p.2 *
        (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ)) ≤
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          (3 * (G.base p.1 p.2 *
            (G.weight p.1 * (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) +
              G.weight p.2 * (G.inverseDegree p.2 - a p.2) ^ (2 : ℕ))) +
           3 * (G.base p.1 p.2 * G.weight p.2 *
              (a p.1 - a p.2) ^ (2 : ℕ))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hw := G.weight_anti_of_le (le_of_lt (mem_strictPairs.mp hp).2.2)
      have hb := G.base_nonneg p.1 p.2
      have hwp := G.weight_nonneg p.2
      have hs :
          (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ) ≤
            3 * (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) +
              3 * (a p.1 - a p.2) ^ (2 : ℕ) +
                3 * (G.inverseDegree p.2 - a p.2) ^ (2 : ℕ) := by
        nlinarith [
          sq_nonneg ((G.inverseDegree p.1 - a p.1) - (a p.1 - a p.2)),
          sq_nonneg ((G.inverseDegree p.1 - a p.1) +
            (G.inverseDegree p.2 - a p.2)),
          sq_nonneg ((a p.1 - a p.2) +
            (G.inverseDegree p.2 - a p.2))]
      have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg hb hwp)
      have hreplace :
          G.base p.1 p.2 * G.weight p.2 *
              (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) ≤
            G.base p.1 p.2 * G.weight p.1 *
              (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) := by
        gcongr
      calc
        G.base p.1 p.2 * G.weight p.2 *
              (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ) ≤
            G.base p.1 p.2 * G.weight p.2 *
              (3 * (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) +
                3 * (a p.1 - a p.2) ^ (2 : ℕ) +
                  3 * (G.inverseDegree p.2 - a p.2) ^ (2 : ℕ)) := hmul
        _ ≤ 3 * (G.base p.1 p.2 *
              (G.weight p.1 * (G.inverseDegree p.1 - a p.1) ^ (2 : ℕ) +
                G.weight p.2 * (G.inverseDegree p.2 - a p.2) ^ (2 : ℕ))) +
            3 * (G.base p.1 p.2 * G.weight p.2 *
              (a p.1 - a p.2) ^ (2 : ℕ)) := by
          nlinarith
    _ = 3 * G.inverseDegreeProfileResidualEnergy a +
          3 * G.inverseDegreeProfileDirichletEnergy a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        G.strict_profileResidualIncidence_eq a]
      rfl

/-- Any scalar approximation to reciprocal degree controls its edge Dirichlet energy. -/
theorem inverseDegreeDirichletEnergy_le_two_centeredEnergy
    (G : RouteEWeightedGibbsGraph ι) (a : ℝ) :
    G.inverseDegreeDirichletEnergy ≤ 2 * G.inverseDegreeCenteredEnergy a := by
  rw [inverseDegreeDirichletEnergy]
  calc
    (∑ p ∈ strictPairs (Finset.univ : Finset ι),
      G.base p.1 p.2 * G.weight p.2 *
        (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ)) ≤
        ∑ p ∈ strictPairs (Finset.univ : Finset ι),
          2 * (G.base p.1 p.2 *
            (G.weight p.1 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) +
              G.weight p.2 * (G.inverseDegree p.2 - a) ^ (2 : ℕ))) := by
      apply Finset.sum_le_sum
      intro p hp
      have hw := G.weight_anti_of_le (le_of_lt (mem_strictPairs.mp hp).2.2)
      have hb := G.base_nonneg p.1 p.2
      have hwp := G.weight_nonneg p.2
      have hs :
          (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ) ≤
            2 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) +
              2 * (G.inverseDegree p.2 - a) ^ (2 : ℕ) := by
        nlinarith [sq_nonneg
          ((G.inverseDegree p.1 - a) + (G.inverseDegree p.2 - a))]
      have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg hb hwp)
      have hreplace :
          G.base p.1 p.2 * G.weight p.2 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) ≤
            G.base p.1 p.2 * G.weight p.1 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) := by
        gcongr
      calc
        G.base p.1 p.2 * G.weight p.2 *
              (G.inverseDegree p.1 - G.inverseDegree p.2) ^ (2 : ℕ) ≤
            G.base p.1 p.2 * G.weight p.2 *
              (2 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) +
                2 * (G.inverseDegree p.2 - a) ^ (2 : ℕ)) := hmul
        _ ≤ 2 * (G.base p.1 p.2 *
              (G.weight p.1 * (G.inverseDegree p.1 - a) ^ (2 : ℕ) +
                G.weight p.2 * (G.inverseDegree p.2 - a) ^ (2 : ℕ))) := by
          nlinarith
    _ = 2 * G.inverseDegreeCenteredEnergy a := by
      rw [← Finset.mul_sum]
      apply congrArg (2 * ·)
      exact G.strict_centeredIncidence_eq a

/-- If every physical degree is at least a fixed fraction of `D`, ordinary degree variance
controls reciprocal-degree vertex variance. -/
theorem inverseDegreeCenteredEnergy_inv_le_degreeCenteredEnergy
    (G : RouteEWeightedGibbsGraph ι) {δ D : ℝ}
    (hδ : 0 < δ) (hD : 0 < D) (hfloor : ∀ i, δ * D ≤ G.degree i) :
    G.inverseDegreeCenteredEnergy D⁻¹ ≤
      (δ * D ^ (3 : ℕ))⁻¹ * G.degreeCenteredEnergy D := by
  rw [inverseDegreeCenteredEnergy, degreeCenteredEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  have hδD : 0 < δ * D := mul_pos hδ hD
  have hd : 0 < G.degree i := lt_of_lt_of_le hδD (hfloor i)
  have hdenLower : 0 < δ * D ^ (3 : ℕ) := mul_pos hδ (pow_pos hD 3)
  have hdenUpper : 0 < G.degree i * D ^ (2 : ℕ) := mul_pos hd (pow_pos hD 2)
  have hden : δ * D ^ (3 : ℕ) ≤ G.degree i * D ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right (hfloor i) (sq_nonneg D)
    nlinarith
  have hinv : (G.degree i * D ^ (2 : ℕ))⁻¹ ≤ (δ * D ^ (3 : ℕ))⁻¹ := by
    rw [inv_le_inv₀ hdenUpper hdenLower]
    exact hden
  have halgebra :
      G.degree i * (G.inverseDegree i - D⁻¹) ^ (2 : ℕ) =
        (G.degree i - D) ^ (2 : ℕ) * (G.degree i * D ^ (2 : ℕ))⁻¹ := by
    rw [inverseDegree, if_neg hd.ne']
    field_simp
    ring
  rw [show G.weight i * G.degree i * (G.inverseDegree i - D⁻¹) ^ (2 : ℕ) =
    G.weight i * (G.degree i * (G.inverseDegree i - D⁻¹) ^ (2 : ℕ)) by ring, halgebra]
  have hscale := mul_le_mul_of_nonneg_left hinv (sq_nonneg (G.degree i - D))
  have hw := G.weight_nonneg i
  nlinarith [mul_le_mul_of_nonneg_left hscale hw]

/-- Pointwise lower control by a varying positive degree profile converts ordinary degree
variance into the exact reciprocal-degree vertex residual. -/
theorem inverseDegreeProfileResidualEnergy_inv_le_relativeVarianceBudget
    (G : RouteEWeightedGibbsGraph ι) {δ : ℝ} (D : ι → ℝ)
    (hδ : 0 < δ) (hD : ∀ i, 0 < D i)
    (hfloor : ∀ i, δ * D i ≤ G.degree i) :
    G.inverseDegreeProfileResidualEnergy (fun i => (D i)⁻¹) ≤
      G.degreeProfileRelativeVarianceBudget δ D := by
  rw [inverseDegreeProfileResidualEnergy, degreeProfileRelativeVarianceBudget]
  apply Finset.sum_le_sum
  intro i _hi
  have hδD : 0 < δ * D i := mul_pos hδ (hD i)
  have hd : 0 < G.degree i := lt_of_lt_of_le hδD (hfloor i)
  have hdenLower : 0 < δ * (D i) ^ (3 : ℕ) := mul_pos hδ (pow_pos (hD i) 3)
  have hdenUpper : 0 < G.degree i * (D i) ^ (2 : ℕ) :=
    mul_pos hd (pow_pos (hD i) 2)
  have hden : δ * (D i) ^ (3 : ℕ) ≤ G.degree i * (D i) ^ (2 : ℕ) := by
    have hmul := mul_le_mul_of_nonneg_right (hfloor i) (sq_nonneg (D i))
    nlinarith
  have hinv : (G.degree i * (D i) ^ (2 : ℕ))⁻¹ ≤ (δ * (D i) ^ (3 : ℕ))⁻¹ := by
    rw [inv_le_inv₀ hdenUpper hdenLower]
    exact hden
  have halgebra :
      G.degree i * (G.inverseDegree i - (D i)⁻¹) ^ (2 : ℕ) =
        (G.degree i - D i) ^ (2 : ℕ) * (G.degree i * (D i) ^ (2 : ℕ))⁻¹ := by
    rw [inverseDegree, if_neg hd.ne']
    field_simp [hd.ne', (hD i).ne']
    ring
  rw [show G.weight i * G.degree i *
      (G.inverseDegree i - (fun j => (D j)⁻¹) i) ^ (2 : ℕ) =
    G.weight i * (G.degree i * (G.inverseDegree i - (D i)⁻¹) ^ (2 : ℕ)) by ring,
    halgebra]
  have hscale := mul_le_mul_of_nonneg_left hinv (sq_nonneg (G.degree i - D i))
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hscale (G.weight_nonneg i)

/-- Closed deterministic interface: a positive lower degree profile, its relative variance, and
its reciprocal edge smoothness together control the physical inverse-degree energy. -/
theorem inverseDegreeDirichletEnergy_le_relativeVariance_add_profileEnergy
    (G : RouteEWeightedGibbsGraph ι) {δ : ℝ} (D : ι → ℝ)
    (hδ : 0 < δ) (hD : ∀ i, 0 < D i)
    (hfloor : ∀ i, δ * D i ≤ G.degree i) :
    G.inverseDegreeDirichletEnergy ≤
      3 * G.degreeProfileRelativeVarianceBudget δ D +
        3 * G.inverseDegreeProfileDirichletEnergy (fun i => (D i)⁻¹) := by
  calc
    G.inverseDegreeDirichletEnergy ≤
        3 * G.inverseDegreeProfileResidualEnergy (fun i => (D i)⁻¹) +
          3 * G.inverseDegreeProfileDirichletEnergy (fun i => (D i)⁻¹) :=
      G.inverseDegreeDirichletEnergy_le_profileResidual_add_profileEnergy _
    _ ≤ 3 * G.degreeProfileRelativeVarianceBudget δ D +
          3 * G.inverseDegreeProfileDirichletEnergy (fun i => (D i)⁻¹) := by
      gcongr
      exact G.inverseDegreeProfileResidualEnergy_inv_le_relativeVarianceBudget
        D hδ hD hfloor

end RouteEWeightedGibbsGraph

end

end RHTower
