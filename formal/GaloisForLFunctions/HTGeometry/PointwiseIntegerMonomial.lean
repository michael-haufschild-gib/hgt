import GaloisForLFunctions.HTGeometry.PointwiseIntegerGradedIndependence
import GaloisForLFunctions.HTGeometry.IntegerMonomialIndependence

/-!
# Jet monomials with rates that vary from point to point

A companion jet may vanish to different orders at different sample points.  Bundling the rate vector
with the point removes the need for any uniformity: at each point one reads off the rates there, and
the only requirement is that the resulting order form separates the exponents *at that point*.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Jet blow-up data with integer rates chosen at each point, together with separation of the
exponent family by the order form there. -/
def PointwiseIntegerMultiBlowUpData {κ : Type*} {n : ℕ} (S : Set ℂ) (F : Fin n → ℂ → ℂ)
    (Z : Set ℂ) (exponent : κ → (Fin n →₀ ℕ)) : Prop :=
  Z.Infinite ∧ ∀ ζ ∈ Z, ∃ (u t : ℕ → ℂ) (c : Fin n → ℂ) (d : Fin n → ℤ),
    (∀ j, u j ∈ S) ∧ (∀ j, t j ≠ 0) ∧ Tendsto u atTop (𝓝 ζ) ∧ Tendsto t atTop (𝓝 0) ∧
      (∀ k, c k ≠ 0) ∧
      Function.Injective (fun a => integerBlowUpOrder d (exponent a)) ∧
      ∀ k, Tendsto (fun j => F k (u j) * t j ^ (d k)) atTop (𝓝 (c k))

/-- Point-dependent jet rates give a point-dependent integer grading of the monomials. -/
theorem pointwiseIntegerGradedFamily_of_pointwiseIntegerMultiBlowUp {κ : Type*} {n : ℕ}
    {S : Set ℂ} {F : Fin n → ℂ → ℂ} {Z : Set ℂ} {exponent : κ → (Fin n →₀ ℕ)}
    (hdata : PointwiseIntegerMultiBlowUpData S F Z exponent) :
    PointwiseIntegerGradedFamily S
      (fun a w => ∏ k ∈ (exponent a).support, (F k w) ^ (exponent a k)) Z := by
  obtain ⟨hZ, hblow⟩ := hdata
  refine ⟨hZ, ?_⟩
  intro ζ hζ
  obtain ⟨u, t, c, d, humem, htne, hu, ht, hcne, hinj, hlim⟩ := hblow ζ hζ
  refine ⟨u, t, fun a => ∏ k ∈ (exponent a).support, (c k) ^ (exponent a k),
    fun a => integerBlowUpOrder d (exponent a), humem, htne, hu, ht, hinj, ?_, ?_⟩
  · intro a
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcne k)
  · intro a
    have hprod := tendsto_finsetProd (M := ℂ) (exponent a).support
      (f := fun k j => (F k (u j) * t j ^ (d k)) ^ (exponent a k))
      (a := fun k => (c k) ^ (exponent a k)) (fun k _ => (hlim k).pow _)
    refine hprod.congr fun j => ?_
    exact prod_mul_zpow_eq_prod_mul_zpow_order d (exponent a) (fun k => F k (u j)) (htne j)

/-- **The expanded monomial box, with point-dependent integer jet rates.** -/
theorem linearIndependent_restrict_expandedMonomialFamily_of_pointwiseIntegerMultiBlowUp
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n q : ℕ} {S : Set ℂ} {F : Fin n → ℂ → ℂ}
    {Z : Set ℂ} {exponent : κ → (Fin n →₀ ℕ)}
    (hdata : PointwiseIntegerMultiBlowUpData S F Z exponent) :
    LinearIndependent ℂ
      (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c)) := by
  have hgen := linearIndependent_restrict_degreeBox_of_pointwiseIntegerGraded (q := q)
    (pointwiseIntegerGradedFamily_of_pointwiseIntegerMultiBlowUp hdata)
  have hfam : (fun c : κ × Fin (q + 1) => Set.restrict S (expandedMonomialFamily F exponent q c))
      = (fun p : κ × Fin (q + 1) => Set.restrict S
          (fun w => w ^ (p.2 : ℕ) * ∏ k ∈ (exponent p.1).support, (F k w) ^ (exponent p.1 k))) := by
    funext p x
    exact expandedMonomialFamily_apply F exponent p (x : ℂ)
  rw [hfam]
  exact hgen

end GaloisForLFunctions.HTGeometry
