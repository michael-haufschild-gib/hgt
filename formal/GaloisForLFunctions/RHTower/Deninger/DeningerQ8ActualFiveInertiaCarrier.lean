import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualOddInertiaCyclic
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualMonomialSourceLaw

/-!
# The actual five-adic inertia is the source-selected quartic carrier

The literal `√41` coordinate selects the `C₄` subgroup inducing the documented
two-dimensional Artin representation. At every top prime over `5`, actual
inertia is exactly this subgroup. The inclusion is coefficient-faithful: an
inertial automorphism negating `√41` would move the integral source coordinate
`(1 + √41) / 2` by an element whose square is `41`; residue triviality would
then force `5 ∣ 41`. Exact order four upgrades the inclusion to equality.
-/

namespace RHTower

open scoped NumberField Pointwise
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8FiveCarrierCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance q8FiveCarrierFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8FiveCarrierFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8FiveCarrierFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8FiveCarrierFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8FiveCarrierFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance q8FiveCarrierNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8FiveCarrierIsGaloisRatK3 : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- At every top prime over `5`, actual inertia lies in the literal `C₄`
carrier selected by `√41`. -/
theorem q8Actual_five_inertia_le_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    P.inertia Gal(K3/ℚ) ≤ deningerQ8ActualCyclicSubgroup := by
  intro g hg
  rw [deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY]
  change (g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY =
    deningerQ8RootNumberNegOneTopY
  rcases hq : deningerQ8RootNumberNegOne_galoisEquivQ8 (g : Gal(K3/ℚ)) with i | i
  · rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply
      (g : Gal(K3/ℚ)), hq]
    change q8IAlgPow i deningerQ8RootNumberNegOneTopY =
      deningerQ8RootNumberNegOneTopY
    exact q8IAlgPow_topY _
  · exfalso
    have hy : (g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY =
        -deningerQ8RootNumberNegOneTopY := by
      rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply
        (g : Gal(K3/ℚ)), hq]
      change q8JAlgEquiv (q8IAlgPow i deningerQ8RootNumberNegOneTopY) =
        -deningerQ8RootNumberNegOneTopY
      rw [q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY]
    let v : 𝓞 K3 := q8LiteralTwoAdicV
    have hgv : (g : Gal(K3/ℚ)) • v = 1 - v := by
      apply Subtype.ext
      change (g : Gal(K3/ℚ)) q8LiteralTwoAdicVField =
        1 - q8LiteralTwoAdicVField
      rw [q8LiteralTwoAdicVField]
      rw [map_div₀, map_add, map_one, hy]
      have htwoMap : (g : Gal(K3/ℚ)) (2 : K3) = 2 := map_ofNat _ 2
      rw [htwoMap]
      field_simp
      ring
    have hdiff : (1 - v) - v ∈ P := by
      rw [← hgv]
      exact hg v
    have hsquare : ((1 - v) - v) ^ (2 : ℕ) = (41 : 𝓞 K3) := by
      calc
        ((1 - v) - v) ^ (2 : ℕ) = 1 - 4 * v + 4 * v ^ (2 : ℕ) := by ring
        _ = 41 := by rw [q8LiteralTwoAdicV_sq]; ring
    have h41 : (41 : 𝓞 K3) ∈ P := by
      rw [← hsquare, pow_two]
      exact P.mul_mem_left _ hdiff
    have h41base : (41 : ℤ) ∈ Ideal.span {(5 : ℤ)} := by
      rw [hPover.over]
      exact h41
    norm_num [Ideal.mem_span_singleton] at h41base

/-- At every top prime over `5`, actual inertia is literally the global
source-selected `C₄` carrier of the monomial Artin representation. -/
theorem q8Actual_five_inertia_eq_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    P.inertia Gal(K3/ℚ) = deningerQ8ActualCyclicSubgroup := by
  have hsource : Nat.card deningerQ8ActualCyclicSubgroup = 4 :=
    deningerQ8ActualCyclicSubgroup_natCard
  have hinertia : Nat.card (P.inertia Gal(K3/ℚ)) = 4 :=
    q8Actual_five_inertia_natCard_eq_four P hPover
  apply Subgroup.eq_of_le_of_card_ge
    (q8Actual_five_inertia_le_cyclicSource P hPover)
  exact (hsource.trans hinertia.symm).le

/-- At every top prime over `5`, decomposition lies in the same literal
`√41`-selected source carrier. A decomposition element exchanging the two
orientations would preserve a prime containing one factor of
`v(1-v) = -10` and hence force that prime to contain both factors. -/
theorem q8Actual_five_decomposition_le_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P ≤ deningerQ8ActualCyclicSubgroup := by
  intro g hg
  rw [deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY]
  change (g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY =
    deningerQ8RootNumberNegOneTopY
  rcases hq : deningerQ8RootNumberNegOne_galoisEquivQ8 (g : Gal(K3/ℚ)) with i | i
  · rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply
      (g : Gal(K3/ℚ)), hq]
    change q8IAlgPow i deningerQ8RootNumberNegOneTopY =
      deningerQ8RootNumberNegOneTopY
    exact q8IAlgPow_topY _
  · exfalso
    have hy : (g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopY =
        -deningerQ8RootNumberNegOneTopY := by
      rw [← deningerQ8RootNumberNegOne_galoisEquivQ8.symm_apply_apply
        (g : Gal(K3/ℚ)), hq]
      change q8JAlgEquiv (q8IAlgPow i deningerQ8RootNumberNegOneTopY) =
        -deningerQ8RootNumberNegOneTopY
      rw [q8IAlgPow_topY, q8JAlgEquiv_apply, q8J_topY]
    let v : 𝓞 K3 := q8LiteralTwoAdicV
    have hgv : (g : Gal(K3/ℚ)) • v = 1 - v := by
      apply Subtype.ext
      change (g : Gal(K3/ℚ)) q8LiteralTwoAdicVField =
        1 - q8LiteralTwoAdicVField
      rw [q8LiteralTwoAdicVField, map_div₀, map_add, map_one, hy]
      have htwoMap : (g : Gal(K3/ℚ)) (2 : K3) = 2 := map_ofNat _ 2
      rw [htwoMap]
      field_simp
      ring
    have hmove {x : 𝓞 K3} (hx : x ∈ P) :
        (g : Gal(K3/ℚ)) • x ∈ P := by
      have hx' := Ideal.smul_mem_pointwise_smul (g : Gal(K3/ℚ)) x P hx
      rwa [hg] at hx'
    have hPfive : (5 : 𝓞 K3) ∈ P := by
      exact (Ideal.liesOver_span_iff
        (Ideal.IsMaximal.ne_top inferInstance) (by norm_num : Prime (5 : ℤ))).mp hPover
    have hminusTen : (-10 : 𝓞 K3) ∈ P := by
      have hten : (10 : 𝓞 K3) ∈ P := by
        convert P.mul_mem_left (2 : 𝓞 K3) hPfive using 1
        norm_num
      exact P.neg_mem hten
    have hprod : v * (1 - v) = (-10 : 𝓞 K3) := by
      dsimp [v]
      calc
        q8LiteralTwoAdicV * (1 - q8LiteralTwoAdicV) =
            q8LiteralTwoAdicV - q8LiteralTwoAdicV ^ (2 : ℕ) := by ring
        _ = -10 := by rw [q8LiteralTwoAdicV_sq]; ring
    have hv_or : v ∈ P ∨ (1 - v) ∈ P :=
      (Ideal.IsPrime.mem_or_mem inferInstance) (hprod.symm ▸ hminusTen)
    rcases hv_or with hv | hv
    · have hw : 1 - v ∈ P := by
        rw [← hgv]
        exact hmove hv
      have hone : (1 : 𝓞 K3) ∈ P := by simpa using P.add_mem hv hw
      exact (Ideal.IsMaximal.ne_top inferInstance) (P.eq_top_iff_one.mpr hone)
    · have hv' : v ∈ P := by
        have hw := hmove hv
        rw [smul_sub, smul_one, hgv] at hw
        have : -(v : 𝓞 K3) ∈ P := by simpa using hw
        simpa only [neg_neg] using P.neg_mem this
      have hone : (1 : 𝓞 K3) ∈ P := by simpa using P.add_mem hv' hv
      exact (Ideal.IsMaximal.ne_top inferInstance) (P.eq_top_iff_one.mpr hone)

/-- The five-adic decomposition group, inertia group, and global inducing
carrier are the same literal subgroup. -/
theorem q8Actual_five_decomposition_eq_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P = deningerQ8ActualCyclicSubgroup := by
  apply le_antisymm (q8Actual_five_decomposition_le_cyclicSource P hPover)
  rw [← q8Actual_five_inertia_eq_cyclicSource P hPover]
  exact Ideal.inertia_le_stabilizer P

/-- Every five-adic prime in the actual quaternion field has residue degree
one: decomposition equals inertia before scalarization. -/
theorem q8Actual_five_decomposition_eq_inertia
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(5 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P = P.inertia Gal(K3/ℚ) := by
  rw [q8Actual_five_decomposition_eq_cyclicSource P hPover,
    q8Actual_five_inertia_eq_cyclicSource P hPover]

end
end RHTower
