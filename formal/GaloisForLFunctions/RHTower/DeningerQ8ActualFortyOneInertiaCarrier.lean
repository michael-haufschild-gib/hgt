import GaloisForLFunctions.RHTower.DeningerQ8ActualOddInertiaCyclic
import GaloisForLFunctions.RHTower.DeningerQ8ActualMonomialSourceLaw

/-!
# The actual forty-one-adic carrier is selected by `√5`

At every top prime over `41`, decomposition and inertia equal the literal
stabilizer of `√5`. The two residue orientations are detected by the integral
coordinate `u = (1 + √5) / 2`: modulo `41`, its roots are `7` and `35`, since
`(u - 7)(u + 6) = -41`. A decomposition automorphism exchanging them would
force the prime to contain their difference `13`.

This identifies the second odd local carrier before any epsilon-factor
scalarization; no abstract conjugate subgroup or chosen local orientation is
substituted.
-/

namespace RHTower

open scoped NumberField Pointwise
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3
noncomputable local instance : NumberField K3 := NumberField.mk
noncomputable local instance : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- The global stabilizer of the literal `√5` source coordinate has at most
four elements. -/
theorem q8Actual_topX_stabilizer_natCard_le_four :
    Nat.card (MulAction.stabilizer Gal(K3/ℚ)
      deningerQ8RootNumberNegOneTopX) ≤ 4 := by
  let H := MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX
  change Nat.card H ≤ 4
  have hHne : H ≠ ⊤ := by
    intro htop
    have hi : q8IAlgEquiv ∈ H := by rw [htop]; exact Subgroup.mem_top _
    change q8IAlgEquiv • deningerQ8RootNumberNegOneTopX =
      deningerQ8RootNumberNegOneTopX at hi
    change q8IAlgEquiv deningerQ8RootNumberNegOneTopX =
      deningerQ8RootNumberNegOneTopX at hi
    rw [q8IAlgEquiv_apply, q8I_topX] at hi
    exact q8TopX_ne_zero (CharZero.neg_eq_self_iff.mp hi)
  have hcard := H.card_mul_index
  have hgalcard : Nat.card Gal(K3/ℚ) = 8 := by
    calc
      Nat.card Gal(K3/ℚ) = Nat.card (QuaternionGroup 2) :=
        Nat.card_congr deningerQ8RootNumberNegOne_galoisEquivQ8.toEquiv
      _ = 8 := by rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hgalcard] at hcard
  have hindex0 : H.index ≠ 0 := by intro h; rw [h] at hcard; norm_num at hcard
  have hindex1 : H.index ≠ 1 := by
    intro h
    exact hHne (Subgroup.index_eq_one.mp h)
  have hindex : 2 ≤ H.index := by omega
  nlinarith

/-- At every top prime over `41`, decomposition fixes the literal `√5`
source coordinate. -/
theorem q8Actual_fortyOne_decomposition_le_topXStabilizer
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P ≤
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  change (g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopX =
    deningerQ8RootNumberNegOneTopX
  have hsq :
      ((g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopX) ^ 2 =
        deningerQ8RootNumberNegOneTopX ^ 2 := by
    calc
      ((g : Gal(K3/ℚ)) deningerQ8RootNumberNegOneTopX) ^ 2 =
          (g : Gal(K3/ℚ)) (deningerQ8RootNumberNegOneTopX ^ 2) := by
            rw [map_pow]
      _ = (g : Gal(K3/ℚ)) 5 := by
        rw [deningerQ8RootNumberNegOne_topX_sq]
      _ = 5 := map_ofNat _ 5
      _ = deningerQ8RootNumberNegOneTopX ^ 2 :=
        deningerQ8RootNumberNegOne_topX_sq.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hfix | hneg
  · exact hfix
  · exfalso
    let u : 𝓞 K3 := q8LiteralTwoAdicU
    have hgu : (g : Gal(K3/ℚ)) • u = 1 - u := by
      apply Subtype.ext
      change (g : Gal(K3/ℚ)) q8LiteralTwoAdicUField =
        1 - q8LiteralTwoAdicUField
      rw [q8LiteralTwoAdicUField, map_div₀, map_add, map_one, hneg]
      have htwoMap : (g : Gal(K3/ℚ)) (2 : K3) = 2 := map_ofNat _ 2
      rw [htwoMap]
      field_simp
      ring
    have hmove {x : 𝓞 K3} (hx : x ∈ P) :
        (g : Gal(K3/ℚ)) • x ∈ P := by
      have hx' := Ideal.smul_mem_pointwise_smul (g : Gal(K3/ℚ)) x P hx
      rwa [hg] at hx'
    have hPfortyOne : (41 : 𝓞 K3) ∈ P := by
      exact (Ideal.liesOver_span_iff
        (Ideal.IsMaximal.ne_top inferInstance) (by norm_num : Prime (41 : ℤ))).mp hPover
    have hminusFortyOne : (-41 : 𝓞 K3) ∈ P := P.neg_mem hPfortyOne
    have hprod : (u - 7) * (u + 6) = (-41 : 𝓞 K3) := by
      dsimp [u]
      calc
        (q8LiteralTwoAdicU - 7) * (q8LiteralTwoAdicU + 6) =
            q8LiteralTwoAdicU ^ 2 - q8LiteralTwoAdicU - 42 := by ring
        _ = -41 := by rw [q8LiteralTwoAdicU_sq]; ring
    have hor : u - 7 ∈ P ∨ u + 6 ∈ P :=
      (Ideal.IsPrime.mem_or_mem inferInstance) (hprod.symm ▸ hminusFortyOne)
    have hswapLeft : (g : Gal(K3/ℚ)) • (u - 7) = -(u + 6) := by
      have hseven : (g : Gal(K3/ℚ)) • (7 : 𝓞 K3) = 7 := by
        apply Subtype.ext
        change (g : Gal(K3/ℚ)) (7 : K3) = 7
        exact map_ofNat _ 7
      rw [smul_sub, hgu, hseven]
      ring
    have hswapRight : (g : Gal(K3/ℚ)) • (u + 6) = -(u - 7) := by
      have hsix : (g : Gal(K3/ℚ)) • (6 : 𝓞 K3) = 6 := by
        apply Subtype.ext
        change (g : Gal(K3/ℚ)) (6 : K3) = 6
        exact map_ofNat _ 6
      rw [smul_add, hgu, hsix]
      ring
    have hleft : u - 7 ∈ P := by
      rcases hor with h | h
      · exact h
      · have hm := hmove h
        rw [hswapRight] at hm
        simpa using P.neg_mem hm
    have hright : u + 6 ∈ P := by
      rcases hor with h | h
      · have hm := hmove h
        rw [hswapLeft] at hm
        simpa using P.neg_mem hm
      · exact h
    have h13 : (13 : 𝓞 K3) ∈ P := by
      convert P.sub_mem hright hleft using 1
      ring
    have h13base : (13 : ℤ) ∈ Ideal.span {(41 : ℤ)} := by
      rw [hPover.over]
      exact h13
    norm_num [Ideal.mem_span_singleton] at h13base

/-- At every top prime over `41`, actual inertia is literally the global
stabilizer selected by `√5`. -/
theorem q8Actual_fortyOne_inertia_eq_topXStabilizer
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    P.inertia Gal(K3/ℚ) =
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX := by
  have hle : P.inertia Gal(K3/ℚ) ≤
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX :=
    le_trans (Ideal.inertia_le_stabilizer P)
      (q8Actual_fortyOne_decomposition_le_topXStabilizer P hPover)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [q8Actual_fortyOne_inertia_natCard_eq_four P hPover]
  exact q8Actual_topX_stabilizer_natCard_le_four

/-- The forty-one-adic decomposition group, inertia group, and literal
`√5`-selected carrier are the same subgroup. -/
theorem q8Actual_fortyOne_decomposition_eq_topXStabilizer
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P =
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopX := by
  apply le_antisymm
    (q8Actual_fortyOne_decomposition_le_topXStabilizer P hPover)
  rw [← q8Actual_fortyOne_inertia_eq_topXStabilizer P hPover]
  exact Ideal.inertia_le_stabilizer P

/-- Every forty-one-adic top prime has residue degree one. -/
theorem q8Actual_fortyOne_decomposition_eq_inertia
    (P : Ideal (𝓞 K3)) [P.IsMaximal]
    (hPover : P.LiesOver (Ideal.span {(41 : ℤ)})) :
    MulAction.stabilizer Gal(K3/ℚ) P = P.inertia Gal(K3/ℚ) := by
  rw [q8Actual_fortyOne_decomposition_eq_topXStabilizer P hPover,
    q8Actual_fortyOne_inertia_eq_topXStabilizer P hPover]

end
end RHTower
