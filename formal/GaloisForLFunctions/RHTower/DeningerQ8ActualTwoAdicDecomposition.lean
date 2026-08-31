import GaloisForLFunctions.RHTower.DeningerQ8ActualTwoAdicInertia
import GaloisForLFunctions.RHTower.DeningerQ8ActualMonomialSourceLaw

/-!
# Exact two-adic decomposition carrier of the literal SST quaternion field

The two-adic inertia group is already the central subgroup of order two.  This
file identifies the larger decomposition group without importing a quadratic
splitting table.  The integral element

`u = (1 + sqrt 5) / 2`

satisfies `u^2 = u + 1`; modulo every prime above two its residue is distinct
from both zero and one.  Thus the residue field has at least three elements.
Combining this lower bound with the exact inertia order and the literal
order-four source stabilizer forces residue degree two and decomposition order
four.  A separate integral argument with

`v = (1 + sqrt 41) / 2`

shows that the decomposition group lies in the stabilizer of `sqrt 41`.
Equality of orders then identifies it with the same cyclic subgroup carrying
the already formalized primitive quartic monomial character.

This is the local/global carrier weld required before a wild two-adic epsilon
factor calculation: the local decomposition group is not merely abstractly
cyclic of order four; it is literally the source-selected quartic carrier.
-/

namespace RHTower

open scoped NumberField Pointwise
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8DecompositionCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance q8DecompositionFiniteDimensionalRatK1 :
    FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis

noncomputable local instance q8DecompositionFiniteDimensionalK1K2 :
    FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis

noncomputable local instance q8DecompositionFiniteDimensionalRatK2 :
    FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis

noncomputable local instance q8DecompositionFiniteDimensionalK2K3 :
    FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8DecompositionFiniteDimensionalRatK3 :
    FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

noncomputable local instance q8DecompositionNumberFieldK3 : NumberField K3 :=
  NumberField.mk

noncomputable local instance q8DecompositionIsGalois : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- The residue ring at every prime above two contains the three distinct
classes `0`, `1`, and `(1 + sqrt 5) / 2`. -/
theorem q8Literal_two_three_le_residue_natCard
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    3 ≤ Nat.card ((𝓞 K3) ⧸ P) := by
  letI : Nontrivial ((𝓞 K3) ⧸ P) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  let ubar : (𝓞 K3) ⧸ P := Ideal.Quotient.mk P q8LiteralTwoAdicU
  have hrel : ubar ^ 2 = ubar + 1 := by
    exact congrArg (Ideal.Quotient.mk P) q8LiteralTwoAdicU_sq
  have htwo : (2 : (𝓞 K3) ⧸ P) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hPtwo
  have hu0 : ubar ≠ 0 := by
    intro hu
    rw [hu] at hrel
    simp at hrel
  have hu1 : ubar ≠ 1 := by
    intro hu
    rw [hu] at hrel
    norm_num at hrel
    have : (1 : (𝓞 K3) ⧸ P) = 0 := hrel.trans htwo
    exact one_ne_zero this
  let f : Fin 3 → ((𝓞 K3) ⧸ P)
    | 0 => 0
    | 1 => 1
    | 2 => ubar
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa using Nat.card_le_card_of_injective f hf

/-- Every two-adic decomposition automorphism lies in the literal quartic
source subgroup selected by `sqrt 41`. -/
theorem q8Literal_two_decomposition_le_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
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
      rw [q8LiteralTwoAdicVField]
      rw [map_div₀, map_add, map_one, hy]
      have htwoMap : (g : Gal(K3/ℚ)) (2 : K3) = 2 := map_ofNat _ 2
      rw [htwoMap]
      field_simp
      ring
    have hmove {x : 𝓞 K3} (hx : x ∈ P) :
        (g : Gal(K3/ℚ)) • x ∈ P := by
      have hx' := Ideal.smul_mem_pointwise_smul (g : Gal(K3/ℚ)) x P hx
      rwa [hg] at hx'
    have hminusTen : (-10 : 𝓞 K3) ∈ P := by
      have hten : (10 : 𝓞 K3) ∈ P := by
        convert P.mul_mem_left (5 : 𝓞 K3) hPtwo using 1
        norm_num
      exact P.neg_mem hten
    have hprod : v * (1 - v) = (-10 : 𝓞 K3) := by
      dsimp [v]
      calc
        q8LiteralTwoAdicV * (1 - q8LiteralTwoAdicV) =
            q8LiteralTwoAdicV - q8LiteralTwoAdicV ^ 2 := by ring
        _ = -10 := by rw [q8LiteralTwoAdicV_sq]; ring
    have hv_or : v ∈ P ∨ (1 - v) ∈ P := by
      exact (Ideal.IsPrime.mem_or_mem inferInstance) (hprod.symm ▸ hminusTen)
    rcases hv_or with hv | hv
    · have hw : 1 - v ∈ P := by
        rw [← hgv]
        exact hmove hv
      have hone : (1 : 𝓞 K3) ∈ P := by
        simpa using P.add_mem hv hw
      exact (Ideal.IsMaximal.ne_top inferInstance) (P.eq_top_iff_one.mpr hone)
    · have hv' : v ∈ P := by
        have hw := hmove hv
        rw [smul_sub, smul_one, hgv] at hw
        have : -(v : 𝓞 K3) ∈ P := by simpa using hw
        simpa only [neg_neg] using P.neg_mem this
      have hone : (1 : 𝓞 K3) ∈ P := by
        simpa using P.add_mem hv' hv
      exact (Ideal.IsMaximal.ne_top inferInstance) (P.eq_top_iff_one.mpr hone)

/-- The residue degree at every prime above two is exactly two. -/
theorem q8Literal_two_inertiaDeg_eq_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.inertiaDeg ℤ = 2 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : p.IsPrime := by
    dsimp [p]
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  letI : p.IsMaximal := Int.prime_two.isMaximal_span_singleton
  have hPover : P.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hPtwo
  letI : P.LiesOver p := hPover
  have hcardEq := Ideal.card_stabilizer_eq_card_inertia_mul_finrank
    (G := Gal(K3/ℚ)) p P
  rw [q8Literal_two_inertia_natCard_eq_two P hPtwo] at hcardEq
  have hle := q8Literal_two_decomposition_le_cyclicSource P hPtwo
  let embed : (MulAction.stabilizer Gal(K3/ℚ) P) →
      deningerQ8ActualCyclicSubgroup :=
    fun g => ⟨(g : Gal(K3/ℚ)), hle g.2⟩
  have hembed : Function.Injective embed := by
    intro g h hgh
    apply Subtype.ext
    exact congrArg (fun x => x.1) hgh
  have hcardLe : Nat.card (MulAction.stabilizer Gal(K3/ℚ) P) ≤ 4 := by
    calc
      Nat.card (MulAction.stabilizer Gal(K3/ℚ) P) ≤
          Nat.card deningerQ8ActualCyclicSubgroup :=
        Nat.card_le_card_of_injective embed hembed
      _ = 4 := deningerQ8ActualCyclicSubgroup_natCard
  have hfLe : P.inertiaDeg ℤ ≤ 2 := by omega
  have hfPos : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
  have hnorm : Nat.card ((𝓞 K3) ⧸ P) = 2 ^ P.inertiaDeg ℤ := by
    calc
      Nat.card ((𝓞 K3) ⧸ P) = Submodule.cardQuot P := by
        rw [Submodule.cardQuot_apply]
      _ = Ideal.absNorm P := (Ideal.absNorm_apply P).symm
      _ = 2 ^ (Ideal.span {(2 : ℤ)}).inertiaDeg' P :=
        Ideal.absNorm_eq_pow_inertiaDeg' P Nat.prime_two
      _ = 2 ^ P.inertiaDeg ℤ := by
        rw [Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(2 : ℤ)}) P]
  have hthree := q8Literal_two_three_le_residue_natCard P hPtwo
  have hfCases : P.inertiaDeg ℤ = 1 ∨ P.inertiaDeg ℤ = 2 := by omega
  rcases hfCases with hf | hf
  · rw [hf] at hnorm
    norm_num at hnorm
    omega
  · exact hf

/-- Every prime-two decomposition group has exactly four elements. -/
theorem q8Literal_two_decomposition_natCard_eq_four
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Nat.card (MulAction.stabilizer Gal(K3/ℚ) P) = 4 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : p.IsPrime := by
    dsimp [p]
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  have hPover : P.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hPtwo
  letI : P.LiesOver p := hPover
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank p P,
    q8Literal_two_inertia_natCard_eq_two P hPtwo,
    q8Literal_two_inertiaDeg_eq_two P hPtwo]

/-- The local decomposition carrier is literally the global quartic source
carrier of the monomial Artin representation. -/
theorem q8Literal_two_decomposition_eq_cyclicSource
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    MulAction.stabilizer Gal(K3/ℚ) P = deningerQ8ActualCyclicSubgroup := by
  have hsource : Nat.card deningerQ8ActualCyclicSubgroup = 4 :=
    deningerQ8ActualCyclicSubgroup_natCard
  have hdecomp : Nat.card (MulAction.stabilizer Gal(K3/ℚ) P) = 4 :=
    q8Literal_two_decomposition_natCard_eq_four P hPtwo
  apply Subgroup.eq_of_le_of_card_ge
    (q8Literal_two_decomposition_le_cyclicSource P hPtwo)
  exact (hsource.trans hdecomp.symm).le

/-- Equivalent fixed-carrier form: decomposition at two is the stabilizer of
the literal `sqrt 41` source coordinate. -/
theorem q8Literal_two_decomposition_eq_stabilizer_topY
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    MulAction.stabilizer Gal(K3/ℚ) P =
      MulAction.stabilizer Gal(K3/ℚ) deningerQ8RootNumberNegOneTopY := by
  exact (q8Literal_two_decomposition_eq_cyclicSource P hPtwo).trans
    deningerQ8ActualCyclicSubgroup_eq_stabilizer_topY

end

end RHTower
