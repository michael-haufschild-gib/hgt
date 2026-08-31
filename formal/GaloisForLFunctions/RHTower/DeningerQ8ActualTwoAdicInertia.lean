import GaloisForLFunctions.RHTower.DeningerQ8ActualBiquadraticDiscriminant
import GaloisForLFunctions.RHTower.DeningerQ8ArtinGaloisRealization
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory

/-!
# Exact two-adic inertia of the literal SST quaternion field

The maximal abelian subfield `ℚ(√5, √41)` has odd discriminant, hence is
unramified at two, while the literal quaternion field is ramified at every
prime above two.  Since the top relative extension has degree two, the tower
law forces exact ramification index two.  This is the local group-theoretic
carrier needed by a coefficient-faithful epsilon-factor calculation.
-/

namespace RHTower

open scoped NumberField Pointwise
noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8InertiaCharZeroK2 : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance q8InertiaCharZeroK3 : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

noncomputable local instance q8InertiaFiniteDimensionalRatK1 : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance q8InertiaFiniteDimensionalK1K2 : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance q8InertiaFiniteDimensionalRatK2 : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance q8InertiaFiniteDimensionalK2K3 : FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis
noncomputable local instance q8InertiaFiniteDimensionalRatK3 : FiniteDimensional ℚ K3 :=
  FiniteDimensional.trans ℚ K2 K3

noncomputable local instance q8InertiaNumberFieldK2 : NumberField K2 := NumberField.mk
noncomputable local instance q8InertiaNumberFieldK3 : NumberField K3 := NumberField.mk
noncomputable local instance q8InertiaIsGalois : IsGalois ℚ K3 :=
  deningerQ8RootNumberNegOne_isGalois

/-- Every prime above two in the literal SST quaternion field has exact
ramification index two. -/
theorem q8Literal_two_ramificationIdx_eq_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.ramificationIdx ℤ = 2 := by
  let Q : Ideal (𝓞 K2) := P.comap (algebraMap (𝓞 K2) (𝓞 K3))
  letI : Q.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := 𝓞 K2) (S := 𝓞 K3) P
  letI : P.LiesOver Q := ⟨rfl⟩
  have hQtwo : (2 : 𝓞 K2) ∈ Q := by
    change algebraMap (𝓞 K2) (𝓞 K3) 2 ∈ P
    simpa only [map_ofNat] using hPtwo
  have hQover : Q.LiesOver (Ideal.span {(2 : ℤ)}) := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    exact hQtwo
  letI : Algebra.IsUnramifiedAt ℤ Q :=
    q8Biquad_two_isUnramifiedIn Q inferInstance hQover
  have heQ : Q.ramificationIdx ℤ = 1 := by
    exact Ideal.ramificationIdx_eq_one Q ℤ
  have heTower := Ideal.ramificationIdx_tower (R := ℤ) Q P
  have hQne : Q ≠ ⊥ := by
    intro hQ
    rw [hQ, Ideal.mem_bot] at hQtwo
    norm_num at hQtwo
  have hOinj : Function.Injective (algebraMap (𝓞 K2) (𝓞 K3)) := by
    intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg (fun z : 𝓞 K3 => (z : K3)) hxy
    exact (algebraMap K2 K3).injective hxy'
  letI : NoZeroSMulDivisors (𝓞 K2) (𝓞 K3) := by
    constructor
    intro c x hcx
    have hmul : algebraMap (𝓞 K2) (𝓞 K3) c * x = 0 := by
      simpa only [Algebra.smul_def] using hcx
    rcases mul_eq_zero.mp hmul with hc | hx
    · exact Or.inl (hOinj (by simpa using hc))
    · exact Or.inr hx
  have hle' : Q.ramificationIdx' P ≤ Module.finrank K2 K3 :=
    Ideal.ramificationIdx_le_finrank (R := 𝓞 K2) (S := 𝓞 K3) K2 K3 P
  have hrel : P.ramificationIdx (𝓞 K2) ≤ 2 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx Q P hQne] at hle'
    simpa [deningerQ8RootNumberNegOneTopField_finrank_over_second] using hle'
  have htop_ne : P.ramificationIdx ℤ ≠ 1 := by
    intro he
    apply q8Literal_not_isUnramifiedAt_two P hPtwo
    exact Ideal.ramificationIdx_eq_one_iff.mp he
  rw [heQ, one_mul] at heTower
  rw [heTower]
  have hpos : 0 < P.ramificationIdx (𝓞 K2) := Ideal.ramificationIdx_pos P (𝓞 K2)
  omega

/-- The center is the unique subgroup of concrete `Q₈` with two elements. -/
theorem deningerQ8_subgroup_eq_center_of_natCard_eq_two
    (H : Subgroup (QuaternionGroup 2)) (hcard : Nat.card H = 2) :
    H = Subgroup.center (QuaternionGroup 2) := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    have hdvd : orderOf g ∣ 2 := by
      have hdvd' := H.orderOf_dvd_natCard hg
      conv at hdvd' => rhs; rw [hcard]
      exact hdvd'
    rcases g with i | i
    · fin_cases i
      · exact Subgroup.one_mem _
      · exfalso
        rw [QuaternionGroup.orderOf_a] at hdvd
        change 4 / Nat.gcd 4 1 ∣ 2 at hdvd
        norm_num at hdvd
      · exact deningerQ8_a_two_mem_center
      · exfalso
        rw [QuaternionGroup.orderOf_a] at hdvd
        change 4 / Nat.gcd 4 3 ∣ 2 at hdvd
        norm_num at hdvd
    · exfalso
      rw [QuaternionGroup.orderOf_xa] at hdvd
      norm_num at hdvd
  · rw [hcard, deningerQ8_center_natCard]

/-- Ideal-theoretic inertia at every prime above two has exactly two
elements. -/
theorem q8Literal_two_inertia_natCard_eq_two
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Nat.card (P.inertia Gal(K3/ℚ)) = 2 := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  letI : p.IsPrime := by
    dsimp [p]
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  have hPover : P.LiesOver p := by
    rw [Ideal.liesOver_span_iff (Ideal.IsMaximal.ne_top inferInstance) Int.prime_two]
    simpa [p] using hPtwo
  letI : P.LiesOver p := hPover
  calc
    Nat.card (P.inertia Gal(K3/ℚ)) = Ideal.ramificationIdxIn p (𝓞 K3) :=
      Ideal.card_inertia_eq_ramificationIdxIn p P
    _ = P.ramificationIdx ℤ := Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(K3/ℚ)
    _ = 2 := q8Literal_two_ramificationIdx_eq_two P hPtwo

/-- The actual Galois equivalence transports the literal central subgroup to
the center of concrete `Q₈`. -/
theorem deningerQ8ActualCentralSubgroup_map_galoisEquivQ8 :
    deningerQ8ActualCentralSubgroup.map
        deningerQ8RootNumberNegOne_galoisEquivQ8.toMonoidHom =
      Subgroup.center (QuaternionGroup 2) := by
  change (Subgroup.zpowers q8CAlgEquiv).map
      deningerQ8RootNumberNegOne_galoisEquivQ8.toMonoidHom =
    Subgroup.center (QuaternionGroup 2)
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers
      (deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv) =
    Subgroup.center (QuaternionGroup 2)
  rw [deningerQ8_galoisEquiv_q8C,
    ← deningerQ8_center_eq_centralGenerator]

/-- At every prime above two, ideal inertia is literally the center of the
actual quaternion Galois group. -/
theorem q8Literal_two_inertia_eq_center
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    P.inertia Gal(K3/ℚ) = deningerQ8ActualCentralSubgroup := by
  let e := deningerQ8RootNumberNegOne_galoisEquivQ8
  have hcardMap :
      Nat.card ((P.inertia Gal(K3/ℚ)).map e.toMonoidHom) = 2 := by
    calc
      Nat.card ((P.inertia Gal(K3/ℚ)).map e.toMonoidHom) =
          Nat.card (P.inertia Gal(K3/ℚ)) :=
        (Nat.card_congr
          ((P.inertia Gal(K3/ℚ)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
      _ = 2 := q8Literal_two_inertia_natCard_eq_two P hPtwo
  have hmap :
      (P.inertia Gal(K3/ℚ)).map e.toMonoidHom =
        Subgroup.center (QuaternionGroup 2) :=
    deningerQ8_subgroup_eq_center_of_natCard_eq_two _ hcardMap
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [hmap, deningerQ8ActualCentralSubgroup_map_galoisEquivQ8]

/-- The literal two-dimensional Artin representation has no nonzero vectors
fixed by full inertia at two: the inertial central involution acts as `-1`. -/
theorem q8Literal_two_artin_fullInertia_invariants_eq_bot
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Representation.invariants
        ((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (P.inertia Gal(K3/ℚ)).subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hc : q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ) := by
    rw [q8Literal_two_inertia_eq_center P hPtwo]
    exact Subgroup.mem_zpowers q8CAlgEquiv
  have hfix := (Representation.mem_invariants _ v).mp hv ⟨q8CAlgEquiv, hc⟩
  change deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv v = v at hfix
  rw [deningerQ8ArtinRepresentation_central_apply
    deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv
    deningerQ8_galoisEquiv_q8C] at hfix
  have hvzero : v = 0 := by
    apply Prod.ext
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.fst hfix)
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.snd hfix)
  simpa using hvzero

/-- The same vanishing holds for the stabilizer-internal inertia subgroup
used by the literal Artin local Euler factor. -/
theorem q8Literal_two_artin_localInertia_invariants_eq_bot
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    Representation.invariants
        (((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (MulAction.stabilizer Gal(K3/ℚ) P).subtype).comp
              (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)).subtype) = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have hc : q8CAlgEquiv ∈ P.inertia Gal(K3/ℚ) := by
    rw [q8Literal_two_inertia_eq_center P hPtwo]
    exact Subgroup.mem_zpowers q8CAlgEquiv
  let cD : MulAction.stabilizer Gal(K3/ℚ) P :=
    ⟨q8CAlgEquiv, Ideal.inertia_le_stabilizer P hc⟩
  have hcD : cD ∈ P.inertia (MulAction.stabilizer Gal(K3/ℚ) P) := by
    exact AddSubgroup.coe_mem_inertia.mp hc
  have hfix := (Representation.mem_invariants _ v).mp hv ⟨cD, hcD⟩
  change deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv v = v at hfix
  rw [deningerQ8ArtinRepresentation_central_apply
    deningerQ8RootNumberNegOne_galoisEquivQ8 q8CAlgEquiv
    deningerQ8_galoisEquiv_q8C] at hfix
  have hvzero : v = 0 := by
    apply Prod.ext
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.fst hfix)
    · exact CharZero.neg_eq_self_iff.mp (by
        simpa using congrArg Prod.snd hfix)
  simpa using hvzero

/-- Consequently every Frobenius lift gives prime-two Artin local polynomial
`1`: wild inertia kills the whole two-dimensional carrier before Frobenius
scalarization.  This formulation is stronger than choosing an arithmetic
Frobenius and does not hide the local calculation behind that choice. -/
theorem q8Literal_two_localEulerPolynomial_eq_one
    (P : Ideal (𝓞 K3)) [P.IsMaximal] (hPtwo : (2 : 𝓞 K3) ∈ P)
    (φ : MulAction.stabilizer Gal(K3/ℚ) P) :
    GaloisForLFunctions.localEulerPolynomial
        ((deningerQ8ArtinRepresentation
          deningerQ8RootNumberNegOne_galoisEquivQ8).comp
            (MulAction.stabilizer Gal(K3/ℚ) P).subtype)
        (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)) φ = 1 := by
  let W := Representation.invariants
    (((deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8).comp
        (MulAction.stabilizer Gal(K3/ℚ) P).subtype).comp
          (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)).subtype)
  let A : Module.End ℂ W := Representation.toInvariants
    ((deningerQ8ArtinRepresentation
      deningerQ8RootNumberNegOne_galoisEquivQ8).comp
        (MulAction.stabilizer Gal(K3/ℚ) P).subtype)
    (P.inertia (MulAction.stabilizer Gal(K3/ℚ) P)) φ
  have hW : W = ⊥ := by
    simpa [W] using q8Literal_two_artin_localInertia_invariants_eq_bot P hPtwo
  have hfinrank : Module.finrank ℂ W = 0 := by
    rw [hW]
    simp
  have hchar : A.charpoly = 1 := by
    apply A.charpoly_monic.natDegree_eq_zero.mp
    rw [A.charpoly_natDegree, hfinrank]
  change A.charpoly.reverse = 1
  rw [hchar]
  change Polynomial.reverse (Polynomial.C (1 : ℂ)) = Polynomial.C 1
  rw [Polynomial.reverse_C]

end
end RHTower
