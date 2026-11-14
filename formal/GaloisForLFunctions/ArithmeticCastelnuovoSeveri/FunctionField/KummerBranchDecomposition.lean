import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExactRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.AdicDecompositionCardinality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerBranchResidueConstants

/-!
# Rationality of nonzero Kummer branch places

A constant residue of the quotient radical forces the decomposition
character to have order dividing `N/gcd(N,R)`. The decomposition order
`e f` is therefore at most this number. Exact Kummer ramification gives
`e=N/gcd(N,R)`, so `f=1`. For inverse-power coefficients, norm
surjectivity discharges the splitting condition at every nonzero
auxiliary-field branch point.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Decomposition order is the product of the actual ramification and residue degrees. -/
theorem squareKummer_decomposition_card (a : SquareConstantField p s)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    Nat.card ((w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X])) =
      (Ideal.span {X - C a}).ramificationIdx' w.asIdeal *
        (Ideal.span {X - C a}).inertiaDeg' w.asIdeal := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI := squareKummer_isGalois p s c b R
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C a})
    infer_instance
  letI : Finite (Ideal.ResidueField (Ideal.span {X - C a})) :=
    polynomial_irreduciblePlace_finite_residue (irreducible_X_sub_C a)
  letI : PerfectField v.asIdeal.ResidueField := by
    change PerfectField (Ideal.ResidueField (Ideal.span {X - C a}))
    infer_instance
  exact heightOne_decomposition_card (K := FractionRing (SquareConstantField p s)[X])
    (L := SquareKummerField p s c b R) v w

/-- A split branch residue forces every decomposition phase to have order dividing `N/gcd(N,R)`. -/
theorem squareKummer_decomposition_character_pow
    (a : SquareConstantField p s) (ha : a ≠ 0)
    (β : SquareConstantField p s) (hβ : β ≠ 0)
    (hβpow : β ^ Nat.gcd (p ^ (s + 1) + 1) R = (c : SquareConstantField p s) * a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (g : (w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X])) :
    ((((squareKummerAutEquiv p s c b R).symm g : rootsOfUnity (p ^ (s + 1) + 1)
      (SquareConstantField p s)) : (SquareConstantField p s)ˣ) : SquareConstantField p s) ^
        ((p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R) = 1 := by
  let L := SquareKummerField p s c b R
  let W := (w.valuation L).valuationSubring
  let σ : L ≃ₐ[FractionRing (SquareConstantField p s)[X]] L := g
  let ζ := (squareKummerAutEquiv p s c b R).symm σ
  let N := p ^ (s + 1) + 1
  let δ := Nat.gcd N R
  let u := kummerBranchResidueUnit p s c b R a ha w
  let f := kummerPlaceConstantHom p s c b R w
  obtain ⟨t, ht⟩ := kummerBranchResidueUnit_constant p s c b R a ha β hβ hβpow w
  have hfix : g • f t = f t := by
    apply Subtype.ext
    change σ (f t : L) = (f t : L)
    rw [kummerPlaceConstantHom_coe, IsScalarTower.algebraMap_apply (SquareConstantField p s)
      (FractionRing (SquareConstantField p s)[X]) L, σ.commutes]
  have hunit : w.valuation L (u : L) = 1 :=
    squareKummerBranchUnitRoot_valuation_one p s c b R a ha w
  have hzσ := squareKummerAutEquiv_root p s c b R ζ
  rw [MulEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply] at hzσ
  have htσ : σ (algebraMap (SquareConstantField p s)[X] L (1 - X ^ (b + 1))) =
      algebraMap (SquareConstantField p s)[X] L (1 - X ^ (b + 1)) := by
    rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X]) L, σ.commutes]
  change (((ζ : (SquareConstantField p s)ˣ) : SquareConstantField p s)) ^ (N / δ) = 1
  apply decomposition_unit_character_eq_one (w.valuation L) f
    (fun x hx => by rw [kummerPlaceConstantHom_coe]; exact heightOne_valuation_constant w x hx)
    g hunit ht.symm hfix
  apply Subtype.ext
  change σ (kummerBranchUnitRoot c b R (p ^ (s + 1))) =
    (f (((ζ : (SquareConstantField p s)ˣ) : SquareConstantField p s) ^ (N / δ)) : L) *
      kummerBranchUnitRoot c b R (p ^ (s + 1))
  rw [kummerPlaceConstantHom_coe, kummerBranchUnitRoot, map_div₀, map_pow, map_pow,
    hzσ, htσ, mul_pow, ← map_pow, mul_div_assoc]

/-- The split unit character bounds the full decomposition group. -/
theorem squareKummer_decomposition_card_le
    (a : SquareConstantField p s) (ha : a ≠ 0)
    (β : SquareConstantField p s) (hβ : β ≠ 0)
    (hβpow : β ^ Nat.gcd (p ^ (s + 1) + 1) R = (c : SquareConstantField p s) * a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    Nat.card ((w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X])) ≤
        (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R := by
  classical
  letI := squareKummer_isGalois p s c b R
  let L := SquareKummerField p s c b R
  let G := (w.valuation L).valuationSubring.decompositionSubgroup
    (FractionRing (SquareConstantField p s)[X])
  let N := p ^ (s + 1) + 1
  let D := N / Nat.gcd N R
  have hD : 0 < D := Nat.div_pos
    (Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left N R))
    (Nat.gcd_pos_of_pos_left R (Nat.succ_pos _))
  let j : G → SquareConstantField p s := fun g =>
    (((squareKummerAutEquiv p s c b R).symm g : (SquareConstantField p s)ˣ) : SquareConstantField p s)
  have hj : Function.Injective j := by
    intro g h hgh
    apply Subtype.ext
    apply (squareKummerAutEquiv p s c b R).symm.injective
    apply Subtype.ext
    exact Units.ext hgh
  have hmem : ∀ g : G, j g ∈ (Polynomial.nthRoots D (1 : SquareConstantField p s)).toFinset := by
    intro g
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hD]
    exact squareKummer_decomposition_character_pow p s c b R a ha β hβ hβpow w g
  have hcard : Nat.card G ≤
      Nat.card {x // x ∈ (Polynomial.nthRoots D (1 : SquareConstantField p s)).toFinset} :=
    Nat.card_le_card_of_injective (fun g : G => ⟨j g, hmem g⟩)
      (fun g h hgh => hj (congrArg Subtype.val hgh))
  rw [Nat.card_eq_finsetCard] at hcard
  exact hcard.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots D 1))

/-- Exact inertia and a split branch residue force residue degree one. -/
theorem squareKummer_split_branch_inertia
    (a : SquareConstantField p s) (ha : a ≠ 0)
    (hm : (kummerBranch c b R).rootMultiplicity a = R)
    (β : SquareConstantField p s) (hβ : β ≠ 0)
    (hβpow : β ^ Nat.gcd (p ^ (s + 1) + 1) R = (c : SquareConstantField p s) * a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h := squareKummer_decomposition_card_le p s c b R a ha β hβ hβpow w
  rw [squareKummer_decomposition_card p s c b R a w,
    squareKummer_rationalPlace_ramification p s c b R a w, hm] at h
  have hD : 0 < (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R := Nat.div_pos
    (Nat.le_of_dvd (Nat.succ_pos _) (Nat.gcd_dvd_left _ _))
    (Nat.gcd_pos_of_pos_left R (Nat.succ_pos _))
  have hfle : (Ideal.span {X - C a}).inertiaDeg' w.asIdeal ≤ 1 := by
    apply le_of_mul_le_mul_left (a := (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R)
      (by simpa only [mul_one] using h) hD
  exact Nat.le_antisymm hfle
    (Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero (Ideal.span {X - C a}) w.asIdeal))

/-- Every nonzero auxiliary-field branch has residue degree one for the inverse-power coefficient family. -/
theorem squareKummer_primePowerBranch_inertia (d n R : ℕ)
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ)
    (a : (KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p (kummerSquareIndex d n)
      ((η⁻¹) ^ R) (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) :
        SquareConstantField p (kummerSquareIndex d n))})] :
    (Ideal.span {X - C ((a : KummerAuxiliaryField p (kummerSquareIndex d n) (d + 1)) :
      SquareConstantField p (kummerSquareIndex d n))}).inertiaDeg' w.asIdeal = 1 := by
  obtain ⟨β, hβ, hβpow⟩ := squareConstantField_exists_auxiliary_branch_residue_root p d n R η a
  apply squareKummer_split_branch_inertia p (kummerSquareIndex d n) ((η⁻¹) ^ R)
    (p ^ (d + 1) - 2) R _ _ _ β hβ hβpow w
  · intro h
    exact Units.ne_zero a (Subtype.ext h)
  · exact kummerBranch_primePower_rootMultiplicity p (kummerSquareIndex d n) ((η⁻¹) ^ R) R d a

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
