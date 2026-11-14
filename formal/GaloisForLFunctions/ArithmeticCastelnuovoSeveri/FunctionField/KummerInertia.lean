import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.AdicInertiaCardinality
import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.InertiaUnitCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations

/-!
# Inertia characters at every finite Kummer place

For a prime polynomial of branch multiplicity `m`, the quotient
`z^(N/gcd(N,m)) / π^(m/gcd(N,m))` is a valuation unit. Inertia acts
trivially on its residue, forcing the corresponding constant phase to
have order dividing `N/gcd(N,m)`. The faithful phase character and the
adic inertia comparison give this bound for the actual ramification index.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- At every finite base place, the actual inertia group has order equal to ramification. -/
theorem squareKummer_inertia_card (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    Nat.card ((w.valuation (SquareKummerField p s c b R)).valuationSubring.inertiaSubgroup
      (FractionRing (SquareConstantField p s)[X])) =
      (Ideal.span {π}).ramificationIdx' w.asIdeal := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace hπ
  letI := squareKummer_isGalois p s c b R
  letI : (Ideal.span {π}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {π})
    infer_instance
  letI : Finite (Ideal.ResidueField (Ideal.span {π})) :=
    polynomial_irreduciblePlace_finite_residue hπ
  letI : PerfectField v.asIdeal.ResidueField := by
    change PerfectField (Ideal.ResidueField (Ideal.span {π}))
    infer_instance
  exact heightOne_inertia_card (K := FractionRing (SquareConstantField p s)[X])
    (L := SquareKummerField p s c b R) v w

/-- The radical divided by a matched power of the base parameter at a finite place. -/
def squareKummerBalancedRoot (π : (SquareConstantField p s)[X]) : SquareKummerField p s c b R :=
  let N := p ^ (s + 1) + 1
  let m := multiplicity π (kummerBranch c b R)
  let δ := Nat.gcd N m
  AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))) ^ (N / δ) /
    (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) π) ^ (m / δ)

/-- The balanced radical is a valuation unit at every place above the chosen base point. -/
theorem squareKummerBalancedRoot_valuation_one (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    w.valuation (SquareKummerField p s c b R) (squareKummerBalancedRoot p s c b R π) = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace hπ
  let L := SquareKummerField p s c b R
  let z : L := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  let t : L := algebraMap (SquareConstantField p s)[X] L π
  let m := multiplicity π (kummerBranch c b R)
  let N := p ^ (s + 1) + 1
  let δ := Nat.gcd N m
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {π})
    infer_instance
  have hf : kummerBranch c b R ≠ 0 := by
    intro h
    have hc := congrArg (fun f : (SquareConstantField p s)[X] => f.coeff 1) h
    rw [kummerBranch_coeff_one, coeff_zero] at hc
    exact Units.ne_zero c hc
  have htbase : v.valuation (FractionRing (SquareConstantField p s)[X])
      (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
        (π)) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton v hπ.ne_zero rfl
  have hb : v.valuation (FractionRing (SquareConstantField p s)[X])
      (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
        (kummerBranch c b R)) =
      (v.valuation (FractionRing (SquareConstantField p s)[X])
        (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
          (π))) ^ m := by
    rw [polynomial_irreduciblePlace_valuation hπ _ hf, htbase,
      ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one]
  have ht := HeightOneSpectrum.valuation_liesOver L v w
    (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X]) (π))
  rw [htbase, ← IsScalarTower.algebraMap_apply] at ht
  have ht0 : w.valuation L t ≠ 0 := by
    rw [← ht]
    exact pow_ne_zero _ WithZero.exp_ne_zero
  have hval : w.valuation L z ^ N = w.valuation L t ^ m := by
    have h := congrArg (w.valuation L) (kummerBranchField_root_pow c b R (p ^ (s + 1)))
    rw [map_pow, ← HeightOneSpectrum.valuation_liesOver L v w, hb, ← pow_mul,
      Nat.mul_comm m, pow_mul, HeightOneSpectrum.valuation_liesOver L v w,
      ← IsScalarTower.algebraMap_apply] at h
    exact h
  have hunit : w.valuation L (z ^ (N / δ) / t ^ (m / δ)) = 1 :=
    valuation_balanced_radical (w.valuation L) (Nat.gcd_pos_of_pos_left m (Nat.succ_pos _))
      (Nat.gcd_dvd_left N m) (Nat.gcd_dvd_right N m) ht0 hval
  exact hunit

/-- Inertia phases have order dividing `N/gcd(N,m)` at a point of branch multiplicity `m`. -/
theorem squareKummer_inertia_character_pow (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})]
    (g : (w.valuation (SquareKummerField p s c b R)).valuationSubring.inertiaSubgroup
      (FractionRing (SquareConstantField p s)[X])) :
    (((squareKummerAutEquiv p s c b R).symm
      ((g : (w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
        (FractionRing (SquareConstantField p s)[X])) :
          SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
            SquareKummerField p s c b R) : (SquareConstantField p s)ˣ) : SquareConstantField p s) ^
      ((p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) (multiplicity π (kummerBranch c b R))) = 1 := by
  let L := SquareKummerField p s c b R
  let z : L := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  let t : L := algebraMap (SquareConstantField p s)[X] L π
  let m := multiplicity π (kummerBranch c b R)
  let N := p ^ (s + 1) + 1
  let δ := Nat.gcd N m
  let σ : L ≃ₐ[FractionRing (SquareConstantField p s)[X]] L :=
    (g : (w.valuation L).valuationSubring.decompositionSubgroup
      (FractionRing (SquareConstantField p s)[X]))
  let ζ := (squareKummerAutEquiv p s c b R).symm σ
  have hunit : w.valuation L (z ^ (N / δ) / t ^ (m / δ)) = 1 :=
    squareKummerBalancedRoot_valuation_one p s c b R π hπ w
  have hzσ : σ z = algebraMap (SquareConstantField p s) L
      (((ζ : (SquareConstantField p s)ˣ) : SquareConstantField p s)) * z := by
    have h := squareKummerAutEquiv_root p s c b R ζ
    rw [MulEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  have htσ : σ t = t := by
    change σ (algebraMap (SquareConstantField p s)[X] L π) = _
    rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X]) L, σ.commutes]
    rfl
  change (((ζ : (SquareConstantField p s)ˣ) : SquareConstantField p s)) ^ (N / δ) = 1
  apply inertia_unit_character_eq_one (w.valuation L) (algebraMap (SquareConstantField p s) L)
    (fun x hx => heightOne_valuation_constant w x hx) g hunit
  change σ (z ^ (N / δ) / t ^ (m / δ)) = _
  rw [map_div₀, map_pow, map_pow, hzσ, htσ, mul_pow, ← map_pow, mul_div_assoc]

/-- The inertia character bounds ramification by the reduced radical degree. -/
theorem squareKummer_ramification_le_degree_div_gcd (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    (Ideal.span {π}).ramificationIdx' w.asIdeal ≤
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) (multiplicity π (kummerBranch c b R)) := by
  classical
  letI := squareKummer_isGalois p s c b R
  let L := SquareKummerField p s c b R
  let I := (w.valuation L).valuationSubring.inertiaSubgroup
    (FractionRing (SquareConstantField p s)[X])
  let N := p ^ (s + 1) + 1
  let m := multiplicity π (kummerBranch c b R)
  let D := N / Nat.gcd N m
  have hD : 0 < D := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := Nat.div_mul_cancel (Nat.gcd_dvd_left N m)
    change D * Nat.gcd N m = N at h
    rw [hz, zero_mul] at h
    exact Nat.succ_ne_zero (p ^ (s + 1)) h.symm
  let j : I → SquareConstantField p s := fun g =>
    (((squareKummerAutEquiv p s c b R).symm
      ((g : (w.valuation L).valuationSubring.decompositionSubgroup
        (FractionRing (SquareConstantField p s)[X])) : L ≃ₐ[FractionRing (SquareConstantField p s)[X]] L)
          : (SquareConstantField p s)ˣ) : SquareConstantField p s)
  have hj : Function.Injective j := by
    intro g h hgh
    apply Subtype.ext
    apply Subtype.ext
    apply (squareKummerAutEquiv p s c b R).symm.injective
    apply Subtype.ext
    exact Units.ext hgh
  have hmem : ∀ g : I, j g ∈ (Polynomial.nthRoots D (1 : SquareConstantField p s)).toFinset := by
    intro g
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hD]
    exact squareKummer_inertia_character_pow p s c b R π hπ w g
  have hcard : Nat.card I ≤
      Nat.card {x // x ∈ (Polynomial.nthRoots D (1 : SquareConstantField p s)).toFinset} :=
    Nat.card_le_card_of_injective
      (fun g : I => ⟨j g, hmem g⟩) (fun g h hgh => hj (congrArg Subtype.val hgh))
  rw [Nat.card_eq_finsetCard] at hcard
  have hbound : Nat.card I ≤ D := hcard.trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots D 1))
  rw [← squareKummer_inertia_card p s c b R π hπ w]
  exact hbound

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
