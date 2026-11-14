import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchDecomposition

/-!
# Constant radical residues in nonzero Kummer fibers

At a finite place above a rational coordinate, polynomial reduction is
evaluation. The radical is a valuation unit when the defining value
is nonzero. A nonzero constant solution of its power equation forces
the radical residue to be constant, since all covering roots of unity
lie in the constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Every polynomial has its evaluated constant residue above a rational base coordinate. -/
theorem kummerPlaceResidue_polynomial
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    (a : SquareConstantField p s) [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (f : (SquareConstantField p s)[X]) :
    IsLocalRing.residue _ (kummerPlacePolynomialHom p s c b R w f) =
      IsLocalRing.residue _ (kummerPlaceConstantHom p s c b R w (f.eval a)) := by
  let W := (w.valuation (SquareKummerField p s c b R)).valuationSubring
  let φ := (IsLocalRing.residue W).comp (kummerPlacePolynomialHom p s c b R w)
  let ψ := ((IsLocalRing.residue W).comp (kummerPlaceConstantHom p s c b R w)).comp (evalRingHom a)
  have h : φ = ψ := by
    apply Polynomial.ringHom_ext
    · intro x
      change IsLocalRing.residue W (kummerPlacePolynomialHom p s c b R w (C x)) =
        IsLocalRing.residue W (kummerPlaceConstantHom p s c b R w ((C x).eval a))
      rw [eval_C]
      rfl
    · change IsLocalRing.residue W (kummerPlacePolynomialHom p s c b R w X) =
        IsLocalRing.residue W (kummerPlaceConstantHom p s c b R w (X.eval a))
      rw [eval_X]
      exact kummerPlaceResidue_coordinate p s c b R w a
  exact RingHom.congr_fun h f

/-- The radical is a valuation unit above a nonzero value of the defining polynomial. -/
theorem squareKummer_root_valuation_one
    (a : SquareConstantField p s) (ha : (kummerBranch c b R).eval a ≠ 0)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    w.valuation (SquareKummerField p s c b R)
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))) = 1 := by
  let L := SquareKummerField p s c b R
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  let N := p ^ (s + 1) + 1
  have hN : 0 < N := Nat.succ_pos _
  have hp : w.valuation L z ^ N = 1 := by
    rw [← map_pow, kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply]
    exact squareKummer_valuation_of_eval_ne_zero p s c b R a _ ha w
  have h := valuation_balanced_radical (w.valuation L) (z := z) (t := 1)
    (N := N) (m := 0) (g := N) hN (dvd_refl _) (dvd_zero _)
    (by rw [map_one]; exact one_ne_zero) (by simpa only [pow_zero] using hp)
  simpa only [Nat.div_self hN, Nat.zero_div, pow_one, pow_zero, div_one] using h

/-- The radical as an element of the actual finite-place valuation ring. -/
def kummerPlaceRadical
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R)) :
    (w.valuation (SquareKummerField p s c b R)).valuationSubring :=
  ⟨AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))), by
    change w.valuation (SquareKummerField p s c b R)
      (algebraMap (SquareKummerNormalization p s c b R) (SquareKummerField p s c b R)
        (squareKummerIntegralRoot p s c b R)) ≤ 1
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one _⟩

/-- The residue of the radical is constant when the defining value has a nonzero constant root. -/
theorem kummerPlaceRadical_residue_constant
    (a β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    ∃ t : SquareConstantField p s,
      IsLocalRing.residue _ (kummerPlaceConstantHom p s c b R w t) =
        IsLocalRing.residue _ (kummerPlaceRadical p s c b R w) := by
  let W := (w.valuation (SquareKummerField p s c b R)).valuationSubring
  let φ := (IsLocalRing.residue W).comp (kummerPlaceConstantHom p s c b R w)
  let u := kummerPlaceRadical p s c b R w
  have hu : u ^ (p ^ (s + 1) + 1) = kummerPlacePolynomialHom p s c b R w (kummerBranch c b R) := by
    apply Subtype.ext
    exact (kummerBranchField_root_pow c b R (p ^ (s + 1))).trans
      (IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
        (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) _).symm
  have hres := congrArg (IsLocalRing.residue W) hu
  rw [map_pow, kummerPlaceResidue_polynomial p s c b R w a] at hres
  have hp : (IsLocalRing.residue W u) ^ (p ^ (s + 1) + 1) = φ β ^ (p ^ (s + 1) + 1) := by
    rw [← map_pow φ, hpow]
    exact hres
  exact exists_constant_of_power_eq φ (Nat.succ_pos _) (dvd_refl _)
    (squareConstantField_primitiveRoots p s) hβ hp

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
