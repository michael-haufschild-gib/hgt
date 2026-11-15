import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalDifferentialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialPrimeParameters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExactRamification

/-!
# Differential orders at all finite Kummer places

At a prime above an irreducible polynomial the base parameter has order
equal to the ramification index, which is tame. Its derivative is a
valuation unit over the finite constant field. The local order of `dy`
is therefore exactly the ramification index minus one, including places
of higher residue degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.HTGeometry

/-- Every finite normalization prime lies above an actual irreducible polynomial prime. -/
theorem squareKummer_finitePlace_liesOver_irreducible
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R)) :
    ∃ f : (SquareConstantField p s)[X], ∃ hf : Irreducible f,
      w.asIdeal.LiesOver (Ideal.span {f}) := by
  let A := (SquareConstantField p s)[X]
  let v : HeightOneSpectrum A :=
    ⟨w.asIdeal.under A, inferInstance, Ideal.under_ne_bot A w.ne_bot⟩
  have hover : w.asIdeal.LiesOver v.asIdeal := inferInstance
  obtain ⟨f, hf, hv⟩ := polynomial_heightOne_exists_irreducible v
  rw [hv] at hover
  exact ⟨f, hf, hover⟩

/-- The rational coordinate differential has order `e-1` at every finite normalization place. -/
theorem squareKummer_finite_derivative_coordinate
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (f : (SquareConstantField p s)[X]) (hf : Irreducible f)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {f})] :
    w.valuation (SquareKummerField p s c b R)
      (squareKummerUniformizerDerivation p s c b R
        (placeUniformizer (SquareKummerField p s c b R) w)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) =
          WithZero.exp (-(((Ideal.span {f}).ramificationIdx' w.asIdeal - 1 : ℕ) : ℤ)) := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let v₀ := polyPlace hf
  let v := w.valuation L
  let π := placeUniformizer L w
  let e := (Ideal.span {f}).ramificationIdx' w.asIdeal
  let D := squareKummerUniformizerDerivation p s c b R π
  letI : w.asIdeal.LiesOver v₀.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {f})
    infer_instance
  have he : 0 < e := squareKummer_ramification_pos p s c b R v₀ w
  have heK : (e : K) ≠ 0 := by
    intro h
    have hd : p ∣ e := (CharP.cast_eq_zero_iff K p e).mp h
    have hg : p ∣ Nat.gcd e p := Nat.dvd_gcd hd (dvd_refl p)
    have hgcd : Nat.gcd e p = 1 := squareKummer_finitePlace_tame p s c b R f hf w
    rw [hgcd] at hg
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hg)
  have hfval : v (algebraMap K[X] L f) = WithZero.exp (-(e : ℤ)) := by
    have h := HeightOneSpectrum.valuation_liesOver L v₀ w (algebraMap K[X] F f)
    rw [polynomial_irreduciblePlace_parameter hf, ← IsScalarTower.algebraMap_apply,
      ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg_one] at h
    exact h.symm
  have hdf : v (algebraMap K[X] L f.derivative) = 1 := by
    have h := HeightOneSpectrum.valuation_liesOver L v₀ w (algebraMap K[X] F f.derivative)
    rw [polynomial_irreduciblePlace_derivative hf, one_pow, ← IsScalarTower.algebraMap_apply] at h
    exact h.symm
  have horder : v (D (algebraMap K[X] L f)) = WithZero.exp (-((e - 1 : ℕ) : ℤ)) :=
    squareKummerUniformizerDerivation_order p s c b R v (heightOne_constants_mem w)
      π (placeUniformizer_valuation L w) _ e he hfval heK
  have hchain : D (algebraMap K[X] L f) =
      algebraMap K[X] L f.derivative * D (algebraMap K[X] L X) := by
    dsimp only [D]
    rw [squareKummerUniformizerDerivation_apply, squareKummerUniformizerDerivation_apply,
      squareKummerCoordinateDerivation_polynomial, squareKummerCoordinateDerivation_polynomial,
      derivative_X, map_one, mul_one, mul_comm]
  rw [hchain, map_mul, hdf, one_mul] at horder
  exact horder

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
