import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalDerivation

/-!
# The exact differential kernel in a Kummer function field

The Frobenius subfield has prime index. Every element outside it
therefore generates the whole field. A derivation that kills such an
element would kill the field, contradicting its value on the rational
coordinate. Thus vanishing differential is exactly being a `p`th power.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Every element outside the Frobenius subfield generates the entire Kummer field over it. -/
theorem squareKummer_frobenius_adjoin_of_notMem
    (x : SquareKummerField p s c b R) (hx : x ∉ SquareKummerFrobeniusField p s c b R) :
    (SquareKummerFrobeniusField p s c b R)⟮x⟯ = ⊤ := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  have hd : Module.finrank P P⟮x⟯ = p := frobeniusPowerField_adjoin_finrank K L p x hx
  letI : FiniteDimensional P L := squareKummer_frobenius_finiteDimensional p s c b R
  have hdim : Module.finrank P P⟮x⟯ = Module.finrank P L :=
    hd.trans (squareKummer_frobenius_finrank p s c b R).symm
  have htop : P⟮x⟯.toSubalgebra.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hdim
  apply top_unique
  intro y _
  have hy : y ∈ P⟮x⟯.toSubalgebra.toSubmodule := by rw [htop]; trivial
  exact hy

/-- The coordinate derivation vanishes precisely on the actual Frobenius subfield. -/
theorem squareKummerCoordinateDerivation_eq_zero_iff
    (x : SquareKummerField p s c b R) :
    squareKummerCoordinateDerivation p s c b R x = 0 ↔
      x ∈ SquareKummerFrobeniusField p s c b R := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  let D := squareKummerCoordinateDerivation p s c b R
  constructor
  · intro hx
    by_contra hnot
    have htop := squareKummer_frobenius_adjoin_of_notMem p s c b R x hnot
    have hbase (a : P) : D (algebraMap P L a) = 0 := by
      obtain ⟨u, hu⟩ := a.property
      change D a.val = 0
      rw [← hu]
      exact derivation_frobenius_power_eq_zero p D u
    have hzero (z : L) (hz : z ∈ P⟮x⟯) : D z = 0 := by
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
          rw [Set.mem_singleton_iff.mp hz]
          exact hx
      | algebraMap a => exact hbase a
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | mul a b _ _ ha hb => rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      | inv a _ ha =>
          by_cases ha0 : a = 0
          · rw [ha0, inv_zero, map_zero]
          · rw [D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha0), ha, smul_zero]
    have hy : algebraMap K[X] L X ∈ P⟮x⟯ := by rw [htop]; trivial
    have hone : D (algebraMap K[X] L X) = 1 := by
      rw [squareKummerCoordinateDerivation_polynomial, derivative_X, map_one]
    exact one_ne_zero (hone.symm.trans (hzero _ hy))
  · rintro ⟨u, hu⟩
    change u ^ p = x at hu
    rw [← hu]
    exact derivation_frobenius_power_eq_zero p D u

/-- A function has zero Kähler differential exactly when it is a `p`th power in the same field. -/
theorem squareKummer_differential_eq_zero_iff
    (x : SquareKummerField p s c b R) :
    KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) x = 0 ↔
      ∃ y : SquareKummerField p s c b R, y ^ p = x := by
  have he : KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R) x = 0 ↔
      squareKummerCoordinateDerivation p s c b R x = 0 := by
    rw [squareKummerCoordinateDerivation_apply]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (squareKummerDifferentialEquiv p s c b R).injective
      simpa only [map_zero] using h
  rw [he, squareKummerCoordinateDerivation_eq_zero_iff]
  rfl

/-- A differential-zero normalization element has its Frobenius root in the same normalization. -/
theorem squareKummer_normalization_differential_eq_zero_iff
    (x : SquareKummerNormalization p s c b R) :
    KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
      (x : SquareKummerField p s c b R) = 0 ↔
      ∃ y : SquareKummerNormalization p s c b R, y ^ p = x := by
  rw [squareKummer_differential_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hyint : IsIntegral (SquareConstantField p s)[X] y := by
      apply IsIntegral.of_pow (Fact.out : p.Prime).pos
      rw [hy]
      exact x.property
    refine ⟨⟨y, hyint⟩, Subtype.ext ?_⟩
    exact hy
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
