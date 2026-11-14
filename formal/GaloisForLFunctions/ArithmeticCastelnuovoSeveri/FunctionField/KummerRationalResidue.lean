import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceResidues
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# Rational residues give constant fiber solutions

The quotient map above a rational linear prime evaluates polynomial
functions at that coordinate. Residue degree one makes every residue
a constant. Reducing the integral radical equation therefore produces
a constant solution of the original affine fiber equation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain

/-- Polynomial reduction above a rational linear ideal is evaluation at that coordinate. -/
theorem linearPrime_quotient_polynomial {K B : Type*} [Field K] [CommRing B]
    [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    (a : K) (P : Ideal B) [P.LiesOver (Ideal.span {X - C a})] (f : K[X]) :
    Ideal.Quotient.mk P (algebraMap K[X] B f) = algebraMap K (B ⧸ P) (f.eval a) := by
  let φ := (Ideal.Quotient.mk P).comp (algebraMap K[X] B)
  let ψ := (algebraMap K (B ⧸ P)).comp (evalRingHom a)
  have hx : φ X = algebraMap K (B ⧸ P) a := by
    have hm := (Ideal.mem_of_liesOver P (Ideal.span {X - C a}) (X - C a)).mp
      (Ideal.mem_span_singleton_self _)
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    change φ (X - C a) = 0 at hz
    rw [map_sub, sub_eq_zero] at hz
    exact hz.trans (IsScalarTower.algebraMap_apply K K[X] (B ⧸ P) a).symm
  have h : φ = ψ := by
    apply Polynomial.ringHom_ext
    · intro x
      change Ideal.Quotient.mk P (algebraMap K[X] B (C x)) =
        algebraMap K (B ⧸ P) ((C x).eval a)
      rw [eval_C]
      exact (IsScalarTower.algebraMap_apply K K[X] (B ⧸ P) x).symm
    · change φ X = algebraMap K (B ⧸ P) (X.eval a)
      rw [eval_X]
      exact hx
  exact RingHom.congr_fun h f

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- A residue-degree-one prime above a rational coordinate has only constant residues. -/
theorem squareKummer_rational_residue_surjective
    (a : SquareConstantField p s)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (hf : (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1) :
    Function.Surjective (algebraMap (SquareConstantField p s)
      (SquareKummerNormalization p s c b R ⧸ w.asIdeal)) := by
  let K := SquareConstantField p s
  let B := SquareKummerNormalization p s c b R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI := Ideal.Quotient.field (Ideal.span {X - C a})
  letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hf
  have hsurj := (bijective_algebraMap_of_linearEquiv e).surjective
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  let e0 := Polynomial.quotientSpanXSubCAlgEquiv a
  have hbase : algebraMap K (K[X] ⧸ Ideal.span {X - C a}) (e0 y) = y := by
    apply e0.injective
    rw [e0.commutes]
    rfl
  refine ⟨e0 y, ?_⟩
  calc
    algebraMap K (B ⧸ w.asIdeal) (e0 y) =
        algebraMap (K[X] ⧸ Ideal.span {X - C a}) (B ⧸ w.asIdeal)
          (algebraMap K (K[X] ⧸ Ideal.span {X - C a}) (e0 y)) := by
      rw [IsScalarTower.algebraMap_apply K K[X] (B ⧸ w.asIdeal),
        IsScalarTower.algebraMap_apply K[X] (K[X] ⧸ Ideal.span {X - C a}) (B ⧸ w.asIdeal),
        ← IsScalarTower.algebraMap_apply K K[X] (K[X] ⧸ Ideal.span {X - C a})]
    _ = x := by rw [hbase, hy]

/-- Every rational normalization prime gives a constant solution of the defining fiber equation. -/
theorem squareKummer_rationalPlace_has_root
    (a : SquareConstantField p s)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})]
    (hf : (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1) :
    ∃ β : SquareConstantField p s, β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a := by
  let B := SquareKummerNormalization p s c b R
  letI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  obtain ⟨β, hβ⟩ := squareKummer_rational_residue_surjective p s c b R a w hf
    (Ideal.Quotient.mk w.asIdeal (squareKummerIntegralRoot p s c b R))
  refine ⟨β, (algebraMap (SquareConstantField p s) (B ⧸ w.asIdeal)).injective ?_⟩
  rw [map_pow, hβ, ← map_pow, squareKummerIntegralRoot_pow,
    linearPrime_quotient_polynomial a w.asIdeal]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
