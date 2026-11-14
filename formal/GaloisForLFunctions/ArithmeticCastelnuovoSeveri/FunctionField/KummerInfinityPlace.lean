import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TotallyRamifiedFiber

/-!
# The unique rational point at infinity

For the prime-power Kummer family, full ramification and the fundamental
degree identity leave exactly one prime above the reciprocal origin.
Its residue degree is one; evaluation at the base origin identifies its
residue field with the specified constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

private theorem infinity_prime_ne_bot
    (P : Ideal (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))
    [P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] : P ≠ ⊥ := by
  let f := algebraMap (SquareConstantField p s)[X]
    (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
  have hf : Function.Injective f := Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have hx : f X ∈ P := (Ideal.mem_of_liesOver P _ X).mp (Ideal.mem_span_singleton_self _)
  intro h
  have hzero : f X = 0 := by simpa only [h, Ideal.mem_bot] using hx
  exact X_ne_zero (hf (hzero.trans (map_zero f).symm))

private theorem squareKummerInfinity_singleton :
    ∃ P : Ideal (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)),
      IsDedekindDomain.primesOverFinset (Ideal.span {(X : (SquareConstantField p s)[X])})
        (SquareKummerInfinityNormalization p s c
          (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) = {P} ∧
      (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg' P = 1 := by
  apply singleton_primesOver_of_full_ramification
    (FractionRing (SquareConstantField p s)[X])
    (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))
    (kummerInfinityBasePlace (K := SquareConstantField p s))
  intro P hP hOver
  letI := hP
  letI : P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])}) := hOver
  rw [kummerInfinityField_finrank]
  exact squareKummerInfinity_primePower_ramification p s c d r
    ⟨P, hP, infinity_prime_ne_bot p s c d r P⟩

/-- The normalized prime-power cover has exactly one place at infinity. -/
theorem squareKummerInfinity_unique :
    ∃! P : Ideal (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)),
      P.IsPrime ∧ P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])}) := by
  classical
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal :=
    ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isMaximal
      (mt Ideal.span_singleton_eq_bot.mp X_ne_zero)
  have hv0 : (Ideal.span {(X : (SquareConstantField p s)[X])}) ≠ ⊥ :=
    (kummerInfinityBasePlace (K := SquareConstantField p s)).ne_bot
  obtain ⟨P, hP, _⟩ := squareKummerInfinity_singleton p s c d r
  have hm : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(X : (SquareConstantField p s)[X])})
      (SquareKummerInfinityNormalization p s c
        (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) := by
    rw [hP]
    exact Finset.mem_singleton_self _
  refine ⟨P, (IsDedekindDomain.mem_primesOverFinset_iff hv0 _).mp hm, ?_⟩
  intro Q hQ
  have hQm := (IsDedekindDomain.mem_primesOverFinset_iff hv0 _).mpr hQ
  rw [hP, Finset.mem_singleton] at hQm
  exact hQm

/-- The unique place at infinity has residue degree one. -/
theorem squareKummerInfinity_inertia
    (P : Ideal (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) [hP : P.IsPrime]
    [P.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg' P = 1 := by
  classical
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal :=
    ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isMaximal
      (mt Ideal.span_singleton_eq_bot.mp X_ne_zero)
  obtain ⟨Q, hQ, hf⟩ := squareKummerInfinity_singleton p s c d r
  have hm := (IsDedekindDomain.mem_primesOverFinset_iff
    (show (Ideal.span {(X : (SquareConstantField p s)[X])}) ≠ ⊥ from
      (kummerInfinityBasePlace (K := SquareConstantField p s)).ne_bot)
    (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))).mpr ⟨hP, inferInstance⟩
  rw [hQ, Finset.mem_singleton] at hm
  exact hm.symm ▸ hf

/-- The unique prime at infinity in the normalized reciprocal chart. -/
def squareKummerInfinityIdeal : Ideal (SquareKummerInfinityNormalization p s c
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  (squareKummerInfinity_unique p s c d r).choose

/-- The chosen infinity ideal is prime. -/
instance squareKummerInfinityIdeal_prime : (squareKummerInfinityIdeal p s c d r).IsPrime :=
  (squareKummerInfinity_unique p s c d r).choose_spec.1.1

/-- The infinity ideal lies above the reciprocal origin. -/
instance squareKummerInfinityIdeal_liesOver :
    (squareKummerInfinityIdeal p s c d r).LiesOver
      (Ideal.span {(X : (SquareConstantField p s)[X])}) :=
  (squareKummerInfinity_unique p s c d r).choose_spec.1.2

/-- The chosen infinity prime is nonzero. -/
theorem squareKummerInfinityIdeal_ne_bot : squareKummerInfinityIdeal p s c d r ≠ ⊥ :=
  infinity_prime_ne_bot p s c d r _

/-- The nonzero infinity prime is maximal. -/
instance squareKummerInfinityIdeal_maximal : (squareKummerInfinityIdeal p s c d r).IsMaximal :=
  (squareKummerInfinityIdeal_prime p s c d r).isMaximal
    (squareKummerInfinityIdeal_ne_bot p s c d r)

/-- Infinity as an actual height-one place of the reciprocal normalization. -/
def squareKummerInfinityPlace : HeightOneSpectrum (SquareKummerInfinityNormalization p s c
    (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) :=
  ⟨squareKummerInfinityIdeal p s c d r, inferInstance, squareKummerInfinityIdeal_ne_bot p s c d r⟩

/-- The named infinity place contracts to the reciprocal origin. -/
instance squareKummerInfinityPlace_liesOver :
    (squareKummerInfinityPlace p s c d r).asIdeal.LiesOver
      (Ideal.span {(X : (SquareConstantField p s)[X])}) :=
  squareKummerInfinityIdeal_liesOver p s c d r

/-- The canonical place at infinity has ramification index `Q+1`. -/
theorem squareKummerInfinityPlace_ramification :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx'
      (squareKummerInfinityPlace p s c d r).asIdeal = p ^ (s + 1) + 1 :=
  squareKummerInfinity_primePower_ramification p s c d r _

/-- The canonical place at infinity has residue degree one. -/
theorem squareKummerInfinityPlace_inertia :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).inertiaDeg'
      (squareKummerInfinityPlace p s c d r).asIdeal = 1 :=
  squareKummerInfinity_inertia p s c d r _

/-- Every residue at infinity is represented by a constant. -/
theorem squareKummerInfinity_residue_surjective : Function.Surjective
    (algebraMap (SquareConstantField p s)
      (SquareKummerInfinityNormalization p s c (p ^ (d + 1) - 2)
        (kummerExponent (p ^ (d + 1)) r) ⧸ squareKummerInfinityIdeal p s c d r)) := by
  letI : (Ideal.span {(X : (SquareConstantField p s)[X])}).IsMaximal :=
    ((Ideal.span_singleton_prime X_ne_zero).mpr prime_X).isMaximal
      (mt Ideal.span_singleton_eq_bot.mp X_ne_zero)
  letI := Ideal.Quotient.field (Ideal.span {(X : (SquareConstantField p s)[X])})
  have hdim := squareKummerInfinity_inertia p s c d r (squareKummerInfinityIdeal p s c d r)
  rw [Ideal.inertiaDeg'_algebraMap] at hdim
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hdim
  have hsurj := (bijective_algebraMap_of_linearEquiv e).surjective
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  let e0 : ((SquareConstantField p s)[X] ⧸ Ideal.span {(X : (SquareConstantField p s)[X])})
      ≃ₐ[SquareConstantField p s] SquareConstantField p s :=
    (Ideal.quotientEquivAlgOfEq (SquareConstantField p s)
      (show Ideal.span {(X : (SquareConstantField p s)[X])} =
        Ideal.span {X - C (0 : SquareConstantField p s)} by rw [map_zero, sub_zero])).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : SquareConstantField p s))
  have hbase : algebraMap (SquareConstantField p s)
      ((SquareConstantField p s)[X] ⧸ Ideal.span {(X : (SquareConstantField p s)[X])}) (e0 y) = y := by
    apply e0.injective
    rw [e0.commutes]
    rfl
  refine ⟨e0 y, ?_⟩
  rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)
    ((SquareConstantField p s)[X] ⧸ Ideal.span {(X : (SquareConstantField p s)[X])}), hbase, hy]

/-- The unique point at infinity is rational over the stated constant field. -/
def squareKummerInfinityResidueEquiv :
    (SquareKummerInfinityNormalization p s c (p ^ (d + 1) - 2)
      (kummerExponent (p ^ (d + 1)) r) ⧸ squareKummerInfinityIdeal p s c d r)
      ≃ₐ[SquareConstantField p s] SquareConstantField p s :=
  (AlgEquiv.ofBijective (Algebra.ofId _ _)
    ⟨(algebraMap (SquareConstantField p s) _).injective,
      squareKummerInfinity_residue_surjective p s c d r⟩).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
