import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RadicalRamification
import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import GaloisForLFunctions.HTGeometry.RationalOrderComposition
import Mathlib.FieldTheory.Separable
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterFields
import GaloisForLFunctions.RHTower.Sieve.PrimeBlockPowerCofactorMeanSquare

/-!
# Finite branch orders and Kummer ramification

The radical equation implies `N ∣ e·m`, where `m` is the order of the
branch polynomial and `e` is the actual ramification index in its
Dedekind normalization. At a nonzero `q`-fixed branch point the order is
`R`, so `N/gcd(N,R)` divides `e`; the field degree bounds `e` above by `N`.
The characteristic condition is discharged for every prime power `q`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open scoped Classical

/-- The simple zero coefficient ensures that the branch polynomial is nonzero. -/
private theorem kummerBranch_ne_zero {K : Type*} [Field K] (c : Kˣ) (b R : ℕ) :
    kummerBranch c b R ≠ 0 := by
  intro h
  have hc := congrArg (fun f : K[X] => f.coeff 1) h
  rw [kummerBranch_coeff_one, coeff_zero] at hc
  exact Units.ne_zero c hc

variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The covering degree divides the ramified ideal order of the branch polynomial. -/
theorem squareKummer_ramification_multiplicity_dvd
    (v : HeightOneSpectrum (SquareConstantField p s)[X])
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver v.asIdeal] :
    p ^ (s + 1) + 1 ∣ v.asIdeal.ramificationIdx' w.asIdeal *
      multiplicity v.asIdeal (Ideal.span {kummerBranch c b R}) := by
  have h := radical_ramification_log_dvd v w (p ^ (s + 1) + 1)
    (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))))
    (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
      (kummerBranch c b R)) (kummerBranchField_root_pow c b R (p ^ (s + 1)))
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v (kummerBranch_ne_zero c b R),
    WithZero.log_exp, mul_neg] at h
  apply Int.natCast_dvd_natCast.mp
  rw [Nat.cast_mul]
  exact dvd_neg.mp h


/-- At a rational base point, ideal order is polynomial root multiplicity. -/
theorem squareKummer_ramification_rootMultiplicity_dvd
    (a : SquareConstantField p s)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    p ^ (s + 1) + 1 ∣ (Ideal.span {X - C a}).ramificationIdx' w.asIdeal *
      (kummerBranch c b R).rootMultiplicity a := by
  classical
  letI : w.asIdeal.LiesOver
      (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)).asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C a})
    infer_instance
  have h := squareKummer_ramification_multiplicity_dvd p s c b R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)) w
  change p ^ (s + 1) + 1 ∣ (Ideal.span {X - C a}).ramificationIdx' w.asIdeal *
    multiplicity (Ideal.span {X - C a}) (Ideal.span {kummerBranch c b R}) at h
  rw [rootMultiplicity_eq_multiplicity, if_neg (kummerBranch_ne_zero c b R)]
  rwa [multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span] at h


/-- Every nonzero simple root of the branch factor has multiplicity exactly `R`. -/
theorem kummerBranch_rootMultiplicity_nonzero {K : Type*} [Field K]
    (c : Kˣ) (b R : ℕ) (hb : (b + 1 : K) ≠ 0) (a : K) (ha : a ≠ 0)
    (haroot : a ^ (b + 1) = 1) : (kummerBranch c b R).rootMultiplicity a = R := by
  have hg : (X ^ (b + 1) - C (1 : K)) ≠ 0 :=
    (monic_X_pow_sub_C (1 : K) (Nat.succ_ne_zero b)).ne_zero
  have hm : rootMultiplicity a (X ^ (b + 1) - C (1 : K)) = 1 := by
    apply Nat.le_antisymm
    · exact rootMultiplicity_le_one_of_separable
        (separable_X_pow_sub_C 1 (by simpa only [Nat.cast_add, Nat.cast_one] using hb) one_ne_zero) a
    · apply (rootMultiplicity_pos hg).mpr
      simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, haroot, sub_self]
  have he : (1 - X ^ (b + 1) : K[X]) = C (-1) * (X ^ (b + 1) - C 1) := by
    rw [map_neg, map_one]
    ring
  have hf : (1 - X ^ (b + 1) : K[X]) ≠ 0 := by
    rw [he]
    exact mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)) hg
  have hmf : rootMultiplicity a (1 - X ^ (b + 1) : K[X]) = 1 := by
    rw [he, rootMultiplicity_mul (by rw [← he]; exact hf), rootMultiplicity_C, zero_add, hm]
  rw [kummerBranch, rootMultiplicity_mul (kummerBranch_ne_zero c b R),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (Units.ne_zero c)) X_ne_zero),
    rootMultiplicity_C, rootMultiplicity_eq_zero (show ¬ (X : K[X]).IsRoot a from by simpa only [IsRoot, eval_X] using ha),
    zero_add, zero_add, GaloisForLFunctions.HTGeometry.rootMultiplicity_pow hf, hmf, mul_one]

/-- At a nonzero simple branch root, `N` divides the ramification index times `R`. -/
theorem squareKummer_nonzeroBranch_ramification_dvd
    (hb : (b + 1 : SquareConstantField p s) ≠ 0) (a : SquareConstantField p s)
    (ha : a ≠ 0) (haroot : a ^ (b + 1) = 1)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    p ^ (s + 1) + 1 ∣ (Ideal.span {X - C a}).ramificationIdx' w.asIdeal * R := by
  have h := squareKummer_ramification_rootMultiplicity_dvd p s c b R a w
  rwa [kummerBranch_rootMultiplicity_nonzero c b R hb a ha haroot] at h


/-- Cancelling the gcd forces `N/gcd(N,R)` to divide the ramification index. -/
theorem squareKummer_nonzeroBranch_ramification_gcd_dvd
    (hb : (b + 1 : SquareConstantField p s) ≠ 0) (a : SquareConstantField p s)
    (ha : a ≠ 0) (haroot : a ^ (b + 1) = 1)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R ∣
      (Ideal.span {X - C a}).ramificationIdx' w.asIdeal := by
  apply RHTower.Sieve.div_gcd_dvd_of_dvd_mul (Nat.succ_pos _)
  simpa only [Nat.mul_comm R] using
    squareKummer_nonzeroBranch_ramification_dvd p s c b R hb a ha haroot w

/-- The gcd divisibility holds at every nonzero auxiliary-field branch point. -/
theorem squareKummer_primePowerBranch_ramification_gcd_dvd (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})] :
    (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R ∣
      (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have hcast : (p ^ (d + 1) : SquareConstantField p s) = 0 := by
    rw [CharP.cast_eq_zero (SquareConstantField p s) p, zero_pow (Nat.succ_ne_zero d)]
  have hb : ((p ^ (d + 1) - 2 : ℕ) : SquareConstantField p s) + 1 ≠ 0 := by
    have hs := congrArg (fun n : ℕ => (n : SquareConstantField p s))
      (show p ^ (d + 1) - 2 + 1 + 1 = p ^ (d + 1) by omega)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hs
    rw [hcast] at hs
    intro h
    rw [h, zero_add] at hs
    exact one_ne_zero hs
  have ha : ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s) ≠ 0 := by
    intro h
    exact Units.ne_zero a (Subtype.ext h)
  apply squareKummer_nonzeroBranch_ramification_gcd_dvd p s c (p ^ (d + 1) - 2) R hb _ ha
    (w := w)
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]
  apply mul_right_cancel₀ ha
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p ^ (d + 1))]
  exact (a : KummerAuxiliaryField p s (d + 1)).property


/-- The branch divisor is the sum of the simple origin and `R` times the other factor. -/
theorem kummerBranch_rootMultiplicity_formula {K : Type*} [Field K]
    (c : Kˣ) (b R : ℕ) (a : K) :
    (kummerBranch c b R).rootMultiplicity a = (if a = 0 then 1 else 0) +
      R * rootMultiplicity a (1 - X ^ (b + 1) : K[X]) := by
  classical
  have hf : (1 - X ^ (b + 1) : K[X]) ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval 0) h
    have hz : (1 : K) = 0 := by
      simpa only [eval_sub, eval_one, eval_pow, eval_X,
        zero_pow (Nat.succ_ne_zero b), sub_zero, eval_zero] using he
    exact one_ne_zero hz
  have hx : rootMultiplicity a (X : K[X]) = if a = 0 then 1 else 0 := by
    simpa only [map_zero, sub_zero] using (rootMultiplicity_X_sub_C (x := a) (y := (0 : K)))
  rw [kummerBranch, rootMultiplicity_mul (kummerBranch_ne_zero c b R),
    rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr (Units.ne_zero c)) X_ne_zero),
    rootMultiplicity_C, zero_add, hx, GaloisForLFunctions.HTGeometry.rootMultiplicity_pow hf]

/-- The origin has branch multiplicity one for all parameters. -/
theorem kummerBranch_rootMultiplicity_origin {K : Type*} [Field K]
    (c : Kˣ) (b R : ℕ) : (kummerBranch c b R).rootMultiplicity 0 = 1 := by
  rw [kummerBranch_rootMultiplicity_formula, if_pos rfl,
    rootMultiplicity_eq_zero (by simp [IsRoot]), mul_zero, add_zero]

/-- Every prime above a nonzero base prime has positive ramification index. -/
theorem squareKummer_ramification_pos
    (v : HeightOneSpectrum (SquareConstantField p s)[X])
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver v.asIdeal] : 0 < v.asIdeal.ramificationIdx' w.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    w.asIdeal v.ne_bot)

/-- The ramification index cannot exceed the covering degree. -/
theorem squareKummer_ramification_le_degree
    (v : HeightOneSpectrum (SquareConstantField p s)[X])
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver v.asIdeal] : v.asIdeal.ramificationIdx' w.asIdeal ≤ p ^ (s + 1) + 1 := by
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : NoZeroSMulDivisors (SquareConstantField p s)[X]
      (SquareKummerNormalization p s c b R) := ⟨fun {a x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with ha | hx
    · exact Or.inl ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
        (ha.trans (map_zero _).symm))
    · exact Or.inr hx⟩
  have h := Ideal.ramificationIdx_le_finrank (SquareKummerNormalization p s c b R)
    (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R) (p := v.asIdeal) w.asIdeal
  exact h.trans_eq (kummerBranchField_finrank c b R _)


/-- At a nonzero prime-power branch point the ramification index lies between `N/gcd(N,R)` and `N`. -/
theorem squareKummer_primePowerBranch_ramification_bounds (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})] :
    (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R ≤
      (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal ∧
    (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal ≤
      p ^ (s + 1) + 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace
    (irreducible_X_sub_C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s))
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})
    infer_instance
  exact ⟨Nat.le_of_dvd (squareKummer_ramification_pos p s c (p ^ (d + 1) - 2) R v w)
    (squareKummer_primePowerBranch_ramification_gcd_dvd p s c R d a w),
    squareKummer_ramification_le_degree p s c (p ^ (d + 1) - 2) R v w⟩

/-- Every nonzero auxiliary-field branch point has an actual prime above it with the stated gcd divisibility and degree bounds. -/
theorem squareKummer_exists_primePowerBranch (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R),
      w.asIdeal.LiesOver (Ideal.span
        {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) ∧
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R ∣
        (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal ∧
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R ≤
        (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal ∧
      (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx' w.asIdeal ≤
        p ^ (s + 1) + 1 := by
  obtain ⟨w, hw⟩ := squareKummer_exists_primeAbove p s c (p ^ (d + 1) - 2) R
    (GaloisForLFunctions.HTGeometry.polyPlace
      (irreducible_X_sub_C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)))
  change w.asIdeal.LiesOver (Ideal.span
    {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) at hw
  letI := hw
  exact ⟨w, hw, squareKummer_primePowerBranch_ramification_gcd_dvd p s c R d a w,
    squareKummer_primePowerBranch_ramification_bounds p s c R d a w⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
