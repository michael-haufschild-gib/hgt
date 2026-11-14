import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerUnramifiedDecomposition
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalResidue


/-!
# Rationality and complete splitting of nonzero Kummer fibers

The decomposition group is trivial when the defining value has a nonzero
constant radical root. The degree identity then gives `Q+1` distinct
normalization primes. Conversely a rational residue field supplies a
constant root, so rationality is equivalent to the norm-solubility criterion.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- A nonzero soluble fiber splits into exactly the covering degree many normalization primes. -/
theorem squareKummer_unramified_split_primes_card
    (a β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {X - C a})
      (SquareKummerNormalization p s c b R)).card = p ^ (s + 1) + 1 := by
  classical
  let B := SquareKummerNormalization p s c b R
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a)
  letI : (Ideal.span {X - C a}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C a}) ≠ ⊥ := v.ne_bot
  have ha : (kummerBranch c b R).eval a ≠ 0 := by
    rw [← hpow]
    exact pow_ne_zero _ hβ
  have hsum := Ideal.sum_ramification_inertia B (FractionRing (SquareConstantField p s)[X])
    (SquareKummerField p s c b R) hv0
  rw [kummerBranchField_finrank] at hsum
  rw [Finset.card_eq_sum_ones]
  refine (Finset.sum_congr rfl fun P hP => ?_).trans hsum
  obtain ⟨hprime, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
  letI := hprime
  letI := hover
  let w : HeightOneSpectrum B := ⟨P, hprime, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
  have he := squareKummer_nonbranch_ramification p s c b R a ha w
  have hf := squareKummer_unramified_split_inertia p s c b R a β hβ hpow w
  change (Ideal.span {X - C a}).ramificationIdx' P = 1 at he
  change (Ideal.span {X - C a}).inertiaDeg' P = 1 at hf
  rw [he, hf, one_mul]

/-- Above a nonzero defining value, rationality of any normalization prime is equivalent to solubility of the fiber. -/
theorem squareKummer_nonzero_fiber_rational_iff
    (a : SquareConstantField p s) (ha : (kummerBranch c b R).eval a ≠ 0)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1 ↔
      ∃ β : SquareConstantField p s, β ^ (p ^ (s + 1) + 1) = (kummerBranch c b R).eval a := by
  constructor
  · exact squareKummer_rationalPlace_has_root p s c b R a w
  · rintro ⟨β, hβ⟩
    have hβ0 : β ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.succ_ne_zero _)] at hβ
      exact ha hβ.symm
    exact squareKummer_unramified_split_inertia p s c b R a β hβ0 hβ w

/-- A nonzero fiber is rational exactly when its defining value is fixed by the square-field involution. -/
theorem squareKummer_nonzero_fiber_rational_iff_fixed
    (a : SquareConstantField p s) (ha : (kummerBranch c b R).eval a ≠ 0)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).inertiaDeg' w.asIdeal = 1 ↔
      ((kummerBranch c b R).eval a) ^ p ^ (s + 1) = (kummerBranch c b R).eval a := by
  rw [squareKummer_nonzero_fiber_rational_iff p s c b R a ha w,
    squareConstantField_exists_norm_iff]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
