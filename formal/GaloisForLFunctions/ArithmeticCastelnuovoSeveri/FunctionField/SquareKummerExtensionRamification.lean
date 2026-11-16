import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionInertia
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRamificationOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TotallyRamifiedFiber

/-!
# Exact ramification over enlarged perfect constants

The radical equation forces divisibility by the reduced covering degree.
The inertia character supplies the reverse bound. Thus extending the
constants preserves the exact ramification formula, including unramified
points and the totally ramified simple origin.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (b R : ℕ)
local notation "N" => p ^ (s + 1) + 1
local notation "B" => SquareKummerExtensionNormalization p s E c b R
local notation "L" => SquareKummerExtensionField p s E c b R
local notation "F" => FractionRing E[X]

private theorem branch_ne_zero : kummerBranch c b R ≠ 0 := by
  intro h
  have hc := congrArg (fun f : E[X] => f.coeff 1) h
  rw [kummerBranch_coeff_one, coeff_zero] at hc
  exact Units.ne_zero c hc

/-- Every finite base prime has a prime in the actual enlarged normalization. -/
theorem squareKummerExtension_exists_primeAbove (v : HeightOneSpectrum E[X]) :
    ∃ w : HeightOneSpectrum B, w.asIdeal.LiesOver v.asIdeal := by
  let f := algebraMap E[X] B
  have hf : Function.Injective f := Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have hker : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hf
  obtain ⟨P, _, hP, hunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (⊥ : Ideal B) (by
      rw [← RingHom.ker_eq_comap_bot, hker]
      exact bot_le)
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, ← RingHom.ker_eq_comap_bot, hker] at hunder
    exact v.ne_bot hunder.symm
  exact ⟨⟨P, hP, hP0⟩, (Ideal.liesOver_iff P v.asIdeal).mpr hunder.symm⟩

/-- The radical degree divides ramification times the ideal order of the branch polynomial. -/
theorem squareKummerExtension_ramification_multiplicity_dvd
    (v : HeightOneSpectrum E[X]) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] :
    N ∣ v.asIdeal.ramificationIdx' w.asIdeal *
      multiplicity v.asIdeal (Ideal.span {kummerBranch c b R}) := by
  have h := radical_ramification_log_dvd v w N
    (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))))
    (algebraMap E[X] F (kummerBranch c b R))
    (kummerBranchField_root_pow c b R (p ^ (s + 1)))
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v (branch_ne_zero E c b R),
    WithZero.log_exp, mul_neg] at h
  apply Int.natCast_dvd_natCast.mp
  rw [Nat.cast_mul]
  exact dvd_neg.mp h

/-- Every prime above a finite base prime has positive ramification index. -/
theorem squareKummerExtension_ramification_pos
    (v : HeightOneSpectrum E[X]) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] : 0 < v.asIdeal.ramificationIdx' w.asIdeal :=
  Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

variable [PerfectField E]

/-- The actual ramification index is the covering degree divided by the branch gcd. -/
theorem squareKummerExtension_finitePlace_ramification (π : E[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {π})] :
    (Ideal.span {π}).ramificationIdx' w.asIdeal = N / Nat.gcd N (multiplicity π (kummerBranch c b R)) := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace hπ
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {π})
    infer_instance
  apply Nat.le_antisymm
    (squareKummerExtension_ramification_le_degree_div_gcd p s E c b R π hπ w)
  apply Nat.le_of_dvd (squareKummerExtension_ramification_pos p s E c b R v w)
  apply RHTower.Sieve.div_gcd_dvd_of_dvd_mul (Nat.succ_pos _)
  have h := squareKummerExtension_ramification_multiplicity_dvd p s E c b R v w
  change N ∣ (Ideal.span {π}).ramificationIdx' w.asIdeal *
    multiplicity (Ideal.span {π}) (Ideal.span {kummerBranch c b R}) at h
  rw [multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span] at h
  simpa only [Nat.mul_comm] using h

/-- The exact formula at a rational base point uses ordinary root multiplicity. -/
theorem squareKummerExtension_rationalPlace_ramification (a : E)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).ramificationIdx' w.asIdeal =
      N / Nat.gcd N ((kummerBranch c b R).rootMultiplicity a) := by
  classical
  rw [rootMultiplicity_eq_multiplicity, if_neg (branch_ne_zero E c b R)]
  exact squareKummerExtension_finitePlace_ramification p s E c b R
    (X - C a) (irreducible_X_sub_C a) w

/-- Every rational base point has a place with the exact ramification index. -/
theorem squareKummerExtension_exists_rationalPlace_ramification (a : E) :
    ∃ w : HeightOneSpectrum B,
      w.asIdeal.LiesOver (Ideal.span {X - C a}) ∧
        (Ideal.span {X - C a}).ramificationIdx' w.asIdeal =
          N / Nat.gcd N ((kummerBranch c b R).rootMultiplicity a) := by
  obtain ⟨w, hw⟩ := squareKummerExtension_exists_primeAbove p s E c b R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a))
  change w.asIdeal.LiesOver (Ideal.span {X - C a}) at hw
  letI := hw
  exact ⟨w, hw, squareKummerExtension_rationalPlace_ramification p s E c b R a w⟩

/-- Every rational point outside the branch divisor is unramified. -/
theorem squareKummerExtension_nonbranch_ramification (a : E)
    (ha : (kummerBranch c b R).eval a ≠ 0)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).ramificationIdx' w.asIdeal = 1 := by
  rw [squareKummerExtension_rationalPlace_ramification, rootMultiplicity_eq_zero ha,
    Nat.gcd_zero_right, Nat.div_self (Nat.succ_pos _)]

/-- The simple origin remains totally ramified after any perfect constant extension. -/
theorem squareKummerExtension_origin_ramification (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C (0 : E)})] :
    (Ideal.span {X - C (0 : E)}).ramificationIdx' w.asIdeal = N := by
  rw [squareKummerExtension_rationalPlace_ramification, kummerBranch_rootMultiplicity_origin,
    Nat.gcd_one_right, Nat.div_one]

/-- The normalized fiber at the origin consists of a single rational prime. -/
theorem squareKummerExtension_origin_singleton :
    ∃ P : Ideal B,
      IsDedekindDomain.primesOverFinset (Ideal.span {X - C (0 : E)}) B = {P} ∧
        (Ideal.span {X - C (0 : E)}).inertiaDeg' P = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : E))
  apply singleton_primesOver_of_full_ramification F L v
  intro P hP hover
  letI := hP
  letI : P.LiesOver (Ideal.span {X - C (0 : E)}) := hover
  let w : HeightOneSpectrum B := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  exact (squareKummerExtension_origin_ramification p s E c b R w).trans
    (squareKummerExtension_finrank p s E c b R).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
