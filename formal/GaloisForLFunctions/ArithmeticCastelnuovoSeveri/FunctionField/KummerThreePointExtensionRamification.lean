import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRamificationOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TotallyRamifiedFiber

/-!
# Ramification after extending three-point constants

The radical equation still forces its fixed degree to divide the ramified
order of the branch polynomial. The simple origin is therefore totally
ramified and rational over every extension of constants. At one, the
reduced degree `M / gcd(M,a)` divides the ramification index.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "F" => FractionRing E[X]

private theorem branch_ne_zero : kummerBranch c 0 a ≠ 0 := by
  intro h
  have hc := congrArg (fun f : E[X] => f.coeff 1) h
  rw [kummerBranch_coeff_one, coeff_zero] at hc
  exact Units.ne_zero c hc

/-- The unchanged covering degree divides ramification times the literal branch multiplicity. -/
theorem primePowerThreePointExtension_ramification_rootMultiplicity_dvd
    (x : E) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    M ∣ (Ideal.span {X - C x}).ramificationIdx' w.asIdeal *
      (kummerBranch c 0 a).rootMultiplicity x := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {X - C x})
    infer_instance
  have h := radical_ramification_log_dvd v w (M - 1 + 1)
    (AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a (M - 1)))
    (algebraMap E[X] F (kummerBranch c 0 a))
    (kummerBranchField_root_pow c 0 a (M - 1))
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v (branch_ne_zero E c a),
    WithZero.log_exp, mul_neg] at h
  have hm : M ∣ v.asIdeal.ramificationIdx' w.asIdeal *
      multiplicity v.asIdeal (Ideal.span {kummerBranch c 0 a}) := by
    have hd : M - 1 + 1 ∣ v.asIdeal.ramificationIdx' w.asIdeal *
        multiplicity v.asIdeal (Ideal.span {kummerBranch c 0 a}) := by
      apply Int.natCast_dvd_natCast.mp
      rw [Nat.cast_mul]
      exact dvd_neg.mp h
    exact (congrArg (fun k : ℕ => k ∣ v.asIdeal.ramificationIdx' w.asIdeal *
      multiplicity v.asIdeal (Ideal.span {kummerBranch c 0 a}))
      (primePowerThreePointExtension_index p d n)).mp hd
  change M ∣ (Ideal.span {X - C x}).ramificationIdx' w.asIdeal *
    multiplicity (Ideal.span {X - C x}) (Ideal.span {kummerBranch c 0 a}) at hm
  rw [rootMultiplicity_eq_multiplicity, if_neg (branch_ne_zero E c a)]
  rwa [multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span] at hm

/-- A prime above a rational point has positive ramification index. -/
theorem primePowerThreePointExtension_ramification_pos
    (x : E) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    0 < (Ideal.span {X - C x}).ramificationIdx' w.asIdeal := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  exact Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

/-- No ramification index exceeds the unchanged field degree. -/
theorem primePowerThreePointExtension_ramification_le_degree
    (x : E) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    (Ideal.span {X - C x}).ramificationIdx' w.asIdeal ≤ M := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : (Ideal.span {X - C x}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : NoZeroSMulDivisors E[X] B := ⟨fun {u z} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hu | hz
    · exact Or.inl ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
        (hu.trans (map_zero _).symm))
    · exact Or.inr hz⟩
  exact (Ideal.ramificationIdx_le_finrank B F L
    (p := Ideal.span {X - C x}) w.asIdeal).trans_eq
    (primePowerThreePointExtension_finrank p d n E c a)

/-- The simple origin is totally ramified over arbitrary extended constants. -/
theorem primePowerThreePointExtension_origin_ramification
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (0 : E)})] :
    (Ideal.span {X - C (0 : E)}).ramificationIdx' w.asIdeal = M := by
  have h := primePowerThreePointExtension_ramification_rootMultiplicity_dvd p d n E c a 0 w
  rw [kummerBranch_rootMultiplicity_origin, mul_one] at h
  exact Nat.le_antisymm
    (primePowerThreePointExtension_ramification_le_degree p d n E c a 0 w)
    (Nat.le_of_dvd (primePowerThreePointExtension_ramification_pos p d n E c a 0 w) h)

/-- At one, cancellation of the branch gcd gives the exact lower divisibility bound. -/
theorem primePowerThreePointExtension_one_ramification_gcd_dvd
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    M / Nat.gcd M a ∣ (Ideal.span {X - C (1 : E)}).ramificationIdx' w.asIdeal := by
  have h := primePowerThreePointExtension_ramification_rootMultiplicity_dvd p d n E c a 1 w
  rw [kummerBranch_rootMultiplicity_nonzero c 0 a (by simp) 1 one_ne_zero (by simp)] at h
  apply RHTower.Sieve.div_gcd_dvd_of_dvd_mul (primePowerKummerCyclicDegree_pos p d n)
  simpa only [Nat.mul_comm a] using h

/-- The entire normalized fiber at the origin consists of one rational prime. -/
theorem primePowerThreePointExtension_origin_singleton :
    ∃ P : Ideal B,
      IsDedekindDomain.primesOverFinset (Ideal.span {X - C (0 : E)}) B = {P} ∧
        (Ideal.span {X - C (0 : E)}).inertiaDeg' P = 1 := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : E))
  apply singleton_primesOver_of_full_ramification F L v
  intro P hP hover
  letI := hP
  letI : P.LiesOver (Ideal.span {X - C (0 : E)}) := hover
  let w : HeightOneSpectrum B := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  exact (primePowerThreePointExtension_origin_ramification p d n E c a w).trans
    (primePowerThreePointExtension_finrank p d n E c a).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
