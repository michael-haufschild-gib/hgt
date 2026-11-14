import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInertia
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRamificationOrders


/-!
# Exact finite ramification of the Kummer normalization

At every irreducible polynomial `π`, the ramification index is
`N/gcd(N,multiplicity π f)`. The inertia character supplies the upper
bound and the radical equation supplies divisibility. Thus all finite
ramification is tame and every prime outside the branch divisor is
unramified. At nonzero prime-power branch points the multiplicity is `R`,
with the characteristic and root conditions discharged in the auxiliary field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The exact ramification index above every irreducible polynomial. -/
theorem squareKummer_finitePlace_ramification
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    (Ideal.span {π}).ramificationIdx' w.asIdeal =
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) (multiplicity π (kummerBranch c b R)) := by
  let v := GaloisForLFunctions.HTGeometry.polyPlace hπ
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {π})
    infer_instance
  apply Nat.le_antisymm (squareKummer_ramification_le_degree_div_gcd p s c b R π hπ w)
  apply Nat.le_of_dvd (squareKummer_ramification_pos p s c b R v w)
  apply RHTower.Sieve.div_gcd_dvd_of_dvd_mul (Nat.succ_pos _)
  have h := squareKummer_ramification_multiplicity_dvd p s c b R v w
  change p ^ (s + 1) + 1 ∣ (Ideal.span {π}).ramificationIdx' w.asIdeal *
    multiplicity (Ideal.span {π}) (Ideal.span {kummerBranch c b R}) at h
  rw [multiplicity_eq_of_emultiplicity_eq Ideal.emultiplicity_eq_emultiplicity_span] at h
  change p ^ (s + 1) + 1 ∣ multiplicity π (kummerBranch c b R) *
    (Ideal.span {π}).ramificationIdx' w.asIdeal
  simpa only [Nat.mul_comm] using h

/-- No prime polynomial outside the branch divisor ramifies. -/
theorem squareKummer_finitePlace_unramified
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (hbranch : ¬ π ∣ kummerBranch c b R)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    (Ideal.span {π}).ramificationIdx' w.asIdeal = 1 := by
  have hm : multiplicity π (kummerBranch c b R) = 0 := multiplicity_eq_zero.mpr hbranch
  rw [squareKummer_finitePlace_ramification p s c b R π hπ w, hm,
    Nat.gcd_zero_right, Nat.div_self (Nat.succ_pos _)]

/-- Every finite ramification index is prime to the characteristic. -/
theorem squareKummer_finitePlace_tame
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    ((Ideal.span {π}).ramificationIdx' w.asIdeal).Coprime p := by
  rw [squareKummer_finitePlace_ramification p s c b R π hπ w]
  have hpow : (p ^ (s + 1) + 1).Coprime (p ^ (s + 1)) :=
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hbase : (p ^ (s + 1) + 1).Coprime p :=
    (Nat.coprime_pow_right_iff (Nat.succ_pos s) _ _).mp hpow
  exact hbase.of_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))

/-- Every finite base place has a prime in the normalization with the exact Kummer index. -/
theorem squareKummer_exists_finitePlace_ramification
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c b R),
      w.asIdeal.LiesOver (Ideal.span {π}) ∧
      (Ideal.span {π}).ramificationIdx' w.asIdeal =
        (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) (multiplicity π (kummerBranch c b R)) := by
  obtain ⟨w, hw⟩ := squareKummer_exists_primeAbove p s c b R
    (GaloisForLFunctions.HTGeometry.polyPlace hπ)
  change w.asIdeal.LiesOver (Ideal.span {π}) at hw
  letI := hw
  exact ⟨w, hw, squareKummer_finitePlace_ramification p s c b R π hπ w⟩

/-- The exact Kummer ramification index at every rational base point. -/
theorem squareKummer_rationalPlace_ramification (a : SquareConstantField p s)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).ramificationIdx' w.asIdeal =
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) ((kummerBranch c b R).rootMultiplicity a) := by
  classical
  have hf : kummerBranch c b R ≠ 0 := by
    intro h
    have hc := congrArg (fun f : (SquareConstantField p s)[X] => f.coeff 1) h
    rw [kummerBranch_coeff_one, coeff_zero] at hc
    exact Units.ne_zero c hc
  rw [rootMultiplicity_eq_multiplicity, if_neg hf]
  exact squareKummer_finitePlace_ramification p s c b R (X - C a) (irreducible_X_sub_C a) w

/-- Every rational base point has an actual place with the exact multiplicity formula. -/
theorem squareKummer_exists_rationalPlace_ramification (a : SquareConstantField p s) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c b R),
      w.asIdeal.LiesOver (Ideal.span {X - C a}) ∧
      (Ideal.span {X - C a}).ramificationIdx' w.asIdeal =
        (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) ((kummerBranch c b R).rootMultiplicity a) := by
  obtain ⟨w, hw⟩ := squareKummer_exists_primeAbove p s c b R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C a))
  change w.asIdeal.LiesOver (Ideal.span {X - C a}) at hw
  letI := hw
  exact ⟨w, hw, squareKummer_rationalPlace_ramification p s c b R a w⟩

/-- No rational place away from the branch divisor ramifies. -/
theorem squareKummer_nonbranch_ramification (a : SquareConstantField p s)
    (ha : (kummerBranch c b R).eval a ≠ 0)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).ramificationIdx' w.asIdeal = 1 := by
  rw [squareKummer_rationalPlace_ramification, rootMultiplicity_eq_zero ha,
    Nat.gcd_zero_right, Nat.div_self (Nat.succ_pos _)]

/-- A nonzero simple root of the branch factor has ramification index `N/gcd(N,R)`. -/
theorem squareKummer_nonzeroBranch_ramification_exact
    (hb : (b + 1 : SquareConstantField p s) ≠ 0) (a : SquareConstantField p s)
    (ha : a ≠ 0) (haroot : a ^ (b + 1) = 1)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (Ideal.span {X - C a}).ramificationIdx' w.asIdeal =
      (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R := by
  rw [squareKummer_rationalPlace_ramification,
    kummerBranch_rootMultiplicity_nonzero c b R hb a ha haroot]

/-- A nonzero prime-power fixed point has branch multiplicity exactly `R`. -/
theorem kummerBranch_primePower_rootMultiplicity (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ) :
    (kummerBranch c (p ^ (d + 1) - 2) R).rootMultiplicity
      ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s) = R := by
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
  apply kummerBranch_rootMultiplicity_nonzero c (p ^ (d + 1) - 2) R hb _ ha
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]
  apply mul_right_cancel₀ ha
  rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p ^ (d + 1))]
  exact (a : KummerAuxiliaryField p s (d + 1)).property

/-- Exact ramification at every nonzero auxiliary-field branch point, with characteristic inputs discharged. -/
theorem squareKummer_primePowerBranch_ramification_exact (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})] :
    (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx'
      w.asIdeal = (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R := by
  rw [squareKummer_rationalPlace_ramification, kummerBranch_primePower_rootMultiplicity]

/-- Every nonzero auxiliary-field branch point has an actual place with the exact ramification index. -/
theorem squareKummer_exists_primePowerBranch_ramification_exact (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R),
      w.asIdeal.LiesOver (Ideal.span
        {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) ∧
      (Ideal.span {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}).ramificationIdx'
        w.asIdeal = (p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) R := by
  obtain ⟨w, hw, he⟩ := squareKummer_exists_rationalPlace_ramification p s c (p ^ (d + 1) - 2) R
    ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)
  rw [kummerBranch_primePower_rootMultiplicity] at he
  exact ⟨w, hw, he⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
