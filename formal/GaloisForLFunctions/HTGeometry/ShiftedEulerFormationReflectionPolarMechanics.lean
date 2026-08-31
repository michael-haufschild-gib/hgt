import GaloisForLFunctions.HTGeometry.FormationReflectionPolarMechanics

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Prime logarithm realizes the universal generator weight. -/
def primeLogFormationWeight (p : ℕ) : ℝ := Real.log p

/-- Prime factorization realizes an integer as a finite free-commutative formation profile. -/
def integerFormationProfile (n : ℕ) : ℕ →₀ ℕ := n.factorization

theorem integerFormationProfile_support (n : ℕ) :
    (integerFormationProfile n).support = n.primeFactors := by
  exact Nat.support_factorization n

theorem primeLogFormationWeight_pos_of_mem (n : ℕ) {p : ℕ}
    (hp : p ∈ (integerFormationProfile n).support) :
    0 < primeLogFormationWeight p := by
  rw [integerFormationProfile_support] at hp
  exact Real.log_pos (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt)

theorem formationSupportWeight_integerFormationProfile (n : ℕ) :
    formationSupportWeight primeLogFormationWeight (integerFormationProfile n) =
      ∑ p ∈ n.primeFactors, Real.log p := by
  rw [formationSupportWeight, integerFormationProfile_support]
  rfl

theorem formationTotalWeight_integerFormationProfile {n : ℕ} (hn : n ≠ 0) :
    formationTotalWeight primeLogFormationWeight (integerFormationProfile n) = Real.log n := by
  rw [formationTotalWeight, integerFormationProfile_support]
  calc
    (∑ p ∈ n.primeFactors,
        ((integerFormationProfile n p : ℕ) : ℝ) * primeLogFormationWeight p) =
      ∑ p ∈ n.primeFactors, Real.log ((p : ℝ) ^ n.factorization p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Real.log_pow]
        rfl
    _ = Real.log (∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p)) := by
        rw [Real.log_prod]
        intro p hp
        have hp0 : (p : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        exact pow_ne_zero _ hp0
    _ = Real.log n := by
        congr 1
        exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm

/-- Aggregate logarithmic multiplicity beyond the squarefree radical. -/
def shiftedEulerValuationDefect (n : ℕ) : ℝ :=
  Real.log n - ∑ p ∈ n.primeFactors, Real.log p

theorem formationMultiplicityDefect_integerFormationProfile {n : ℕ} (hn : n ≠ 0) :
    formationMultiplicityDefect primeLogFormationWeight (integerFormationProfile n) =
      shiftedEulerValuationDefect n := by
  rw [formationMultiplicityDefect, formationTotalWeight_integerFormationProfile hn,
    formationSupportWeight_integerFormationProfile, shiftedEulerValuationDefect]

/-- Squarefree radical: one copy of every occupied prime. -/
def shiftedEulerSquarefreeRadical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

theorem shiftedEulerSquarefreeRadical_pos (n : ℕ) :
    0 < shiftedEulerSquarefreeRadical n := by
  rw [shiftedEulerSquarefreeRadical]
  exact Finset.prod_pos fun p hp => Nat.pos_of_mem_primeFactors hp

theorem shiftedEulerSquarefreeRadical_dvd (n : ℕ) :
    shiftedEulerSquarefreeRadical n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

theorem shiftedEulerSquarefreeRadical_squarefree (n : ℕ) :
    Squarefree (shiftedEulerSquarefreeRadical n) := by
  rw [shiftedEulerSquarefreeRadical]
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · rintro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

theorem shiftedEulerSquarefreeRadical_eq_iff (n : ℕ) :
    shiftedEulerSquarefreeRadical n = n ↔ Squarefree n := by
  constructor
  · intro h
    rw [← h]
    exact shiftedEulerSquarefreeRadical_squarefree n
  · intro h
    exact Nat.prod_primeFactors_of_squarefree h

theorem log_shiftedEulerSquarefreeRadical (n : ℕ) :
    Real.log (shiftedEulerSquarefreeRadical n) =
      ∑ p ∈ n.primeFactors, Real.log p := by
  rw [shiftedEulerSquarefreeRadical]
  push_cast
  rw [Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem shiftedEulerValuationDefect_eq_log_sub (n : ℕ) :
    shiftedEulerValuationDefect n =
      Real.log n - Real.log (shiftedEulerSquarefreeRadical n) := by
  rw [shiftedEulerValuationDefect, log_shiftedEulerSquarefreeRadical]

theorem shiftedEulerValuationDefect_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ shiftedEulerValuationDefect n := by
  rw [shiftedEulerValuationDefect_eq_log_sub, sub_nonneg]
  apply Real.strictMonoOn_log.monotoneOn
  · show (0 : ℝ) < shiftedEulerSquarefreeRadical n
    exact_mod_cast shiftedEulerSquarefreeRadical_pos n
  · show (0 : ℝ) < n
    exact_mod_cast hn
  · exact_mod_cast Nat.le_of_dvd hn (shiftedEulerSquarefreeRadical_dvd n)

theorem shiftedEulerValuationDefect_eq_zero_iff {n : ℕ} (hn : 0 < n) :
    shiftedEulerValuationDefect n = 0 ↔ Squarefree n := by
  rw [shiftedEulerValuationDefect_eq_log_sub, sub_eq_zero]
  constructor
  · intro hlog
    apply (shiftedEulerSquarefreeRadical_eq_iff n).mp
    apply Nat.cast_injective (R := ℝ)
    calc
      (shiftedEulerSquarefreeRadical n : ℝ) =
          Real.exp (Real.log (shiftedEulerSquarefreeRadical n)) := by
            rw [Real.exp_log]
            exact_mod_cast shiftedEulerSquarefreeRadical_pos n
      _ = Real.exp (Real.log n) := by rw [hlog]
      _ = (n : ℝ) := by
            rw [Real.exp_log]
            exact_mod_cast hn
  · intro hs
    have hcast : (shiftedEulerSquarefreeRadical n : ℝ) = (n : ℝ) :=
      congrArg (fun m : ℕ => (m : ℝ)) ((shiftedEulerSquarefreeRadical_eq_iff n).mpr hs)
    exact congrArg Real.log hcast.symm

theorem formationSquarefree_integerFormationProfile_iff {n : ℕ} (hn : 0 < n) :
    FormationSquarefree (integerFormationProfile n) ↔ Squarefree n := by
  rw [← formationMultiplicityDefect_eq_zero_iff (integerFormationProfile n)
      (fun p hp => primeLogFormationWeight_pos_of_mem n hp),
    formationMultiplicityDefect_integerFormationProfile hn.ne',
    shiftedEulerValuationDefect_eq_zero_iff hn]

/-- Polar multiplier induced on the full Euler coefficient by `ω ↦ -ω`. -/
def shiftedEulerReflectionMultiplier (n : ℕ) (ω : ℂ) : ℂ :=
  (-1 : ℂ) ^ n.primeFactors.card *
    Complex.exp (-(2 * ω) * (shiftedEulerValuationDefect n : ℂ))

theorem formationReflectionPacketCoefficient_integerFormationProfile
    (n : ℕ) (ω : ℂ) :
    formationReflectionPacketCoefficient primeLogFormationWeight
        (integerFormationProfile n) ω = shiftedEulerCoeff n ω := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [formationReflectionPacketCoefficient, formationTotalWeight,
      integerFormationProfile, shiftedEulerCoeff]
  · rw [formationReflectionPacketCoefficient, shiftedEulerCoeff,
      formationTotalWeight_integerFormationProfile hn,
      integerFormationProfile_support]
    rfl

theorem formationReflectionMultiplier_integerFormationProfile
    (n : ℕ) (ω : ℂ) :
    formationReflectionMultiplier primeLogFormationWeight
        (integerFormationProfile n) ω = shiftedEulerReflectionMultiplier n ω := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [formationReflectionMultiplier, formationMultiplicityDefect,
      formationTotalWeight, formationSupportWeight, integerFormationProfile,
      shiftedEulerReflectionMultiplier, shiftedEulerValuationDefect]
  · rw [formationReflectionMultiplier, shiftedEulerReflectionMultiplier,
      integerFormationProfile_support,
      formationMultiplicityDefect_integerFormationProfile hn]

/-- Exact nonperturbative reflection law for the full shifted-Euler source. -/
theorem shiftedEulerCoeff_neg (n : ℕ) (ω : ℂ) :
    shiftedEulerCoeff n (-ω) =
      shiftedEulerReflectionMultiplier n ω * shiftedEulerCoeff n ω := by
  calc
    shiftedEulerCoeff n (-ω) =
        formationReflectionPacketCoefficient primeLogFormationWeight
          (integerFormationProfile n) (-ω) :=
      (formationReflectionPacketCoefficient_integerFormationProfile n (-ω)).symm
    _ = formationReflectionMultiplier primeLogFormationWeight
          (integerFormationProfile n) ω *
        formationReflectionPacketCoefficient primeLogFormationWeight
          (integerFormationProfile n) ω :=
      formationReflectionPacketCoefficient_neg primeLogFormationWeight
        (integerFormationProfile n) ω
    _ = shiftedEulerReflectionMultiplier n ω * shiftedEulerCoeff n ω := by
      rw [formationReflectionMultiplier_integerFormationProfile,
        formationReflectionPacketCoefficient_integerFormationProfile]

/-- Reflection is information-neutral on the lifted source: its two polar multipliers cancel. -/
theorem shiftedEulerReflectionMultiplier_neg_mul (n : ℕ) (ω : ℂ) :
    shiftedEulerReflectionMultiplier n (-ω) *
      shiftedEulerReflectionMultiplier n ω = 1 := by
  rw [shiftedEulerReflectionMultiplier, shiftedEulerReflectionMultiplier]
  have hsign :
      ((-1 : ℂ) ^ n.primeFactors.card) * ((-1 : ℂ) ^ n.primeFactors.card) = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  have hexp :
      Complex.exp (-(2 * (-ω)) * (shiftedEulerValuationDefect n : ℂ)) *
        Complex.exp (-(2 * ω) * (shiftedEulerValuationDefect n : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have harg :
        -(2 * (-ω)) * (shiftedEulerValuationDefect n : ℂ) +
          -(2 * ω) * (shiftedEulerValuationDefect n : ℂ) = 0 := by ring
    rw [harg, Complex.exp_zero]
  calc
    ((-1 : ℂ) ^ n.primeFactors.card *
        Complex.exp (-(2 * (-ω)) * (shiftedEulerValuationDefect n : ℂ))) *
      ((-1 : ℂ) ^ n.primeFactors.card *
        Complex.exp (-(2 * ω) * (shiftedEulerValuationDefect n : ℂ))) =
      (((-1 : ℂ) ^ n.primeFactors.card) * ((-1 : ℂ) ^ n.primeFactors.card)) *
        (Complex.exp (-(2 * (-ω)) * (shiftedEulerValuationDefect n : ℂ)) *
          Complex.exp (-(2 * ω) * (shiftedEulerValuationDefect n : ℂ))) := by ring
    _ = 1 := by rw [hsign, hexp, one_mul]

/-- Positive observer sees only exponential valuation excess, not prime-support parity. -/
theorem norm_shiftedEulerReflectionMultiplier_ofReal (n : ℕ) (a : ℝ) :
    ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ =
      Real.exp (-2 * a * shiftedEulerValuationDefect n) := by
  rw [shiftedEulerReflectionMultiplier, norm_mul, norm_pow, Complex.norm_exp]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  congr 1
  simp

/-- Exact phase-times-modulus polar decomposition on a real radial line. -/
theorem shiftedEulerReflectionMultiplier_ofReal (n : ℕ) (a : ℝ) :
    shiftedEulerReflectionMultiplier n (a : ℂ) =
      (-1 : ℂ) ^ n.primeFactors.card *
        (Real.exp (-2 * a * shiftedEulerValuationDefect n) : ℂ) := by
  rw [shiftedEulerReflectionMultiplier]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  simp

/-- Normalization by the positive observer norm recovers precisely prime-support parity. -/
theorem shiftedEulerReflectionMultiplier_div_norm_ofReal (n : ℕ) (a : ℝ) :
    shiftedEulerReflectionMultiplier n (a : ℂ) /
        (‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ : ℂ) =
      (-1 : ℂ) ^ n.primeFactors.card := by
  rw [norm_shiftedEulerReflectionMultiplier_ofReal,
    shiftedEulerReflectionMultiplier_ofReal]
  have hne : (Real.exp (-2 * a * shiftedEulerValuationDefect n) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_ne_zero (-2 * a * shiftedEulerValuationDefect n))
  field_simp

/-- Logarithmic modulus reconstructs aggregate repeated-prime valuation depth. -/
theorem shiftedEulerValuationDefect_reconstruct {n : ℕ} {a : ℝ} (ha : a ≠ 0) :
    shiftedEulerValuationDefect n =
      -Real.log ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ / (2 * a) := by
  rw [norm_shiftedEulerReflectionMultiplier_ofReal, Real.log_exp]
  field_simp

/-- Joint reconstruction: the full reflected packet recovers both orientation and depth. -/
theorem shiftedEulerReflection_joint_reconstruction (n : ℕ) {a : ℝ} (ha : a ≠ 0) :
    shiftedEulerReflectionMultiplier n (a : ℂ) /
          (‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ : ℂ) =
        (-1 : ℂ) ^ n.primeFactors.card ∧
      shiftedEulerValuationDefect n =
        -Real.log ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ / (2 * a) :=
  ⟨shiftedEulerReflectionMultiplier_div_norm_ofReal n a,
    shiftedEulerValuationDefect_reconstruct ha⟩

theorem norm_shiftedEulerReflectionMultiplier_le_one {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ ≤ 1 := by
  rw [norm_shiftedEulerReflectionMultiplier_ofReal, Real.exp_le_one_iff]
  nlinarith [shiftedEulerValuationDefect_nonneg hn]

/-- The squarefree sector is exactly the unitary locus of positive radial reflection. -/
theorem norm_shiftedEulerReflectionMultiplier_eq_one_iff {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ = 1 ↔ Squarefree n := by
  rw [norm_shiftedEulerReflectionMultiplier_ofReal, Real.exp_eq_one_iff]
  constructor
  · intro h
    apply (shiftedEulerValuationDefect_eq_zero_iff hn).mp
    nlinarith
  · intro hs
    rw [(shiftedEulerValuationDefect_eq_zero_iff hn).mpr hs]
    ring

theorem cardFactors_eq_card_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ArithmeticFunction.cardFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardFactors_apply]
  exact (List.toFinset_card_of_nodup hn.nodup_primeFactorsList).symm

theorem moebius_cast_eq_primeSupportParity {n : ℕ} (hn : Squarefree n) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) = (-1 : ℂ) ^ n.primeFactors.card := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hn,
    cardFactors_eq_card_primeFactors_of_squarefree hn]
  push_cast
  rfl

theorem formationMobius_integerFormationProfile {n : ℕ} (hn : 0 < n) :
    formationMobius (integerFormationProfile n) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  by_cases hs : Squarefree n
  · have hformation : FormationSquarefree (integerFormationProfile n) :=
      (formationSquarefree_integerFormationProfile_iff hn).mpr hs
    rw [formationMobius, if_pos hformation, integerFormationProfile_support,
      moebius_cast_eq_primeSupportParity hs]
  · have hformation : ¬ FormationSquarefree (integerFormationProfile n) := by
      intro h
      exact hs ((formationSquarefree_integerFormationProfile_iff hn).mp h)
    rw [formationMobius, if_neg hformation,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    simp

/-- Möbius is reconstructed, without being inserted as input, from the unitary-boundary phase of
the full functional-reflection multiplier. -/
theorem moebius_cast_eq_shiftedEulerReflection_boundaryPhase {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) =
      if ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ = 1 then
        shiftedEulerReflectionMultiplier n (a : ℂ) /
          (‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ : ℂ)
      else 0 := by
  calc
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) =
        formationMobius (integerFormationProfile n) :=
      (formationMobius_integerFormationProfile hn).symm
    _ = if ‖formationReflectionMultiplier primeLogFormationWeight
          (integerFormationProfile n) (a : ℂ)‖ = 1 then
        formationReflectionMultiplier primeLogFormationWeight
            (integerFormationProfile n) (a : ℂ) /
          (‖formationReflectionMultiplier primeLogFormationWeight
            (integerFormationProfile n) (a : ℂ)‖ : ℂ)
      else 0 :=
        formationMobius_eq_reflection_boundaryPhase (integerFormationProfile n)
          (fun p hp => primeLogFormationWeight_pos_of_mem n hp) ha
    _ = if ‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ = 1 then
        shiftedEulerReflectionMultiplier n (a : ℂ) /
          (‖shiftedEulerReflectionMultiplier n (a : ℂ)‖ : ℂ)
      else 0 := by
        rw [formationReflectionMultiplier_integerFormationProfile]

/-- On the squarefree (exterior) sector, reflection is exactly Möbius parity. -/
theorem shiftedEulerCoeff_neg_of_squarefree {n : ℕ} (hn : Squarefree n) (ω : ℂ) :
    shiftedEulerCoeff n (-ω) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * shiftedEulerCoeff n ω := by
  rw [shiftedEulerCoeff_neg, shiftedEulerReflectionMultiplier,
    (shiftedEulerValuationDefect_eq_zero_iff (Nat.pos_of_ne_zero hn.ne_zero)).mpr hn]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [moebius_cast_eq_primeSupportParity hn]

/-- Predicted fourth-organ law: squarefree projection after functional reflection is exactly
Möbius multiplication of the positive shifted-Euler source. -/
theorem squarefreeProjection_shiftedEulerCoeff_neg (n : ℕ) (ω : ℂ) :
    (if Squarefree n then shiftedEulerCoeff n (-ω) else 0) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * shiftedEulerCoeff n ω := by
  by_cases hn : Squarefree n
  · simp only [if_pos hn]
    exact shiftedEulerCoeff_neg_of_squarefree hn ω
  · simp only [if_neg hn]
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
    simp

end

end GaloisForLFunctions.HTGeometry
