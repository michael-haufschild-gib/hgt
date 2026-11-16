import GaloisForLFunctions.RHTower.CCM.Characters.ProfiniteUnitCharacters
import GaloisForLFunctions.RHTower.CCM.CCMRationalStrongClassSpace
import GaloisForLFunctions.HTGeometry.RealCharacterExp

/-!
# Finite character data and norm twists on the rational class-space section

Every continuous unitary character of the canonical section
`Ẑˣ × ℝ₊ˣ` is a finite residue-unit character times an imaginary power of
the actual module. The profinite factor has finite conductor; logarithmic
coordinates turn the positive-real factor into a character of the line.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.CCMCharacters

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Every continuous character of the positive-real group is an imaginary norm power. -/
theorem positiveCharacter_eq_normTwist (χ : Units NNReal →ₜ* Circle) :
    ∃ t : ℝ, ∀ r : Units NNReal,
      (χ r : ℂ) = Complex.exp ((t * ccmRationalPositiveUnitLog r : ℝ) * Complex.I) := by
  let ψ : ℝ → ℂ := fun s => (χ (ccmRationalPositiveLogUnit s) : ℂ)
  have hcont : Continuous ψ := continuous_subtype_val.comp
    (χ.continuous.comp ccmRationalPositiveLogUnit_continuous)
  have hmul (s t : ℝ) : ψ (s + t) = ψ s * ψ t := by
    change (χ (ccmRationalPositiveLogUnit (s + t)) : ℂ) = _
    rw [ccmRationalPositiveLogUnit_add, map_mul, Circle.coe_mul]
  have hnorm (s : ℝ) : ‖ψ s‖ = 1 := Circle.norm_coe _
  obtain ⟨t, ht⟩ := exists_exp_of_continuous_character hcont hmul hnorm
  refine ⟨t, fun r => ?_⟩
  simpa only [ψ, ccmRationalPositiveLogUnit_unitLog] using ht (ccmRationalPositiveUnitLog r)

/-- The norm frequency is unique because the positive-real radius is continuous. -/
theorem positiveCharacter_exists_unique_normTwist (χ : Units NNReal →ₜ* Circle) :
    ∃! t : ℝ, ∀ r : Units NNReal,
      (χ r : ℂ) = Complex.exp ((t * ccmRationalPositiveUnitLog r : ℝ) * Complex.I) := by
  obtain ⟨t, ht⟩ := positiveCharacter_eq_normTwist χ
  refine ⟨t, ht, fun s hs => ?_⟩
  have hder (a : ℝ) : HasDerivAt
      (fun x : ℝ => Complex.exp ((a * x : ℝ) * Complex.I)) ((a : ℂ) * Complex.I) 0 := by
    have hlin := (((hasDerivAt_id (0 : ℝ)).const_mul a).ofReal_comp).mul_const Complex.I
    simpa only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      one_mul, mul_one] using hlin.cexp
  have heq : (fun x : ℝ => Complex.exp ((s * x : ℝ) * Complex.I)) =
      (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I)) := by
    funext x
    have h := (hs (ccmRationalPositiveLogUnit x)).symm.trans
      (ht (ccmRationalPositiveLogUnit x))
    simpa only [ccmRationalPositiveUnitLog_logUnit] using h
  have hds := hder s
  rw [heq] at hds
  simpa using congrArg Complex.im (hds.unique (hder t))

/-- Restriction to the actual profinite units in the canonical section. -/
def classSpaceFiniteRestriction (χ : CCMRationalClassSpaceSection →ₜ* Circle) :
    CCMRationalProfiniteUnit →ₜ* Circle :=
  χ.comp (ContinuousMonoidHom.inl CCMRationalProfiniteUnit (Units NNReal))

/-- Restriction to the positive-real factor in the canonical section. -/
def classSpaceRadialRestriction (χ : CCMRationalClassSpaceSection →ₜ* Circle) :
    Units NNReal →ₜ* Circle :=
  χ.comp (ContinuousMonoidHom.inr CCMRationalProfiniteUnit (Units NNReal))

/-- Multiplicativity separates the finite and positive-real factors exactly. -/
theorem classSpaceCharacter_split (χ : CCMRationalClassSpaceSection →ₜ* Circle)
    (b : CCMRationalClassSpaceSection) :
    χ b = classSpaceFiniteRestriction χ b.1 * classSpaceRadialRestriction χ b.2 := by
  calc
    χ b = χ ((b.1, 1) * (1, b.2)) := by simp
    _ = _ := by rw [map_mul]; rfl

/-- Finite residue data and a real frequency define an actual continuous section character. -/
def classSpaceCharacter (S : Finset Nat.Primes) (n : Nat.Primes → ℕ)
    (θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle) (t : ℝ) :
    CCMRationalClassSpaceSection →ₜ* Circle where
  toFun b := θ (profiniteUnitReduction S n b.1) *
    Circle.exp (t * Real.log (ccmRationalClassSpaceModule b))
  map_one' := by
    change θ (profiniteUnitReduction S n 1) * Circle.exp (t * ccmRationalPositiveUnitLog 1) = 1
    simp only [map_one, ccmRationalPositiveUnitLog_one, mul_zero, Circle.exp_zero, mul_one]
  map_mul' b c := by
    change θ (profiniteUnitReduction S n (b.1 * c.1)) *
        Circle.exp (t * ccmRationalPositiveUnitLog (b.2 * c.2)) =
      (θ (profiniteUnitReduction S n b.1) * Circle.exp (t * ccmRationalPositiveUnitLog b.2)) *
        (θ (profiniteUnitReduction S n c.1) * Circle.exp (t * ccmRationalPositiveUnitLog c.2))
    rw [map_mul, map_mul, ccmRationalPositiveUnitLog_mul, mul_add, Circle.exp_add]
    ac_rfl
  continuous_toFun := ((finiteDataCharacter S n θ).continuous.comp continuous_fst).mul
    (Circle.exp.continuous.comp (continuous_const.mul
      (ccmRationalClassSpaceModule_continuous.log
        (fun b => (ccmRationalClassSpaceModule_pos b).ne'))))

/-- Finite prime-power residue data and one real norm frequency exhaust all section characters. -/
theorem exists_finite_character_normTwist (χ : CCMRationalClassSpaceSection →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        ∃ t : ℝ, ∀ b : CCMRationalClassSpaceSection,
          (χ b : ℂ) = (θ (profiniteUnitReduction S n b.1) : ℂ) *
            Complex.exp ((t * Real.log (ccmRationalClassSpaceModule b) : ℝ) * Complex.I) := by
  obtain ⟨S, n, θ, hθ, _⟩ := exists_unique_finite_quotient_character
    (classSpaceFiniteRestriction χ)
  obtain ⟨t, ht⟩ := positiveCharacter_eq_normTwist (classSpaceRadialRestriction χ)
  refine ⟨S, n, θ, t, fun b => ?_⟩
  rw [classSpaceCharacter_split, Circle.coe_mul, ← hθ b.1, ht b.2]

/-- The finite-data-and-norm-twist family exhausts all continuous unitary section characters. -/
theorem exists_classSpaceCharacter (χ : CCMRationalClassSpaceSection →ₜ* Circle) :
    ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        ∃ t : ℝ, χ = classSpaceCharacter S n θ t := by
  obtain ⟨S, n, θ, t, h⟩ := exists_finite_character_normTwist χ
  refine ⟨S, n, θ, t, ?_⟩
  apply ContinuousMonoidHom.ext
  intro b
  apply Subtype.ext
  change (χ b : ℂ) =
    ((θ (profiniteUnitReduction S n b.1) *
      Circle.exp (t * Real.log (ccmRationalClassSpaceModule b)) : Circle) : ℂ)
  rw [Circle.coe_mul, Circle.coe_exp]
  exact h b

/-- Changing finite conductor data cannot change the real norm frequency. -/
theorem exists_unique_norm_frequency (χ : CCMRationalClassSpaceSection →ₜ* Circle) :
    ∃! t : ℝ, ∃ S : Finset Nat.Primes, ∃ n : Nat.Primes → ℕ,
      ∃ θ : (∀ p : S, (ZMod (p.1.1 ^ n p.1))ˣ) →* Circle,
        ∀ b : CCMRationalClassSpaceSection,
          (χ b : ℂ) = (θ (profiniteUnitReduction S n b.1) : ℂ) *
            Complex.exp ((t * Real.log (ccmRationalClassSpaceModule b) : ℝ) * Complex.I) := by
  obtain ⟨t, ht, ht_unique⟩ := positiveCharacter_exists_unique_normTwist
    (classSpaceRadialRestriction χ)
  obtain ⟨S, n, θ, hθ, _⟩ := exists_unique_finite_quotient_character
    (classSpaceFiniteRestriction χ)
  refine ⟨t, ⟨S, n, θ, fun b => ?_⟩, ?_⟩
  · rw [classSpaceCharacter_split, Circle.coe_mul, ← hθ b.1, ht b.2]
  · rintro s ⟨T, m, φ, hφ⟩
    apply ht_unique s
    intro r
    change (χ (1, r) : ℂ) =
      Complex.exp ((s * ccmRationalPositiveUnitLog r : ℝ) * Complex.I)
    simpa only [map_one, Circle.coe_one, one_mul] using hφ (1, r)

#print axioms positiveCharacter_eq_normTwist
#print axioms positiveCharacter_exists_unique_normTwist
#print axioms exists_finite_character_normTwist
#print axioms exists_classSpaceCharacter
#print axioms exists_unique_norm_frequency

end GaloisForLFunctions.RHTower.CCMCharacters
