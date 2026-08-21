import GaloisForLFunctions.RHTower.EulerSquarefreeWickQuadraticCharacterBridge

/-!
# Artin interaction completion and scalar-landing no-go for Euler--Wick

The two independent quadratic gauges do have a canonical all-prime-power completion, but it is
not the untwisted Xi channel.  Inclusion--exclusion over the four gauge sectors gives the virtual
Euler coefficient

`1 + (χ₃χ₄)^k - χ₃^k - χ₄^k = (1 - χ₃^k)(1 - χ₄^k)`.

Because both characters are quadratic on units, every even valuation layer cancels and every odd
layer is exactly the anchored Euler--Wick interaction.  Analytically this is the coefficient
pattern of the virtual Artin cross-ratio

`ζ(s) L(s, χ₁₂) / (L(s, χ₃) L(s, χ₄))`,

not a scalar component of `Xi`.

The final theorem makes the source/receiver firewall exact.  The interaction carrier is a
nontrivial character for residue-gauge translation, so every translation-invariant scalar reader
annihilates it.  Consequently no scalar Xi landing can be both residue-gauge equivariant and
coefficient-faithful on the Euler--Wick class.  A surviving continuation must retain a nontrivial
twisted/vector-valued target and therefore has its own Dirichlet-L divisor.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The literal product of the two residue-unit gauge groups. -/
abbrev QuadraticResidueGaugeSpace := (ZMod 3)ˣ × (ZMod 4)ˣ

/-- The modulo-three character has order two on every unit. -/
theorem quadraticCharacterThreeUnit_sq (u : (ZMod 3)ˣ) :
    quadraticCharacterThreeUnit u ^ 2 = 1 := by
  have hquadratic : quadraticCharacterThree.IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod 3)).comp (Int.castRingHom ℂ)
  have hne : quadraticCharacterThreeUnit u ≠ 0 := by
    exact ((u.isUnit.map quadraticCharacterThree).ne_zero)
  rcases hquadratic (u : ZMod 3) with hzero | hone | hneg
  · exact (hne hzero).elim
  · simp [quadraticCharacterThreeUnit, hone]
  · simp [quadraticCharacterThreeUnit, hneg]

/-- The modulo-four character has order two on every unit. -/
theorem quadraticCharacterFourUnit_sq (u : (ZMod 4)ˣ) :
    quadraticCharacterFourUnit u ^ 2 = 1 := by
  have hquadratic : RHTower.quadraticCharacterFour.IsQuadratic :=
    RHTower.quadraticCharacterFour_isQuadratic
  have hne : quadraticCharacterFourUnit u ≠ 0 := by
    exact ((u.isUnit.map RHTower.quadraticCharacterFour).ne_zero)
  rcases hquadratic (u : ZMod 4) with hzero | hone | hneg
  · exact (hne hzero).elim
  · simp [quadraticCharacterFourUnit, hone]
  · simp [quadraticCharacterFourUnit, hneg]

private theorem pow_even_of_sq_eq_one {a : ℂ} (ha : a ^ 2 = 1) (n : ℕ) :
    a ^ (2 * n) = 1 := by
  rw [pow_mul, ha, one_pow]

private theorem pow_odd_of_sq_eq_one {a : ℂ} (ha : a ^ 2 = 1) (n : ℕ) :
    a ^ (2 * n + 1) = a := by
  rw [pow_add, pow_even_of_sq_eq_one ha, one_mul, pow_one]

/-- Prime-power logarithmic coefficient of the four-sector virtual Artin cross-ratio. -/
def quadraticResidueVirtualEulerDepthCoefficient
    (k : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) : ℂ :=
  1 + (quadraticCharacterThreeUnit w.1.1 *
        quadraticCharacterFourUnit w.1.2) ^ k -
      quadraticCharacterThreeUnit w.1.1 ^ k -
      quadraticCharacterFourUnit w.1.2 ^ k

/-- The virtual-character coefficient is exactly the anchored two-gauge interaction. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_eq
    (k : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) :
    quadraticResidueVirtualEulerDepthCoefficient k w =
      (1 - quadraticCharacterThreeUnit w.1.1 ^ k) *
        (1 - quadraticCharacterFourUnit w.1.2 ^ k) := by
  rw [quadraticResidueVirtualEulerDepthCoefficient, mul_pow]
  ring

/-- Every even prime-power layer of the virtual interaction cancels exactly. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_even
    (n : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) :
    quadraticResidueVirtualEulerDepthCoefficient (2 * n) w = 0 := by
  rw [quadraticResidueVirtualEulerDepthCoefficient_eq,
    pow_even_of_sq_eq_one (quadraticCharacterThreeUnit_sq w.1.1),
    pow_even_of_sq_eq_one (quadraticCharacterFourUnit_sq w.1.2)]
  ring

/-- Every odd prime-power layer is the same anchored interaction class. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_odd
    (n : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) :
    quadraticResidueVirtualEulerDepthCoefficient (2 * n + 1) w =
      (1 - quadraticCharacterThreeUnit w.1.1) *
        (1 - quadraticCharacterFourUnit w.1.2) := by
  rw [quadraticResidueVirtualEulerDepthCoefficient_eq,
    pow_odd_of_sq_eq_one (quadraticCharacterThreeUnit_sq w.1.1),
    pow_odd_of_sq_eq_one (quadraticCharacterFourUnit_sq w.1.2)]

/-- The normalized literal Euler--Wick packet is `-2` times every odd virtual Euler layer. -/
theorem eulerSquarefreeWickQuadraticAnchoredObservable_normalized_eq_virtualOdd
    (n : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace) :
    eulerSquarefreeWickQuadraticAnchoredObservable
        eulerSquarefreeWickNormalizedPacket w =
      -2 * quadraticResidueVirtualEulerDepthCoefficient (2 * n + 1) w := by
  rw [eulerSquarefreeWickQuadraticAnchoredObservable_eq,
    eulerSquarefreeWickNormalizedDefect,
    quadraticResidueVirtualEulerDepthCoefficient_odd]
  ring

/-- The virtual coefficient is supported only where both gauge legs are nontrivial. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_odd_eq_zero_of_fst_one
    (n : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace)
    (h : quadraticCharacterThreeUnit w.1.1 = 1) :
    quadraticResidueVirtualEulerDepthCoefficient (2 * n + 1) w = 0 := by
  rw [quadraticResidueVirtualEulerDepthCoefficient_odd, h]
  ring

/-- Symmetric support statement for the second gauge leg. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_odd_eq_zero_of_snd_one
    (n : ℕ) (w : FullValueSubtype QuadraticResidueGaugeSpace)
    (h : quadraticCharacterFourUnit w.1.2 = 1) :
    quadraticResidueVirtualEulerDepthCoefficient (2 * n + 1) w = 0 := by
  rw [quadraticResidueVirtualEulerDepthCoefficient_odd, h]
  ring

/-- At the doubly nontrivial CRT class every odd logarithmic coefficient is exactly four. -/
theorem quadraticResidueVirtualEulerDepthCoefficient_odd_neg_neg (n : ℕ) :
    quadraticResidueVirtualEulerDepthCoefficient (2 * n + 1)
      (⟨((-1 : (ZMod 3)ˣ), (-1 : (ZMod 4)ˣ)), Set.mem_univ _⟩) = 4 := by
  rw [quadraticResidueVirtualEulerDepthCoefficient_odd]
  norm_num

/-- Left translation of a residue-gauge observable. -/
def quadraticResidueGaugeLeftTranslate
    (u : QuadraticResidueGaugeSpace)
    (f : FullValueSubtype QuadraticResidueGaugeSpace → ℂ) :
    FullValueSubtype QuadraticResidueGaugeSpace → ℂ :=
  fun w => f ⟨u * w.1, Set.mem_univ _⟩

/-- The product observable is an eigenvector for translation with its literal joint character. -/
theorem quadraticResidueGaugeLeftTranslate_product
    (u : QuadraticResidueGaugeSpace) :
    quadraticResidueGaugeLeftTranslate u quadraticResidueProductObservable =
      (quadraticCharacterThreeUnit u.1 * quadraticCharacterFourUnit u.2) •
        quadraticResidueProductObservable := by
  funext w
  simp [quadraticResidueGaugeLeftTranslate, quadraticResidueProductObservable,
    quadraticCharacterThreeUnit, quadraticCharacterFourUnit, map_mul]
  ring

/-- Translating only the first nontrivial gauge leg negates the joint carrier. -/
theorem quadraticResidueGaugeLeftTranslate_product_neg_fst :
    quadraticResidueGaugeLeftTranslate
        ((-1 : (ZMod 3)ˣ), (1 : (ZMod 4)ˣ))
        quadraticResidueProductObservable =
      -quadraticResidueProductObservable := by
  rw [quadraticResidueGaugeLeftTranslate_product]
  simp

/-- A scalar reader is gauge invariant when every residue translation leaves its value fixed. -/
def QuadraticResidueGaugeInvariantScalarReader
    (L : (FullValueSubtype QuadraticResidueGaugeSpace → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u f, L (quadraticResidueGaugeLeftTranslate u f) = L f

/-- Every invariant scalar reader annihilates the nontrivial joint character sector. -/
theorem quadraticResidueGaugeInvariantScalarReader_product_eq_zero
    (L : (FullValueSubtype QuadraticResidueGaugeSpace → ℂ) →ₗ[ℂ] ℂ)
    (hL : QuadraticResidueGaugeInvariantScalarReader L) :
    L quadraticResidueProductObservable = 0 := by
  have h := hL ((-1 : (ZMod 3)ˣ), (1 : (ZMod 4)ˣ))
    quadraticResidueProductObservable
  rw [quadraticResidueGaugeLeftTranslate_product_neg_fst, map_neg] at h
  exact neg_eq_self.mp h

/-- **Scalar Xi-landing no-go.** No scalar reader is simultaneously residue-gauge invariant and
coefficient-faithful on the Euler--Wick interaction sector. -/
theorem no_quadraticResidueGaugeInvariantScalarReader_product_one :
    ¬ ∃ L : (FullValueSubtype QuadraticResidueGaugeSpace → ℂ) →ₗ[ℂ] ℂ,
      QuadraticResidueGaugeInvariantScalarReader L ∧
        L quadraticResidueProductObservable = 1 := by
  rintro ⟨L, hL, hone⟩
  rw [quadraticResidueGaugeInvariantScalarReader_product_eq_zero L hL] at hone
  norm_num at hone

end

end GaloisForLFunctions.RHTower
