/-
# Bondarenko--Heap Lemma 9: finite two-adic local transfer

The final sentence of Lemma 9 says that fundamental-discriminant conductors
with a factor `4` or `8` change its bound only by a constant.  This module
proves the exact CRT decomposition behind that statement and the literal
finite local bounds `4` and `8`.
-/
import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaNine
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicCRTProduct

open scoped BigOperators

noncomputable section

namespace RHTower

/-- The finite two-adic generalized Jacobi factor in the final paragraph of
Bondarenko--Heap Lemma 9. -/
def twoAdicGeneralizedJacobiLocalSum (A : ℕ) [NeZero A]
    (χ ψ : MulChar (ZMod A) ℂ) (y : ZMod A) : ℂ :=
  ∑ u : ZMod A, χ (u + y) * star (ψ u)

/-- A complete generalized Jacobi sum modulo the fixed two-adic factor has
norm at most its literal modulus. -/
theorem norm_twoAdicGeneralizedJacobiLocalSum_le_modulus (A : ℕ) [NeZero A]
    (χ ψ : MulChar (ZMod A) ℂ) (y : ZMod A) :
    ‖twoAdicGeneralizedJacobiLocalSum A χ ψ y‖ ≤ (A : ℝ) := by
  unfold twoAdicGeneralizedJacobiLocalSum
  calc
    ‖∑ u : ZMod A, χ (u + y) * star (ψ u)‖ ≤
      ∑ u : ZMod A, ‖χ (u + y) * star (ψ u)‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ _u : ZMod A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, norm_star]
      have hχ := norm_mulChar_apply_le_one χ (u + y)
      have hψ := norm_mulChar_apply_le_one ψ u
      nlinarith [norm_nonneg (χ (u + y)), norm_nonneg (ψ u)]
    _ = (A : ℝ) := by simp

/-- Generalized Jacobi sum for an arbitrary two-factor CRT decomposition. -/
def twoFactorGeneralizedJacobiSum {A Q N : ℕ} [NeZero N]
    (e : ZMod N ≃+* (ZMod A × ZMod Q))
    (χA : ZMod A → ℂ) (χQ : ZMod Q → ℂ)
    (ψA : ZMod A → ℂ) (ψQ : ZMod Q → ℂ)
    (y : ZMod N) : ℂ :=
  ∑ u : ZMod N,
    (χA (e (u + y)).1 * χQ (e (u + y)).2) *
      star (ψA (e u).1 * ψQ (e u).2)

/-- Exact CRT factorization of a two-factor generalized Jacobi sum. -/
theorem twoFactorGeneralizedJacobiSum_factor {A Q N : ℕ} [NeZero A] [NeZero Q] [NeZero N]
    (e : ZMod N ≃+* (ZMod A × ZMod Q))
    (χA : ZMod A → ℂ) (χQ : ZMod Q → ℂ)
    (ψA : ZMod A → ℂ) (ψQ : ZMod Q → ℂ)
    (y : ZMod N) :
    twoFactorGeneralizedJacobiSum e χA χQ ψA ψQ y =
      (∑ a : ZMod A, χA (a + (e y).1) * star (ψA a)) *
      ∑ b : ZMod Q, χQ (b + (e y).2) * star (ψQ b) := by
  unfold twoFactorGeneralizedJacobiSum
  simp only [map_add, Prod.fst_add, Prod.snd_add, star_mul]
  calc
    ∑ u : ZMod N,
        (χA ((e u).1 + (e y).1) * χQ ((e u).2 + (e y).2)) *
          (star (ψQ (e u).2) * star (ψA (e u).1)) =
      ∑ z : ZMod A × ZMod Q,
        (χA (z.1 + (e y).1) * χQ (z.2 + (e y).2)) *
          (star (ψQ z.2) * star (ψA z.1)) := by
        exact Equiv.sum_comp e.toEquiv (fun z : ZMod A × ZMod Q =>
          (χA (z.1 + (e y).1) * χQ (z.2 + (e y).2)) *
            (star (ψQ z.2) * star (ψA z.1)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hreorder (a : ZMod A) (b : ZMod Q) :
          (χA (a + (e y).1) * χQ (b + (e y).2)) *
              (star (ψQ b) * star (ψA a)) =
            (χA (a + (e y).1) * star (ψA a)) *
              (χQ (b + (e y).2) * star (ψQ b)) := by ring
      simp_rw [hreorder]
      conv_lhs =>
        enter [2, a]
        rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

namespace OddPrimeFamily

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The level-four/odd CRT generalized Jacobi sum. -/
def fourOddGeneralizedJacobiLocalSum (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (fourOddModulus P)) : ℂ :=
  twoFactorGeneralizedJacobiSum (fourOddCrtProductEquiv P)
    quadraticCharacterFour (quadraticCharacter P) ψ₂
    (generalizedJacobiLocalCharacter P ψ) y

omit [DecidableEq I] in
/-- Exact level-four CRT factorization into a finite two-adic factor and the
odd square-free generalized Jacobi sum. -/
theorem fourOddGeneralizedJacobiLocalSum_factor (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (fourOddModulus P)) :
    fourOddGeneralizedJacobiLocalSum P ψ₂ ψ y =
      twoAdicGeneralizedJacobiLocalSum 4 quadraticCharacterFour ψ₂ (fourCoordinate P y) *
        generalizedJacobiLocalSum P ψ (oddCoordinate P y) := by
  unfold fourOddGeneralizedJacobiLocalSum twoAdicGeneralizedJacobiLocalSum
    generalizedJacobiLocalSum
  rw [twoFactorGeneralizedJacobiSum_factor]
  rfl

omit [DecidableEq I] in
/-- A level-four factor costs at most the constant four in the Lemma-9 local
bound. -/
theorem norm_fourOddGeneralizedJacobiLocalSum_le (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (fourOddModulus P)) :
    ‖fourOddGeneralizedJacobiLocalSum P ψ₂ ψ y‖ ≤
      4 * ‖generalizedJacobiLocalSum P ψ (oddCoordinate P y)‖ := by
  rw [fourOddGeneralizedJacobiLocalSum_factor, norm_mul]
  gcongr
  exact norm_twoAdicGeneralizedJacobiLocalSum_le_modulus 4 quadraticCharacterFour ψ₂ _

/-- The level-eight/odd CRT generalized Jacobi sum, for either two-adic
quadratic choice. -/
def eightOddGeneralizedJacobiLocalSum (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (eightOddModulus P)) : ℂ :=
  twoFactorGeneralizedJacobiSum (eightOddCrtProductEquiv P)
    χ₂ (quadraticCharacter P) ψ₂ (generalizedJacobiLocalCharacter P ψ) y

omit [DecidableEq I] in
/-- Exact level-eight CRT factorization into its finite two-adic factor and
the odd square-free generalized Jacobi sum. -/
theorem eightOddGeneralizedJacobiLocalSum_factor (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (eightOddModulus P)) :
    eightOddGeneralizedJacobiLocalSum P χ₂ ψ₂ ψ y =
      twoAdicGeneralizedJacobiLocalSum 8 χ₂ ψ₂ (eightCoordinate P y) *
        generalizedJacobiLocalSum P ψ (eightOddCoordinate P y) := by
  unfold eightOddGeneralizedJacobiLocalSum twoAdicGeneralizedJacobiLocalSum
    generalizedJacobiLocalSum
  rw [twoFactorGeneralizedJacobiSum_factor]
  rfl

omit [DecidableEq I] in
/-- A level-eight factor costs at most the constant eight in the Lemma-9
local bound. -/
theorem norm_eightOddGeneralizedJacobiLocalSum_le (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (y : ZMod (eightOddModulus P)) :
    ‖eightOddGeneralizedJacobiLocalSum P χ₂ ψ₂ ψ y‖ ≤
      8 * ‖generalizedJacobiLocalSum P ψ (eightOddCoordinate P y)‖ := by
  rw [eightOddGeneralizedJacobiLocalSum_factor, norm_mul]
  gcongr
  exact norm_twoAdicGeneralizedJacobiLocalSum_le_modulus 8 χ₂ ψ₂ _

/-- The CRT-coordinate source shift `r m⁻¹` for a modulus with a fixed
two-adic factor and an odd square-free factor. -/
def twoAdicCoefficientShift {A N : ℕ} [NeZero A] [NeZero N]
    (P : OddPrimeFamily I) (e : ZMod N ≃+* (ZMod A × ZMod P.modulus))
    (r : ℤ) (m : (ZMod A)ˣ × (ZMod P.modulus)ˣ) : ZMod N :=
  e.symm ((r : ZMod A) * (↑(m.1⁻¹) : ZMod A),
    (r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))

/-- Pointwise two-adic transfer of the Lemma-9 local estimate.  The odd
factor retains its exact exceptional Ramanujan sum; the fixed two-adic
factor contributes at most its modulus. -/
theorem norm_twoAdicTransferredJacobiAtShift_le {A N : ℕ} [NeZero A] [NeZero N]
    (P : OddPrimeFamily I) (e : ZMod N ≃+* (ZMod A × ZMod P.modulus))
    (χA ψA : MulChar (ZMod A) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (r : ℤ) (m : (ZMod A)ˣ × (ZMod P.modulus)ˣ) :
    ‖twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
      (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ ≤
      (A : ℝ) *
        (‖exceptionalRamanujanAdditiveProduct P ψ
          ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ *
          Real.sqrt (P.modulus : ℝ)) := by
  rw [twoFactorGeneralizedJacobiSum_factor]
  simp only [twoAdicCoefficientShift, RingEquiv.apply_symm_apply]
  change ‖twoAdicGeneralizedJacobiLocalSum A χA ψA
      ((r : ZMod A) * (↑(m.1⁻¹) : ZMod A)) *
      generalizedJacobiLocalSum P ψ
        ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ ≤ _
  rw [norm_mul]
  calc
    ‖twoAdicGeneralizedJacobiLocalSum A χA ψA
        ((r : ZMod A) * (↑(m.1⁻¹) : ZMod A))‖ *
        ‖generalizedJacobiLocalSum P ψ
          ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ ≤
      (A : ℝ) * ‖generalizedJacobiLocalSum P ψ
        ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ := by
        gcongr
        exact norm_twoAdicGeneralizedJacobiLocalSum_le_modulus A χA ψA _
    _ ≤ (A : ℝ) *
        (‖exceptionalRamanujanAdditiveProduct P ψ
          ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ *
          Real.sqrt (P.modulus : ℝ)) := by
        gcongr
        exact norm_generalizedJacobiLocalSum_unitInverse_le P ψ r m.2

/-- The literal finite coefficient sum from source equation (32), written in
CRT coordinates for a fixed two-adic factor.  Coefficients are bundled with
their unit-ball proof, so this theorem has no external analytic premise. -/
def twoAdicLemmaNineCoefficientSum {A N : ℕ} [NeZero A] [NeZero N]
    (P : OddPrimeFamily I) (e : ZMod N ≃+* (ZMod A × ZMod P.modulus))
    (χA ψA : MulChar (ZMod A) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod A)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod A)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) : ℂ :=
  ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, ∑ m ∈ mset,
    c r * b m * twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
      (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)

/-- Exact finite two-adic lift of the unnormalized generic branch of
Bondarenko--Heap Lemma 9.  A factor `A` costs only the fixed constant `A` in
front of the already-certified odd square-free Ramanujan/gcd mass. -/
theorem twoAdicLemmaNineCoefficientSum_norm_le_mass {A N : ℕ} [NeZero A] [NeZero N]
    (P : OddPrimeFamily I) (e : ZMod N ≃+* (ZMod A × ZMod P.modulus))
    (χA ψA : MulChar (ZMod A) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod A)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod A)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) :
    ‖twoAdicLemmaNineCoefficientSum P e χA ψA ψ R mset b c‖ ≤
      (A : ℝ) * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
  unfold twoAdicLemmaNineCoefficientSum
  calc
    ‖∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, ∑ m ∈ mset,
        c r * b m * twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
          (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ ≤
      ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0,
        ‖∑ m ∈ mset, c r * b m * twoFactorGeneralizedJacobiSum e χA
          (quadraticCharacter P) ψA (generalizedJacobiLocalCharacter P ψ)
          (twoAdicCoefficientShift P e r m)‖ := by
        exact norm_sum_le ((Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0) _
    _ ≤ ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, ∑ m ∈ mset,
        ‖c r * b m * twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
          (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ := by
        apply Finset.sum_le_sum
        intro r hr
        exact norm_sum_le mset _
    _ ≤ ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, ∑ m ∈ mset,
        (A : ℝ) *
          (‖exceptionalRamanujanAdditiveProduct P ψ
            ((r : ZMod P.modulus) * (↑(m.2⁻¹) : ZMod P.modulus))‖ *
            Real.sqrt (P.modulus : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, norm_mul]
        have hT := norm_twoAdicTransferredJacobiAtShift_le P e χA ψA ψ r m
        have hb := b.norm_le_one m
        have hc := c.norm_le_one r
        calc
          ‖c r‖ * ‖b m‖ *
              ‖twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
                (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ ≤
            1 * 1 * ‖twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
              (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ := by
              gcongr
          _ = ‖twoFactorGeneralizedJacobiSum e χA (quadraticCharacter P) ψA
              (generalizedJacobiLocalCharacter P ψ) (twoAdicCoefficientShift P e r m)‖ := by ring
          _ ≤ _ := hT
    _ ≤ ∑ r ∈ (Finset.Icc (-(R : ℤ)) (R : ℤ)).erase 0, ∑ m ∈ mset,
        (A : ℝ) * ((P.modulus.gcd r.natAbs : ℝ) * Real.sqrt (P.modulus : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro m hm
        gcongr
        exact exceptionalRamanujanAdditiveProduct_norm_le_gcd_unitInverse P ψ r m.2
    _ = (A : ℝ) * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
        unfold ramanujanGcdSymmetricIntervalMass
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hreorder (r : ℤ) : (mset.card : ℝ) *
            ((A : ℝ) * ((P.modulus.gcd r.natAbs : ℝ) * Real.sqrt (P.modulus : ℝ))) =
          ((A : ℝ) * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ)) *
            (P.modulus.gcd r.natAbs : ℝ) := by ring
        simp_rw [hreorder]
        rw [← Finset.mul_sum]

/-- The literal level-four coefficient sum from the final sentence of
Bondarenko--Heap Lemma 9, in CRT coordinates. -/
def fourOddLemmaNineCoefficientSum (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) : ℂ :=
  twoAdicLemmaNineCoefficientSum P (fourOddCrtProductEquiv P) quadraticCharacterFour ψ₂ ψ
    R mset b c

/-- A level-four conductor changes the generic Lemma-9 coefficient estimate
by at most the literal constant `4`. -/
theorem fourOddLemmaNineCoefficientSum_norm_le_mass (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) :
    ‖fourOddLemmaNineCoefficientSum P ψ₂ ψ R mset b c‖ ≤
      4 * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
  convert twoAdicLemmaNineCoefficientSum_norm_le_mass P (fourOddCrtProductEquiv P)
    quadraticCharacterFour ψ₂ ψ R mset b c using 1 <;>
    norm_num [fourOddLemmaNineCoefficientSum]

/-- The literal level-eight coefficient sum from the final sentence of
Bondarenko--Heap Lemma 9.  The arbitrary two-adic character covers both
primitive quadratic choices at conductor eight. -/
def eightOddLemmaNineCoefficientSum (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) : ℂ :=
  twoAdicLemmaNineCoefficientSum P (eightOddCrtProductEquiv P) χ₂ ψ₂ ψ R mset b c

/-- A level-eight conductor changes the generic Lemma-9 coefficient estimate
by at most the literal constant `8`. -/
theorem eightOddLemmaNineCoefficientSum_norm_le_mass (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) :
    ‖eightOddLemmaNineCoefficientSum P χ₂ ψ₂ ψ R mset b c‖ ≤
      8 * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
  convert twoAdicLemmaNineCoefficientSum_norm_le_mass P (eightOddCrtProductEquiv P) χ₂ ψ₂ ψ
    R mset b c using 1 <;>
    norm_num [eightOddLemmaNineCoefficientSum]

omit [DecidableEq I] in
/-- The exact totient normalization at a level-four fundamental-discriminant
conductor. -/
theorem fourOddModulus_totient_eq (P : OddPrimeFamily I) :
    (fourOddModulus P).totient = 2 * P.modulus.totient := by
  rw [fourOddModulus_eq, Nat.totient_mul (four_coprime_modulus P)]
  have h4 : Nat.totient 4 = 2 := by native_decide
  rw [h4]

omit [DecidableEq I] in
/-- The exact totient normalization at a level-eight fundamental-discriminant
conductor. -/
theorem eightOddModulus_totient_eq (P : OddPrimeFamily I) :
    (eightOddModulus P).totient = 4 * P.modulus.totient := by
  rw [eightOddModulus_eq, Nat.totient_mul (eight_coprime_modulus P)]
  have h8 : Nat.totient 8 = 4 := by native_decide
  rw [h8]

/-- After its actual full-conductor totient normalization, the level-four
coefficient sum costs only the fixed factor two relative to the certified odd
square-free Lemma-9 mass. -/
theorem fourOddLemmaNineCoefficientSum_normalized_le_mass (P : OddPrimeFamily I)
    (ψ₂ : MulChar (ZMod 4) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 4)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) :
    ((fourOddModulus P).totient : ℝ)⁻¹ *
        ‖fourOddLemmaNineCoefficientSum P ψ₂ ψ R mset b c‖ ≤
      2 * (P.modulus.totient : ℝ)⁻¹ * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
  have hsum := fourOddLemmaNineCoefficientSum_norm_le_mass P ψ₂ ψ R mset b c
  have hphi : 0 < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (P.modulus_neZero.out |> Nat.pos_of_ne_zero)
  rw [fourOddModulus_totient_eq]
  calc
    ((2 * P.modulus.totient : ℕ) : ℝ)⁻¹ *
        ‖fourOddLemmaNineCoefficientSum P ψ₂ ψ R mset b c‖ ≤
      ((2 * P.modulus.totient : ℕ) : ℝ)⁻¹ *
        (4 * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
          ramanujanGcdSymmetricIntervalMass P R) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (P.modulus.totient : ℝ)⁻¹ * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
      push_cast
      field_simp
      ring

/-- After its actual full-conductor totient normalization, the level-eight
coefficient sum has the same fixed factor two relative to the odd
square-free Lemma-9 mass. -/
theorem eightOddLemmaNineCoefficientSum_normalized_le_mass (P : OddPrimeFamily I)
    (χ₂ ψ₂ : MulChar (ZMod 8) ℂ) (ψ : ∀ i, MulChar (ZMod (P.prime i).1) ℂ)
    (R : ℕ) (mset : Finset ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (b : UnitBallCoefficient ((ZMod 8)ˣ × (ZMod P.modulus)ˣ))
    (c : UnitBallCoefficient ℤ) :
    ((eightOddModulus P).totient : ℝ)⁻¹ *
        ‖eightOddLemmaNineCoefficientSum P χ₂ ψ₂ ψ R mset b c‖ ≤
      2 * (P.modulus.totient : ℝ)⁻¹ * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
  have hsum := eightOddLemmaNineCoefficientSum_norm_le_mass P χ₂ ψ₂ ψ R mset b c
  have hphi : 0 < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (P.modulus_neZero.out |> Nat.pos_of_ne_zero)
  rw [eightOddModulus_totient_eq]
  calc
    ((4 * P.modulus.totient : ℕ) : ℝ)⁻¹ *
        ‖eightOddLemmaNineCoefficientSum P χ₂ ψ₂ ψ R mset b c‖ ≤
      ((4 * P.modulus.totient : ℕ) : ℝ)⁻¹ *
        (8 * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
          ramanujanGcdSymmetricIntervalMass P R) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (P.modulus.totient : ℝ)⁻¹ * (mset.card : ℝ) * Real.sqrt (P.modulus : ℝ) *
        ramanujanGcdSymmetricIntervalMass P R := by
      push_cast
      field_simp
      ring

end OddPrimeFamily
end RHTower
