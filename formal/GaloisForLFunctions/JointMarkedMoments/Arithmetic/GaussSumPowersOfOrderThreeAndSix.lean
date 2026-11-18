import GaloisForLFunctions.MetaplecticMobiusDescent.TheSexticCharacterBecomesQuadratic
import GaloisForLFunctions.FamilyContinuationTheory.TheMoebiusParityOfAGaussMonomial

/-!
# Powers of cubic and sextic Gauss sums

Normalized Gauss sums `g_j = q^{-1/2} Σ_x χ(x)^j ψ(x)` over a finite field `F` of order `q`, with a
nontrivial additive character `ψ`.

* `cubic_gauss_power_identities` (Lemma 8.1): for `χ` of exact order three,
  `τ³ = qJ`, `|J| = √q` and `g⁴ = (J/√q) g`, `J = J(χ, χ)`. The fourth power keeps the Jacobi
  phase `J/√q`.
* `sextic_duplication`: for `χ` of exact order six in odd characteristic,
  `χ(4) g₁g₄ = g₂g₃`; the cube `χ³` is the quadratic character (`cube_eq_quadraticChar`) and
  `J(χ, χ³) = χ(4) J(χ, χ)`.
* `sextic_conversion` (Lemma 8.4): with `A = −g₂³`, `C = A ḡ₂`, `G = χ(4)⁻¹ g₃`,
  `|A| = |C| = |G| = 1`, `g₄ = ḡ₂`, `g₁ = G g₂²`, `C = −g₂²`, `g₁g₂ = G g₂³`, `−g₁Ḡ = C`,
  `g₅ = χ(−1) ḡ₁` and `−g₅G = χ(−1) C̄`. No restriction on the residue degree enters.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open ComplexConjugate MetaplecticMobiusDescent FamilyContinuationTheory ArithmeticEffectivityTheory

variable {F : Type*} [Field F] [Fintype F]

noncomputable section

/-- The normalized Gauss sum `g_j = q^{-1/2} G(χ^j, ψ)`. -/
def normalizedGauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  gaussSum (χ ^ j) ψ / (Real.sqrt (Fintype.card F) : ℂ)

theorem sqrt_card_ne_zero : (Real.sqrt (Fintype.card F) : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Fintype.card F := Nat.cast_pos.2 Fintype.card_pos
  exact_mod_cast (Real.sqrt_pos.2 this).ne'

omit [Field F] in
theorem sqrt_card_sq : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = Fintype.card F := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

theorem norm_normalizedGauss {χ : MulChar F ℂ} {ψ : AddChar F ℂ} {j : ℕ} (hj : χ ^ j ≠ 1)
    (hψ : ψ.IsPrimitive) : ‖normalizedGauss χ ψ j‖ = 1 := by
  unfold normalizedGauss
  rw [norm_div, norm_gaussSum_eq_sqrt_card hj hψ, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (by exact_mod_cast (sqrt_card_ne_zero (F := F)))

/-- A complex number of modulus one is inverted by conjugation. -/
theorem mul_conj_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  simp

/-- Lemma 8.1: `τ³ = qJ`, `|J| = √q`, `g⁴ = (J/√q) g` for a cubic character. -/
theorem cubic_gauss_power_identities (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (horder : orderOf χ = 3)
    (hψ : ψ ≠ 1) :
    gaussSum χ ψ ^ 3 = Fintype.card F * jacobiSum χ χ ∧
      ‖jacobiSum χ χ‖ = Real.sqrt (Fintype.card F) ∧
      normalizedGauss χ ψ 1 ^ 4 =
        jacobiSum χ χ / (Real.sqrt (Fintype.card F) : ℂ) * normalizedGauss χ ψ 1 := by
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hχ : χ ≠ 1 := by
    rintro rfl; rw [orderOf_one] at horder; norm_num at horder
  have h3 := cubic_gauss_cube χ ψ horder hψp
  refine ⟨h3, ?_, ?_⟩
  · have hn := norm_gaussSum_eq_sqrt_card hχ hψp
    have h := congrArg norm h3
    rw [norm_pow, hn, norm_mul, Complex.norm_natCast] at h
    have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.2 Fintype.card_pos
    have hs := Real.sq_sqrt hq.le
    have hs0 := Real.sqrt_pos.2 hq
    -- `(√q)³ = q ‖J‖` and `q = (√q)²`
    have : Real.sqrt (Fintype.card F) ^ 2 * (Real.sqrt (Fintype.card F) - ‖jacobiSum χ χ‖) = 0 := by
      linear_combination h - ‖jacobiSum χ χ‖ * hs
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (pow_ne_zero 2 hs0.ne')
    · linarith
  · unfold normalizedGauss
    rw [pow_one, div_pow, show gaussSum χ ψ ^ 4 = gaussSum χ ψ * gaussSum χ ψ ^ 3 by ring, h3,
      ← sqrt_card_sq (F := F)]
    have := sqrt_card_ne_zero (F := F)
    field_simp

omit [Fintype F] in
theorem sextic_pow_ne_one {χ : MulChar F ℂ} (horder : orderOf χ = 6) {j : ℕ} (hj0 : j ≠ 0)
    (hj : j < 6) : χ ^ j ≠ 1 :=
  pow_ne_one_of_lt_orderOf hj0 (horder ▸ hj)

omit [Fintype F] in
theorem norm_char_four_eq_one {χ : MulChar F ℂ} (horder : orderOf χ = 6) (hchar : ringChar F ≠ 2) :
    ‖χ (4 : F)‖ = 1 := by
  have h4 : (4 : F) ≠ 0 := by
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  refine Complex.norm_eq_one_of_pow_eq_one (n := 6) ?_ (by norm_num)
  rw [← χ.pow_apply' (by norm_num), ← horder, pow_orderOf_eq_one,
    MulChar.one_apply (Ne.isUnit h4)]

omit [Fintype F] in
theorem char_neg_one_sq {χ : MulChar F ℂ} : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

section OrderSix

variable [DecidableEq F]

/-- The cube of a sextic character is the quadratic character. -/
theorem cube_eq_quadraticChar {χ : MulChar F ℂ} (horder : orderOf χ = 6) (hchar : ringChar F ≠ 2) :
    χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ) := by
  apply mulChar_hasUniqueOrderTwo F ℂ
  · rw [orderOf_pow_of_dvd (by norm_num) (by rw [horder]; norm_num), horder]
  · apply orderOf_eq_prime
    · exact ((quadraticChar_isQuadratic (F := F)).comp _).sq_eq_one
    · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2 (quadraticChar_ne_one hchar)

/-- `χ(4) G(χ)G(χ⁴) = G(χ²)G(χ³)` for a sextic character in odd characteristic. -/
theorem sextic_duplication_gaussSum {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (horder : orderOf χ = 6)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive) :
    χ (4 : F) * (gaussSum χ ψ * gaussSum (χ ^ 4) ψ) =
      gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ := by
  have hχ1 : χ ≠ 1 := by simpa using sextic_pow_ne_one horder (j := 1) one_ne_zero (by norm_num)
  have hJ1 := jacobiSum_mul_nontrivial (χ := χ) (φ := χ)
    (by rw [← pow_two]; exact sextic_pow_ne_one horder two_ne_zero (by norm_num)) ψ
  have hJ3 := jacobiSum_mul_nontrivial (χ := χ) (φ := χ ^ 3)
    (by rw [← pow_succ']; exact sextic_pow_ne_one horder (by norm_num) (by norm_num)) ψ
  rw [show χ * χ ^ 3 = χ ^ 4 by rw [← pow_succ'], cube_eq_quadraticChar horder hchar,
    jacobiSum_quadraticChar_eq hchar hχ1, ← cube_eq_quadraticChar horder hchar] at hJ3
  rw [← pow_two] at hJ1
  have hg1 : gaussSum χ ψ ≠ 0 := by
    intro h
    have := norm_gaussSum_eq_sqrt_card hχ1 hψ
    rw [h, norm_zero] at this
    have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.2 Fintype.card_pos
    exact (Real.sqrt_pos.2 hq).ne' this.symm
  have key : gaussSum χ ψ * (χ (4 : F) * (gaussSum χ ψ * gaussSum (χ ^ 4) ψ) -
      gaussSum (χ ^ 2) ψ * gaussSum (χ ^ 3) ψ) = 0 := by
    linear_combination (-(χ (4 : F) * gaussSum (χ ^ 4) ψ)) * hJ1 + gaussSum (χ ^ 2) ψ * hJ3
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h hg1
  · exact sub_eq_zero.1 h

/-- The normalized duplication identity `χ(4) g₁g₄ = g₂g₃`. -/
theorem sextic_duplication {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (horder : orderOf χ = 6)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive) :
    χ (4 : F) * (normalizedGauss χ ψ 1 * normalizedGauss χ ψ 4) =
      normalizedGauss χ ψ 2 * normalizedGauss χ ψ 3 := by
  have h := sextic_duplication_gaussSum horder hchar hψ
  unfold normalizedGauss
  rw [pow_one]
  have := sqrt_card_ne_zero (F := F)
  field_simp
  linear_combination h

omit [DecidableEq F] in
/-- `g_j g_{6−j} = χ^j(−1)` for `χ^j ≠ 1`. -/
theorem normalizedGauss_mul_compl {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (horder : orderOf χ = 6)
    (hψ : ψ.IsPrimitive) {j : ℕ} (hj0 : j ≠ 0) (hj : j < 6) :
    normalizedGauss χ ψ j * normalizedGauss χ ψ (6 - j) = (χ ^ j) (-1) := by
  have hinv : (χ ^ j)⁻¹ = χ ^ (6 - j) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, Nat.add_sub_cancel' hj.le, ← horder, pow_orderOf_eq_one]
  have h := gaussSum_mul_inv_eq_sign_card (sextic_pow_ne_one horder hj0 hj) hψ
  rw [hinv] at h
  unfold normalizedGauss
  have := sqrt_card_ne_zero (F := F)
  rw [div_mul_div_comm, h, ← pow_two, sqrt_card_sq]
  have hq : (Fintype.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

/-- The conversion factors of Lemma 8.4. -/
def conversionA (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ := -(normalizedGauss χ ψ 2) ^ 3

/-- `C = A ḡ₂`. -/
def conversionC (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  conversionA χ ψ * conj (normalizedGauss χ ψ 2)

/-- `G = χ(4)⁻¹ g₃`. -/
def conversionG (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ := (χ (4 : F))⁻¹ * normalizedGauss χ ψ 3

/-- Lemma 8.4: cubic-to-Möbius conversion of sextic Gauss coefficients. -/
theorem sextic_conversion {χ : MulChar F ℂ} {ψ : AddChar F ℂ} (horder : orderOf χ = 6)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    ‖conversionA χ ψ‖ = 1 ∧ ‖conversionC χ ψ‖ = 1 ∧ ‖conversionG χ ψ‖ = 1 ∧
      normalizedGauss χ ψ 4 = conj (normalizedGauss χ ψ 2) ∧
      normalizedGauss χ ψ 1 = conversionG χ ψ * normalizedGauss χ ψ 2 ^ 2 ∧
      conversionC χ ψ = -(normalizedGauss χ ψ 2) ^ 2 ∧
      normalizedGauss χ ψ 1 * normalizedGauss χ ψ 2 =
        conversionG χ ψ * normalizedGauss χ ψ 2 ^ 3 ∧
      -(normalizedGauss χ ψ 1 * conj (conversionG χ ψ)) = conversionC χ ψ ∧
      normalizedGauss χ ψ 5 = χ (-1) * conj (normalizedGauss χ ψ 1) ∧
      -(normalizedGauss χ ψ 5 * conversionG χ ψ) = χ (-1) * conj (conversionC χ ψ) := by
  have hψp : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  set g := normalizedGauss χ ψ with hg
  have n1 : ‖g 1‖ = 1 := norm_normalizedGauss (sextic_pow_ne_one horder one_ne_zero (by norm_num)) hψp
  have n2 : ‖g 2‖ = 1 := norm_normalizedGauss (sextic_pow_ne_one horder two_ne_zero (by norm_num)) hψp
  have n3 : ‖g 3‖ = 1 := norm_normalizedGauss (sextic_pow_ne_one horder (by norm_num) (by norm_num)) hψp
  have n4 := norm_char_four_eq_one horder hchar
  have c1 := mul_conj_of_norm_eq_one n1
  have c2 := mul_conj_of_norm_eq_one n2
  have c4 := mul_conj_of_norm_eq_one n4
  have h4ne : χ (4 : F) ≠ 0 := by intro h; rw [h, norm_zero] at n4; norm_num at n4
  -- `g₂g₄ = χ²(−1) = 1` and `g₁g₅ = χ(−1)`
  have p24 : g 2 * g 4 = 1 := by
    have := normalizedGauss_mul_compl horder hψp (j := 2) two_ne_zero (by norm_num)
    rw [show 6 - 2 = 4 by norm_num, χ.pow_apply' two_ne_zero, pow_two, char_neg_one_sq] at this
    exact this
  have p15 : g 1 * g 5 = χ (-1) := by
    have := normalizedGauss_mul_compl horder hψp (j := 1) one_ne_zero (by norm_num)
    rwa [show 6 - 1 = 5 by norm_num, pow_one] at this
  have hdup := sextic_duplication horder hchar hψp
  have e4 : g 4 = conj (g 2) := by linear_combination (-(g 4)) * c2 + conj (g 2) * p24
  have hG : conversionG χ ψ = (χ (4 : F))⁻¹ * g 3 := rfl
  have e1 : g 1 = conversionG χ ψ * g 2 ^ 2 := by
    rw [hG]
    field_simp
    linear_combination (g 2) * hdup - (χ (4 : F)) * (g 1) * p24
  have nG : ‖conversionG χ ψ‖ = 1 := by
    rw [hG, norm_mul, norm_inv, n4, n3]; norm_num
  have cG := mul_conj_of_norm_eq_one nG
  have eC : conversionC χ ψ = -(g 2) ^ 2 := by
    unfold conversionC conversionA
    rw [← hg]
    linear_combination (-(g 2) ^ 2) * c2
  have e5 : g 5 = χ (-1) * conj (g 1) := by
    linear_combination (-(g 5)) * c1 + conj (g 1) * p15
  refine ⟨?_, ?_, nG, e4, e1, eC, ?_, ?_, e5, ?_⟩
  · unfold conversionA; rw [← hg, norm_neg, norm_pow, n2, one_pow]
  · rw [eC, norm_neg, norm_pow, n2, one_pow]
  · rw [e1]; ring
  · rw [eC, e1]; linear_combination (-(g 2) ^ 2) * cG
  · rw [eC, e5, e1]
    simp only [map_neg, map_mul, map_pow]
    linear_combination (-(χ (-1) * conj (g 2) ^ 2)) * cG

end OrderSix

end

end GaloisForLFunctions.JointMarkedMoments
