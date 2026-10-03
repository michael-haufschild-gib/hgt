import GaloisForLFunctions.RHTower.DirichletCharacterTheta
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Quantitative prime sums in each reduced residue class

The constants are constructed for each fixed positive modulus. The full actual
prime sum is recovered by finite-character orthogonality from proved character
main terms. No progression estimate or conductor-uniform bound is assumed.
-/

noncomputable section
namespace RHTower
open Complex
variable {Q : ℕ} [NeZero Q]

/-- One power-log rate controls all characters of a fixed positive modulus. -/
theorem exists_uniform_characterChebyshevTheta_power_log :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ (χ : DirichletCharacter ℂ Q) (x : ℝ), x₀ ≤ x →
        ‖characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
          C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  classical
  have hfinite (s : Finset (DirichletCharacter ℂ Q)) :
      ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
        ∀ χ ∈ s, ∀ x : ℝ, x₀ ≤ x →
          ‖characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤
            C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, 0, 3, by norm_num, le_rfl, le_rfl, by simp⟩
    | @insert χ s hnot ih =>
      obtain ⟨c, C, X, hc, hC, hX, hbound⟩ := ih
      obtain ⟨d, D, Y, hd, hD, hY, hχ⟩ := exists_characterChebyshevTheta_main_power_log χ
      refine ⟨min c d, max C D, max X Y, lt_min hc hd,
        hC.trans (le_max_left _ _), hX.trans (le_max_left _ _), ?_⟩
      intro ψ hψ x hx
      have hxX := (le_max_left X Y).trans hx
      have hxY := (le_max_right X Y).trans hx
      have hx0 : 0 ≤ x := by linarith only [hX, hxX]
      have hu : 0 ≤ Real.log x ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Real.log_nonneg (by linarith only [hX, hxX])) _
      have hscale (b B : ℝ) (hb : min c d ≤ b) (hB : 0 ≤ B) (hBC : B ≤ max C D) :
          B * x * Real.exp (-(b * Real.log x ^ ((1 : ℝ) / 10))) ≤
            max C D * x * Real.exp (-(min c d * Real.log x ^ ((1 : ℝ) / 10))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hBC hx0)
          (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hb hu)))
          (Real.exp_nonneg _) (mul_nonneg (hB.trans hBC) hx0)
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · exact (hχ x hxY).trans (hscale d D (min_le_right _ _) hD (le_max_right _ _))
      · exact (hbound ψ hψ x hxX).trans (hscale c C (min_le_left _ _) hC (le_max_left _ _))
  obtain ⟨c, C, X, hc, hC, hX, hb⟩ := hfinite Finset.univ
  exact ⟨c, C, X, hc, hC, hX, fun χ x hx => hb χ (Finset.mem_univ _) x hx⟩

/-- Logarithmically weighted primes in one residue class. -/
def primeProgressionTheta (Q : ℕ) (a : ZMod Q) (x : ℝ) : ℝ :=
  ∑ p ∈ ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime).filter (fun p : ℕ => (p : ZMod Q) = a), Real.log p

/-- Exact finite-character recovery, retaining every prime in the reduced class. -/
theorem primeProgressionTheta_eq_character_sum {a : ZMod Q} (ha : IsUnit a) (x : ℝ) :
    (primeProgressionTheta Q a x : ℂ) = (Q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ Q, χ a⁻¹ * characterChebyshevTheta χ x := by
  classical
  have htot : (Q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne Q))).ne'
  calc
    _ = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        if (p : ZMod Q) = a then (Real.log p : ℂ) else 0 := by
      rw [primeProgressionTheta, Complex.ofReal_sum, Finset.sum_filter]
    _ = ∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
        (Q.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ Q, χ a⁻¹ * χ p) * (Real.log p : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
      by_cases heq : (p : ZMod Q) = a
      · simp only [heq, ↓reduceIte, inv_mul_cancel₀ htot, one_mul]
      · simp only [heq, Ne.symm heq, ↓reduceIte, mul_zero, zero_mul]
    _ = _ := by
      simp only [characterChebyshevTheta, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- Every reduced residue class has an actual quantitative prime number theorem.
Constants may depend on the fixed modulus but are uniform over its reduced classes. -/
theorem exists_primeProgressionTheta_power_log :
    ∃ c C x₀ : ℝ, 0 < c ∧ 0 ≤ C ∧ 3 ≤ x₀ ∧
      ∀ (a : ZMod Q), IsUnit a → ∀ x : ℝ, x₀ ≤ x →
        |primeProgressionTheta Q a x - x / Q.totient| ≤
          C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
  classical
  obtain ⟨c, C, X, hc, hC, hX, hb⟩ := exists_uniform_characterChebyshevTheta_power_log (Q := Q)
  refine ⟨c, ‖(Q.totient : ℂ)⁻¹‖ * Fintype.card (DirichletCharacter ℂ Q) * C,
    X, hc, by positivity, hX, fun a ha x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith only [hX, hx]
  have hmain : (∑ χ : DirichletCharacter ℂ Q,
      χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
    have hunit : (1 : DirichletCharacter ℂ Q) a⁻¹ = 1 := by
      obtain ⟨u, rfl⟩ := ha
      simp
    simp [mul_ite, hunit]
  have hidentity : ((primeProgressionTheta Q a x - x / Q.totient : ℝ) : ℂ) =
      (Q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ Q,
        χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast,
      primeProgressionTheta_eq_character_sum ha]
    simp only [mul_sub, Finset.sum_sub_distrib, hmain]
    ring
  have hterm (χ : DirichletCharacter ℂ Q) :
      ‖χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0))‖ ≤
        C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10))) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hb χ x hx)
  calc
    _ = ‖((primeProgressionTheta Q a x - x / Q.totient : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(Q.totient : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ Q,
        χ a⁻¹ * (characterChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0))‖ := by
      rw [hidentity, norm_mul]
    _ ≤ ‖(Q.totient : ℂ)⁻¹‖ * ∑ χ : DirichletCharacter ℂ Q,
        (C * x * Real.exp (-(c * Real.log x ^ ((1 : ℝ) / 10)))) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun χ _ => hterm χ)) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end RHTower
