import GaloisForLFunctions.HTGeometry.BidirectionalReserveFormation
import GaloisForLFunctions.RHTower.CCMRationalIntegralAdeleHaarIndex
import GaloisForLFunctions.RHTower.Sieve.TwistedMainTermMerge
import Mathlib

open Set

namespace GaloisForLFunctions.RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-!
# Arithmetic and adelic realization of bidirectional reserve formation

Positive arithmetic histories split uniquely into a primitive observer and a diagonal gcd reserve.
Componentwise multiplication creates a cross-gcd reserve whose square pays the exact reduced-product
defect. Bounded unreduced activity is proper although the primitive observer has an unbounded
diagonal fibre. The gauge/reflection-selected half-density is simultaneously the critical reduced-
ray coefficient and the square root of the actual finite-adele lattice-mass ratio.
-/

/-- Primitive observer after removing common arithmetic reserve. -/
def arithmeticPrimitiveObserver (a b : ℕ) : ℕ × ℕ :=
  (a / Nat.gcd a b, b / Nat.gcd a b)

/-- Common diagonal reserve of an arithmetic bidirectional history. -/
def arithmeticReserve (a b : ℕ) : ℕ := Nat.gcd a b

/-- Multiplicative activity of an arithmetic bidirectional history. -/
def arithmeticActivity (a b : ℕ) : ℕ := a * b

/-- Componentwise multiplicative fusion of two arithmetic histories. -/
def arithmeticFusion (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.1, x.2 * y.2)

/-- New common reserve created by arithmetic fusion. -/
def arithmeticReserveTransgression (a b c d : ℕ) : ℕ :=
  Nat.gcd (a * c) (b * d) / (Nat.gcd a b * Nat.gcd c d)

theorem arithmeticPrimitiveObserver_activity_reconstruction (a b : ℕ) :
    (arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2 * arithmeticReserve a b ^ 2 =
      arithmeticActivity a b := by
  exact RHTower.Sieve.reducedProduct_mul_gcd_sq a b

theorem arithmeticReserve_product_dvd_fusedReserve (a b c d : ℕ) :
    Nat.gcd a b * Nat.gcd c d ∣ Nat.gcd (a * c) (b * d) := by
  apply Nat.dvd_gcd
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_left c d)
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right a b) (Nat.gcd_dvd_right c d)

theorem arithmeticReserveTransgression_mul_oldReserve (a b c d : ℕ) :
    arithmeticReserveTransgression a b c d *
        (Nat.gcd a b * Nat.gcd c d) =
      Nat.gcd (a * c) (b * d) := by
  exact Nat.div_mul_cancel (arithmeticReserve_product_dvd_fusedReserve a b c d)

theorem arithmeticPrimitiveObserver_fusion_conservation (a b c d : ℕ) :
    ((arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2) *
        ((arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2) =
      ((arithmeticPrimitiveObserver (a * c) (b * d)).1 *
          (arithmeticPrimitiveObserver (a * c) (b * d)).2) *
        arithmeticReserveTransgression a b c d ^ 2 := by
  let g₁ := Nat.gcd a b
  let g₂ := Nat.gcd c d
  let g₃ := Nat.gcd (a * c) (b * d)
  let P₁ := (arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2
  let P₂ := (arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2
  let P₃ := (arithmeticPrimitiveObserver (a * c) (b * d)).1 *
    (arithmeticPrimitiveObserver (a * c) (b * d)).2
  let K := arithmeticReserveTransgression a b c d
  have h₁ : P₁ * g₁ ^ 2 = a * b := arithmeticPrimitiveObserver_activity_reconstruction a b
  have h₂ : P₂ * g₂ ^ 2 = c * d := arithmeticPrimitiveObserver_activity_reconstruction c d
  have h₃ : P₃ * g₃ ^ 2 = (a * c) * (b * d) :=
    arithmeticPrimitiveObserver_activity_reconstruction (a * c) (b * d)
  have hK : K * (g₁ * g₂) = g₃ :=
    arithmeticReserveTransgression_mul_oldReserve a b c d
  by_cases hz : g₁ * g₂ = 0
  · have hg₁ : g₁ = 0 ∨ g₂ = 0 := Nat.mul_eq_zero.mp hz
    rcases hg₁ with hg₁ | hg₂
    · have hab : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp hg₁
      simp [arithmeticPrimitiveObserver, hab.1, hab.2]
    · have hcd : c = 0 ∧ d = 0 := Nat.gcd_eq_zero_iff.mp hg₂
      simp [arithmeticPrimitiveObserver, hcd.1, hcd.2]
  · apply Nat.mul_right_cancel (Nat.pos_of_ne_zero (pow_ne_zero 2 hz))
    calc
      (P₁ * P₂) * (g₁ * g₂) ^ 2 = (P₁ * g₁ ^ 2) * (P₂ * g₂ ^ 2) := by ring
      _ = (a * b) * (c * d) := by rw [h₁, h₂]
      _ = (a * c) * (b * d) := by ring
      _ = P₃ * g₃ ^ 2 := h₃.symm
      _ = (P₃ * K ^ 2) * (g₁ * g₂) ^ 2 := by rw [← hK]; ring

/-- Bounded multiplicative activity has finite unreduced arithmetic sublevels. -/
theorem finite_arithmeticFormationSublevel (B : ℕ) :
    {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧ arithmeticActivity x.1 x.2 ≤ B}.Finite := by
  apply (Set.finite_Icc (1, 1) (B, B)).subset
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have haB : a ≤ B := by
    have haab : a ≤ a * b := by
      simpa using Nat.mul_le_mul_left a (show 1 ≤ b by omega)
    exact haab.trans hab
  have hbB : b ≤ B := by
    have hbab : b ≤ a * b := by
      simpa [mul_comm] using Nat.mul_le_mul_left b (show 1 ≤ a by omega)
    exact hbab.trans hab
  exact ⟨⟨by omega, by omega⟩, ⟨haB, hbB⟩⟩

theorem arithmeticPrimitiveObserver_diagonal {k : ℕ} (hk : 0 < k) :
    arithmeticPrimitiveObserver k k = (1, 1) := by
  simp [arithmeticPrimitiveObserver, Nat.gcd_self, Nat.div_self hk]

theorem arithmeticActivity_diagonal (k : ℕ) : arithmeticActivity k k = k ^ 2 := by
  simp [arithmeticActivity, pow_two]

/-- One observer fibre has unbounded unreduced activity. -/
theorem arithmeticPrimitiveObserver_notProper :
    ∀ B : ℕ, ∃ k : ℕ,
      arithmeticPrimitiveObserver k k = (1, 1) ∧ B < arithmeticActivity k k := by
  intro B
  refine ⟨B + 1, arithmeticPrimitiveObserver_diagonal (by omega), ?_⟩
  rw [arithmeticActivity_diagonal]
  have hle : B + 1 ≤ (B + 1) ^ 2 := by
    rw [pow_two]
    simpa only [mul_one] using
      Nat.mul_le_mul_left (B + 1) (show 1 ≤ B + 1 by omega)
  omega

theorem arithmeticFusion_reflected_closes (a : ℕ) :
    arithmeticFusion (a, 1) (1, a) = (a, a) := by
  simp [arithmeticFusion]

/-- Gauge/reflection-selected arithmetic half-density. -/
def arithmeticHalfDensity (a b : ℕ) : ℝ :=
  (Nat.gcd a b : ℝ) / Real.sqrt ((a : ℝ) * (b : ℝ))

theorem arithmeticHalfDensity_eq_inv_sqrt_primitiveProduct
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b =
      (Real.sqrt (((arithmeticPrimitiveObserver a b).1 *
        (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ))⁻¹ := by
  exact (RHTower.Sieve.inv_sqrt_reducedProduct ha hb).symm

/-- Real-valued normalized Haar mass of the actual lattice `n Zhat`. -/
def integralAdeleLatticeMassReal (n : ℕ) : ℝ :=
  (ccmRationalFiniteAdeleHaar (ccmRationalIntegralFiniteAdelesNSMulSet n)).toReal

theorem integralAdeleLatticeMassReal_eq_inv {n : ℕ} (hn : n ≠ 0) :
    integralAdeleLatticeMassReal n = (n : ℝ)⁻¹ := by
  rw [integralAdeleLatticeMassReal,
    ccmRationalFiniteAdeleHaar_integralSubring_nsmul hn,
    ENNReal.toReal_inv]
  simp

theorem integralAdeleLatticeMassRatio_gcd_lcm
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    integralAdeleLatticeMassReal (Nat.lcm a b) /
        integralAdeleLatticeMassReal (Nat.gcd a b) =
      (Nat.gcd a b : ℝ) / (Nat.lcm a b : ℝ) := by
  have hg : Nat.gcd a b ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left b ha)
  have hl : Nat.lcm a b ≠ 0 := Nat.ne_of_gt (Nat.lcm_pos ha hb)
  rw [integralAdeleLatticeMassReal_eq_inv hl,
    integralAdeleLatticeMassReal_eq_inv hg]
  field_simp

theorem arithmeticHalfDensity_sq_eq_adelicMassRatio
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b ^ 2 =
      integralAdeleLatticeMassReal (Nat.lcm a b) /
        integralAdeleLatticeMassReal (Nat.gcd a b) := by
  rw [integralAdeleLatticeMassRatio_gcd_lcm ha hb]
  have hab : (0 : ℝ) < (a : ℝ) * (b : ℝ) := by positivity
  have hg : (0 : ℝ) < (Nat.gcd a b : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left b ha
  have hl : (0 : ℝ) < (Nat.lcm a b : ℝ) := by
    exact_mod_cast (Nat.lcm_pos ha hb)
  have hgl : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = (a : ℝ) * (b : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  rw [arithmeticHalfDensity, div_pow, Real.sq_sqrt hab.le]
  field_simp [ne_of_gt hab, ne_of_gt hg, ne_of_gt hl]
  nlinarith

/-- The selected half-density is exactly the square root of the actual adelic lattice interval. -/
theorem arithmeticHalfDensity_eq_sqrt_adelicMassRatio
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    arithmeticHalfDensity a b =
      Real.sqrt
        (integralAdeleLatticeMassReal (Nat.lcm a b) /
          integralAdeleLatticeMassReal (Nat.gcd a b)) := by
  rw [← arithmeticHalfDensity_sq_eq_adelicMassRatio ha hb,
    Real.sqrt_sq_eq_abs]
  rw [abs_of_nonneg]
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- Closed certificate joining reserve conservation, arithmetic fusion/properness, forced
half-density, actual finite-adele Haar mass, and the critical reduced-ray coefficient. -/
theorem bidirectionalReserveArithmeticAdelicFormation_certificate :
    (∀ x y : BidirectionalFormation ℝ,
      BidirectionalFormation.visible x + BidirectionalFormation.visible y =
        BidirectionalFormation.visible (x + y) +
          (2 : ℕ) • BidirectionalFormation.transgression x y) ∧
    (∀ α β : ℝ,
      ((∀ r x y t, formationLogPotential α β (r + t) (x + t) (y + t) =
          formationLogPotential α β r x y) ∧
        (∀ r x y, formationLogPotential α β r y x =
          formationLogPotential α β r x y)) ↔
        α = 1 / 2 ∧ β = 1 / 2) ∧
    (∀ a b : ℕ,
      (arithmeticPrimitiveObserver a b).1 *
          (arithmeticPrimitiveObserver a b).2 * arithmeticReserve a b ^ 2 =
        arithmeticActivity a b) ∧
    (∀ a b c d : ℕ,
      ((arithmeticPrimitiveObserver a b).1 * (arithmeticPrimitiveObserver a b).2) *
          ((arithmeticPrimitiveObserver c d).1 * (arithmeticPrimitiveObserver c d).2) =
        ((arithmeticPrimitiveObserver (a * c) (b * d)).1 *
            (arithmeticPrimitiveObserver (a * c) (b * d)).2) *
          arithmeticReserveTransgression a b c d ^ 2) ∧
    (∀ B : ℕ,
      {x : ℕ × ℕ | 0 < x.1 ∧ 0 < x.2 ∧ arithmeticActivity x.1 x.2 ≤ B}.Finite) ∧
    (∀ B : ℕ, ∃ k : ℕ,
      arithmeticPrimitiveObserver k k = (1, 1) ∧ B < arithmeticActivity k k) ∧
    (∀ a b : ℕ, 0 < a → 0 < b →
      arithmeticHalfDensity a b =
          (Real.sqrt (((arithmeticPrimitiveObserver a b).1 *
            (arithmeticPrimitiveObserver a b).2 : ℕ) : ℝ))⁻¹ ∧
        arithmeticHalfDensity a b =
          Real.sqrt
            (integralAdeleLatticeMassReal (Nat.lcm a b) /
              integralAdeleLatticeMassReal (Nat.gcd a b))) := by
  exact ⟨BidirectionalFormation.visible_fusion_conservation,
    formationLogPotential_gauge_reflection_unique,
    arithmeticPrimitiveObserver_activity_reconstruction,
    arithmeticPrimitiveObserver_fusion_conservation,
    finite_arithmeticFormationSublevel,
    arithmeticPrimitiveObserver_notProper,
    fun _ _ ha hb =>
      ⟨arithmeticHalfDensity_eq_inv_sqrt_primitiveProduct ha hb,
        arithmeticHalfDensity_eq_sqrt_adelicMassRatio ha hb⟩⟩

end

end GaloisForLFunctions.RHTower
