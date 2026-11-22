import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ChebyshevStatement
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveTruncatedRamp
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrincipalTruncatedRamp
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.TruncatedRampChangeLevel

/-! The truncated normalized explicit formula, uniform over all characters of a modulus. -/

open Complex Finset WindowedLandauTheory.HC WindowedLandauTheory.ZeroFreeDirichlet
open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

def ExplicitSWithOrders : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 → ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (K : ℂ),
      (∀ ρ ∈ Z, IsLZero χ ρ ∧ 1 - κ < ρ.re ∧ |ρ.im| ≤ T + 1) ∧
      (∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) ∧
      (∀ ρ ∈ Z, m ρ = analyticOrderNatAt χ.LFunction ρ) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), m ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) ∧
      ∀ y : ℝ, 2 ≤ y →
        ‖WindowedLandauTheory.HC.An.sumLamChi χ y / (y : ℂ) - K - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                  ∑ ρ ∈ Z, (m ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
          C * (((M : ℝ) * T) ^ C * y ^ (-(κ / 2)) + Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T)

private theorem kernel_eq_shift {y : ℝ} (hy : 0 < y) (ρ : ℂ) :
    QH.zeroKernel y ρ = (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
  rw [QH.zeroKernel, Complex.cpow_sub _ _ (ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
  simp only [div_div, mul_comm (ρ * (ρ - 1)) (y : ℂ)]

/-- Primitive zero sums with their actual multiplicities give a finite uniform formula at
every modulus. The finite Euler correction changes only the constant and the power error. -/
theorem truncated_explicit_formula_with_orders : ExplicitSWithOrders := by
  intro κ hκ hκ'
  obtain ⟨A, hA, hprimitive⟩ := primitive_truncated_ramp
  obtain ⟨B, hB, hprincipal⟩ := principal_truncated_ramp
  let D := max A B + 8
  let C := 2 * D + 3
  have hD : 0 < D := add_pos_of_pos_of_nonneg (hA.trans_le (le_max_left _ _)) (by norm_num)
  have hDC : D ≤ C := by dsimp only [C]; linarith
  have hC3 : 3 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, by linarith, ?_⟩
  intro M _ χ T hM hT
  have hf : TruncatedRamp χ κ T D := by
    by_cases hχ : χ = 1
    · subst χ
      rw [← DirichletCharacter.changeLevel_one (one_dvd M)]
      exact (truncated_ramp_changeLevel (one_dvd M) (1 : DirichletCharacter ℂ 1) hκ' hT hB.le
        (hprincipal κ T hκ hκ' hT)).mono (add_le_add (le_max_right _ _) le_rfl) hT
    · let ψ := χ.primitiveCharacter
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hψ : ψ ≠ 1 := fun he => hχ (by rw [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from he, map_one])
      have hp := hprimitive χ.conductor ψ hψ χ.primitiveCharacter_isPrimitive κ T hκ hκ' hT
      rw [← χ.changeLevel_primitiveCharacter]
      exact (truncated_ramp_changeLevel χ.conductor_dvd_level ψ hκ' hT hA.le hp).mono
        (add_le_add (le_max_left _ _) le_rfl) hT
  obtain ⟨Z, K, hZ, hmult, hcount, herror⟩ := hf
  let m := analyticOrderNatAt χ.LFunction
  refine ⟨Z, m, K, ?_, ?_, fun _ _ => rfl, hmult, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hz, hre, him⟩ := (hZ ρ).mp hρ
    exact ⟨hz, hre, by linarith⟩
  · intro ρ hz hre him
    exact (hZ ρ).mpr ⟨hz, by show 1 - κ < ρ.re; linarith, him⟩
  · intro ρ hρ hd
    have hz := ((hZ ρ).mp hρ).1
    have he := (lFunction_analyticAt χ hz.1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz.2 hd
    simp [m, analyticOrderNatAt, he]
  · intro t
    push_cast
    refine (hcount t).trans (mul_le_mul_of_nonneg_right hDC ?_)
    have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
    exact Real.log_nonneg ((show (1 : ℝ) ≤ |t| + 2 by linarith [abs_nonneg t]).trans
      (le_mul_of_one_le_left (by positivity) hM₁))
  · intro y hy
    have hy₀ : 0 < y := by linarith
    simp only [mul_div_assoc, ← kernel_eq_shift hy₀]
    have hmain : rampMain χ y = (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) := by
      by_cases hχ : χ = 1 <;> simp [rampMain, hχ]
    have herr := herror y hy
    rw [hmain] at herr
    refine herr.trans ?_
    have hM₁ : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
    have hMT : (1 : ℝ) ≤ (M : ℝ) * T := one_le_mul_of_one_le_of_one_le hM₁ (by linarith)
    have hpow : (M : ℝ) ^ 3 ≤ ((M : ℝ) * T) ^ C := by
      rw [show (M : ℝ) ^ (3 : ℕ) = (M : ℝ) ^ (3 : ℝ) by norm_num [Real.rpow_natCast]]
      refine (Real.rpow_le_rpow (by positivity)
        (le_mul_of_one_le_right (by positivity) (by linarith : 1 ≤ T)) (by norm_num : (0 : ℝ) ≤ 3)).trans
        (Real.rpow_le_rpow_of_exponent_le hMT hC3)
    have hlogy : (1 / 2 : ℝ) ≤ Real.log y :=
      (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
        (Real.log_le_log (by norm_num) hy)
    rw [mul_add, mul_add]
    refine add_le_add
      (mul_le_mul hDC (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity) (by positivity)) ?_
    have hCd : 2 * D ≤ C := by dsimp only [C]; linarith
    have hcyl : D ≤ C * Real.log y := by
      linarith only [mul_le_mul_of_nonneg_left hlogy (show 0 ≤ C by linarith), hCd]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcyl (by positivity)

theorem truncated_normalized_explicit_formula : ExplicitS := by
  intro κ hκ hκ'
  obtain ⟨C, hC, hE⟩ := truncated_explicit_formula_with_orders κ hκ hκ'
  refine ⟨C, hC, fun M _ χ T hM hT => ?_⟩
  obtain ⟨Z, m, K, hZ, hcover, -, hm, hsimple, hcount, herr⟩ := hE M χ T hM hT
  exact ⟨Z, m, K, hZ, hcover, hm, hsimple, hcount, herr⟩

end QH.PrimeProgressions
