import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsThePositivityLevel
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsHaveGlobalContinuation
import GaloisForLFunctions.HeckeLFunctions.HeckeEulerLogarithmsGiveTheThreeFourOneInequality

/-!
# The continuation frame holds for Hecke L-functions

The family of the continuation is the set of `L`-functions of the nontrivial ray class characters
of a number field. For each of them the kernel `exp((s − c)²)/L(s, ψ)` is a signal kernel, so the
continuation step applies to the whole family.

* **A lower bound in the half-plane of convergence** (`exp_neg_le_norm_heckeL`). For `Re s ≥ 2`,
  `|L(s, ψ)| ≥ exp(−(3/2) Σ_𝔭 N𝔭^{−2})`: the Euler logarithm is at most `(3/2) Σ_𝔭 N𝔭^{−Re s}`.
* **The kernel** (`isSignalKernel_heckeKernel`).
* **One function** (`heckeLFunction_ne_zero_of_signal_le`). If the signal of the kernel of `ψ`
  is `O(Z^b)`, `b < 1`, then `L(s, ψ)` has no zero in `Re s > b`.
* **The family** (`heckeLFunction_ne_zero_of_family_common_signal`). Suppose that whenever all
  nontrivial ray class characters of all moduli are zero-free in `Re s > β`, each of them has a
  sum with a direct bound `Z^{a₁}` and a comparison `Z^{a₂}` with its signal, `a₁, a₂ < β` the
  same for all. Then none of them has a zero in `Re s > σ₀`.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- The norm of `N𝔭^{−2}`. -/
theorem norm_absNorm_cpow_neg_two (v : HeightOneSpectrum (𝓞 K)) :
    ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ = ((v.asIdeal.absNorm : ℝ) ^ 2)⁻¹ := by
  have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
    ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
  have hv0 : 0 < Ideal.absNorm v.asIdeal := by omega
  rw [Complex.norm_natCast_cpow_of_pos hv0]
  have hre : (-(2 : ℂ)).re = -(2 : ℝ) := by simp
  rw [hre, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]

/-- **A lower bound for a Hecke `L`-series on `Re s ≥ 2`.** -/
theorem exp_neg_le_norm_heckeL {s : ℂ} (hs : 2 ≤ s.re) :
    Real.exp (-(3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K),
        ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖)) ≤ ‖heckeL 𝔪 ψ s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hS : Summable fun v : HeightOneSpectrum (𝓞 K) =>
      ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ :=
    numberField_summable_finitePlace_norm_cpow (K := K) (s := 2) (by norm_num)
  have hterm : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖heckePrimeTerm 𝔪 ψ s v‖ ≤ ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ := by
    intro v
    have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
      ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
    have hv0 : 0 < Ideal.absNorm v.asIdeal := by omega
    have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
    calc ‖heckePrimeTerm 𝔪 ψ s v‖
        = ‖heckeValue 𝔪 ψ v.asIdeal‖ * ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ := norm_mul _ _
      _ ≤ ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (norm_heckeValue_le_one 𝔪 ψ _)
      _ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
          rw [Complex.norm_natCast_cpow_of_pos hv0, Complex.neg_re]
      _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = ‖(Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 : ℂ))‖ := by
          rw [norm_absNorm_cpow_neg_two, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two]
  have hhalf : ∀ v : HeightOneSpectrum (𝓞 K), ‖-heckePrimeTerm 𝔪 ψ s v‖ ≤ 1 / 2 := by
    intro v
    have hv : 2 ≤ Ideal.absNorm v.asIdeal :=
      ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot
    have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hv
    have h4 : (4 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ 2 := by nlinarith
    rw [norm_neg]
    calc ‖heckePrimeTerm 𝔪 ψ s v‖ ≤ ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ := hterm v
      _ = ((v.asIdeal.absNorm : ℝ) ^ 2)⁻¹ := norm_absNorm_cpow_neg_two v
      _ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h4
      _ ≤ 1 / 2 := by norm_num
  have hlog : ∀ v : HeightOneSpectrum (𝓞 K), ‖-log (1 - heckePrimeTerm 𝔪 ψ s v)‖ ≤
      3 / 2 * ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ := by
    intro v
    rw [norm_neg, sub_eq_add_neg]
    refine (Complex.norm_log_one_add_half_le_self (hhalf v)).trans ?_
    rw [norm_neg]
    exact mul_le_mul_of_nonneg_left (hterm v) (by norm_num)
  have hsumlog : Summable fun v : HeightOneSpectrum (𝓞 K) =>
      ‖-log (1 - heckePrimeTerm 𝔪 ψ s v)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hlog (hS.mul_left _)
  have hT : ‖∑' v : HeightOneSpectrum (𝓞 K), -log (1 - heckePrimeTerm 𝔪 ψ s v)‖ ≤
      3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K), ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ := by
    calc ‖∑' v : HeightOneSpectrum (𝓞 K), -log (1 - heckePrimeTerm 𝔪 ψ s v)‖
        ≤ ∑' v : HeightOneSpectrum (𝓞 K), ‖-log (1 - heckePrimeTerm 𝔪 ψ s v)‖ :=
          norm_tsum_le_tsum_norm hsumlog
      _ ≤ ∑' v : HeightOneSpectrum (𝓞 K),
            3 / 2 * ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ :=
          Summable.tsum_le_tsum hlog hsumlog (hS.mul_left _)
      _ = 3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K), ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖ :=
          tsum_mul_left
  rw [← exp_tsum_heckeEulerLog 𝔪 ψ hs1, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre := Complex.abs_re_le_norm
    (∑' v : HeightOneSpectrum (𝓞 K), -log (1 - heckePrimeTerm 𝔪 ψ s v))
  have hneg := neg_abs_le (∑' v : HeightOneSpectrum (𝓞 K),
    -log (1 - heckePrimeTerm 𝔪 ψ s v)).re
  linarith

/-- The kernel of a Hecke character with Gaussian centre `c`: `exp((s − c)²)/L(s, ψ)`. -/
def heckeKernel (c : ℝ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2) / heckeLFunction 𝔪 ψ s

variable {𝔪 ψ}

/-- **The kernel of a nontrivial Hecke character is a signal kernel.** -/
theorem isSignalKernel_heckeKernel (hψ : ψ ≠ 1) (c : ℝ) :
    IsSignalKernel (heckeKernel 𝔪 ψ c) where
  differentiableAt s hs := by
    unfold heckeKernel
    exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).div
      (differentiable_heckeLFunction 𝔪 hψ s)
      (by rw [heckeLFunction_eq_heckeL 𝔪 ψ hs]; exact heckeL_ne_zero 𝔪 ψ hs)
  decay B := by
    refine ⟨Real.exp ((B + |c|) ^ 2) * Real.exp (3 / 2 * ∑' v : HeightOneSpectrum (𝓞 K),
      ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖), fun s h2 hB => ?_⟩
    have hs1 : 1 < s.re := by linarith
    have hz := exp_neg_le_norm_heckeL 𝔪 ψ h2
    have hzpos : 0 < ‖heckeL 𝔪 ψ s‖ := lt_of_lt_of_le (Real.exp_pos _) hz
    have hsq : (s.re - c) ^ 2 ≤ (B + |c|) ^ 2 := by
      have habs : |s.re - c| ≤ B + |c| := by
        rw [abs_le]
        constructor <;> linarith [neg_abs_le c, le_abs_self c]
      calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
        _ ≤ (B + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hexp : Real.exp (-(s.im ^ 2)) ≤ 1 / (1 + s.im ^ 2) := by
      rw [Real.exp_neg, one_div]
      refine inv_anti₀ (by positivity) ?_
      linarith [Real.add_one_le_exp (s.im ^ 2)]
    have hnum : ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := by
      rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul (Real.exp_le_exp.mpr hsq) hexp (Real.exp_pos _).le (Real.exp_pos _).le
    unfold heckeKernel
    rw [heckeLFunction_eq_heckeL 𝔪 ψ hs1, norm_div, div_le_iff₀ hzpos]
    set S := ∑' v : HeightOneSpectrum (𝓞 K), ‖((v.asIdeal.absNorm : ℂ) ^ (-(2 : ℂ)))‖
    have hE : 0 < Real.exp (3 / 2 * S) := Real.exp_pos _
    calc ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((B + |c|) ^ 2) * (1 / (1 + s.im ^ 2)) := hnum
      _ = Real.exp ((B + |c|) ^ 2) * Real.exp (3 / 2 * S) / (1 + s.im ^ 2) *
            Real.exp (-(3 / 2 * S)) := by
          rw [Real.exp_neg]
          field_simp
      _ ≤ Real.exp ((B + |c|) ^ 2) * Real.exp (3 / 2 * S) / (1 + s.im ^ 2) *
            ‖heckeL 𝔪 ψ s‖ :=
          mul_le_mul_of_nonneg_left hz (by positivity)

/-- **One function.** If the signal of the kernel of a nontrivial Hecke character is `O(Z^b)`
with `b < 1`, its `L`-function has no zero in `Re s > b`. -/
theorem heckeLFunction_ne_zero_of_signal_le (hψ : ψ ≠ 1) {c b C Z₀ : ℝ} (hb : b < 1)
    (hZ₀ : 0 < Z₀) (hC : ∀ Z : ℝ, Z₀ ≤ Z → ‖signal (heckeKernel 𝔪 ψ c) 2 Z‖ ≤ C * Z ^ b)
    (ρ : ℂ) (hρ : b < ρ.re) : heckeLFunction 𝔪 ψ ρ ≠ 0 :=
  ne_zero_of_signal_le (isSignalKernel_heckeKernel hψ c) hb hZ₀ hC
    (differentiable_heckeLFunction 𝔪 hψ).differentiableOn
    (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn
    (fun s _ => Complex.exp_ne_zero _)
    (fun s hs => by
      unfold heckeKernel
      exact div_mul_cancel₀ _
        (by rw [heckeLFunction_eq_heckeL 𝔪 ψ hs]; exact heckeL_ne_zero 𝔪 ψ hs))
    ρ hρ

/-- **Family continuation for the Hecke `L`-functions of a number field.** The family is indexed
by the nontrivial ray class characters of all moduli. -/
theorem heckeLFunction_ne_zero_of_family_common_signal (K : Type*) [Field K] [NumberField K]
    {σ₀ : ℝ} (hσ₀ : σ₀ < 1) (c : ℝ)
    (hstep : ∀ β : ℝ, σ₀ < β → β ≤ 1 →
      (∀ (η : Σ 𝔫 : Modulus K, {φ : HeckeCharacter 𝔫 // φ ≠ 1}) (ρ : ℂ), β < ρ.re →
        heckeLFunction η.1 η.2.1 ρ ≠ 0) →
      ∃ a₁ a₂ : ℝ, a₁ < β ∧ a₂ < β ∧
        ∀ η : Σ 𝔫 : Modulus K, {φ : HeckeCharacter 𝔫 // φ ≠ 1},
          ∃ (J : ℝ → ℂ) (C Z₀ : ℝ), 1 ≤ Z₀ ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z‖ ≤ C * Z ^ a₁) ∧
            (∀ Z : ℝ, Z₀ ≤ Z → ‖J Z - signal (heckeKernel η.1 η.2.1 c) 2 Z‖ ≤ C * Z ^ a₂))
    (𝔫 : Modulus K) {φ : HeckeCharacter 𝔫} (hφ : φ ≠ 1) (ρ : ℂ) (hρ : σ₀ < ρ.re) :
    heckeLFunction 𝔫 φ ρ ≠ 0 :=
  ne_zero_of_family_common_signal
    (ι := Σ 𝔫 : Modulus K, {φ : HeckeCharacter 𝔫 // φ ≠ 1})
    (G := fun η => heckeKernel η.1 η.2.1 c) (L := fun η => heckeLFunction η.1 η.2.1)
    (E := fun _ s => cexp ((s - c) ^ 2)) hσ₀
    (fun η => isSignalKernel_heckeKernel η.2.2 c)
    (fun η => (differentiable_heckeLFunction η.1 η.2.2).differentiableOn)
    (fun _ => (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((s - c) ^ 2)).differentiableOn)
    (fun _ s _ => Complex.exp_ne_zero _)
    (fun η s hs => by
      show heckeKernel η.1 η.2.1 c s * heckeLFunction η.1 η.2.1 s = cexp ((s - c) ^ 2)
      unfold heckeKernel
      exact div_mul_cancel₀ _
        (by rw [heckeLFunction_eq_heckeL η.1 η.2.1 hs]; exact heckeL_ne_zero η.1 η.2.1 hs))
    hstep ⟨𝔫, φ, hφ⟩ ρ hρ

end GaloisForLFunctions.FamilyContinuationTheory
