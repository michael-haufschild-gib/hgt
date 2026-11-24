import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.PrimeTower
import GaloisForLFunctions.U0.U0NaturalBoundary

/-! # Unit probability law on lacunary powers of one prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open U0 U0NaturalBoundary
open _root_.RHTower.PrimeCoShift

/-- Probabilities on prime exponents, supported at 2^(j+1)-1. -/
def lacunaryMass (k : ℕ) := ‖lacCoeff k‖

theorem lacunaryMass_cast (k : ℕ) : (lacunaryMass k:ℂ) = lacCoeff k := by
  by_cases h : ∃ j : ℕ, 2^(j+1)-1 = k
  · obtain ⟨j,rfl⟩ := h
    rw [lacunaryMass,lacCoeff_emb,norm_zpow,Complex.norm_two,Complex.ofReal_zpow]
    norm_num
  · rw [lacunaryMass,lacCoeff_zero (fun j hj => h ⟨j,hj.symm⟩),norm_zero,Complex.ofReal_zero]

theorem lacunaryMass_sum : HasSum lacunaryMass 1 := by
  have hz (k : ℕ) (hk : k ∉ Set.range (fun j : ℕ => 2^(j+1)-1)) : lacunaryMass k = 0 := by
    rw [lacunaryMass,lacCoeff_zero (fun j hj => hk ⟨j,hj.symm⟩),norm_zero]
  apply (emb_inj.hasSum_iff hz).mp
  have hg := (hasSum_geometric_of_lt_one (r := (2:ℝ)⁻¹) (by norm_num) (by norm_num)).mul_right ((2:ℝ)⁻¹)
  have h1 : ((1-(2:ℝ)⁻¹)⁻¹*(2:ℝ)⁻¹) = 1 := by norm_num
  rw [h1] at hg
  have he (j : ℕ) : (lacunaryMass ∘ fun n : ℕ => 2^(n+1)-1) j = ((2:ℝ)⁻¹)^j*(2:ℝ)⁻¹ := by
    rw [Function.comp_apply,lacunaryMass,lacCoeff_emb,norm_zpow,Complex.norm_two,← pow_succ,inv_pow,zpow_neg]
    congr 1
  exact (congrArg (fun f : ℕ → ℝ => HasSum f 1) (funext he)).mpr hg

/-- The probability at the positive integer label, extended by zero outside the prime ray. -/
def lacunaryLaw (p : Nat.Primes) : ℕ+ → ℝ :=
  Function.extend (primeRayLabel p) lacunaryMass (fun _ => 0)

theorem lacunaryLaw_at (p : Nat.Primes) (k : ℕ) : lacunaryLaw p (primeRayLabel p k) = lacunaryMass k :=
  (primeRayLabel_injective p).extend_apply _ _ _

theorem lacunaryLaw_off (p : Nat.Primes) {n : ℕ+} (hn : n ∉ Set.range (primeRayLabel p)) : lacunaryLaw p n = 0 :=
  Function.extend_apply' _ _ _ hn

theorem lacunaryLaw_nonneg (p : Nat.Primes) (n : ℕ+) : 0 ≤ lacunaryLaw p n := by
  by_cases h : n ∈ Set.range (primeRayLabel p)
  · obtain ⟨k,rfl⟩ := h
    rw [lacunaryLaw_at]
    exact norm_nonneg _
  · exact (lacunaryLaw_off p h).ge

theorem lacunaryLaw_sum (p : Nat.Primes) : HasSum (lacunaryLaw p) 1 := by
  apply ((primeRayLabel_injective p).hasSum_iff (fun n hn => lacunaryLaw_off p hn)).mp
  have he : lacunaryLaw p ∘ primeRayLabel p = lacunaryMass := funext (lacunaryLaw_at p)
  rw [he]
  exact lacunaryMass_sum

theorem heat_primeRayLabel (p : Nat.Primes) (s : ℂ) (k : ℕ) :
    heat s (primeRayLabel p k) = heat s (primePNat p)^k := by
  rw [heat,heat,energy_primeRayLabel,Complex.ofReal_mul,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Removing zero labels gives the lacunary power series, with multiplicities and phases preserved. -/
theorem lacunaryLaw_hasSum_iff (p : Nat.Primes) (s b : ℂ) :
    HasSum (fun n => (lacunaryLaw p n:ℂ)*heat s n) b ↔
      HasSum (fun k => lacCoeff k*heat s (primePNat p)^k) b := by
  let f (n : ℕ+) := (lacunaryLaw p n:ℂ)*heat s n
  have hz (n : ℕ+) (hn : n ∉ Set.range (primeRayLabel p)) : f n = 0 := by
    change (lacunaryLaw p n:ℂ)*heat s n = 0
    rw [lacunaryLaw_off p hn,Complex.ofReal_zero,zero_mul]
  change HasSum f b ↔ _
  rw [← (primeRayLabel_injective p).hasSum_iff hz]
  have he (k : ℕ) : (f ∘ primeRayLabel p) k = lacCoeff k*heat s (primePNat p)^k := by
    change (lacunaryLaw p (primeRayLabel p k):ℂ)*heat s (primeRayLabel p k) = _
    rw [lacunaryLaw_at,lacunaryMass_cast,heat_primeRayLabel]
  exact (congrArg (fun g : ℕ → ℂ => HasSum g b) (funext he)).to_iff

#print axioms lacunaryMass_cast
#print axioms lacunaryMass_sum
#print axioms lacunaryLaw_at
#print axioms lacunaryLaw_off
#print axioms lacunaryLaw_nonneg
#print axioms lacunaryLaw_sum
#print axioms heat_primeRayLabel
#print axioms lacunaryLaw_hasSum_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
