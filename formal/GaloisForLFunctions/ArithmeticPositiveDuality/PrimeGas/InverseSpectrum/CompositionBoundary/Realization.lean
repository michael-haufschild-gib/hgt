import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.Response
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.CompositionBoundary.LacunaryLaw

/-! # The physical exterior wave underlying the lacunary response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open U0 U0NaturalBoundary
open _root_.RHTower.PrimeCoShift

private theorem lawTerm_norm (p : Nat.Primes) (s : ℂ) (n : ℕ+) :
    ‖(lacunaryLaw p n:ℂ)*heat (2*s-1) n‖ = shellMass s n*lacunaryLaw p n := by
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (lacunaryLaw_nonneg p n),composition_heat_norm,mul_comm]

private theorem lawTerm_summable_iff (p : Nat.Primes) (s : ℂ) :
    Summable (fun n => (lacunaryLaw p n:ℂ)*heat (2*s-1) n) ↔ 1/2 ≤ s.re := by
  constructor
  · intro hs
    by_contra! h
    have hg : 1 < ‖heat (2*s-1) (primePNat p)‖ := by
      rw [composition_heat_norm,shellMass,Real.one_lt_exp_iff]
      exact mul_pos (by linarith only [h]) (prime_energy_pos p)
    exact lac_not_summable hg ((lacunaryLaw_hasSum_iff p _ _).mp hs.hasSum).summable
  · intro hs
    apply Summable.of_norm_bounded (lacunaryLaw_sum p).summable
    intro n
    have h := shellMass_antitone_re (t := ((1/2:ℝ):ℂ)) (s := s) hs n
    have he : shellMass ((1/2:ℝ):ℂ) n = 1 := by norm_num [shellMass]
    rw [he] at h
    rw [lawTerm_norm]
    exact mul_le_of_le_one_left (lacunaryLaw_nonneg p _) h

/-- The mean label diverges because the lacunary series is outside its disk at time zero. -/
def lacunaryExteriorLaw (p : Nat.Primes) : ExteriorLaw := by
  refine ⟨lacunaryLaw p,lacunaryLaw_nonneg p,Equiv.pnatEquivNat.symm.hasSum_iff.mpr (lacunaryLaw_sum p),?_⟩
  intro h
  have hn : Summable (fun n => ‖(lacunaryLaw p n:ℂ)*heat (2*(0:ℂ)-1) n‖) := by
    apply Equiv.pnatEquivNat.symm.summable_iff.mp
    apply h.congr
    intro k
    change lacunaryLaw p (number k)/occupationWeight k = ‖(lacunaryLaw p (number k):ℂ)*heat (2*(0:ℂ)-1) (number k)‖
    rw [lawTerm_norm,shellMass_zero_eq_inv_occupationWeight,div_eq_inv_mul]
  exact (show ¬(1/2:ℝ) ≤ (0:ℂ).re by norm_num) ((lawTerm_summable_iff p 0).mp hn.of_norm)

def lacunaryOmission (p : Nat.Primes) := lawOmission (lacunaryExteriorLaw p)

theorem lacunary_probability (p : Nat.Primes) : occupationProbability (lacunaryOmission p) = lacunaryLaw p :=
  lawOmission_probability _

theorem lacunary_prime_support (p : Nat.Primes) : onPrimeRay p (lacunaryOmission p).val := by
  intro n hn
  change lawVector (lacunaryExteriorLaw p) n = 0
  rw [lawVector_apply]
  change (Real.sqrt (lacunaryLaw p n):ℂ) = 0
  rw [lacunaryLaw_off p hn,Real.sqrt_zero,Complex.ofReal_zero]

theorem lacunary_split_iff (p : Nat.Primes) (s : ℂ) : finiteSplit (lacunaryOmission p) s ↔ 1/2 ≤ s.re := by
  refine ⟨fun hf => ?_,fun h => (forall_finiteSplit_iff s).mpr h _⟩
  have ha := (response_absolute_iff _ _).mpr hf
  rw [lacunary_probability] at ha
  exact (lawTerm_summable_iff p s).mp ha.of_norm

/-- Explicit response on the full closed domain of absolute convergence. -/
theorem lacunary_response_eq (p : Nat.Primes) {s : ℂ} (hs : 1/2 ≤ s.re) :
    compositionResponse (lacunaryOmission p) s = u0 (heat (2*s-1) (primePNat p))⁻¹ := by
  rw [compositionResponse,lacunary_probability]
  have ht := (lacunaryLaw_hasSum_iff p (2*s-1) _).mp ((lawTerm_summable_iff p s).mpr hs).hasSum
  exact ht.tsum_eq.symm.trans ((lac_reindex _).trans (u0_inv_eq_companion _).symm)

#print axioms lacunary_probability
#print axioms lacunary_prime_support
#print axioms lacunary_split_iff
#print axioms lacunary_response_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
