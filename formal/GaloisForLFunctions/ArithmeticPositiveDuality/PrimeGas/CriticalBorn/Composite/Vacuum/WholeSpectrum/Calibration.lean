import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Preparation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Tomography.Extraction
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.TraceAbscissa

/-! # A self-calibrating vacuum detector for the unrestricted gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Finset Filter Real InverseSpectrum.ShellMixing
open scoped Topology

theorem plateau_limit (z : ℕ → SplitParameter) (s : ℂ) (N : ℕ) :
    Tendsto (reading z s N) atTop (𝓝 ((prefixMass (2*s.re) N)⁻¹)) := by
  have lim := Tomography.estimate_limit z (input s N) 0
  rw [population_eq,if_pos (Nat.succ_pos N),occupationWeight_zero,one_rpow,one_div] at lim
  apply lim.congr
  intro j
  simp only [Tomography.estimate,range_zero,sum_empty,sub_zero,occupationWeight_zero,one_pow,div_one]
  rfl

/-- The normalizer is the plateau of the same binary measurement at fixed cutoff. -/
def calibrated (z : ℕ → SplitParameter) (s : ℂ) (N j : ℕ) :=
  reading z s N j / limUnder atTop (reading z s N)

theorem calibrated_eq (z : ℕ → SplitParameter) (s : ℂ) (N j : ℕ) :
    calibrated z s N j = prefixMass (2*s.re+(j:ℝ)) N := by
  rw [calibrated,(plateau_limit z s N).limUnder_eq,reading_eq,div_inv_eq_mul,
    div_mul_cancel₀ _ (prefix_pos _ _).ne']

theorem prefix_limit (b : {b : ℝ // 1<b}) :
    Tendsto (prefixMass b.val) atTop (𝓝 (riemannZeta (b.val:ℂ)).re) := by
  let β : GibbsExponent := ⟨b.val,zero_lt_one.trans b.property⟩
  have hs := (hasSum_shellPower (β:=β) b.property).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply hs.congr
  intro N
  exact sum_congr rfl fun k _ => (occupation_rpow_eq_shellPower β k).symm

theorem critical_limit (k : ℕ) (t : ℕ → SplitParameter) (z : ℕ → ℕ → SplitParameter) :
    Tendsto (fun N => calibrated (z N) (t N).val N (k+1)) atTop
      (𝓝 (riemannZeta ((k+2:ℕ):ℂ)).re) := by
  let b : {a : ℝ // 1<a} := ⟨((k+2:ℕ):ℝ),by exact_mod_cast (show 1<k+2 by omega)⟩
  have h := prefix_limit b
  change Tendsto (prefixMass ((k+2:ℕ):ℝ)) atTop (𝓝 (riemannZeta (((k+2:ℕ):ℝ):ℂ)).re) at h
  rw [Complex.ofReal_natCast] at h
  apply h.congr
  intro N
  rw [calibrated_eq,(t N).property]
  congr 1
  push_cast
  ring

#print axioms plateau_limit
#print axioms calibrated_eq
#print axioms prefix_limit
#print axioms critical_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
