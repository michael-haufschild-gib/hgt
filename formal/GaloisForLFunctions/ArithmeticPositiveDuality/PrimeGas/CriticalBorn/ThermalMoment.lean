import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Parseval
import GaloisForLFunctions.LatticeSectionTheory.TheBoostTransformRestoresTheEulerProduct
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace

/-! # Thermal partition fluctuations measured by elementary clocks -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real
open scoped Topology

private def thermalCoefficient (σ : ℝ) (n : ℕ) := ((n:ℝ)+1)^(-σ)

def thermalDiagonal (σ : ℝ) (M : ℕ) := ∑ n ∈ range M, thermalCoefficient (2*σ) n

/-- The energy-cutoff Gibbs trace evolved for clock time log p. -/
def thermalTrace (σ : ℝ) (M p : ℕ) :=
  _root_.RHTower.Sieve.dirPoly M (fun n => (thermalCoefficient σ n.val : ℂ)) (-log p)

theorem thermalTrace_eq_sum_heat (σ : ℝ) (M p : ℕ) :
    thermalTrace σ M p = ∑ n : Fin M,
      heat ((σ : ℂ) + (log p : ℂ)*Complex.I) ⟨n.val+1,Nat.succ_pos _⟩ := by
  rw [thermalTrace,_root_.RHTower.Sieve.dirPoly]
  apply sum_congr rfl
  intro n _
  rw [thermalCoefficient,rpow_def_of_pos (by positivity),Complex.ofReal_exp,
    ←Complex.exp_add,heat,energy]
  change _ = Complex.exp (-((σ : ℂ) + (log p : ℂ)*Complex.I)*
    ((log (((n.val+1 : ℕ):ℝ)) : ℝ):ℂ))
  rw [Nat.cast_add,Nat.cast_one]
  congr 1
  push_cast
  ring

private theorem coefficient_square (σ : ℝ) (n : ℕ) :
    ‖(thermalCoefficient σ n : ℂ)‖^2 = thermalCoefficient (2*σ) n := by
  have pos : 0<(n:ℝ)+1 := by positivity
  rw [Complex.norm_real,Real.norm_eq_abs,thermalCoefficient,sq_abs,sq,←rpow_add pos,
    thermalCoefficient]
  congr 1
  ring

/-- At each fixed occupation cutoff the limiting second moment of the
thermal trace is the finite doubled-temperature partition sum. -/
theorem thermal_mean_square (σ : ℝ) (M : ℕ) :
    Tendsto (fun N => (∑ p ∈ primes N, weight p*‖thermalTrace σ M p‖^2)/mass N) atTop
      (𝓝 (thermalDiagonal σ M)) := by
  have h := preparation_mean_square (fun n : Fin M => (thermalCoefficient σ n.val : ℂ))
  simpa only [coefficient_square,Fin.sum_univ_eq_sum_range,thermalDiagonal,thermalTrace] using h

private theorem summable_thermal_iff (σ : ℝ) :
    Summable (thermalCoefficient (2*σ)) ↔ 1/2 < σ := by
  let f := fun n : ℕ => (n:ℝ)^(-(2*σ))
  have h (n : ℕ) : thermalCoefficient (2*σ) n = f (n+1) := by simp only [thermalCoefficient,f,Nat.cast_add,Nat.cast_one]
  rw [show thermalCoefficient (2*σ) = (fun n => f (n+1)) from funext h,
    summable_nat_add_iff (f := f) 1]
  change Summable (fun n : ℕ => (n:ℝ)^(-(2*σ))) ↔ _
  rw [Real.summable_nat_rpow]
  constructor <;> intro hh <;> linarith only [hh]

/-- Above the isometry line the second limit reads the zeta partition
function of the whole gas at doubled inverse temperature. -/
theorem thermal_zeta_limit {σ : ℝ} (hσ : 1/2 < σ) :
    Tendsto (thermalDiagonal σ) atTop (𝓝 (riemannZeta ((2*σ:ℝ):ℂ)).re) := by
  rw [GaloisForLFunctions.LatticeSectionTheory.riemannZeta_ofReal_eq_tsum
    (by linarith only [hσ] : 1 < 2*σ),Complex.ofReal_re]
  exact ((summable_thermal_iff σ).mpr hσ).hasSum.tendsto_sum_nat

/-- On and below the isometry line the same limiting second moments
diverge as the occupation cutoff is removed. -/
theorem thermal_diverges {σ : ℝ} (hσ : σ ≤ 1/2) : Tendsto (thermalDiagonal σ) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := thermalCoefficient (2*σ)) (fun n => rpow_nonneg (by positivity) _)).mp
  exact fun hs => hσ.not_gt ((summable_thermal_iff σ).mp hs)

#print axioms thermalTrace_eq_sum_heat
#print axioms thermal_mean_square
#print axioms thermal_zeta_limit
#print axioms thermal_diverges

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
