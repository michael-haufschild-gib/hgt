import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimePhaseSectors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LocalPhaseContinuation

/-!
# Hamiltonian clocks in the phase sectors

Distinct times define orthogonal boundary sectors. Rotating a single prime,
in contrast, preserves the sector and leaves an explicitly measurable overlap.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology GaloisForLFunctions.HTGeometry

theorem clockPhase_div (t u : ℝ) : clockPhase u / clockPhase t = clockPhase (u-t) := by
  apply MonoidHom.ext
  intro n
  change Circle.exp (u*energy n) / Circle.exp (t*energy n) = Circle.exp ((u-t)*energy n)
  rw [sub_mul, Circle.exp_sub]

/-- A clock translates the partition argument along the imaginary axis. -/
theorem phaseTrace_clock (t : ℝ) (β : TraceTemperature) :
    phaseTrace (clockPhase t) β = riemannZeta ((β.val : ℂ) - (t : ℂ)*Complex.I) := by
  let s : {w : ℂ // 1 < w.re} := ⟨(β.val : ℂ) - (t : ℂ)*Complex.I, by
    simpa using β.property⟩
  change _ = riemannZeta s.val
  rw [← insertedPartition_one s, insertedPartition_eq_series, phaseTrace]
  apply tsum_congr
  intro n
  rw [Circle.coe_one, one_mul]
  change Complex.exp (((t * energy n : ℝ) : ℂ)*Complex.I) * (Real.exp (-β.val*energy n) : ℂ) =
    Complex.exp (-((β.val : ℂ)-(t : ℂ)*Complex.I)*(energy n : ℂ))
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem phaseOverlap_clocks (t u : ℝ) (β : TraceTemperature) :
    phaseOverlap (clockPhase t) (clockPhase u) β =
      riemannZeta ((β.val : ℂ)-((u-t : ℝ) : ℂ)*Complex.I) / riemannZeta β.val := by
  rw [phaseOverlap_eq_trace, clockPhase_div, phaseTrace_clock]

/-- The reciprocal partition vanishes at its simple pole. -/
theorem inverse_partition_limit :
    Tendsto (fun β : TraceTemperature => (riemannZeta β.val)⁻¹) atPartitionPole (𝓝 0) := by
  have hb := tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds
  have h := ((hb.sub_const 1).div (riemannZeta_residue_one.comp tendsto_temperature_punctured) one_ne_zero)
  rw [sub_self, zero_div] at h
  apply h.congr (fun β => ?_)
  have hne : (β.val : ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast β.property.ne')
  exact div_mul_cancel_left₀ hne _

/-- The simple pole separates every pair of distinct times. -/
theorem clock_samePhaseSector_iff (t u : ℝ) :
    samePhaseSector (clockPhase t) (clockPhase u) ↔ t = u := by
  constructor
  · intro hs
    by_contra htu
    let a := ((u-t : ℝ) : ℂ)*Complex.I
    have hreg : 1-a ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp [a] at hi
      exact htu (by linarith only [hi])
    have hb := tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds
    have hnum := (differentiableAt_riemannZeta hreg).continuousAt.tendsto.comp (hb.sub_const a)
    have hlim := hnum.mul inverse_partition_limit
    rw [mul_zero] at hlim
    apply ((phaseOverlap_zero_iff _ _).mp ?_) hs
    exact hlim.congr fun β => by rw [phaseOverlap_clocks, div_eq_mul_inv]; rfl
  · rintro rfl
    exact samePhaseSector_refl _

theorem phaseSector_clock_subsingleton (χ : ℕ+ →* Circle) :
    Set.Subsingleton {t : ℝ | samePhaseSector χ (clockPhase t)} := by
  intro t ht u hu
  exact (clock_samePhaseSector_iff t u).mp
    (samePhaseSector_trans ((samePhaseSector_symm _ _).mp ht) hu)

/-- A clock reference measures the phase-inserted trace at a shifted temperature. -/
theorem phaseOverlap_clock_inserted (t : ℝ) (ρ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseOverlap (clockPhase t) ρ β =
      insertedPartition ρ ⟨(β.val : ℂ)+(t : ℂ)*Complex.I, by simpa using β.property⟩ /
      riemannZeta β.val := by
  rw [phaseOverlap_eq_trace, phaseTrace, insertedPartition_eq_series]
  congr 1
  apply tsum_congr
  intro n
  rw [MonoidHom.div_apply, Circle.coe_div, div_eq_mul_inv, mul_assoc]
  congr 1
  change (Complex.exp (((t*energy n : ℝ) : ℂ)*Complex.I))⁻¹ * (Real.exp (-β.val*energy n) : ℂ) =
    Complex.exp (-((β.val : ℂ)+(t : ℂ)*Complex.I)*(energy n : ℂ))
  rw [← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  congr 1
  ring

private theorem phaseTrace_eq_inserted (ρ : ℕ+ →* Circle) (β : TraceTemperature) :
    phaseTrace ρ β = insertedPartition ρ ⟨(β.val : ℂ), β.property⟩ := by
  rw [phaseTrace, insertedPartition_eq_series]
  apply tsum_congr
  intro n
  simp only [heat, thermalWeight, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]

/-- Rotating one prime leaves precisely its Euler correction in the normalized scalar product. -/
theorem primeRotation_overlap (χ : ℕ+ →* Circle) (p : Nat.Primes) (z : Circle) (β : TraceTemperature) :
    phaseOverlap χ (primeRotation p z * χ) β = HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ) β.val := by
  rw [phaseOverlap_eq_trace, mul_div_cancel_right, phaseTrace_eq_inserted, primeRotation_trace,
    rotatedPartition, mul_div_cancel_left₀ _ (riemannZeta_ne_zero_of_one_lt_re β.property)]

theorem primeRotation_overlap_limit (χ : ℕ+ →* Circle) (p : Nat.Primes) (z : Circle) :
    Tendsto (phaseOverlap χ (primeRotation p z * χ)) atPartitionPole
      (𝓝 (HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ) 1)) := by
  have h := (primeCorrection_analytic_unit p z ⟨1,zero_lt_one⟩).1.continuousAt.tendsto.comp
    (tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds)
  exact h.congr fun β => (primeRotation_overlap χ p z β).symm

theorem primeRotation_samePhaseSector (χ : ℕ+ →* Circle) (p : Nat.Primes) (z : Circle) :
    samePhaseSector χ (primeRotation p z * χ) :=
  ((phaseOverlap_nonzero_limit_iff _ _).mp
    ⟨_, (primeCorrection_analytic_unit p z ⟨1,zero_lt_one⟩).2, primeRotation_overlap_limit χ p z⟩).1

#print axioms phaseOverlap_clocks
#print axioms clock_samePhaseSector_iff
#print axioms phaseSector_clock_subsingleton
#print axioms primeRotation_overlap_limit
#print axioms primeRotation_samePhaseSector

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
