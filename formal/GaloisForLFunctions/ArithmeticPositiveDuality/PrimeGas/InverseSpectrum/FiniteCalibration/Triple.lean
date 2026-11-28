import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Statistics
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace

/-! # The centered third moment of three distinct prime energies never vanishes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration

open Finset Real

def mode (p : Nat.Primes) : ℕ+ := ⟨p.val,p.property.pos⟩

def sample {n : ℕ} (P : Fin n ↪ Nat.Primes) (E : ℕ+ → ℝ) (i : Fin n) := E (mode (P i))

private theorem three_factors (x : Fin 3 → ℝ) :
    cubic x = 3*(2*x 0-x 1-x 2)*(2*x 1-x 0-x 2)*(2*x 2-x 0-x 1) := by
  simp only [cubic,Fin.sum_univ_three,Nat.cast_ofNat]
  ring

private theorem not_middle (p q r : Nat.Primes) (pq : p≠q) (pr : p≠r) :
    2*energy (mode p)-energy (mode q)-energy (mode r)≠0 := by
  intro h
  have logs : energy (mode p)+energy (mode p)=energy (mode q)+energy (mode r) := by linarith only [h]
  have e := congrArg exp logs
  have inv (x : Nat.Primes) : exp (energy (mode x))=(x.val:ℝ) := exp_log (Nat.cast_pos.mpr x.property.pos)
  rw [exp_add,exp_add,inv,inv,inv] at e
  have factor : p.val*p.val=q.val*r.val := by exact_mod_cast e
  have hd : p.val ∣ q.val*r.val := ⟨p.val,factor.symm⟩
  have identify (x : Nat.Primes) (d : p.val ∣ x.val) : p=x := by
    rcases (Nat.dvd_prime x.property).mp d with one|self
    · exact False.elim (p.property.ne_one one)
    · exact Subtype.ext self
  rcases p.property.dvd_mul.mp hd with d|d
  · exact pq (identify q d)
  · exact pr (identify r d)

/-- Unique factorization excludes a geometric progression of three distinct primes. -/
theorem prime_cubic_ne_zero (P : Fin 3 ↪ Nat.Primes) : cubic (sample P energy)≠0 := by
  rw [three_factors]
  have diff (i j : Fin 3) (h : i≠j) : P i ≠ P j := fun e => h (P.injective e)
  have h01 : (0:Fin 3)≠1 := by intro e; have hv := congrArg Fin.val e; norm_num at hv
  have h02 : (0:Fin 3)≠2 := by intro e; have hv := congrArg Fin.val e; norm_num at hv
  have h12 : (1:Fin 3)≠2 := by intro e; have hv := congrArg Fin.val e; norm_num at hv
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (not_middle _ _ _ (diff _ _ h01) (diff _ _ h02)))
    (not_middle _ _ _ (diff _ _ h01.symm) (diff _ _ h12)))
    (not_middle _ _ _ (diff _ _ h02.symm) (diff _ _ h12.symm))

#print axioms prime_cubic_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration
