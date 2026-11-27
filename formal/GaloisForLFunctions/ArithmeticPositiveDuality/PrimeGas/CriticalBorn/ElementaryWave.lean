import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Normalized elementary heat waves and their reflected Hilbert overlap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Finset Real
open scoped ComplexConjugate

private def shell {x : ℝ} (p : ↥(primes (cutoff x))) : ℕ+ :=
  ⟨p.val,(Nat.mem_primesBelow.mp p.property).2.pos⟩

/-- Heat amplitudes on the finite Hilbert space of elementary excitations. -/
def rawWave (s : ℂ) (x : ℝ) : EuclideanSpace ℂ ↥(primes (cutoff x)) :=
  WithLp.toLp 2 (fun p => heat s (shell p))

/-- Normalized state obtained by restricting the heat wave to elementary labels. -/
def elementaryWave (s : ℂ) (x : ℝ) := ((‖rawWave s x‖:ℂ)⁻¹) • rawWave s x

theorem rawWave_sq (s : ℂ) (x : ℝ) : ‖rawWave s x‖^2 = powerMass (1-2*s.re) x := by
  rw [EuclideanSpace.norm_sq_eq]
  have term (p : ↥(primes (cutoff x))) : ‖rawWave s x p‖^2 =
      (p.val:ℝ)^((1-2*s.re)-1) := by
    let q : Nat.Primes := ⟨p.val,(Nat.mem_primesBelow.mp p.property).2⟩
    have eq := bornWeight_eq_heat s q
    rw [show label (Finsupp.single q 1) = shell p from PNat.coe_injective (label_one_quantum q)] at eq
    change ‖heat s (shell p)‖^2 = _
    simpa only [bornWeight,show 1-2*s.re-1 = -(2*s.re) by ring] using eq.symm
  simp only [term,univ_eq_attach,powerMass]
  exact (primes (cutoff x)).sum_attach (fun p : ℕ => (p:ℝ)^(1-2*s.re-1))

private theorem raw_ne (s : ℂ) (x : ℝ) : ‖rawWave s x‖≠0 := by
  intro e
  have h := powerMass_pos (1-2*s.re) x
  rw [←rawWave_sq,e] at h
  norm_num at h

theorem elementaryWave_unit (s : ℂ) (x : ℝ) : ‖elementaryWave s x‖=1 := by
  simp only [elementaryWave,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (raw_ne s x)]

private theorem raw_overlap (s : ℂ) (x : ℝ) :
    inner ℂ (rawWave s x) (rawWave (1-conj s) x) = (powerMass 0 x:ℂ) := by
  change (∑ p : ↥(primes (cutoff x)), heat (1-conj s) (shell p)*conj (heat s (shell p))) = _
  have term (p : ↥(primes (cutoff x))) :
      heat (1-conj s) (shell p)*conj (heat s (shell p)) = (((p.val:ℝ)⁻¹:ℝ):ℂ) := by
    have c : conj (heat s (shell p)) = heat (conj s) (shell p) := by
      simp [heat,←Complex.exp_conj]
    rw [c,←heat_add,sub_add_cancel,heat_eq_cpow,Complex.cpow_neg,Complex.cpow_one]
    simp only [shell,Complex.ofReal_inv,Complex.ofReal_natCast]
    rfl
  simp only [term,univ_eq_attach,powerMass,zero_sub,rpow_neg_one,Complex.ofReal_sum]
  exact (primes (cutoff x)).sum_attach (fun p : ℕ => (((p:ℝ)⁻¹:ℝ):ℂ))

/-- Transition probability between the elementary heat state and its reflection. -/
def reflectedFidelity (s : ℂ) (x : ℝ) :=
  ‖inner ℂ (elementaryWave s x) (elementaryWave (1-conj s) x)‖^2

/-- All phases cancel coherently. The numerator is the squared harmonic
prime mass, with the two reflected masses supplying the normalization. -/
theorem reflectedFidelity_eq (s : ℂ) (x : ℝ) :
    reflectedFidelity s x = (powerMass 0 x)^2 /
      (powerMass (1-2*s.re) x * powerMass (-(1-2*s.re)) x) := by
  have idx : 1-2*(1-conj s).re = -(1-2*s.re) := by
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
    ring
  simp only [reflectedFidelity,elementaryWave,inner_smul_left,inner_smul_right,norm_mul,
    RCLike.norm_conj,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    raw_overlap,Real.norm_of_nonneg (powerMass_pos 0 x).le,mul_pow,inv_pow,rawWave_sq,idx]
  ring

#print axioms rawWave_sq
#print axioms elementaryWave_unit
#print axioms reflectedFidelity_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
