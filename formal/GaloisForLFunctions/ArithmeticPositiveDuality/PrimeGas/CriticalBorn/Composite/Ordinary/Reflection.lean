import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Heat
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.FidelityLimit

/-! # Critical composition detected by plain fixed-occupation heat states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary

open Filter Real
open GaloisForLFunctions.HTGeometry
open scoped Topology ComplexConjugate

def reflectedProbability (m : ℕ) (s : ℂ) (x : ℝ) :=
  normalizedPureStateFidelity (wave m s x) (wave m (1-conj s) x)

theorem measured (m : ℕ) (s : ℂ) (x : ℝ) :
    reflectedProbability m s x=(mass m 0 x)^2/
      (mass m (1-2*s.re) x * mass m (-(1-2*s.re)) x) := by
  have idx : 1-2*(1-conj s).re= -(1-2*s.re) := by
    simp only [Complex.sub_re,Complex.one_re,Complex.conj_re]
    ring
  rw [reflectedProbability,normalizedPureStateFidelity,reflected_pair,Complex.norm_real,
    Real.norm_of_nonneg (mass_pos m 0 x).le,wave_mass,wave_mass,idx]

private theorem comparison (m : ℕ) (a x : ℝ) :
    (mass m 0 x)^2/(mass m a x*mass m (-a) x) ≤ (m.factorial:ℝ)^2*
      ((powerMass 0 x)^2/(powerMass a x*powerMass (-a) x))^m := by
  let A := (powerMass 0 x)^m
  let D := (powerMass a x)^m*(powerMass (-a) x)^m
  let C : ℝ := m.factorial
  have dp : 0<D := mul_pos (pow_pos (powerMass_pos a x) _) (pow_pos (powerMass_pos (-a) x) _)
  have frac : ((powerMass 0 x)^2/(powerMass a x*powerMass (-a) x))^m=A^2/D := by
    dsimp [A,D]
    rw [div_pow,mul_pow,←pow_mul (powerMass 0 x),←pow_mul (powerMass 0 x),Nat.mul_comm 2 m]
  rw [frac]
  apply (div_le_iff₀ (mul_pos (mass_pos m a x) (mass_pos m (-a) x))).mpr
  have den : D≤(C*mass m a x)*(C*mass m (-a) x) :=
    mul_le_mul (mass_bounds m a x).2 (mass_bounds m (-a) x).2 (pow_pos (powerMass_pos (-a) x) _).le
      (mul_nonneg (Nat.cast_nonneg _) (mass_pos m a x).le)
  calc
    (mass m 0 x)^2 ≤ A^2 := pow_le_pow_left₀ (mass_pos m 0 x).le (mass_bounds m 0 x).1 2
    _ = (A^2/D)*D := (div_mul_cancel₀ _ dp.ne').symm
    _ ≤ (A^2/D)*((C*mass m a x)*(C*mass m (-a) x)) :=
      mul_le_mul_of_nonneg_left den (div_nonneg (sq_nonneg _) dp.le)
    _ = _ := by dsimp [C]; ring

/-- Every fixed positive sector of the ordinary Gibbs amplitudes
distinguishes the critical line from both open half-planes. -/
theorem reflected_limit (m : ℕ) (s : ℂ) :
    Tendsto (reflectedProbability (m+1) s) atTop (𝓝 (if s.re=1/2 then 1 else 0)) := by
  by_cases e : s.re=1/2
  · rw [if_pos e]
    apply tendsto_const_nhds.congr
    intro x
    rw [measured,e,show (1:ℝ)-2*(1/2)=0 by ring,neg_zero,sq,div_self
      (mul_ne_zero (mass_pos (m+1) 0 x).ne' (mass_pos (m+1) 0 x).ne')]
  · rw [if_neg e]
    have upper := ((reflectedFidelity_limit s).pow (m+1)).const_mul (((m+1).factorial:ℝ)^2)
    rw [if_neg e,zero_pow (Nat.succ_ne_zero m),mul_zero] at upper
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper
    · intro x
      rw [measured]
      exact div_nonneg (sq_nonneg _) (mul_nonneg (mass_pos _ _ _).le (mass_pos _ _ _).le)
    · intro x
      change reflectedProbability (m+1) s x ≤ _*(reflectedFidelity s x)^(m+1)
      rw [measured,reflectedFidelity_eq]
      exact comparison (m+1) _ x

/-- One ordinary fixed-occupation sector detects isometric splitting
on the full Hilbert space. Every positive occupation number works. -/
theorem isometric_iff (m : ℕ) (s : ℂ) :
    Tendsto (reflectedProbability (m+1) s) atTop (𝓝 1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x,T f x=split s f x := by
  rw [split_isometric_iff]
  have h := reflected_limit m s
  constructor
  · intro p
    by_contra off
    rw [if_neg off] at h
    exact zero_ne_one (tendsto_nhds_unique h p)
  · intro e
    simpa only [if_pos e] using h

#print axioms measured
#print axioms reflected_limit
#print axioms isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary
