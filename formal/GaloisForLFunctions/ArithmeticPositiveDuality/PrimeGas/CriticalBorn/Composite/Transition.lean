import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Gram
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.FidelityLimit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Spin.Fidelity

/-! # Critical isometry and spin transitions on multiplicative gas shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite

open Filter
open GaloisForLFunctions.HTGeometry
open Crossover
open scoped Topology ComplexConjugate

private theorem reflected_raw (s : ℂ) (x : ℝ) :
    normalizedPureStateFidelity (rawWave s x) (rawWave (1-conj s) x) = reflectedFidelity s x := by
  simp only [normalizedPureStateFidelity,reflectedFidelity,elementaryWave,inner_smul_left,inner_smul_right,
    norm_mul,RCLike.norm_conj,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),mul_pow,
    inv_pow,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Measured overlap of complementary preparations at fixed occupation number. -/
def reflectedProbability (m : ℕ) (s : ℂ) (x : ℝ) :=
  normalizedPureStateFidelity (wave m s x) (wave m (1-conj s) x)

theorem reflected_power (m : ℕ) (s : ℂ) (x : ℝ) :
    reflectedProbability m s x=(reflectedFidelity s x)^m := by
  rw [reflectedProbability,fidelity_power,reflected_raw]

/-- Every positive occupation sector sees exactly the same fixed critical line. -/
theorem reflected_limit (m : ℕ) (s : ℂ) :
    Tendsto (fun x : ℝ => reflectedProbability (m+1) s x) atTop (𝓝 (if s.re=1/2 then 1 else 0)) := by
  have h := (reflectedFidelity_limit s).pow (m+1)
  by_cases e : s.re=1/2
  · simpa only [reflected_power,if_pos e,one_pow] using h
  · simpa only [reflected_power,if_neg e,zero_pow (Nat.succ_ne_zero m)] using h

theorem reflected_iff_isometric (m : ℕ) (s : ℂ) :
    Tendsto (reflectedProbability (m+1) s) atTop (𝓝 1) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x := by
  rw [split_isometric_iff]
  have h := reflected_limit m s
  constructor
  · intro p
    by_contra off
    rw [if_neg off] at h
    exact zero_ne_one (tendsto_nhds_unique h p)
  · intro e
    simpa only [if_pos e] using h

/-- Fixed-occupation composite wave at moving temperature and clock time. -/
def movingWave (m : ℕ) (c t h : ℝ) (N : ℕ) :=
  wave m (indexParameter (drift c N/Real.log N) (t+h/Real.log N)) N

/-- The composite gas transition is the symmetric-power spin fidelity
on the actual integer-product shells. -/
theorem chordal_power (m : ℕ) (c d t h k : ℝ) :
    Tendsto (fun N : ℕ => normalizedPureStateFidelity (movingWave m c t h N) (movingWave m d t k N)) atTop
      (𝓝 ((1-_root_.Bottcher.chordalDist (Spin.coordinate c h) (Spin.coordinate d k)^2)^m)) := by
  apply ((Spin.chordal_fidelity c d t h k).pow m).congr
  intro N
  exact (fidelity_power m _ _ N).symm

#print axioms reflected_power
#print axioms reflected_limit
#print axioms reflected_iff_isometric
#print axioms chordal_power

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite
