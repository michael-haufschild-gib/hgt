import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Shells
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw
import GaloisForLFunctions.HTGeometry.NormalizedPureStateInfidelity

/-! # Exact Hilbert Gram law on composite shells of the prime gas -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite

open Finset Real
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

private theorem elementary_gram (s v : ℂ) (x : ℝ) :
    finiteComplexInner (fun p : PrimeAt x => heat s (primeLabel p))
      (fun p => heat v (primeLabel p)) = inner ℂ (rawWave s x) (rawWave v x) := by
  change (∑ p : PrimeAt x, conj (heat s (primeLabel p))*heat v (primeLabel p)) =
    ∑ p : PrimeAt x, heat v (primeLabel p)*conj (heat s (primeLabel p))
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- Only occupied integer shells contribute to the gas inner product. -/
theorem wave_pair_sum (m : ℕ) (s v : ℂ) (x : ℝ) :
    inner ℂ (wave m s x) (wave m v x) =
      ∑ n ∈ shells m x, conj (wave m s x n)*wave m v x n := by
  calc
    _ = ∑ n ∈ shells m x, inner ℂ (lp.single 2 n ((sqrt (multiplicity m x n):ℂ)*heat s n))
        (wave m v x) := sum_inner _ _ _
    _ = _ := by
      refine sum_congr rfl fun n _ => ?_
      rw [lp.inner_single_left,RCLike.inner_apply,wave_apply m s x n,mul_comm]

/-- Born mass on the product shells is the full squared Hilbert norm. -/
theorem norm_shell_sum (m : ℕ) (s : ℂ) (x : ℝ) :
    ‖wave m s x‖^2 = ∑ n ∈ shells m x, ‖wave m s x n‖^2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow,Complex.ofReal_sum]
  simp only [Complex.ofReal_pow,←Complex.conj_mul']
  have h := wave_pair_sum m s s x
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),RCLike.ofReal_eq_complex_ofReal] at h
  exact h

/-- The Gram pairing of two compressed gas waves is exactly the power
of the one-excitation pairing, including all repeated prime occupations. -/
theorem wave_gram (m : ℕ) (s v : ℂ) (x : ℝ) :
    inner ℂ (wave m s x) (wave m v x) = (inner ℂ (rawWave s x) (rawWave v x))^m := by
  let f (z : ℂ) (p : PrimeAt x) := heat z (primeLabel p)
  calc
    _ = ∑ n ∈ shells m x, conj (wave m s x n)*wave m v x n := wave_pair_sum m s v x
    _ = ∑ n ∈ shells m x, multiplicity m x n • (conj (heat s n)*heat v n) := by
      refine sum_congr rfl fun n _ => ?_
      rw [wave_apply,wave_apply,map_mul,Complex.conj_ofReal,nsmul_eq_mul]
      have sq : (sqrt (multiplicity m x n):ℂ)^2=(multiplicity m x n:ℂ) := by
        exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (multiplicity m x n))
      linear_combination (conj (heat s n)*heat v n)*sq
    _ = ∑ q : Fin m → PrimeAt x, conj (heat s (productLabel q))*heat v (productLabel q) :=
      sum_fibers m x _
    _ = finiteComplexInner (finitePureTensorPower m (f s)) (finitePureTensorPower m (f v)) := by
      unfold finiteComplexInner
      refine sum_congr rfl fun q _ => ?_
      simp only [heat_product,finitePureTensorPower,f]
    _ = _ := (finiteComplexInner_pureTensorPower m (f s) (f v)).trans
      (congrArg (fun z : ℂ => z^m) (elementary_gram s v x))

theorem wave_mass (m : ℕ) (s : ℂ) (x : ℝ) : ‖wave m s x‖^2=(‖rawWave s x‖^2)^m := by
  have g := wave_gram m s s x
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),inner_self_eq_norm_sq_to_K (𝕜:=ℂ)] at g
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_pow,RCLike.ofReal_eq_complex_ofReal] using g

/-- Normalized composite transition probabilities are exact powers
at every cutoff and every pair of complex heat parameters. -/
theorem fidelity_power (m : ℕ) (s v : ℂ) (x : ℝ) :
    normalizedPureStateFidelity (wave m s x) (wave m v x) =
      (normalizedPureStateFidelity (rawWave s x) (rawWave v x))^m := by
  rw [normalizedPureStateFidelity,normalizedPureStateFidelity,wave_gram,wave_mass,wave_mass,
    norm_pow,div_pow,mul_pow]
  have swap (a : ℝ) : (a^m)^2=(a^2)^m := by rw [←pow_mul,←pow_mul,mul_comm m 2]
  rw [swap]

/-- Zero excitations give the vacuum for every cutoff and temperature. -/
theorem vacuum_wave (s : ℂ) (x : ℝ) : wave 0 s x=lp.single 2 (1:ℕ+) (1:ℂ) := by
  classical
  have S : shells 0 x={1} := by simp [shells,productLabel]
  have M : multiplicity 0 x 1=1 := by simp [multiplicity,productLabel]
  rw [wave,S,sum_singleton,M]
  simp [heat,energy]

#print axioms norm_shell_sum
#print axioms wave_gram
#print axioms wave_mass
#print axioms fidelity_power
#print axioms vacuum_wave

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite
