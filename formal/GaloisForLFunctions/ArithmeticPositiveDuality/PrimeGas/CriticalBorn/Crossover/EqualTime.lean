import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Transition

/-! # Gram kernel of equal-time elementary heat waves -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Real
open scoped ComplexConjugate Topology

/-- Complex heat parameter with elementary probability weights p^(a−1). -/
def indexParameter (a t : ℝ) : ℂ := (((1-a)/2 : ℝ):ℂ)+(t:ℂ)*Complex.I

private theorem index_sum (a b t : ℝ) :
    indexParameter b t + conj (indexParameter a t) =
    indexParameter ((a+b)/2) t + conj (indexParameter ((a+b)/2) t) := by
  apply Complex.ext
  · simp only [indexParameter,Complex.add_re,Complex.conj_re,Complex.ofReal_re,Complex.mul_I_re,
      Complex.ofReal_im]
    ring
  · simp only [indexParameter,Complex.add_im,Complex.conj_im,Complex.ofReal_im,Complex.mul_I_im,
      Complex.ofReal_re]

private theorem heat_pair (s v m : ℂ) (h : v+conj s=m+conj m) (n : ℕ+) :
    heat v n*conj (heat s n)=heat m n*conj (heat m n) := by
  have hc (z : ℂ) : conj (heat z n)=heat (conj z) n := by simp [heat,←Complex.exp_conj]
  rw [hc,hc,←heat_add,←heat_add,h]

/-- At a common clock time the off-diagonal Gram entry is exactly
the mass at the arithmetic mean of the two power indices. -/
theorem equal_time_gram (a b t x : ℝ) :
    inner ℂ (rawWave (indexParameter a t) x) (rawWave (indexParameter b t) x) =
      (powerMass ((a+b)/2) x:ℂ) := by
  let m := indexParameter ((a+b)/2) t
  calc
    _ = inner ℂ (rawWave m x) (rawWave m x) := by
      change (∑ p, rawWave (indexParameter b t) x p * conj (rawWave (indexParameter a t) x p)) =
        ∑ p, rawWave m x p * conj (rawWave m x p)
      exact Finset.sum_congr rfl fun p _ => heat_pair _ _ _ (index_sum a b t)
        ⟨p.val,(Nat.mem_primesBelow.mp p.property).2.pos⟩
    _ = ((‖rawWave m x‖^2:ℝ):ℂ) := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ),Complex.ofReal_pow]
      rfl
    _ = _ := by
      rw [rawWave_sq]
      have e : 1-2*m.re = (a+b)/2 := by
        simp only [m,indexParameter,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im]
        ring
      rw [e]

/-- Elementary transition wave on the side favoring large prime labels. -/
def windowWave (c t : ℝ) (N : ℕ) := rawWave (indexParameter (drift c N/log N) t) N

/-- After harmonic normalization, the coherent Gram kernel is the sum
of a constant bulk term and a rank-one terminal term. -/
theorem window_gram (c d t : ℝ) :
    Tendsto (fun N : ℕ => inner ℂ (windowWave c t N) (windowWave d t N) /
      (log (log N):ℂ)) atTop (𝓝 ((1+exp (c/2)*exp (d/2):ℝ):ℂ)) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (transition_masses ((c+d)/2)).1
  have half : (c+d)/2=c/2+d/2 := by ring
  rw [half,exp_add] at h
  apply h.congr
  intro N
  have eq : (drift c N/log N+drift d N/log N)/2 = drift (c/2+d/2) N/log N := by
    unfold drift displacement
    ring
  change ((powerMass (drift (c/2+d/2) N/log N) N/log (log N):ℝ):ℂ) = _
  rw [windowWave,windowWave,equal_time_gram,eq,Complex.ofReal_div]

#print axioms equal_time_gram
#print axioms window_gram

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
