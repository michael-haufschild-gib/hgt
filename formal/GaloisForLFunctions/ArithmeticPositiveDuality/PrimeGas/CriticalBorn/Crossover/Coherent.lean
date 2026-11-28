import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.EqualTime

/-! # Two coherent amplitudes in the elementary transition window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Finset Real
open scoped Topology ComplexConjugate

private theorem cast_sq_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖^2:ℝ):ℂ) = inner ℂ x x := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ),Complex.ofReal_pow]
  rfl

private theorem amplitude_square {ι : Type*} (S : Finset ι) (z : ι → ℂ) :
    ((‖∑ i ∈ S, z i‖^2:ℝ):ℂ) = ∑ i ∈ S, ∑ j ∈ S, conj (z i)*z j := by
  rw [Complex.ofReal_pow,←Complex.conj_mul']
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

private theorem gram_sum {ι : Type*} (S : Finset ι) (z : ι → ℂ) (c : ι → ℝ) :
    (∑ i ∈ S, ∑ j ∈ S, conj (z i)*z j*((1+exp (c i/2)*exp (c j/2):ℝ):ℂ)) =
      ((‖∑ i ∈ S,z i‖^2 + ‖∑ i ∈ S,z i*(exp (c i/2):ℂ)‖^2:ℝ):ℂ) := by
  rw [Complex.ofReal_add,amplitude_square,amplitude_square,←Finset.sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [←Finset.sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_one]
  ring

/-- The limiting norm of every coherent preparation splits into two squared
amplitudes, one common to all offsets and one weighted by their terminal mass. -/
theorem coherent_norm {ι : Type*} (S : Finset ι) (z : ι → ℂ) (c : ι → ℝ) (t : ℝ) :
    Tendsto (fun N : ℕ => ‖∑ i ∈ S, z i • windowWave (c i) t N‖^2 / log (log N)) atTop
      (𝓝 (‖∑ i ∈ S,z i‖^2 + ‖∑ i ∈ S,z i*(exp (c i/2):ℂ)‖^2)) := by
  have lim := tendsto_finsetSum S fun i _ => tendsto_finsetSum S fun j _ =>
    (window_gram (c i) (c j) t).const_mul (conj (z i)*z j)
  rw [gram_sum] at lim
  have hc : Tendsto (fun N : ℕ => ((‖∑ i ∈ S,z i • windowWave (c i) t N‖^2 /
      log (log N):ℝ):ℂ)) atTop (𝓝 ((‖∑ i ∈ S,z i‖^2 + ‖∑ i ∈ S,z i*(exp (c i/2):ℂ)‖^2:ℝ):ℂ)) := by
    apply lim.congr
    intro N
    rw [Complex.ofReal_div,cast_sq_norm,sum_inner]
    simp only [inner_sum,inner_smul_left,inner_smul_right,Finset.sum_div]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  exact Complex.continuous_re.continuousAt.tendsto.comp hc

/-- Complete criterion for destructive interference in the transition window. -/
theorem coherent_vanishes_iff {ι : Type*} (S : Finset ι) (z : ι → ℂ) (c : ι → ℝ) (t : ℝ) :
    Tendsto (fun N : ℕ => ‖∑ i ∈ S,z i • windowWave (c i) t N‖^2/log (log N)) atTop (𝓝 0) ↔
      (∑ i ∈ S,z i)=0 ∧ (∑ i ∈ S,z i*(exp (c i/2):ℂ))=0 := by
  have lim := coherent_norm S z c t
  constructor
  · intro h
    have e := tendsto_nhds_unique lim h
    have h₁ := sq_nonneg ‖∑ i ∈ S,z i‖
    have h₂ := sq_nonneg ‖∑ i ∈ S,z i*(exp (c i/2):ℂ)‖
    constructor <;> apply norm_eq_zero.mp <;> apply sq_eq_zero_iff.mp <;> linarith only [e,h₁,h₂]
  · rintro ⟨h₁,h₂⟩
    simpa only [h₁,h₂,norm_zero,zero_pow (two_ne_zero : (2:ℕ)≠0),add_zero] using lim

/-- Any two distinct offsets have linearly independent limiting amplitudes. -/
theorem distinct_offsets {c d : ℝ} (hd : c≠d) (z w : ℂ) :
    z+w=0 ∧ z*(exp (c/2):ℂ)+w*(exp (d/2):ℂ)=0 ↔ z=0 ∧ w=0 := by
  have diff : (exp (c/2):ℂ) ≠ (exp (d/2):ℂ) := by
    intro h
    have eq := Real.exp_injective (Complex.ofReal_injective h)
    exact hd (by linarith only [eq])
  constructor
  · rintro ⟨h,k⟩
    have zw : w= -z := by linear_combination h
    rw [zw] at k
    have fact : z*((exp (c/2):ℂ)-(exp (d/2):ℂ))=0 := by linear_combination k
    have hz := (mul_eq_zero.mp fact).resolve_right (sub_ne_zero.mpr diff)
    exact ⟨hz,by rw [zw,hz,neg_zero]⟩
  · rintro ⟨rfl,rfl⟩
    simp

#print axioms coherent_norm
#print axioms coherent_vanishes_iff
#print axioms distinct_offsets

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
