import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum.Phases
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Sampling
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Channel

/-! # Distinct orders of optimizing the elementary spectrum and physical height -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum

open Filter Real Set Finset
open PrimeCalibration (log_pos_prime)

/-- The angular strength is measured directly by the elementary
divisor channel after division by its positive radial amplitude. -/
theorem measured (p : Nat.Primes) (σ t : ℝ) (off : σ≠1/2) :
    |reading p 1 ⟨σ,t⟩| / (2*|sinh (radial p σ)|)=strength p t := by
  have hn : radial p σ≠0 := mul_ne_zero (sub_ne_zero.mpr off) (log_pos_prime p).ne'
  have sn : 2*|sinh (radial p σ)|≠0 :=
    mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sinh_ne_zero.mpr hn))
  rw [reading_formula,abs_neg,abs_mul,abs_mul]
  simpa only [strength,PNat.one_coe,Nat.cast_one,one_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    using mul_div_cancel_left₀ |cos (t*log p.val)| sn

/-- On any compact height set, one finite set of elementary primes
above the prescribed cutoff gives almost unit gain throughout. -/
theorem compact_resolution (N : ℕ) (K : Set ℝ) (compact : IsCompact K) (c : ℝ) (hc : c < 1) :
    ∃ F : Finset Nat.Primes, (∀ p ∈ F, N < p.val) ∧
      ∀ t ∈ K, ∃ p ∈ F, c < strength p t := by
  classical
  let U (p : {q : Nat.Primes // N < q.val}) := {t : ℝ | c < strength p.val t}
  have opened (p) : IsOpen (U p) :=
    isOpen_lt continuous_const (Real.continuous_cos.comp (continuous_id.mul_const _)).abs
  have cover : K ⊆ ⋃ p, U p := by
    intro t _
    obtain ⟨p,cut,high⟩ := near_one t c hc N
    exact mem_iUnion.mpr ⟨⟨p,cut⟩,high⟩
  obtain ⟨G,sub⟩ := compact.elim_finite_subcover U opened cover
  refine ⟨G.image Subtype.val,?_,?_⟩
  · intro p hp
    obtain ⟨q,_,rfl⟩ := mem_image.mp hp
    exact q.property
  · intro t ht
    obtain ⟨q,hq⟩ := mem_iUnion.mp (sub ht)
    obtain ⟨inside,high⟩ := mem_iUnion.mp hq
    exact ⟨q.val,mem_image_of_mem _ inside,high⟩

variable (F : Finset Nat.Primes) [Nonempty F]

def finiteError (t : ℝ) := peak fun p : F => strength p.val t

/-- Any fixed finite measurement becomes arbitrarily small at relatively
dense physical heights, even if it uniformly resolves a compact interval. -/
theorem finite_returns (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ T : ℝ, ∃ t ∈ Set.Icc T (T+L), finiteError F t < ε := by
  let k (_ : F) (_ : Unit) : ℕ+ := 1
  let w (_ : F) (_ : Unit) : ℝ := 1
  have eval (θ : F → ℝ) : score k w θ=peak fun p => |cos (θ p)| := by
    simp only [score,k,w,PNat.one_coe,Nat.cast_one,one_mul,peak,sup'_const]
  have zero : score k w (fun _ => π/2)=0 := by simp only [eval,cos_pi_div_two,abs_zero,peak,sup'_const]
  obtain ⟨L,pos,hit⟩ := score_returns k w (fun _ => π/2) ε hε
  refine ⟨L,pos,fun T => ?_⟩
  obtain ⟨t,mem,near⟩ := hit T
  rw [zero,sub_zero,eval] at near
  exact ⟨t,mem,(le_abs_self _).trans_lt near⟩

/-- The full tail has supremum one at every height; the best lower
bound over heights of any fixed nonempty finite spectrum is zero. -/
theorem order_of_resolution (N : ℕ) :
    (∀ t : ℝ, IsLUB {x : ℝ | ∃ p : Nat.Primes, N < p.val ∧ x=strength p t} 1) ∧
    IsGLB (Set.range (finiteError F)) 0 := by
  refine ⟨fun t => tail_supremum t N,?_,?_⟩
  · rintro _ ⟨t,rfl⟩
    let p : F := Classical.choice inferInstance
    exact (abs_nonneg _).trans (to_peak (fun q : F => strength q.val t) p)
  · intro c lower
    by_contra! positive
    obtain ⟨_,_,returns⟩ := finite_returns F c positive
    obtain ⟨t,_,lt⟩ := returns 0
    exact lt.not_ge (lower (Set.mem_range_self t))

#print axioms measured
#print axioms compact_resolution
#print axioms finite_returns
#print axioms order_of_resolution

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Spectrum
