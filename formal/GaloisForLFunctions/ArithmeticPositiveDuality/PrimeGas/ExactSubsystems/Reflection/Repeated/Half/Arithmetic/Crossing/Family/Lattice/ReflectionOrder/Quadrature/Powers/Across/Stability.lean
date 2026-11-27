import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Sampling
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Exact

/-! # Exact and uniform separation of mixed prime-power channels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across

open Finset Real Filter Set
open PrimeCalibration (log_pos_prime)
open scoped Topology

variable {F : Finset Nat.Primes} [Nonempty F] {J : F → Type*}
  [∀ p, Fintype (J p)] [∀ p, Nonempty (J p)]

/-- The actual occupation-normalized absolute readings over all blocks. -/
def totalError (k : (p : F) → J p → ℕ+) (σ t : ℝ) :=
  peak fun p => jointError p.val (k p) ⟨σ,t⟩

private def weight (k : (p : F) → J p → ℕ+) (σ : ℝ) (p : F) (i : J p) :=
  2*|sinh ((k p i : ℝ)*radial p.val σ)| / (k p i : ℝ)

private theorem physical_score (k : (p : F) → J p → ℕ+) (σ t : ℝ) :
    totalError k σ t=score k (weight k σ) (fun p => t*log p.val.val) := by
  unfold totalError score jointError weight
  congr 1; funext p; congr 1; funext i
  rw [reading_formula,abs_neg,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  ring

private theorem single_lower {I : Type*} [Fintype I] [Nonempty I]
    (p : Nat.Primes) (k : I → ℕ+) (σ t : ℝ) (hx : radial p σ≠0) :
    2*|sinh (radial p σ)| * gain k ≤ jointError p k ⟨σ,t⟩ := by
  rw [joint_formula p k (⟨σ,t⟩ : ℂ) hx]
  exact mul_le_mul_of_nonneg_left (sensitivity_lower k (radial p σ) (t*log p.val) hx)
    (mul_nonneg (by norm_num) (abs_nonneg _))

private theorem block_positive (k : (p : F) → J p → ℕ+) (σ : ℝ) (off : σ≠1/2)
    (p : F) (hp : 0<gain (k p)) :
    ∃ c : ℝ, 0<c ∧ ∀ t : ℝ, c≤totalError k σ t := by
  have hx : radial p.val σ≠0 := mul_ne_zero (sub_ne_zero.mpr off) (log_pos_prime p.val).ne'
  have scale : 0 < 2*|sinh (radial p.val σ)| :=
    mul_pos (by norm_num) (abs_pos.mpr (sinh_ne_zero.mpr hx))
  refine ⟨2*|sinh (radial p.val σ)| * gain (k p),mul_pos scale hp,fun t => ?_⟩
  apply (single_lower p.val (k p) σ t hx).trans
  exact to_peak (fun q : F => jointError q.val (k q) (⟨σ,t⟩ : ℂ)) p

/-- Every block admitting a blind phase is equivalent to almost
invisibility in every sufficiently long height interval. -/
theorem small_errors_recur (k : (p : F) → J p → ℕ+) (σ : ℝ) (off : σ≠1/2) :
    (∀ ε : ℝ, 0<ε → ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, ∃ t ∈ Set.Icc T (T+L), totalError k σ t<ε) ↔
      ∀ p i j, (k p i : ℕ).factorization 2=(k p j : ℕ).factorization 2 := by
  constructor
  · intro recur p i j
    by_contra hij
    obtain ⟨c,hc,lo⟩ := block_positive k σ off p ((positive_iff (k p)).mpr ⟨i,j,hij⟩)
    obtain ⟨_,_,visits⟩ := recur c hc
    obtain ⟨t,_,lt⟩ := visits 0
    exact (lo t).not_gt lt
  · intro same ε hε
    choose θ hθ using fun p => attain_gain (k p)
    have blind (p : F) := (angular_zero (k p) (θ p)).mp
      ((hθ p).trans ((zero_gain (k p)).mpr (same p)))
    have allZero : score k (weight k σ) θ=0 := by
      unfold score
      simp only [blind,abs_zero,mul_zero,peak,sup'_const]
    obtain ⟨L,hL,visits⟩ := score_returns k (weight k σ) θ ε hε
    refine ⟨L,hL,fun T => ?_⟩
    obtain ⟨t,ht,near⟩ := visits T
    rw [allZero,sub_zero,←physical_score] at near
    exact ⟨t,ht,(le_abs_self _).trans_lt near⟩

/-- A height-uniform positive lower bound exists precisely when the
two-adic obstruction is removed inside at least one elementary prime. -/
theorem positive_floor (k : (p : F) → J p → ℕ+) (σ : ℝ) (off : σ≠1/2) :
    (∃ c : ℝ, 0<c ∧ ∀ t : ℝ, c≤totalError k σ t) ↔
    ∃ (p : F) (i j : J p), (k p i : ℕ).factorization 2≠(k p j : ℕ).factorization 2 := by
  constructor
  · rintro ⟨c,hc,lower⟩
    by_contra! same
    obtain ⟨_,_,visits⟩ := (small_errors_recur k σ off).mpr same c hc
    obtain ⟨t,_,lt⟩ := visits 0
    exact (lower t).not_gt lt
  · rintro ⟨p,i,j,hij⟩
    exact block_positive k σ off p ((positive_iff _).mpr ⟨i,j,hij⟩)

#print axioms small_errors_recur
#print axioms positive_floor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across
