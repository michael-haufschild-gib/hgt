import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse.Temperature
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Primes

/-! # Affine approximation by distinct powers of a fixed prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse

open Finset Real Set Metric

private theorem rounding_error (n h b k c e : ℝ) (hn : 0<n) (hh : 0<h)
    (lo : b+n*(h*(e+c)-1) ≤ k) (hi : k ≤ b+n*(h*(e+c)+1)) :
    |k/(n*h)-(c+b/(n*h))-e| ≤ 1/h := by
  have pos := mul_pos hn hh
  have eq : k/(n*h)-(c+b/(n*h))-e=(k-(b+n*(h*(e+c))))/(n*h) := by field_simp; ring
  rw [eq,abs_div,abs_of_pos pos,div_le_div_iff₀ pos hh,one_mul]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩) hh.le

/-- A distinct integral occupation list, after a common affine rescaling, can
approximate every finite list, even one with repeated target energies. -/
theorem grid_dense {n : ℕ} (hn : 0<n) {U : Set (Fin n → ℝ)} (op : IsOpen U) (non : U.Nonempty)
    (M : ℕ) (A : ℝ) : ∃ (k : Fin n ↪ ℕ) (K c : ℝ), 0<K ∧ A<K ∧
      (∀ i, M<k i) ∧ (fun i => (k i : ℝ)/K-c) ∈ U := by
  obtain ⟨E,hE⟩ := non
  obtain ⟨ε,hε,ball⟩ := Metric.mem_nhds_iff.mp (op.mem_nhds hE)
  have np : (0 : ℝ)<n := Nat.cast_pos.mpr hn
  obtain ⟨h,large⟩ := exists_gt (max (1/ε) (A/n))
  have first := (le_max_left _ _).trans_lt large
  have hh := (one_div_pos.mpr hε).trans first
  have small : 1/h<ε := (div_lt_iff₀ hh).mpr (by rw [mul_comm]; exact (div_lt_iff₀ hε).mp first)
  let c := ∑ i, |E i|
  let v := fun i => h*(E i+c)
  let k : Fin n ↪ ℕ := ⟨binIndex (M+1) v,index_injective _ _⟩
  have high : A<(n : ℝ)*h := by
    rw [mul_comm]
    exact (div_lt_iff₀ np).mp ((le_max_right _ _).trans_lt large)
  refine ⟨k,(n : ℝ)*h,c+((M+1 : ℕ) : ℝ)/((n : ℝ)*h),mul_pos np hh,high,?_,
    ball ((dist_pi_lt_iff hε).mpr ?_)⟩
  · intro i
    change M<M+1+(n*⌊v i⌋₊+i.val)
    omega
  · intro i
    have le : |E i| ≤ c := single_le_sum (fun j _ => abs_nonneg (E j)) (mem_univ i)
    have vi : 0 ≤ v i := mul_nonneg hh.le (by linarith only [le,neg_le_abs (E i)])
    have bounds := index_bounds (M+1) v i vi
    rw [Real.dist_eq]
    exact (rounding_error n h (M+1 : ℕ) (k i) c (E i) np hh bounds.1
      ((le_add_of_nonneg_right zero_le_one).trans bounds.2)).trans_lt small

/-- Any finite strict pattern is retained by distinct powers of a prescribed prime.
Both the minimum occupation and the common energy magnification can be arbitrarily large. -/
theorem signs_on_powers {n q : ℕ} (p : Nat.Primes) (dim : 2*q+1≤n)
    (t : Fin q ↪o Ioi (0 : ℝ)) (b : Fin q → ℝ) (nz : ∀ j, b j≠0) (M : ℕ) (A : ℝ) :
    ∃ (k : Fin n ↪ ℕ) (K : ℝ), (∀ i, M<k i) ∧ 0<K ∧ A<K ∧
      ∀ j, 0<b j*oddTrace (centered (primeModes p k)) ((t j).val/K) := by
  obtain ⟨E,zero,pattern⟩ := Schedule.signs_on_real_spectrum dim t b nz
  let U := {F : Fin n → ℝ | ∀ j, 0<b j*oddTrace (centered F) (t j).val}
  have op : IsOpen U := by
    change IsOpen {F : Fin n → ℝ | ∀ j, 0<b j*oddTrace (centered F) (t j).val}
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_lt continuous_const
    unfold oddTrace oddTerm centered meanEnergy
    fun_prop
  have belongs : E ∈ U := by
    intro j
    rw [centered_eq_of_sum_zero zero]
    exact pattern j
  let w := log (p.val : ℝ)
  have wp : 0<w := log_pos (Nat.one_lt_cast.mpr p.property.one_lt)
  obtain ⟨k,K,c,pos,large,above,signs⟩ := grid_dense (by omega : 0<n) op ⟨E,belongs⟩ M (A/w)
  have same : (fun i => primeModes p k i/(K*w)-c)=(fun i => (k i : ℝ)/K-c) := by
    rw [mode_grid]
    funext i
    change (w*(k i : ℝ)+0)/(K*w)-c=(k i : ℝ)/K-c
    field_simp
    ring
  refine ⟨k,K*w,above,mul_pos pos wp,(div_lt_iff₀ wp).mp large,fun j => ?_⟩
  rw [← affine_trace _ _ c,same]
  exact signs j

#print axioms grid_dense
#print axioms signs_on_powers

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Sparse
