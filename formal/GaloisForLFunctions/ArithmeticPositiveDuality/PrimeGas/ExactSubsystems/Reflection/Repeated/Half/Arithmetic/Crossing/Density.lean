import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Bins
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Affine rescalings of distinct prime energies are dense -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing

open Finset Real Set Metric

/-- Translation absorbs the bin offset. The common energy scale is the number of
reserved residues times the magnification times the logarithmic bin width. -/
private theorem rescale_error (n h w m c e z : ℝ) (hn : 0<n) (hh : 0<h) (hw : 0<w)
    (lo : (m+n*(h*(e+c)-1))*w ≤ z) (hi : z ≤ (m+n*(h*(e+c)+1))*w) :
    |z/(n*h*w)-(c+m*w/(n*h*w))-e| ≤ 1/h := by
  have k := mul_pos (mul_pos hn hh) hw
  have eq : z/(n*h*w)-(c+m*w/(n*h*w))-e=(z-(m+n*(h*(e+c)))*w)/(n*h*w) := by
    field_simp; ring
  rw [eq,abs_div,abs_of_pos k,div_le_div_iff₀ k hh]
  have error : |z-(m+n*(h*(e+c)))*w| ≤ n*w := abs_le.mpr ⟨by linarith only [lo],by linarith only [hi]⟩
  calc _ ≤ n*w*h := mul_le_mul_of_nonneg_right error hh.le
       _ = _ := by ring

/-- Every nonempty open set of finite real energy lists contains an affine rescaling
of distinct prime logarithms. Both the prime cutoff and the scale lower bound are arbitrary. -/
theorem prime_dense {n : ℕ} (hn : 0<n) {U : Set (Fin n → ℝ)} (op : IsOpen U) (non : U.Nonempty)
    (M : ℕ) (A : ℝ) : ∃ (p : Fin n ↪ Nat.Primes) (K c : ℝ), 0<K ∧ A<K ∧
      (∀ i, M<(p i).val) ∧ (fun i => log ((p i).val : ℝ)/K-c) ∈ U := by
  obtain ⟨E,hE⟩ := non
  obtain ⟨ε,hε,ball⟩ := Metric.mem_nhds_iff.mp (op.mem_nhds hE)
  let w := log 2
  have hw : 0<w := log_pos (by norm_num)
  have pn : (0 : ℝ)<n := Nat.cast_pos.mpr hn
  obtain ⟨h,big⟩ := exists_gt (max (1/ε) (A/((n : ℝ)*w)))
  have first := (le_max_left _ _).trans_lt big
  have second := (le_max_right _ _).trans_lt big
  have hh := (one_div_pos.mpr hε).trans first
  have small : 1/h<ε := (div_lt_iff₀ hh).mpr (by rw [mul_comm]; exact (div_lt_iff₀ hε).mp first)
  let c := ∑ i, |E i|
  let v := fun i => h*(E i+c)
  let p := distinctPrimes M v
  let K := (n : ℝ)*h*w
  have hK : 0<K := mul_pos (mul_pos pn hh) hw
  have high : A<K := by
    calc A < h*((n : ℝ)*w) := (div_lt_iff₀ (mul_pos pn hw)).mp second
         _ = K := by unfold K; ring
  refine ⟨p,K,c+M*w/K,hK,high,above_cutoff M v,ball ((dist_pi_lt_iff hε).mpr ?_)⟩
  intro i
  have bound : |E i| ≤ c := single_le_sum (fun j _ => abs_nonneg (E j)) (mem_univ i)
  have hi : 0 ≤ v i := mul_nonneg hh.le (by linarith only [bound,neg_le_abs (E i)])
  have floor := index_bounds M v i hi
  have bins := log_bounds (binIndex M v i)
  have lo := (mul_le_mul_of_nonneg_right floor.1 hw.le).trans bins.1
  have up := bins.2.trans (mul_le_mul_of_nonneg_right floor.2 hw.le)
  rw [Real.dist_eq]
  exact (rescale_error n h w M c (E i) (log ((p i).val : ℝ)) pn hh hw lo up).trans_lt small

#print axioms prime_dense

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing
