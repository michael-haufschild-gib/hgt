import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.DisjointLayers
import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Counting energetic eigenlines in a disjoint interaction layer -/
open Finset Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Exponential Markov bounds on the positive and negative energies
count both tails, including multiplicity. -/
theorem two_sided_energy_count {I : Type*} [Fintype I] (E : I → ℝ) {B r : ℝ}
    (hB : 0 < B) (hr : 0 ≤ r)
    (h : ∀ q : ℝ, ∑ i, Real.exp (q*E i) ≤ (Fintype.card I:ℝ)*Real.exp (q^2*B/2)) :
    ((univ.filter fun i => r < |E i|).card:ℝ) ≤
      2*(Fintype.card I:ℝ)*Real.exp (-(r^2)/(2*B)) := by
  classical
  let q := r/B
  have hq : 0 ≤ q := div_nonneg hr hB.le
  let S := univ.filter fun i => r < |E i|
  have hi (i : I) (hr' : r ≤ |E i|) :
      Real.exp (q*r) ≤ Real.exp (q*E i)+Real.exp ((-q)*E i) := by
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr' hq)
    rcases le_total 0 (E i) with h'|h'
    · rw [abs_of_nonneg h'] at he
      exact he.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos h',mul_neg,←neg_mul] at he
      exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hh : (S.card:ℝ)*Real.exp (q*r) ≤ 2*(Fintype.card I:ℝ)*Real.exp (q^2*B/2) := by
    calc _ = ∑ _i ∈ S, Real.exp (q*r) := by simp only [sum_const,nsmul_eq_mul]
         _ ≤ ∑ i ∈ S, (Real.exp (q*E i)+Real.exp ((-q)*E i)) := by
           exact sum_le_sum fun i hi' => hi i ((mem_filter.mp hi').2.le)
         _ ≤ ∑ i, (Real.exp (q*E i)+Real.exp ((-q)*E i)) :=
           sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
         _ ≤ _ := by
           rw [sum_add_distrib]
           have hn := h (-q)
           rw [neg_sq] at hn
           linarith only [h q,hn]
  apply ((le_div_iff₀ (Real.exp_pos (q*r))).mpr hh).trans_eq
  rw [mul_div_assoc,←Real.exp_sub]
  congr 2
  dsimp only [q]
  field_simp [hB.ne']
  ring

/-- The spectral counting measure of a disjoint Pauli layer obeys a
Gaussian tail with variance bounded by its squared coefficient mass. -/
theorem disjoint_energy_count {N : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Finset (Fin N)) (P : ι → Reg N) (b : ι → ℝ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j))
    (hp : ∀ i ∈ s, IsSiteSupported (S i) (P i))
    (hinv : ∀ i ∈ s, P i*P i=1) (htr : ∀ i ∈ s, (P i).trace=0)
    (hH : (∑ i ∈ s, (b i:ℂ) • P i).IsHermitian) {B r : ℝ}
    (hB : 0 < B) (hmass : ∑ i ∈ s, (b i)^2 ≤ B) (hr : 0 ≤ r) :
    ((univ.filter fun j => r < |hH.eigenvalues j|).card:ℝ) ≤
      2*(Fintype.card (Fin N → Bool):ℝ)*Real.exp (-(r^2)/(2*B)) := by
  apply two_sided_energy_count _ hB hr
  intro q
  rw [←trace_exp_smul_hermitian hH q]
  simp only [Finset.smul_sum,smul_smul,←Complex.ofReal_mul]
  rw [disjoint_partition s S P (fun i => q*b i) hd hp hinv htr]
  simp only [←Complex.ofReal_cosh,←Complex.ofReal_prod,←Complex.ofReal_natCast,←Complex.ofReal_mul,
    Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc ∏ i ∈ s, Real.cosh (q*b i) ≤ ∏ i ∈ s, Real.exp ((q*b i)^2/2) :=
         prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
       _ = Real.exp (∑ i ∈ s, (q*b i)^2/2) := (Real.exp_sum ..).symm
       _ ≤ _ := by
         apply Real.exp_le_exp.mpr
         simp only [mul_pow,div_eq_mul_inv,←sum_mul,←mul_sum]
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (sq_nonneg _)) (by norm_num)

#print axioms disjoint_energy_count
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
