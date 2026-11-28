import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Statistics

/-! # A symmetric finite statistic which measures signed energy scale -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands

open Finset Real

variable {n : ℕ} [NeZero n]

/-- Twice the displacement of the midrange from the mean, multiplied by the sample size. -/
def edge (x : Fin n → ℝ) :=
  (n:ℝ)*(univ.inf' univ_nonempty x + univ.sup' univ_nonempty x) - 2*∑ i,x i

theorem edge_at (x : Fin n → ℝ) (i j : Fin n)
    (low : ∀ a, x i ≤ x a) (high : ∀ a, x a ≤ x j) :
    edge x = (n:ℝ)*(x i+x j)-2*∑ a,x a := by
  have lo : univ.inf' univ_nonempty x = x i := le_antisymm (inf'_le _ (mem_univ i)) (le_inf' univ_nonempty x fun a _ => low a)
  have hi : univ.sup' univ_nonempty x = x j := le_antisymm (sup'_le univ_nonempty x fun a _ => high a) (le_sup' _ (mem_univ j))
  rw [edge,lo,hi]

theorem extrema (x : Fin n → ℝ) : ∃ i j : Fin n, (∀ a, x i ≤ x a) ∧ ∀ a, x a ≤ x j := by
  obtain ⟨i,_,lo⟩ := exists_min_image univ x univ_nonempty
  obtain ⟨j,_,hi⟩ := exists_max_image univ x univ_nonempty
  exact ⟨i,j,fun a => lo a (mem_univ a),fun a => hi a (mem_univ a)⟩

theorem edge_shift (x : Fin n → ℝ) (c : ℝ) : edge (fun i => x i+c)=edge x := by
  obtain ⟨i,j,lo,hi⟩ := extrema x
  rw [edge_at (fun a => x a+c) i j (fun a => add_le_add (lo a) (le_refl c)) (fun a => add_le_add (hi a) (le_refl c)),
    edge_at x i j lo hi,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Scaling by a negative number exchanges the two extremizers. The sum
of their energies still scales by the original signed multiplier. -/
theorem edge_scale (x : Fin n → ℝ) (c : ℝ) : edge (fun i => c*x i)=c*edge x := by
  obtain ⟨i,j,lo,hi⟩ := extrema x
  rw [edge_at x i j lo hi]
  rcases le_total 0 c with pos|neg
  · rw [edge_at (fun a => c*x a) i j (fun a => mul_le_mul_of_nonneg_left (lo a) pos)
      (fun a => mul_le_mul_of_nonneg_left (hi a) pos),←Finset.mul_sum]
    ring
  · rw [edge_at (fun a => c*x a) j i (fun a => mul_le_mul_of_nonpos_left (hi a) neg)
      (fun a => mul_le_mul_of_nonpos_left (lo a) neg),←Finset.mul_sum]
    ring

def reading (q : Fin n → ℝ) := edge fun i => -log (q i)

theorem gibbs_reading (x : Fin n → ℝ) : reading (law x)=edge x := by
  have h : (fun i => -log (law x i)) = fun i => x i+log (_root_.HTGeometry.finiteGibbsPartition 1 x) := by
    funext i
    rw [law,_root_.HTGeometry.finiteGibbsStateWeight,log_div (exp_ne_zero _)
      (_root_.HTGeometry.finiteGibbsPartition_pos 1 x).ne',log_exp]
    ring
  rw [reading,h,edge_shift]

#print axioms edge_at
#print axioms edge_shift
#print axioms edge_scale
#print axioms gibbs_reading

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.FiniteCalibration.Bands
