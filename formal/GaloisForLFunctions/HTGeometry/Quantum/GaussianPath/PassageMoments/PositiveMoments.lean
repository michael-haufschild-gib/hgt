import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.GaussianTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.GeometricTail

/-! # Finite positive moments of the first robust crossing and its actual first return -/
open MeasureTheory ProbabilityTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.PassageMoments
noncomputable section
open PrescribedTimes

/-- At each sufficiently large fixed Gaussian prefix, the larger of the
onset and the first subsequent wait has finite moments of every positive
order below 1/D!. This holds at every return budget, including zero. -/
theorem gaussian_positive_first_passage_moments :
    ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, ∀ p : ℝ, 0 < p → p < 1/((2^(k+3):ℕ).factorial:ℝ) →
      Integrable (fun x => (passageMax k s x)^p)
        (Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1) := by
  filter_upwards [gaussian_dyadic_passage_tail] with k hk s p hp hq
  let d := (2^(k+3):ℕ).factorial
  have hd : 0 < d := Nat.factorial_pos _
  have hd' : 0 < (d:ℝ) := Nat.cast_pos.mpr hd
  have hδ : 0 < 1-p*(d:ℝ) := sub_pos.mpr ((lt_div_iff₀ hd').mp hq)
  obtain ⟨L,hL⟩ := exists_nat_gt ((p*d+1)/(1-p*d))
  have hpay := (div_lt_iff₀ hδ).mp hL
  have hLpos : 0 < L := Nat.cast_pos.mp ((div_pos (by positivity) hδ).trans hL)
  let M := L*d+(d-1)
  have hM : 0 < M := Nat.add_pos_left (Nat.mul_pos hLpos hd) _
  have hexp : (M:ℝ)*p < L := by
    dsimp [M]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hd,Nat.cast_one]
    linarith only [hpay,hp]
  have hb : (1:ℝ)<(2:ℝ)^M := one_lt_pow₀ (by norm_num) hM.ne'
  have hr : ((2:ℝ)^M)^p*((2:ℝ)^L)⁻¹ < 1 := by
    rw [←div_eq_mul_inv,div_lt_one (by positivity),←Real.rpow_natCast_mul (by norm_num : 0 ≤ (2:ℝ))]
    exact (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp).trans_eq (Real.rpow_natCast 2 L)
  obtain ⟨A,hA,C,hC⟩ := hk L
  exact integrable_rpow_of_geometric_tail _ _ (measurable_passageMax k s) (passageMax_nonneg k s)
    hA hb (by positivity) hp hr (hC s)

#print axioms gaussian_positive_first_passage_moments
end
end GaloisForLFunctions.HTGeometry.PassageMoments
