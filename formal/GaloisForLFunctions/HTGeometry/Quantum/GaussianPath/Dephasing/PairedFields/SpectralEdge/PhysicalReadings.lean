import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.RankedExcess
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.GaussianRanks
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.PhysicalDates

/-! # Gaussian cost of affine phase tests at physical circuit dates -/

open Matrix Set Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private base_law midpoint from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.PhysicalDates
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
private abbrev Index (n : ℕ) := Fin (n+2) → Bool

/-- Sum of the two adjacent cut sizes at each tested rank. It equals r² for the first r rows. -/
def rankWeight {I : Type*} [Fintype I] [DecidableEq I] (R : Finset I) : ℕ :=
  ∑ j ∈ R, ((preceding j).card+(insert j (preceding j)).card)

private def testedEnergy {n : ℕ} (R : Finset (Index n)) (x : Coeff n) :=
  edgeEnergy R (generator x).2.isHermitian.eigenvalues

private theorem energy_moment (n : ℕ) (R : Finset (Index n)) :
    Integrable (testedEnergy R) (fieldLaw n) ∧
      (∫ x, testedEnergy R x ∂fieldLaw n) ≤ (rankWeight R:ℝ)*Fintype.card (PathLabel n) := by
  let E (i : Index n) (x : Coeff n) := (generator x).2.isHermitian.eigenvalues i
  let m : ℝ := Fintype.card (PathLabel n)
  let Q (S : Finset (Index n)) (x : Coeff n) := ∑ i ∈ S, E i x
  have he (i : Index n) : (∫ x, E i x ∂fieldLaw n) ≤ m :=
    (integral_mono (gaussian_rank_energy n i).1 (gaussian_rank_energy n i).1.abs
      (fun x => le_abs_self (E i x))).trans (gaussian_rank_energy n i).2
  have hi (S) : Integrable (Q S) (fieldLaw n) :=
    integrable_finsetSum S fun i _ => (gaussian_rank_energy n i).1
  have hb (S) : (∫ x, Q S x ∂fieldLaw n) ≤ S.card*m := by
    unfold Q
    rw [integral_finsetSum _ (fun i _ => (gaussian_rank_energy n i).1)]
    simpa only [sum_const,nsmul_eq_mul] using (sum_le_sum (s:=S) (fun i _ => he i))
  let f (j : Index n) (x : Coeff n) := Q (preceding j) x+Q (insert j (preceding j)) x
  have hf (j : Index n) : Integrable (f j) (fieldLaw n) := (hi _).add (hi _)
  refine ⟨integrable_finsetSum R (fun j _ => hf j),?_⟩
  change (∫ x, ∑ j ∈ R, f j x ∂fieldLaw n) ≤ _
  rw [integral_finsetSum _ (fun i _ => hf i)]
  simp only [rankWeight,Nat.cast_sum,Nat.cast_add,sum_mul,add_mul]
  apply sum_le_sum
  intro j _
  rw [show (∫ x, f j x ∂fieldLaw n)=_ from integral_add (hi (preceding j)) (hi (insert j (preceding j)))]
  exact add_le_add (hb _) (hb _)

private def loss {n : ℕ} (R : Finset (Index n)) (a b : ℝ) (x : FieldPair n) :=
  testedEnergy R (rotated a b x)+testedEnergy R (rotated a (-b) x)-2*a*testedEnergy R (base x)

/-- Total error for the positively displaced field on the selected rows. -/
def readingError {n : ℕ} (R : Finset (Index n)) (a b : ℝ) (x : FieldPair n) (t : ℝ) :=
  ∑ j ∈ R, phaseError (generator (base x)).2.isHermitian.eigenvectorUnitary (generator (rotated a b x)) t j

private theorem time_bound {n : ℕ} (R : Finset (Index n)) (a b : ℝ) (x : FieldPair n) (t : ℝ) :
    readingError R a b x t ≤ 2*|t| *loss R a b x := by
  have h := paired_edge_error _ _ _ (midpoint a b x) R t
  apply le_trans _ h
  exact sum_le_sum fun j _ => le_add_of_nonneg_right (norm_nonneg _)

private theorem loss_nonneg {n : ℕ} (R : Finset (Index n)) (a b : ℝ) (x : FieldPair n) :
    0 ≤ loss R a b x := by
  have h := time_bound R a b x 1
  have h₀ : 0≤readingError R a b x 1 := sum_nonneg fun j _ => norm_nonneg _
  rw [abs_one,mul_one] at h
  linarith only [h,h₀]

/-- Uniformly through T, the exceptional probability is proportional to the
sum of the tested ranks. No dimension factor or minimum gap enters the bound. -/
theorem gaussian_ranked_readings (n : ℕ) (R : Finset (Index n)) {a b T ρ : ℝ}
    (hab : a^2+b^2=1) (hT : 0<T) (hρ : 0<ρ) :
    (pairLaw n).real {x | ∃ t : ℝ, |t| ≤ T ∧ ρ < readingError R a b x t} ≤
      4*T*(1-a)*rankWeight R*Fintype.card (PathLabel n)/ρ := by
  let F := testedEnergy R
  obtain ⟨hF,hmean⟩ := energy_moment n R
  have law (g : FieldPair n → Coeff n) (hg : MeasurePreserving g (pairLaw n) (fieldLaw n)) :
      Integrable (fun x => F (g x)) (pairLaw n) ∧ (∫ x, F (g x) ∂pairLaw n)=∫ y, F y ∂fieldLaw n := by
    refine ⟨hg.integrable_comp_of_integrable hF,?_⟩
    have hme : AEStronglyMeasurable F (Measure.map g (pairLaw n)) := by rw [hg.map_eq]; exact hF.aestronglyMeasurable
    exact (integral_map hg.measurable.aemeasurable hme).symm.trans (by rw [hg.map_eq])
  obtain ⟨ip,ep⟩ := law _ (rotated_law n hab)
  obtain ⟨im,em⟩ := law _ (rotated_law n (a:=a) (b:=-b) (by simpa only [neg_sq] using hab))
  obtain ⟨ib,eb⟩ := law _ (base_law n)
  have hi : Integrable (loss R a b) (pairLaw n) := (ip.add im).sub (ib.const_mul (2*a))
  have hL : (∫ x, loss R a b x ∂pairLaw n)=2*(1-a)*(∫ y, F y ∂fieldLaw n) := by
    change (∫ x, (F (rotated a b x)+F (rotated a (-b) x))-2*a*F (base x) ∂pairLaw n)=_
    have ix : Integrable (fun x : FieldPair n => F (rotated a b x)+F (rotated a (-b) x)) (pairLaw n) := ip.add im
    rw [integral_sub ix (ib.const_mul (2*a)),integral_add ip im,integral_const_mul,ep,em,eb]
    ring
  let κ := ρ/(2*T)
  have hk : 0<κ := div_pos hρ (by positivity)
  have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (loss_nonneg R a b)) hi κ
  rw [hL] at hm
  have ha : 0 ≤ 1-a := by nlinarith only [hab,sq_nonneg b,sq_nonneg (a-1)]
  apply (measureReal_mono (μ:=pairLaw n) (s₂:={x | κ ≤ loss R a b x}) ?_).trans
  · apply le_of_mul_le_mul_left _ hk
    apply (hm.trans (mul_le_mul_of_nonneg_left hmean (mul_nonneg (by norm_num) ha))).trans_eq
    dsimp only [κ]
    field_simp
    ring
  · rintro x ⟨t,ht,herr⟩
    apply (div_le_iff₀ (by positivity : 0<2*T)).mpr
    apply herr.le.trans ((time_bound R a b x t).trans ?_)
    rw [mul_comm (loss R a b x)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) (loss_nonneg R a b x)

#print axioms gaussian_ranked_readings
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
