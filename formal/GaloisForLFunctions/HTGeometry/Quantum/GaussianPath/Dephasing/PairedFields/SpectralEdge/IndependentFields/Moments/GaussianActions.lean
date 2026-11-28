import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ResolutionBins.AlignedMoment
import Mathlib.MeasureTheory.Integral.Pi

/-! # Gaussian moments for several independent local perturbations -/

open Finset MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private kernel_real replica_twist_le from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ResolutionBins.AlignedMoment
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

private abbrev law (J : Type*) [Fintype J] := Measure.pi fun _ : J => gaussianReal 0 1

/-- The phase slope at each level is linear in the independently drawn
coefficient vector. -/
def fieldEnergy (v : J → I → ℝ) (g : J → ℝ) (i : I) := ∑ l, g l*v l i

/-- The difference of the total local expectations of two level multisets. -/
def slopeDifference (v : J → I → ℝ) (p q : I → ℕ) (l : J) :=
  replicaMultiplicityEnergy (v l) p - replicaMultiplicityEnergy (v l) q

/-- Weighted Gaussian overlap of all pairs of order-q multisets. -/
def slopeMoment (w : I → ℝ) (v : J → I → ℝ) (q : ℕ) (L : ℝ) : ℝ :=
  ∑ p ∈ univ.piAntidiag q, ∑ k ∈ univ.piAntidiag q, fidelityReplicaMultiplicityWeight w p k *
    exp (-(∑ l, (L*slopeDifference v p k l)^2)/2)

private theorem character_integral (a : J → ℝ) :
    (∫ g, Complex.exp (((∑ l, a l*g l : ℝ):ℂ)*Complex.I) ∂law J) =
      (exp (-(∑ l, (a l)^2)/2):ℂ) := by
  have h (g : J → ℝ) : Complex.exp (((∑ l, a l*g l : ℝ):ℂ)*Complex.I) =
      ∏ l, Complex.exp (((a l*g l:ℝ):ℂ)*Complex.I) := by
    rw [←Complex.exp_sum]
    congr 1
    push_cast
    rw [sum_mul]
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (μ:=fun _ : J => gaussianReal 0 1)
    (fun l (x : ℝ) => Complex.exp (((a l*x:ℝ):ℂ)*Complex.I))]
  simp_rw [integral_gaussian_observer_character,kernel_real]
  norm_cast
  rw [←Real.exp_sum,←sum_div,←sum_neg_distrib]

omit [DecidableEq I] in
private theorem total_energy (v : J → I → ℝ) (g : J → ℝ) (p : I → ℕ) :
    replicaMultiplicityEnergy (fieldEnergy v g) p = ∑ l, g l*replicaMultiplicityEnergy (v l) p := by
  simp only [replicaMultiplicityEnergy,fieldEnergy,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun i _ => by ring

omit [DecidableEq I] in
private theorem action (v : J → I → ℝ) (L : ℝ) (p k : I → ℕ) (g : J → ℝ) :
    L*(replicaMultiplicityEnergy (fieldEnergy v g) p-replicaMultiplicityEnergy (fieldEnergy v g) k) =
      ∑ l, (L*slopeDifference v p k l)*g l := by
  rw [total_energy,total_energy,←sum_sub_distrib,mul_sum]
  exact sum_congr rfl fun l _ => by dsimp only [slopeDifference]; ring

private theorem term_integrable (a : J → ℝ) :
    Integrable (fun g : J → ℝ => Complex.exp (((∑ l, a l*g l:ℝ):ℂ)*Complex.I)) (law J) := by
  have h : Continuous (fun g : J → ℝ => Complex.exp (((∑ l, a l*g l:ℝ):ℂ)*Complex.I)) := by fun_prop
  apply (integrable_const (1:ℝ)).mono' h.aestronglyMeasurable
  exact ae_of_all _ fun g => by simp [Complex.norm_exp]

/-- Exact conditional fidelity moment, before any circuit net is chosen.
Every pair of occupation vectors is damped by its full squared Euclidean
separation in local-expectation space. -/
theorem field_fidelity_moment (w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ) (q : ℕ) (L : ℝ) :
    (∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) z L ^ q ∂law J) =
      ∑ p ∈ univ.piAntidiag q, ∑ k ∈ univ.piAntidiag q,
        (fidelityReplicaMultiplicityWeight w p k:ℂ) * replicaMultiplicityTwist z p k *
          (exp (-(∑ l, (L*slopeDifference v p k l)^2)/2):ℂ) := by
  simp_rw [twistedFiniteSpectralFidelity_pow_expansion,action]
  let c (p k : I → ℕ) := (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k
  let a (p k : I → ℕ) (l : J) := L*slopeDifference v p k l
  have hi (p k) := (term_integrable (a p k)).const_mul (c p k)
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun k _ => hi p k))]
  apply sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun k _ => hi p k)]
  apply sum_congr rfl
  intro k _
  rw [integral_const_mul,character_integral]

/-- The identity twist bounds every fixed contraction in the same basis. -/
theorem field_fidelity_moment_le {w : I → ℝ} (hw : ∀ i, 0 ≤ w i) (v : J → I → ℝ)
    {z : I → ℂ} (hz : ∀ i, ‖z i‖ ≤ 1) (q : ℕ) (L : ℝ) :
    ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) z L ^ q ∂law J‖ ≤ slopeMoment w v q L := by
  rw [field_fidelity_moment]
  apply (norm_sum_le ..).trans (sum_le_sum ?_)
  intro p _
  apply (norm_sum_le ..).trans (sum_le_sum ?_)
  intro k _
  have hpk := fidelityReplicaMultiplicityWeight_nonneg hw p k
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hpk,
    Real.norm_of_nonneg (exp_pos _).le]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hpk (replica_twist_le hz p k)) (exp_pos _).le

#print axioms field_fidelity_moment
#print axioms field_fidelity_moment_le
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
