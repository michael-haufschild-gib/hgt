import GaloisForLFunctions.SquareRootThreshold.InghamInequalityForSeparatedSpectra
import GaloisForLFunctions.HTGeometry.TracelessReplicaDyadicActionShellLaw

/-! # A coherent date from the lower Ingham bound on occupation energies -/
open Finset Set Real MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SquareRootThreshold
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Spectral sum with the target and time origin absorbed into its coefficients. -/
def spectralSum (E : I → ℝ) (c : I → ℂ) (t : ℝ) :=
  ∑ i, c i*Complex.exp (Complex.I*(E i:ℂ)*(t:ℂ))

private theorem replica_wave (E : I → ℝ) (c : I → ℂ) (q : ℕ) (t : ℝ) :
    (spectralSum E c t)^q=∑ p : ReplicaMultiplicityIndex I q, complexReplicaMultiplicityAmplitude c p.val*
      Complex.exp (Complex.I*(replicaMultiplicityEnergy E p.val:ℂ)*(t:ℂ)) := by
  rw [spectralSum,←sum_complexReplicaMultiplicityAmplitude_eq_sum_pow,
    Finset.sum_coe_sort (univ.piAntidiag q)]
  apply sum_congr rfl
  intro p _
  have hp : (∏ i, Complex.exp (Complex.I*(E i:ℂ)*(t:ℂ))^p i)=
      Complex.exp (Complex.I*(replicaMultiplicityEnergy E p:ℂ)*(t:ℂ)) := by
    simp_rw [←Complex.exp_nat_mul]
    rw [←Complex.exp_sum]
    congr 1
    unfold replicaMultiplicityEnergy
    push_cast
    rw [mul_sum,sum_mul]
    exact sum_congr rfl fun i _ => by ring
  simp only [complexReplicaMultiplicityAmplitude,mul_pow,prod_mul_distrib,hp,mul_assoc]

/-- Normalized lower Ingham constant on a span of length 4π at unit spacing. -/
def coherentFraction : ℝ := inghamConst (2*π) 1/(4*π)

theorem coherentFraction_pos : 0 < coherentFraction := div_pos
  (inghamConst_pos (by positivity) (by linarith only [pi_pos] : π < 2*π*1)) (by positivity)

/-- A unit-spaced replica of small enough cardinality forces an actual
time with trace above threshold, for every choice of normalized complex
coefficients. The bound retains the full occupation count. -/
theorem coherent_date (E : I → ℝ) (c : I → ℂ) (hc : ∑ i, ‖c i‖=1) (q : ℕ)
    (hg : ∀ p z : ReplicaMultiplicityIndex I q, p≠z →
      1 ≤ |replicaMultiplicityEnergy E p.val-replicaMultiplicityEnergy E z.val|)
    {τ : ℝ}
    (hprice : (Fintype.card (ReplicaMultiplicityIndex I q):ℝ)*τ^(2*q) < coherentFraction) :
    ∃ t ∈ Icc (-(2*π)) (2*π), τ < ‖spectralSum E c t‖ := by
  classical
  let E' (p : ReplicaMultiplicityIndex I q) := replicaMultiplicityEnergy E p.val
  let C (p : ReplicaMultiplicityIndex I q) := complexReplicaMultiplicityAmplitude c p.val
  let B : ℝ := Fintype.card (ReplicaMultiplicityIndex I q)
  have hm : ∑ p, ‖C p‖=1 := by
    rw [Finset.sum_coe_sort (univ.piAntidiag q),sum_norm_complexReplicaMultiplicityAmplitude_eq_pow,hc,one_pow]
  have hs := sq_sum_le_card_mul_sum_sq (s:=univ) (f:=fun p => ‖C p‖)
  rw [hm,one_pow,card_univ] at hs
  have hpos := inghamConst_pos (by positivity) (by linarith only [pi_pos] : π < 2*π*1)
  have hI := ingham_inequality E' C (by norm_num : (0:ℝ)<1) (by positivity)
    (by linarith only [pi_pos] : π < 2*π*1) hg
  by_contra! hmiss
  have hmono : (∫ t in -(2*π)..2*π, ‖∑ p, C p*Complex.exp (Complex.I*(E' p:ℂ)*(t:ℂ))‖^2) ≤
      ∫ _t in -(2*π)..2*π, τ^(2*q) := by
    apply intervalIntegral.integral_mono_on (by linarith only [pi_pos])
      ((show Continuous fun t : ℝ => ‖∑ p, C p*Complex.exp (Complex.I*(E' p:ℂ)*(t:ℂ))‖^2 by
        fun_prop).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro t ht
    rw [show (∑ p, C p*Complex.exp (Complex.I*(E' p:ℂ)*(t:ℂ)))=(spectralSum E c t)^q
      from (replica_wave E c q t).symm,norm_pow,←pow_mul,Nat.mul_comm q 2]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmiss t ht) _
  rw [intervalIntegral.integral_const,smul_eq_mul] at hmono
  have hbound := mul_le_mul_of_nonneg_left (hI.trans hmono) (show 0 ≤ B from Nat.cast_nonneg _)
  have hfloor := mul_le_mul_of_nonneg_left hs hpos.le
  have htest := (lt_div_iff₀ (by positivity : 0 < 4*π)).mp hprice
  change B*τ^(2*q)*(4*π) < inghamConst (2*π) 1 at htest
  change B*(inghamConst (2*π) 1*_) ≤ B*((2*π- -(2*π))*τ^(2*q)) at hbound
  change inghamConst (2*π) 1*1 ≤ inghamConst (2*π) 1*(B*_) at hfloor
  linarith only [hfloor,hbound,htest]

#print axioms coherent_date
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
