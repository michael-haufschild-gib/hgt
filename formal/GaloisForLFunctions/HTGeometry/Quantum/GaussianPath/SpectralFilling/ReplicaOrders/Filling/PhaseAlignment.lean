import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.MomentPeak
import GaloisForLFunctions.HTGeometry.CalibrationSpectrumMechanics

/-! # Simultaneous alignment of all phases from one high replica order -/
open Set Real Complex Finset
noncomputable section
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [DecidableEq I] [Nonempty I] in
private theorem common_phase (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) {ε : ℝ} (hε : 0 < ε)
    (h : (Fintype.card I:ℝ)-ε^2/2 < ‖∑ i, f i‖) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∀ i, ‖f i-z‖ < ε := by
  let S := ∑ i, f i
  let z := coherentUnitPhase S
  have hz : ‖z‖=1 := norm_coherentUnitPhase _
  have hs : (S*star z).re=‖S‖ := by
    rw [mul_comm]
    exact congrArg Complex.re (star_coherentUnitPhase_mul S)
  have hd (i : I) : ‖f i-z‖^2=2-2*(f i*star z).re := by
    rw [Complex.sq_norm,Complex.normSq_sub,←Complex.sq_norm,←Complex.sq_norm,hf,hz,Complex.star_def]
    ring
  have ht : ∑ i, ‖f i-z‖^2=2*((Fintype.card I:ℝ)-‖S‖) := by
    simp only [hd,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,←mul_sum,←Complex.re_sum,←sum_mul]
    change _-2*(S*star z).re=_
    rw [hs]
    ring
  refine ⟨z,hz,fun i => ?_⟩
  have hi := single_le_sum (f:=fun j => ‖f j-z‖^2) (fun j _ => sq_nonneg _) (mem_univ i)
  rw [ht] at hi
  change _ < ‖S‖ at h
  nlinarith only [hi,h,hε,norm_nonneg (f i-z)]

/-- If the order-q diagonal mass beats the threshold price, every target
is visited to chordal accuracy ε in every interval of length 4π/γ. -/
theorem all_targets_at_order (E : I → ℝ) (q : ℕ) {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (hg : ∀ p z : ReplicaMultiplicityIndex I q, p≠z →
      γ ≤ |replicaMultiplicityEnergy E p.val-replicaMultiplicityEnergy E z.val|)
    (hprice : (Fintype.card (ReplicaMultiplicityIndex I q):ℝ)*
      (1-ε^2/(2*(Fintype.card I:ℝ)))^(2*q) < coherentFraction)
    (v : I → ℂ) (hv : ∀ i, ‖v i‖=1) (a : ℝ) :
    ∃ t ∈ Icc a (a+4*π/γ), ∃ z : ℂ, ‖z‖=1 ∧ ∀ i,
      ‖v i*Complex.exp (Complex.I*(E i:ℂ)*(t:ℂ))-z‖ < ε := by
  let D : ℝ := Fintype.card I
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast Fintype.card_pos (α:=I)
  let o := a+2*π/γ
  let F (i : I) := E i/γ
  let P (i : I) (t : ℝ) := Complex.exp (Complex.I*(E i:ℂ)*(t:ℂ))
  have hu (i : I) (t : ℝ) : ‖P i t‖=1 := by
    simpa only [P,show Complex.I*(E i:ℂ)*(t:ℂ)=((E i*t:ℝ):ℂ)*Complex.I by push_cast; ring]
      using Complex.norm_exp_ofReal_mul_I (E i*t)
  let c (i : I) := ((D⁻¹:ℝ):ℂ)*(v i*P i o)
  have hc : ∑ i, ‖c i‖=1 := by
    simp only [c,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hD),hv,hu,
      mul_one,sum_const,card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hD.ne'
  have hF (p : I → ℕ) : replicaMultiplicityEnergy F p=replicaMultiplicityEnergy E p/γ := by
    unfold replicaMultiplicityEnergy
    simp only [F,mul_div_assoc, sum_div]
  have hg' (p z : ReplicaMultiplicityIndex I q) (hpz : p≠z) :
      1 ≤ |replicaMultiplicityEnergy F p.val-replicaMultiplicityEnergy F z.val| := by
    rw [hF,hF,←sub_div,abs_div,abs_of_pos hγ]
    exact (le_div_iff₀ hγ).mpr ((one_mul _).le.trans (hg p z hpz))
  obtain ⟨s,hs,ht⟩ := coherent_date F c hc q hg' hprice
  let t := o+s/γ
  have hphase (i : I) : P i o*Complex.exp (Complex.I*(F i:ℂ)*(s:ℂ))=P i t := by
    dsimp only [P,t,F]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  let f (i : I) := v i*P i t
  have he : spectralSum F c s=((D⁻¹:ℝ):ℂ)*∑ i, f i := by
    rw [spectralSum,mul_sum]
    apply sum_congr rfl
    intro i _
    dsimp only [c,f]
    rw [mul_assoc,mul_assoc (v i),hphase]
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hD)] at ht
  have hsum : D-ε^2/2 < ‖∑ i, f i‖ := by
    have h := mul_lt_mul_of_pos_left ht hD
    change D*(1-ε^2/(2*D)) < D*(D⁻¹*_) at h
    rwa [mul_sub,mul_one,←mul_assoc,mul_inv_cancel₀ hD.ne',one_mul,
      show D*(ε^2/(2*D))=ε^2/2 by field_simp] at h
  have htmem : t ∈ Icc a (a+4*π/γ) := by
    dsimp only [t,o]
    rw [add_assoc,←add_div]
    have hl : -(2*π) ≤ s := hs.1
    have hr : s ≤ 2*π := hs.2
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (by linarith only [hl]) hγ.le)
    · have hnum : 2*π+s ≤ 4*π := by linarith only [hr]
      exact add_le_add (le_refl a) (div_le_div_of_nonneg_right hnum hγ.le)
  exact ⟨t,htmem,common_phase f (fun i => by rw [show f i=v i*P i t from rfl,norm_mul,hv,hu,mul_one])
    hε hsum⟩

#print axioms all_targets_at_order
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
end
