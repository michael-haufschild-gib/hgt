import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalForcingProductBounds

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalHorizonProductDecay
open D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMOriginalReaderCuspBounds D4BMOriginalAngularReaderBounds
open D4BMOriginalAngularProducts D4BMOriginalPrincipalHorizonBounds
open D4BMOriginalHorizonForcingBound D4BMOriginalBaseCircleJets
open D4BMOriginalCausalPotential D4BMOriginalCornerForcing
open D4BMOriginalForcingProductBounds D4BMOriginalForcingAngularPeriod
open D4BMOriginalCollarCurrentBounds D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

private theorem damped_bound (w z : ℂ) (C G n p k : ℝ) (hC : 0≤C)
    (hp : 0≤p) (hw : G+1≤w.re) (hz : ‖z‖≤C*Real.exp (G*p-n*k)) :
    ‖Complex.exp (-w*(p:ℂ))*z‖≤C*Real.exp (-n*k)*Real.exp (-p) := by
  rw [norm_mul,Complex.norm_exp,show (-w*(p:ℂ)).re=-w.re*p by simp]
  calc
    _ ≤ Real.exp (-w.re*p)*(C*Real.exp (G*p-n*k)) :=
      mul_le_mul_of_nonneg_left hz (Real.exp_nonneg _)
    _ = C*Real.exp ((G-w.re)*p-n*k) := by
      rw [show Real.exp (-w.re*p)*(C*Real.exp (G*p-n*k))=
        C*(Real.exp (-w.re*p)*Real.exp (G*p-n*k)) by ring,← Real.exp_add]
      congr 2
      ring
    _ ≤ C*Real.exp (-n*k-p) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add];ring

/-- Every original horizon source-reader product has a uniform damped cusp
bound, including the retained principal-times-reader-tail terms. -/
theorem horizon_angular_product_decay (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (d : Bool) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∃ C : ℝ,0≤C ∧
      ∀ p x k : ℝ,0<p → 0≤k →
        ‖Complex.exp (-w*(p:ℂ))*horizonAngularProduct q br amp w j d p x k‖≤
          C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  classical
  obtain ⟨C,G,hC,hG,hc⟩ := original_action_base_jet_horizon_estimate
    (center q) (physicalRate q br) amp j (N+1)
  obtain ⟨D,hD,hd⟩ := angularJet_bound q d
  have hcoef (i : Fin 3) : ∃ B : ℝ,0≤B ∧ ∀ p : ℝ,0<p →
      ‖horizonCoefficient q br amp i p‖≤B*Real.exp (2*p) := by
    obtain ⟨B,hB,hb⟩ := original_principal_coefficient_horizon_estimate q br amp i
    obtain ⟨L,hL⟩ := eventually_atTop.mp hb
    exact ⟨B,hB,fun p hp => (hL L le_rfl p hp).1⟩
  choose B hB hb using hcoef
  choose E hE he using (fun i : Fin 3 => principal_tail_bound q d (principalExponent q i) N)
  let H := max G 2
  have hGH : G≤H := le_max_left _ _
  have h2H : 2≤H := le_max_right _ _
  refine ⟨H,hG.trans hGH,?_⟩
  intro w hw
  let M := C*D+∑ i : Fin 3,B i*‖jetMultiplier j (principalExponent q i)‖*E i
  have hM : 0≤M := by
    dsimp [M]
    exact add_nonneg (mul_nonneg hC hD) (Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hB i) (norm_nonneg _)) (hE i)))
  refine ⟨‖horizonReader q w‖*M,by positivity,?_⟩
  intro p x k hp hk
  let F := Real.exp (H*p-(N:ℝ)*k)
  have hF : 0≤F := Real.exp_nonneg _
  have hs : ‖horizonJet q br amp j p x k*angularJet q d x k‖≤(C*D)*F := by
    have hc0 := (hc p 0 x k hp.le (by norm_num) (by norm_num) hk).1
    change ‖horizonJet q br amp j p x k‖≤_ at hc0
    rw [norm_mul]
    calc
      _ ≤ (C*Real.exp (G*p-((N+1:ℕ):ℝ)*k))*(D*Real.exp k) :=
        mul_le_mul hc0 (hd x k hk) (norm_nonneg _) (by positivity)
      _ = (C*D)*Real.exp (G*p-(N:ℝ)*k) := by
        rw [show (C*Real.exp (G*p-((N+1:ℕ):ℝ)*k))*(D*Real.exp k)=
          (C*D)*(Real.exp (G*p-((N+1:ℕ):ℝ)*k)*Real.exp k) by ring,← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ (C*D)*F := by dsimp [F];gcongr
  have ht (i : Fin 3) :
      ‖horizonCoefficient q br amp i p*jetMultiplier j (principalExponent q i)*
        (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖≤
      (B i*‖jetMultiplier j (principalExponent q i)‖*E i)*F := by
    have hBi := hB i
    have hEi := hE i
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (B i*Real.exp (2*p))*‖jetMultiplier j (principalExponent q i)‖*
          (E i*Real.exp (-(N:ℝ)*k)) := by gcongr;exact hb i p hp;exact he i x k hk
      _ = (B i*‖jetMultiplier j (principalExponent q i)‖*E i)*Real.exp (2*p-(N:ℝ)*k) := by
        rw [show (B i*Real.exp (2*p))*‖jetMultiplier j (principalExponent q i)‖*(E i*Real.exp (-(N:ℝ)*k))=
          (B i*‖jetMultiplier j (principalExponent q i)‖*E i)*(Real.exp (2*p)*Real.exp (-(N:ℝ)*k)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by dsimp [F];gcongr
  have hsum : ‖∑ i : Fin 3,horizonCoefficient q br amp i p*jetMultiplier j (principalExponent q i)*
      (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖≤
      (∑ i : Fin 3,B i*‖jetMultiplier j (principalExponent q i)‖*E i)*F := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => ht i)
  have hdec : horizonAngularProduct q br amp w j d p x k=horizonReader q w*
      (horizonJet q br amp j p x k*angularJet q d x k+
        ∑ i : Fin 3,horizonCoefficient q br amp i p*jetMultiplier j (principalExponent q i)*
          (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])) := by
    simp only [horizonAngularProduct,horizonPrincipalJet,angularJet_decomposition,Fin.sum_univ_three]
    ring
  apply damped_bound w _ _ H (N:ℝ) p k (by positivity) hp.le hw
  rw [hdec,norm_mul]
  calc
    _ ≤ ‖horizonReader q w‖*((C*D)*F+(∑ i : Fin 3,B i*‖jetMultiplier j (principalExponent q i)‖*E i)*F) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hs hsum)) (norm_nonneg _)
    _ = _ := by dsimp [M,F];ring

private theorem forcing_profile_linear (s amp J K : ℂ) (u : ℝ) :
    forcingProfile s amp J K u=forcingProfile s amp 1 0 u*J+forcingProfile s amp 0 1 u*K := by
  unfold forcingProfile
  ring

private theorem horizon_forcing_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (p x k : ℝ) :
    horizonProduct q br amp w d p x k=horizonReader q w*timeOnset (2*physicalRate q br) p*
      (radialCoefficient q br amp false 1*fixedProduct q br false d x k+
       radialCoefficient q br amp true 1*fixedProduct q br true d x k) := by
  have hlin (i : Fin 3) : profilePrincipal q br amp 1 i=
      radialCoefficient q br amp false 1*sourceCoefficient q br false i+
      radialCoefficient q br amp true 1*sourceCoefficient q br true i :=
    forcing_profile_linear (physicalRate q br) amp (principalAmplitude q i) (principalGradient q br i) 1
  rw [horizonProduct,forcingTrace,forcing_profile_linear]
  simp_rw [hlin]
  simp only [Fin.sum_univ_three,fixedProduct,sourcePrincipal,Matrix.cons_val]
  simp only [radialCoefficient,sourceField,sourceCoefficient,Bool.false_eq_true,↓reduceIte]
  ring

/-- The actual forcing horizon product retains rapid cusp decay in both
reader branches after temporal damping. -/
theorem horizon_forcing_product_decay (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (N : ℕ) (hw : 1≤w.re) :
    ∃ C : ℝ,0≤C ∧ ∀ p x k : ℝ,0<p → 0≤k →
      ‖Complex.exp (-w*(p:ℂ))*horizonProduct q br amp w d p x k‖≤
        C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  obtain ⟨C0,h0,hc0⟩ := fixed_product_decay q br false d N
  obtain ⟨C1,h1,hc1⟩ := fixed_product_decay q br true d N
  let M := ‖horizonReader q w‖*D*(‖radialCoefficient q br amp false 1‖*C0+‖radialCoefficient q br amp true 1‖*C1)
  have hM : 0≤M := by dsimp [M];positivity
  refine ⟨M,hM,?_⟩
  intro p x k hp hk
  have hO : ‖timeOnset (2*physicalRate q br) p‖≤D := by
    have h := (le_add_of_nonneg_right (norm_nonneg (timeOnsetFirst (2*physicalRate q br) p))).trans (hd p)
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using h
  apply damped_bound w _ M 0 (N:ℝ) p k hM hp.le (by simpa using hw)
  rw [horizon_forcing_decomposition,norm_mul,norm_mul]
  calc
    _ ≤ ‖horizonReader q w‖*D*(‖radialCoefficient q br amp false 1‖*(C0*Real.exp (-(N:ℝ)*k))+
        ‖radialCoefficient q br amp true 1‖*(C1*Real.exp (-(N:ℝ)*k))) := by
      gcongr
      exact (norm_add_le _ _).trans (by rw [norm_mul,norm_mul];gcongr;exact hc0 x k hk;exact hc1 x k hk)
    _ = _ := by simp only [zero_mul,zero_sub];dsimp [M];ring

end
end RHTower.D4BMOriginalHorizonProductDecay
