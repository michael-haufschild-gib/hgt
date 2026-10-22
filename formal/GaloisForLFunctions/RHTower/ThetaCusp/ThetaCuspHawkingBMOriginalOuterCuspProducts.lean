import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalOuterCuspSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalForcingProductBounds

/-! The original principal-subtracted source/reader products on the finite outer interval. -/
open Set Filter Topology
namespace RHTower.D4BMOriginalOuterCuspProducts
open D4BMJointSource D4BMModularCore D4BMNativeResponse D4BMOriginalCausalAdmission
open D4BMOriginalCausalPotential D4BMOriginalPrincipalHorizonBounds D4BMOriginalAngularReaderBounds
open D4BMOriginalAngularProducts D4BMOriginalReaderCuspBounds D4BMOriginalOuterCuspSource D4BMOriginalCausalCuspGrowth
noncomputable section
set_option autoImplicit false

private theorem lift_outer_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (A : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ p L : ℝ,L∈Ioc (0:ℝ) A → ‖nullLift (physicalRate q br) amp p (p+L)‖≤C := by
  have hL : Continuous (radialLift (physicalRate q br) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun t => (radialLift_hasDerivAt _ _ _ _ t).continuousAt)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hL.continuousOn (s:=Icc (-A/2) (0:ℝ)))
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  refine ⟨max C 0*D,by positivity,?_⟩
  intro p L hL
  have hT : ‖timeOnset (2*physicalRate q br) p‖≤D := by
    have h := hd p
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    linarith [norm_nonneg (timeOnsetFirst (2*physicalRate q br) p)]
  rw [nullLift,show (p-(p+L))/2=-L/2 by ring,norm_mul]
  exact mul_le_mul ((hC (-L/2) ⟨by linarith [hL.2],by linarith [hL.1]⟩).trans (le_max_left _ _))
    hT (norm_nonneg _) (le_max_right _ _)

/-- Every unchanged principal source coefficient has the same ingoing growth
bound on the finite outer interval, including the original onset lift. -/
theorem outer_coefficient_growth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (i : Fin 3) (A : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ p L : ℝ,0≤p → L∈Ioc (0:ℝ) A →
      ‖coefficient q br amp i p L‖≤C*Real.exp (2*p) := by
  have hm : 0≤(principalExponent q i).re ∧ (principalExponent q i).re≤2 := by
    have hq := xi_divisor_support_re_mem_open_unit q.1
    fin_cases i <;> norm_num [principalExponent,Complex.mul_re] <;> constructor <;> linarith [hq.1,hq.2]
  obtain ⟨C,hC,hc⟩ := physical_radialResponse_ingoing_growth q br amp (principalExponent q i) hm.1
  obtain ⟨D,hD,hd⟩ := lift_outer_bound q br amp A
  refine ⟨‖principalAmplitude q i‖*(C+D),by positivity,?_⟩
  intro p L hp hL
  have hR := hc p (p+L) hp (by linarith [hL.1])
  have hR' : ‖radialResponse (-principalExponent q i) (physicalRate q br) amp ((p+(p+L))/2) ((p-(p+L))/2)‖≤C*Real.exp (2*p) :=
    hR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm.2 hp)) hC)
  have hD' : ‖nullLift (physicalRate q br) amp p (p+L)‖≤D*Real.exp (2*p) :=
    (hd p L hL).trans (le_mul_of_one_le_right hD (Real.one_le_exp (by positivity)))
  rw [coefficient,D4BMOriginalCuspJets.coefficient,principalNullResponse]
  calc
    _ ≤ ‖principalAmplitude q i‖*‖radialResponse (-principalExponent q i) (physicalRate q br) amp ((p+(p+L))/2) ((p-(p+L))/2)‖+
      ‖nullLift (physicalRate q br) amp p (p+L)‖*‖principalAmplitude q i‖ := by
      simpa only [norm_mul] using norm_add_le
        (principalAmplitude q i*radialResponse (-principalExponent q i) (physicalRate q br) amp ((p+(p+L))/2) ((p-(p+L))/2))
        (nullLift (physicalRate q br) amp p (p+L)*principalAmplitude q i)
    _ ≤ ‖principalAmplitude q i‖*(C*Real.exp (2*p))+(D*Real.exp (2*p))*‖principalAmplitude q i‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hR' (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hD' (norm_nonneg _))
    _ = _ := by ring

private theorem product_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (j : Fin 5) (d : Bool) (p L x k : ℝ) :
    angularProduct q br amp w j d p L x k=reader q w L*
      (sourceJet q br amp j p L x k*angularJet q d x k+
        ∑ i : Fin 3,coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*
          (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])) := by
  rw [angularProduct,original_source_jet_expansion,angularJet_decomposition]
  simp only [principalJet,Fin.sum_univ_three]
  ring

/-- Every actual differentiated source/reader product, with its unchanged
three principal products subtracted, has a common integrable time envelope
through the outer endpoint. -/
theorem outer_angular_product_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (j : Fin 5) (d : Bool) (N : ℕ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,∀ p x k : ℝ,0≤p → 0≤k →
        ‖Complex.exp (-w*(p:ℂ))*angularProduct q br amp w j d p L x k‖≤
          C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨G,hG,hg⟩ := source_jet_damped q br amp j (N+1)
  obtain ⟨D,hD,hd⟩ := angularJet_bound q d
  have ht (i : Fin 3) := principal_tail_bound q d (principalExponent q i) N
  choose H hH hh using ht
  refine ⟨max G 2,le_max_of_le_left hG,?_⟩
  intro w hw A hA
  obtain ⟨B,hB,hb⟩ := hg w (by linarith [le_max_left G 2])
  obtain ⟨R,hR,hr⟩ := outer_reader_bound q w A hA (by linarith [le_max_right G 2])
  have hcoef (i : Fin 3) := outer_coefficient_growth q br amp i A
  choose C hC hc using hcoef
  let S := ∑ i : Fin 3,C i*‖jetMultiplier j (principalExponent q i)‖*H i
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hC i) (norm_nonneg _)) (hH i))
  refine ⟨R*(B*D+S),by positivity,?_⟩
  intro L hL p x k hp hk
  let E := Complex.exp (-w*(p:ℂ))
  have he : ‖E‖=Real.exp (-w.re*p) := by simp [E,Complex.norm_exp]
  have hmain : ‖E*sourceJet q br amp j p L x k*angularJet q d x k‖≤
      B*D*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
    rw [norm_mul]
    calc
      _ ≤ (B*Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp (-p))*(D*Real.exp k) :=
        mul_le_mul (hb p L x k hp hL.1 hk) (hd x k hk) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show (B*Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp (-p))*(D*Real.exp k)=
          B*D*(Real.exp (-((N+1:ℕ):ℝ)*k)*Real.exp k)*Real.exp (-p) by ring,← Real.exp_add]
        congr 3
        push_cast
        ring
  have hsum : ‖∑ i : Fin 3,E*coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*
      (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])‖≤
        S*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
    apply (norm_sum_le _ _).trans
    simp only [S,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hCi := hC i
    have hHi := hH i
    have hE : ‖E*coefficient q br amp i p L‖≤C i*Real.exp (-p) := by
      rw [norm_mul,he]
      calc
        _ ≤ Real.exp (-w.re*p)*(C i*Real.exp (2*p)) :=
          mul_le_mul_of_nonneg_left (hc i p L hp hL) (Real.exp_nonneg _)
        _ = C i*Real.exp ((2-w.re)*p) := by rw [mul_left_comm,← Real.exp_add];congr 2;ring
        _ ≤ _ := by gcongr; nlinarith [le_max_right G 2]
    rw [norm_mul,norm_mul]
    calc
      _ ≤ (C i*Real.exp (-p))*‖jetMultiplier j (principalExponent q i)‖*(H i*Real.exp (-(N:ℝ)*k)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hE (norm_nonneg _)) (hh i x k hk) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hid : E*angularProduct q br amp w j d p L x k=reader q w L*
      (E*sourceJet q br amp j p L x k*angularJet q d x k+
        ∑ i : Fin 3,E*coefficient q br amp i p L*jetMultiplier j (principalExponent q i)*
          (Complex.exp (principalExponent q i*(k:ℂ))*tailJet q d ![x,Real.exp k])) := by
    rw [product_decomposition]
    simp only [Fin.sum_univ_three]
    ring
  change ‖E*angularProduct q br amp w j d p L x k‖≤_
  rw [hid,norm_mul]
  calc
    _ ≤ R*((B*D*Real.exp (-(N:ℝ)*k)*Real.exp (-p))+(S*Real.exp (-(N:ℝ)*k)*Real.exp (-p))) :=
      mul_le_mul (hr L hL) ((norm_add_le _ _).trans (add_le_add hmain hsum)) (norm_nonneg _) hR
    _ = _ := by dsimp [S];ring

open D4BMOriginalForcingProductBounds D4BMOriginalCornerForcing D4BMOriginalForcingAngularPeriod
open D4BMGlobalAngularResponse D4BMLaplaceRadial

private theorem profile_coefficient_bound (q : XiZeroCopy) (br : Bool) (amp : ℂ) (d : Bool) (A : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,‖radialCoefficient q br amp d (radialUnit (-L/2))‖≤C := by
  have hu : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun x => (radialUnit_hasDerivAt x).continuousAt)
  have hp : Continuous (fun x : ℝ => power (2*physicalRate q br) (1+radialUnit x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((power_derivatives (2*physicalRate q br) (radialUnit_add_one_pos x)).1.scomp x
      ((radialUnit_hasDerivAt x).const_add 1)).continuousAt
  have hF : Continuous (fun x => radialCoefficient q br amp d (radialUnit x)) := by
    cases d <;> unfold radialCoefficient forcingProfile <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hF.continuousOn (s:=Icc (-A/2) (0:ℝ)))
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro L hL
  exact (hC (-L/2) ⟨by linarith [hL.2],by linarith [hL.1]⟩).trans (le_max_left _ _)

private theorem forcing_decomposition (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (d : Bool) (p L x k : ℝ) (hL : 0<L) :
    normalizedProduct q br amp w d p L x k=reader q w L*timeOnset (2*physicalRate q br) p*
      (radialCoefficient q br amp false (radialUnit (-L/2))*fixedProduct q br false d x k+
        radialCoefficient q br amp true (radialUnit (-L/2))*fixedProduct q br true d x k) := by
  have hlin (J K : ℂ) (u : ℝ) : forcingProfile (physicalRate q br) amp J K u=
      forcingProfile (physicalRate q br) amp 1 0 u*J+forcingProfile (physicalRate q br) amp 0 1 u*K := by
    unfold forcingProfile
    ring
  have hi (i : Fin 3) (u : ℝ) : profilePrincipal q br amp u i=
      radialCoefficient q br amp false u*sourceCoefficient q br false i+
        radialCoefficient q br amp true u*sourceCoefficient q br true i :=
    hlin (principalAmplitude q i) (principalGradient q br i) u
  rw [normalizedProduct,original_full_forcing_normalized q br amp hL,hlin]
  simp_rw [hi]
  simp only [fixedProduct,sourcePrincipal,Fin.sum_univ_three,sourceField,sourceCoefficient,
    radialCoefficient,Matrix.cons_val,Bool.false_eq_true,↓reduceIte]
  ring

/-- The full normalized forcing transfer, including its square and half-gradient
fields and original onset, has uniform cusp/time decay through the outer endpoint. -/
theorem outer_forcing_product_bound (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (d : Bool)
    (N : ℕ) (hw : 1≤w.re) (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ,0≤C ∧ ∀ L∈Ioc (0:ℝ) A,∀ p x k : ℝ,0≤p → 0≤k →
      ‖Complex.exp (-w*(p:ℂ))*normalizedProduct q br amp w d p L x k‖≤
        C*Real.exp (-(N:ℝ)*k)*Real.exp (-p) := by
  obtain ⟨R,hR,hr⟩ := outer_reader_bound q w A hA (by linarith)
  obtain ⟨C0,hC0,hc0⟩ := profile_coefficient_bound q br amp false A
  obtain ⟨C1,hC1,hc1⟩ := profile_coefficient_bound q br amp true A
  obtain ⟨B0,hB0,hb0⟩ := fixed_product_decay q br false d N
  obtain ⟨B1,hB1,hb1⟩ := fixed_product_decay q br true d N
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  obtain ⟨D,hD,hd⟩ := timeOnset_pair_bound (2*physicalRate q br) 0 (by linarith)
  refine ⟨R*D*(C0*B0+C1*B1),by positivity,?_⟩
  intro L hL p x k hp hk
  have hon : ‖timeOnset (2*physicalRate q br) p‖≤D := by
    have h := hd p
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    linarith [norm_nonneg (timeOnsetFirst (2*physicalRate q br) p)]
  have he : ‖Complex.exp (-w*(p:ℂ))‖≤Real.exp (-p) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    nlinarith
  rw [forcing_decomposition q br amp w d p L x k hL.1,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ Real.exp (-p)*(R*D*(C0*(B0*Real.exp (-(N:ℝ)*k))+C1*(B1*Real.exp (-(N:ℝ)*k)))) :=
      mul_le_mul he (mul_le_mul (mul_le_mul (hr L hL) hon (norm_nonneg _) hR)
        ((norm_add_le _ _).trans (add_le_add
          ((norm_mul _ _).trans_le (mul_le_mul (hc0 L hL) (hb0 x k hk) (norm_nonneg _) hC0))
          ((norm_mul _ _).trans_le (mul_le_mul (hc1 L hL) (hb1 x k hk) (norm_nonneg _) hC1))))
        (norm_nonneg _) (by positivity)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by ring

end
end RHTower.D4BMOriginalOuterCuspProducts
