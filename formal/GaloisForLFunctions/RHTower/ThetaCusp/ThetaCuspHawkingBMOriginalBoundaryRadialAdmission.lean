import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalBoundaryRestoration

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace RHTower.D4BMOriginalBoundaryRadialAdmission
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMLaplaceRadial D4BMIngoingCoordinates
open D4BMOriginalAngularCurrent D4BMOriginalOrbitCurrent D4BMOriginalReaderEquation
open D4BMOriginalMetricSourceTransfers D4BMOriginalCompleteTransfer D4BMOriginalCompactBoundary
open D4BMOriginalCuspFlux D4BMOriginalMetricCusp D4BMOriginalCausalPeriod
open D4BMOriginalReaderCuspBounds D4BMOriginalMetricForcingMatch
noncomputable section
set_option autoImplicit false
private abbrev V := ℝ × (ℝ × ℝ)
private abbrev P := Fin 4 → ℝ
private def radius (L : ℝ) := tortoiseRadius (-L/2)
private def chart (k : ℝ) (v : V) : P := ![v.2.1,radius v.1,v.2.2,Real.exp k]

private theorem radius_continuousAt (L : ℝ) (hL : 0<L) : ContinuousAt radius L :=
  (tortoiseRadius_hasDerivAt (-L/2) (by linarith)).continuousAt.comp (f:=fun l : ℝ => -l/2) (x:=L)
    (show ContinuousAt (fun l : ℝ => -l/2) L by fun_prop)

private theorem chart_continuousAt (k : ℝ) (v : V) (hL : 0<v.1) : ContinuousAt (chart k) v := by
  have hR := (radius_continuousAt v.1 hL).comp continuous_fst.continuousAt
  change ContinuousAt (fun t : V => (![t.2.1,radius t.1,t.2.2,Real.exp k]:P)) v
  fun_prop

private theorem forcing_continuousAt (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (k : ℝ) (v : V) (hL : 0<v.1) :
    ContinuousAt (fun t : V => D4BMOriginalSourceContact.originalForcing q br amp (chart k t)) v := by
  let s := physicalRate q br
  have hR := (radius_continuousAt v.1 hL).comp continuous_fst.continuousAt
  have hr := tortoiseRadius_exterior (-v.1/2) (by linarith : -v.1/2<0)
  have hT := (tortoise_hasDerivAt (radius v.1) hr).continuousAt.comp (f:=fun t : V => radius t.1) (x:=v) hR
  have hu := Complex.continuous_ofReal.continuousAt.comp ((radialUnit_hasDerivAt _).continuousAt.comp (f:=fun t : V => tortoise (radius t.1)) (x:=v) hT)
  have hA := (sourceAmplitude_hasDerivAt s 0 amp 1 _).continuousAt.comp (f:=fun t : V => tortoise (radius t.1)) (x:=v) hT
  have hO := (timeOnset_hasDerivAt (2*s) v.2.1).continuousAt.comp (f:=fun t : V => t.2.1) (x:=v)
    (show ContinuousAt (fun t : V => t.2.1) v by fun_prop)
  have hSq := (fullSquarePotential_smooth q ![v.2.2,Real.exp k] (Real.exp_pos k) 0).continuousAt.comp
    (f:=fun t : V => (![t.2.2,Real.exp k]:Fin 2→ℝ)) (show ContinuousAt (fun t : V => (![t.2.2,Real.exp k]:Fin 2→ℝ)) v by fun_prop)
  have hGr := (fullGradientEnergy_smooth q ![v.2.2,Real.exp k] (Real.exp_pos k)).continuousAt.comp
    (f:=fun t : V => (![t.2.2,Real.exp k]:Fin 2→ℝ)) (show ContinuousAt (fun t : V => (![t.2.2,Real.exp k]:Fin 2→ℝ)) v by fun_prop)
  unfold D4BMOriginalSourceContact.originalForcing timeOriginalForcing
  dsimp only [chart,Matrix.cons_val]
  simp only [sub_add_cancel]
  unfold D4BMJointSource.originalForcing
  exact ((((hu.pow 2).const_sub 1).const_mul (-2)).mul hu |>.mul hA |>.mul
    ((hSq.const_mul _).add (((hu.pow 2).const_mul _ |>.div_const 4).mul
      ((hSq.const_mul _).sub (hGr.div_const 2))))).mul hO

private theorem physical_transfer_continuousAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (k : ℝ) (j : Fin 4) (v : V) (hL : 0<v.1) (hp : 0<v.2.1) :
    ContinuousAt (fun t : V => physicalTransfer q br amp w j t.2.1 (radius t.1) t.2.2 (Real.exp k)) v := by
  have hF := chart_continuousAt k v hL
  have hr := tortoiseRadius_exterior (-v.1/2) (by linarith : -v.1/2<0)
  have hU := D4BMOriginalGreenBoundary.sourceScalar_exterior_smooth q br amp (chart k v) hp hr (Real.exp_pos k)
  have hW := modeScalar_smooth q w hw true (chart k v) hr (Real.exp_pos k)
  have hD {U : P→ℂ} (hU : ContDiffAt ℝ ∞ U (chart k v)) (i : Fin 4) :=
    coordDeriv_contDiffAt (m:=∞) hU (by simp) i
  have hLap : ContDiffAt ℝ ∞ (angularLap (sourceScalar q br amp)) (chart k v) := by
    have hY : ContDiffAt ℝ ∞ (fun t : P => (t 3:ℂ)) (chart k v) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (3:Fin 4))).contDiffAt
    exact (hY.pow 2).mul ((hD (hD hU 2) 2).add (hD (hD hU 3) 3))
  fin_cases j
  · exact (hU.continuousAt.mul (hD hW 3).continuousAt).comp hF
  · exact (hW.continuousAt.mul (hD hU 3).continuousAt).comp hF
  · exact (hLap.continuousAt.mul (hD hW 3).continuousAt).comp hF
  · exact (forcing_continuousAt q br amp k v hL).mul ((hD hW 3).continuousAt.comp hF)

private theorem reader_continuousAt (q : XiZeroCopy) (w : ℂ) (L : ℝ) (hL : 0<L) :
    ContinuousAt (reader q w) L := by
  have hZ := (horizonCoordinate_hasDerivAt (-L/2)).continuousAt.comp (f:=fun l : ℝ => -l/2) (x:=L)
    (show ContinuousAt (fun l : ℝ => -l/2) L by fun_prop)
  have hn := (normalizable_derivatives_continued (w:=w) (chi:=physicalRadialFrequency q)
    (horizonCoordinate_interior (-L/2) (by linarith))).1.continuousAt.comp (f:=fun l : ℝ => horizonCoordinate (-l/2)) (x:=L) hZ
  exact (show ContinuousAt (fun l : ℝ => Complex.exp (w*((-l/2:ℝ):ℂ))) L by fun_prop).mul hn

private theorem coefficient_continuousAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (j : Fin 4) (i : Fin 3) (v : V) (hL : 0<v.1) :
    ContinuousAt (fun t : V => modeTransferCoefficient q q br true amp w j t.2.1 (radius t.1) i) v := by
  let s := physicalRate q br
  have hR := (radius_continuousAt v.1 hL).comp continuous_fst.continuousAt
  have hRC := Complex.continuous_ofReal.continuousAt.comp hR
  have hr := tortoiseRadius_exterior (-v.1/2) (by linarith : -v.1/2<0)
  have hT := (tortoise_hasDerivAt (radius v.1) hr).continuousAt.comp (f:=fun t : V => radius t.1) (x:=v) hR
  have hP : ContinuousAt (fun t : V => t.2.1) v := by fun_prop
  have hO := (timeOnset_hasDerivAt (2*s) v.2.1).continuousAt.comp (f:=fun t : V => t.2.1) (x:=v) hP
  have hN := (radialLift_hasDerivAt s 0 amp 1 _).continuousAt.comp
    ((hP.sub (hP.sub (hT.const_mul 2))).div_const 2)
  have hD := (D4BMNativeResponse.radialResponse_continuous (-principalExponent q i) s amp).continuousAt.comp
    (((hP.add (hP.sub (hT.const_mul 2))).div_const 2).prodMk
      ((hP.sub (hP.sub (hT.const_mul 2))).div_const 2))
  have hA : ContinuousAt (fun t : V => D4BMOriginalOrbitCusp.principalCoefficient q br amp t.2.1 (radius t.1) i) v :=
    hRC.mul ((hD.const_mul (principalAmplitude q i)).add ((hN.mul hO).mul_const (principalAmplitude q i)))
  have hn := (reader_continuousAt q w v.1 hL).comp continuous_fst.continuousAt
  have hB : ContinuousAt (fun t : V => modeAmplitude q w true ![t.2.1,radius t.1]*D4BMOriginalCuspFlux.readerCoefficient q) v := by
    have hc := ((hRC.mul (show ContinuousAt (fun t : V => Complex.exp (-w*(t.2.1:ℂ))) v by fun_prop)).mul hn).mul_const
      (D4BMOriginalCuspFlux.readerCoefficient q)
    apply hc.congr_of_eventuallyEq
    have hpos := continuous_fst.continuousAt.eventually (lt_mem_nhds hL)
    filter_upwards [hpos] with t ht
    dsimp only [radius,Function.comp_def,Pi.mul_apply]
    rw [mode_amplitude_collar q w t.2.1 t.1 ht]
  have hu := Complex.continuous_ofReal.continuousAt.comp ((radialUnit_hasDerivAt _).continuousAt.comp (f:=fun t : V => tortoise (radius t.1)) (x:=v) hT)
  have hsA := (sourceAmplitude_hasDerivAt s 0 amp 1 _).continuousAt.comp (f:=fun t : V => tortoise (radius t.1)) (x:=v) hT
  have hS : ContinuousAt (fun t : V => forcingScale q br amp t.2.1 (radius t.1)) v :=
    (((((hu.pow 2).const_sub 1).const_mul (-2)).mul hu).mul hsA).mul hO
  have hFV : ContinuousAt (fun t : V => forcingValueCoefficient q br amp t.2.1 (radius t.1)) v :=
    hS.mul (((((hu.pow 2).const_mul _).mul_const _).mul_const _).div_const 4 |>.const_add _)
  have hFL : ContinuousAt (fun t : V => forcingLaplacianCoefficient q br amp t.2.1 (radius t.1)) v :=
    hS.mul (((hu.pow 2).const_mul _).div_const 8)
  have hFC : ContinuousAt (fun t : V => forcingPrincipalCoefficient q br amp t.2.1 (radius t.1) i) v :=
    (hFV.add ((hFL.mul_const _).mul_const _)).mul_const _
  fin_cases j
  · exact hA.mul (hB.mul_const _)
  · exact (hA.mul_const _).mul hB
  · exact ((hA.mul_const _).mul_const _).mul (hB.mul_const _)
  · exact hFC.mul (hB.mul_const _)

private theorem normalized_cut (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (p L x k : ℝ) (hp : 0<p) (hL : 0<L) (j : Fin 4) :
    transferCut q br amp w j p L x k=
      ![(tortoiseRadius (-L/2):ℂ)^(2 : ℕ),(tortoiseRadius (-L/2):ℂ)^(2 : ℕ),
        (tortoiseRadius (-L/2):ℂ)^(2 : ℕ),(tortoiseRadius (-L/2):ℂ)] j*
        normalizedTransfer q br amp w j p L x k := by
  have hs := physical_source_transfer_products q br amp w hw p L x k hp hL
  have hf := physical_forcing_transfer_product q br amp w hw p L x k hL
  fin_cases j
  · change transferCut q br amp w 0 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.1
  · change transferCut q br amp w 1 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.2.1
  · change transferCut q br amp w 2 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hs.2.2
  · change transferCut q br amp w 3 p L x k=_
    simpa [normalizedTransfer,mul_assoc] using hf

/-- All four original transfers are jointly continuous in horizon depth,
positive source time and horizontal position. -/
theorem radial_transfer_joint_continuousAt (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : w.im≠0) (k : ℝ) (j : Fin 4) (v : V) (hL : 0<v.1) (hp : 0<v.2.1) :
    ContinuousAt (fun t : V => radialTransfer q br amp w j t.2.1 t.1 t.2.2 k) v := by
  let c : ℝ→Fin 4→ℂ := fun L => ![(radius L:ℂ)^(2 : ℕ),(radius L:ℂ)^(2 : ℕ),(radius L:ℂ)^(2 : ℕ),
    (radius L:ℂ)*(horizonCoordinate (-L/2):ℂ)]
  have hR := (radius_continuousAt v.1 hL).comp continuous_fst.continuousAt
  have hZ := (horizonCoordinate_hasDerivAt (-v.1/2)).continuousAt.comp (f:=fun t : V => -t.1/2) (x:=v)
    (show ContinuousAt (fun t : V => -t.1/2) v by fun_prop)
  have hRC := Complex.continuous_ofReal.continuousAt.comp hR
  have hZC := Complex.continuous_ofReal.continuousAt.comp hZ
  have hc : ContinuousAt (fun t : V => c t.1 j) v := by
    fin_cases j
    · exact hRC.pow 2
    · exact hRC.pow 2
    · exact hRC.pow 2
    · exact hRC.mul hZC
  have hR0 : (radius v.1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (by have h:=tortoiseRadius_exterior (-v.1/2) (by linarith : -v.1/2<0);change tortoiseRadius (-v.1/2)≠0;linarith)
  have hZ0 : (horizonCoordinate (-v.1/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (horizonCoordinate_interior (-v.1/2) (by linarith)).1)
  have hc0 : c v.1 j≠0 := by fin_cases j <;> simp [c,hR0,hZ0]
  have hco : ContinuousAt (fun t : V => ∑ i : Fin 3,
      modeTransferCoefficient q q br true amp w j t.2.1 (radius t.1) i*Complex.exp (fluxExponent q q i*(k:ℂ))) v := by
    have h (i : Fin 3) := (coefficient_continuousAt q br amp w j i v hL).mul_const (Complex.exp (fluxExponent q q i*(k:ℂ)))
    convert ((h 0).add (h 1)).add (h 2) using 1
    funext t
    simp only [Fin.sum_univ_three,Pi.add_apply]
  have hcut : ContinuousAt (fun t : V => transferCut q br amp w j t.2.1 t.1 t.2.2 k) v :=
    (physical_transfer_continuousAt q br amp w hw k j v hL hp).sub hco
  have he : (fun t : V => radialTransfer q br amp w j t.2.1 t.1 t.2.2 k) =ᶠ[𝓝 v]
      (fun t : V => transferCut q br amp w j t.2.1 t.1 t.2.2 k/c t.1 j) := by
    have hLp := continuous_fst.continuousAt.eventually (lt_mem_nhds hL)
    have hPp := (continuous_fst.comp continuous_snd).continuousAt.eventually (lt_mem_nhds hp)
    filter_upwards [hLp,hPp] with t htL htp
    have hcT : c t.1 j≠0 := by
      have hR0 : (radius t.1:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
        (by have h:=tortoiseRadius_exterior (-t.1/2) (by linarith : -t.1/2<0);change tortoiseRadius (-t.1/2)≠0;linarith)
      have hZ0 : (horizonCoordinate (-t.1/2):ℂ)≠0 := Complex.ofReal_ne_zero.mpr
        (ne_of_gt (horizonCoordinate_interior (-t.1/2) (by linarith)).1)
      fin_cases j <;> simp [c,hR0,hZ0]
    have hs : transferCut q br amp w j t.2.1 t.1 t.2.2 k=c t.1 j*radialTransfer q br amp w j t.2.1 t.1 t.2.2 k := by
      rw [normalized_cut q br amp w hw t.2.1 t.1 t.2.2 k htp htL j]
      fin_cases j <;> simp [c,radius,radialTransfer,normalizedTransfer,
        D4BMOriginalForcingProductBounds.raw_product_factor q br amp w true t.2.1 t.1 t.2.2 k htL];ring
    rw [hs]
    exact (mul_div_cancel_left₀ _ hcT).symm
  exact (hcut.div hc hc0).congr_of_eventuallyEq he

/-- Separate radial admission of each actual endpoint transfer. -/
theorem endpoint_radial_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (k A B p : ℝ) (hA : 0<A) (hAB : A≤B) (hp : 0<p) (j : Fin 4) :
    IntervalIntegrable (fun L => ∫ x in (-1/2:ℝ)..1/2,radialTransfer q br amp w j p L x k) volume A B := by
  have hc : ContinuousOn (fun t : ℝ×ℝ => radialTransfer q br amp w j p t.1 t.2 k)
      (Icc A B ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) := by
    intro t ht
    exact ((radial_transfer_joint_continuousAt q br amp w hw k j (t.1,(p,t.2))
      (hA.trans_le ht.1.1) hp).comp (f:=fun u : ℝ×ℝ => (u.1,(p,u.2)))
      (show ContinuousAt (fun u : ℝ×ℝ => (u.1,(p,u.2))) t by fun_prop)).continuousWithinAt
  have hi : Integrable (fun t : ℝ×ℝ => radialTransfer q br amp w j p t.1 t.2 k)
      ((volume.restrict (Ioc A B)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),IntegrableOn]
    using hi.integral_prod_left

/-- Separate radial admission of every actual time/horizontal transfer moment;
the proof derives full compact product admission before applying Fubini. -/
theorem moment_radial_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (k A B a b : ℝ) (hA : 0<A) (hAB : A≤B) (ha : 0<a) (hab : a≤b) (j : Fin 4) :
    IntervalIntegrable (fun L => ∫ p in a..b,∫ x in (-1/2:ℝ)..1/2,
      radialTransfer q br amp w j p L x k) volume A B := by
  have hx : (-1/2:ℝ)≤1/2 := by norm_num
  have hc : ContinuousOn (fun t : V => radialTransfer q br amp w j t.2.1 t.1 t.2.2 k)
      (Icc A B ×ˢ (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ))) :=
    fun t ht => (radial_transfer_joint_continuousAt q br amp w hw k j t
      (hA.trans_le ht.1.1) (ha.trans_le ht.2.1.1)).continuousWithinAt
  have hi : Integrable (fun t : V => radialTransfer q br amp w j t.2.1 t.1 t.2.2 k)
      ((volume.restrict (Ioc A B)).prod
        ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ))))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod,Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hc.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).mono_set
      (Set.prod_mono Ioc_subset_Icc_self (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB]
  apply hi.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
  have hcL : ContinuousOn (fun t : ℝ×ℝ => radialTransfer q br amp w j t.1 L t.2 k)
      (Icc a b ×ˢ Icc (-1/2:ℝ) (1/2:ℝ)) := fun t ht =>
    (radial_transfer_continuousAt q br amp w hw L k (hA.trans hL.1) j t (ha.trans_le ht.1.1)).continuousWithinAt
  have hiL : Integrable (fun t : ℝ×ℝ => radialTransfer q br amp w j t.1 L t.2 k)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc (-1/2:ℝ) (1/2:ℝ)))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hcL.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hx]
    using integral_prod (fun t : ℝ×ℝ => radialTransfer q br amp w j t.1 L t.2 k) hiL

/-- The complete physical boundary has genuine radial admission before any
leading-trace subtraction; its two endpoints and four moments remain separate. -/
theorem boundary_radial_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (k A B a b : ℝ) (hA : 0<A) (hAB : A≤B) (ha : 0<a) (hab : a≤b) :
    IntervalIntegrable (fun L => radialBoundary q br amp w a b L k) volume A B := by
  have hE := (endpoint_radial_integrable q br amp w hw k A B b hA hAB (ha.trans_le hab) 0).sub
    (endpoint_radial_integrable q br amp w hw k A B a hA hAB ha 0)
  have hM := moment_radial_integrable q br amp w hw k A B a b hA hAB ha hab
  exact (hE.const_mul _).add (((((hM 1).const_mul _).sub (hM 2)).sub
    ((hM 0).const_mul _)).sub (hM 3) |>.const_mul w)

/-- The retained leading boundary trace has its literal radial integral.
Subtracting it from the admitted physical boundary commutes with radial integration. -/
theorem boundary_radial_trace_subtraction (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (hw : w.im≠0)
    (k A B a b : ℝ) (hA : 0<A) (hAB : A≤B) (ha : 0<a) (hab : a≤b) :
    (∫ L in A..B,radialBoundary q br amp w a b L k-
      D4BMOriginalBoundaryRestoration.horizonBoundary q br amp w a b k)=
      (∫ L in A..B,radialBoundary q br amp w a b L k)-
        (B-A:ℝ)•D4BMOriginalBoundaryRestoration.horizonBoundary q br amp w a b k := by
  rw [intervalIntegral.integral_sub (boundary_radial_integrable q br amp w hw k A B a b hA hAB ha hab)
    intervalIntegrable_const,intervalIntegral.integral_const]

/-- Independent cusp/time/horizon restoration of the separately admitted
complete physical boundary and its literal leading-trace radial counterterm.
The factor one-half is the original collar Jacobian. -/
theorem boundary_radial_joint_limit (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re →
      ∃ L0 : ℝ,0<L0 ∧
      ∀ (T : ℝ×ℝ→{v : ℝ×ℝ // 0<v.1 ∧ v.1≤v.2}) (M : ℝ×ℝ→Ici L0),
        Tendsto (fun z : ℝ×ℝ =>
          ((∫ L in L0..(M z:ℝ),radialBoundary q br amp w (T z).val.1 (T z).val.2 L z.2)-
            ((M z:ℝ)-L0)•D4BMOriginalBoundaryRestoration.horizonBoundary q br amp w (T z).val.1 (T z).val.2 z.2)/2)
          ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨G1,hG1,h1⟩ := D4BMOriginalBoundaryRestoration.physical_boundary_restoration q br amp
  obtain ⟨G2,_,h2⟩ := D4BMOriginalBoundaryCollarBounds.complete_boundary_collar_joint_limit q br amp
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨L0,hL0,hl⟩ := h2 w hwi hw2
  refine ⟨L0,hL0,?_⟩
  intro T M
  have ht := (hl T M).div_const (2:ℂ)
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [((eventually_ge_atTop (0:ℝ)).prod_mk (eventually_ge_atTop (0:ℝ)))] with z hz
  rw [← boundary_radial_trace_subtraction q br amp w hwi z.2 L0 (M z) (T z).val.1 (T z).val.2
    hL0 (M z).property (T z).property.1 (T z).property.2]
  congr 1
  apply intervalIntegral.integral_congr
  intro L hL
  have hMz : L0≤(M z:ℝ) := (M z).property
  have hLI : L∈Icc L0 (M z:ℝ) := by simpa only [uIcc_of_le hMz] using hL
  have hLp := hL0.trans_le hLI.1
  have he := h1 w hwi hw1 (T z).val.1 (T z).val.2 L z.2
    (T z).property.1 (T z).property.2 hLp hz.2
  unfold D4BMOriginalBoundaryRestoration.physicalRestoredBoundary at he
  dsimp only at he
  rw [complete_metric_boundary_products q br amp w hwi (T z).val.1 (T z).val.2 L z.2
    (T z).property.1 (T z).property.2 hLp,
    complete_boundary_radial_density q br amp w (T z).val.1 (T z).val.2 L z.2 hLp] at he
  exact he.symm

end
end RHTower.D4BMOriginalBoundaryRadialAdmission
