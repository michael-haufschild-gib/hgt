import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceDensityDual
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceContactRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFieldMatchingNoGo

/-! Exact classification of local radial source transposes and their unavoidable AdS boundary charge.
The full literal source and onset are retained. This excludes radial multiplication as a
physical fundamental-QNM matching mechanism; no nonlocal matching obstruction is asserted. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMLocalTranspose
open D4BMCommonRadialSource D4BMJointSource D4BMModularCore D4BMHorizon
open D4BMGlobalAngularResponse D4BMLaplaceRadial D4BMSourceDensityDual
open D4BMSourceContactRigidity
noncomputable section
set_option autoImplicit false


theorem exists_sourceContact_ne_zero (q : XiZeroCopy) :
    ∃ z : UpperHalfPlane, sourceContact q (coordinates z) ≠ 0 := by
  by_contra! h
  have hz (p : Point) (hp : 0<p 1) : sourceContact q p=0 := by
    let z : UpperHalfPlane := ⟨⟨p 0,p 1⟩,hp⟩
    have he : coordinates z=p := by ext i; fin_cases i <;> rfl
    simpa only [he] using h z
  have hg (p : Point) (hp : 0<p 1) :
      sourceContact q =ᶠ[𝓝 p] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp] with z hzp
    exact hz z hzp
  have hd (p : Point) (hp : 0<p 1) (i : Fin 2) :
      coordDeriv i (sourceContact q) p=0 := by
    have he := (hg p hp).fderiv_eq (𝕜:=ℝ)
    simp [coordDeriv,he]
  have hdd (p : Point) (hp : 0<p 1) (i j : Fin 2) :
      coordDeriv i (coordDeriv j (sourceContact q)) p=0 := by
    have he : coordDeriv j (sourceContact q) =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp] with z hzp
      exact hd z hzp j
    have hef := he.fderiv_eq (𝕜:=ℝ)
    simp [coordDeriv,hef]
  obtain ⟨X,y,hy,hS⟩ := D4BMNativeFieldMatching.exists_original_scalar_ne_zero q
  let z : UpperHalfPlane := ⟨⟨X,y⟩,hy⟩
  have hi := sourceContact_differential_identity q z
  have hp : 0<(coordinates z) 1 := hy
  rw [scalarLaplacian_eq _ _ hp] at hi
  simp only [h z,scalarContactGradientPair,contactGradientEnergy,
    hd _ hp,hdd _ hp,mul_zero,zero_mul,add_zero,zero_pow (by decide : 2≠0),
    sub_zero] at hi
  exact (mul_ne_zero (sourceContact_rigidity_factor_ne_zero q) (pow_ne_zero 4 hS)) hi

private theorem unit_ne_zero (x : Iio (0:ℝ)) : (radialUnit x.val:ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (radialUnit_bounds x.val x.property).1.ne'

private theorem unit_sub_one_ne_zero (x : Iio (0:ℝ)) : (radialUnit x.val:ℂ)-1 ≠ 0 := by
  exact_mod_cast sub_ne_zero.mpr (radialUnit_bounds x.val x.property).2.ne

private theorem seed_derivative (s a : ℂ) (v x : ℝ) (J : ℂ) :
    HasDerivAt (fun y => seed s a v y J)
      (2*s*((radialUnit x:ℂ)-1)*seed s a v x J) x := by
  apply (((sourceAmplitude_hasDerivAt s 0 a 1 x).mul_const
    (timeOnset (2*s) v)).mul_const J).congr_deriv
  dsimp only [seed,amplitudeRate]
  ring

private theorem seed_ne_zero (s : ℂ) (x : ℝ) : seed s 1 2 x 1 ≠ 0 := by
  have hp := power_ne_zero (2*s) (radialUnit_add_one_pos x)
  simpa [seed,sourceAmplitude,timeOnset,
    Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2)] using
    mul_ne_zero hp (Complex.exp_ne_zero (2*s*(2:ℂ)))

private theorem opposite_rate (q : XiZeroCopy) (br : Bool) :
    physicalRate q (!br) = -physicalRate q br-3 := by
  cases br <;> simp only [physicalRate,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    if_false,if_true] <;> ring

/-- Preserve the literal source-transpose identity at its original clock and angular source.
No independent angular jets or replacement forcing are inserted. -/
def PreservesSource (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ) : Prop :=
  ∀ (a b : ℂ) (v : ℝ) (x : Iio (0:ℝ)) (z : UpperHalfPlane),
    -2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)*
      seed (physicalRate q br) a v x.val 1 *
      transposeProfile (scalarParameter q)
        (fun y => W y*seed (physicalRate q (!br)) b v y (fullSquarePotential q (coordinates z)))
        (fun y => W y*seed (physicalRate q (!br)) b v y
          (scalarLaplacian (fullSquarePotential q) (coordinates z))) x.val =
    W x.val*seed (physicalRate q (!br)) b v x.val 1*
      timeOriginalForcing q br a (v-x.val) x.val (coordinates z)

private theorem weighted_defect (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ)
    (x : Iio (0:ℝ)) (hW : DifferentiableAt ℝ W x.val) (z : UpperHalfPlane) :
    ((radialUnit x.val:ℂ)-1)*
      (-2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)*
        seed (physicalRate q br) 1 2 x.val 1 *
        transposeProfile (scalarParameter q)
          (fun y => W y*seed (physicalRate q (!br)) 1 2 y (fullSquarePotential q (coordinates z)))
          (fun y => W y*seed (physicalRate q (!br)) 1 2 y
            (scalarLaplacian (fullSquarePotential q) (coordinates z))) x.val -
        W x.val*seed (physicalRate q (!br)) 1 2 x.val 1*
          timeOriginalForcing q br 1 (2-x.val) x.val (coordinates z)) =
      -2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)^(3 : ℕ)*
        seed (physicalRate q br) 1 2 x.val 1*
        seed (physicalRate q (!br)) 1 2 x.val 1*sourceContact q (coordinates z)*
        (deriv W x.val-((radialUnit x.val:ℂ)-1)*(1-4/(radialUnit x.val:ℂ))*W x.val) := by
  have hw (J : ℂ) : deriv (fun y => W y*seed (physicalRate q (!br)) 1 2 y J) x.val =
      deriv W x.val*seed (physicalRate q (!br)) 1 2 x.val J+
        W x.val*(2*physicalRate q (!br)*((radialUnit x.val:ℂ)-1)*
          seed (physicalRate q (!br)) 1 2 x.val J) :=
    (hW.hasDerivAt.mul (seed_derivative (physicalRate q (!br)) 1 2 x.val J)).deriv
  have hs (J : ℂ) := (seed_derivative (physicalRate q br) 1 2 x.val J).deriv
  rw [timeOriginalForcing_common_source]
  simp only [transposeProfile,commonSource,radialGenerator,hw,hs]
  rw [opposite_rate]
  dsimp only [seed,sourceContact]
  field_simp [unit_ne_zero x,unit_sub_one_ne_zero x]
  ring

/-- The actual angular contact forces the radial weight equation; it is not a free test input. -/
theorem source_weight_derivative (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ)
    (hW : DifferentiableOn ℝ W (Iio 0)) (hP : PreservesSource q br W)
    (x : Iio (0:ℝ)) :
    deriv W x.val=((radialUnit x.val:ℂ)-1)*(1-4/(radialUnit x.val:ℂ))*W x.val := by
  obtain ⟨z,hz⟩ := exists_sourceContact_ne_zero q
  have hd := weighted_defect q br W x (hW.differentiableAt (isOpen_Iio.mem_nhds x.property)) z
  rw [hP 1 1 2 x z,sub_self,mul_zero] at hd
  have hu := radialUnit_bounds x.val x.property
  have hn : 1-(radialUnit x.val:ℂ)^(2 : ℕ) ≠ 0 := by
    have h : (1:ℝ)-(radialUnit x.val)^(2 : ℕ)>0 := by nlinarith
    exact_mod_cast h.ne'
  have hc := mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-2:ℂ)≠0) hn)
      (pow_ne_zero 3 (unit_ne_zero x))) (seed_ne_zero (physicalRate q br) x.val))
      (seed_ne_zero (physicalRate q (!br)) x.val)) hz
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_left hc)

private theorem dualWeight_ne_zero (x : Iio (0:ℝ)) : dualWeight x.val ≠ 0 := by
  have hn : 1+(radialUnit x.val:ℂ) ≠ 0 := by
    exact_mod_cast (radialUnit_add_one_pos x.val).ne'
  exact div_ne_zero (pow_ne_zero 5 hn) (pow_ne_zero 4 (unit_ne_zero x))

/-- Every differentiable literal source transpose has the same radial weight up to one constant. -/
theorem source_weight_classification (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ)
    (hW : DifferentiableOn ℝ W (Iio 0)) (hP : PreservesSource q br W) :
    ∃ c : ℂ, ∀ x : Iio (0:ℝ), W x.val=c*dualWeight x.val := by
  have hd (x : Iio (0:ℝ)) : HasDerivAt (fun t => W t/dualWeight t) 0 x.val := by
    have hw := (hW.differentiableAt (isOpen_Iio.mem_nhds x.property)).hasDerivAt
    rw [source_weight_derivative q br W hW hP x] at hw
    apply (hw.div (dualWeight_hasDerivAt x) (dualWeight_ne_zero x)).congr_deriv
    ring
  obtain ⟨c,hc⟩ := isOpen_Iio.exists_is_const_of_deriv_eq_zero isPreconnected_Iio
    (show DifferentiableOn ℝ (fun t => W t/dualWeight t) (Iio 0) from
      fun t ht => (hd ⟨t,ht⟩).differentiableAt.differentiableWithinAt)
    (show (Iio (0:ℝ)).EqOn (deriv (fun t => W t/dualWeight t)) 0 from
      fun t ht => (hd ⟨t,ht⟩).deriv)
  exact ⟨c,fun x => (div_eq_iff (dualWeight_ne_zero x)).mp (hc x.val x.property)⟩


private theorem transposeProfile_const_mul (lam c : ℂ) (F LF : ℝ → ℂ) (x : ℝ)
    (hF : DifferentiableAt ℝ F x) (hLF : DifferentiableAt ℝ LF x) :
    transposeProfile lam (fun y => c*F y) (fun y => c*LF y) x=
      c*transposeProfile lam F LF x := by
  simp only [transposeProfile,radialGenerator,(hF.hasDerivAt.const_mul c).deriv,
    (hLF.hasDerivAt.const_mul c).deriv]
  ring

private theorem preservesSource_const_mul (q : XiZeroCopy) (br : Bool) (c : ℂ) :
    PreservesSource q br (fun x => c*dualWeight x) := by
  intro a b v x z
  have hd (J : ℂ) : DifferentiableAt ℝ (fun y => dualSeed (physicalRate q (!br)) b v y J) x.val :=
    ((dualWeight_hasDerivAt x).mul (seed_derivative (physicalRate q (!br)) b v x.val J)).differentiableAt
  have he (J : ℂ) : (fun y => c*dualWeight y*seed (physicalRate q (!br)) b v y J)=
      (fun y => c*dualSeed (physicalRate q (!br)) b v y J) := by
    funext y
    exact mul_assoc _ _ _
  rw [he,he,transposeProfile_const_mul _ _ _ _ _ (hd _) (hd _)]
  have h := densityDual_originalForcing q br a b v x z
  dsimp only at h
  dsimp only [dualSeed] at h
  dsimp only [dualSeed]
  linear_combination c*h

private theorem preservesSource_congr (q : XiZeroCopy) (br : Bool) (W V : ℝ → ℂ)
    (h : ∀ x : Iio (0:ℝ), W x.val=V x.val) (hV : PreservesSource q br V) :
    PreservesSource q br W := by
  intro a b v x z
  have he (J : ℂ) : (fun y => W y*seed (physicalRate q (!br)) b v y J) =ᶠ[𝓝 x.val]
      (fun y => V y*seed (physicalRate q (!br)) b v y J) := by
    filter_upwards [isOpen_Iio.mem_nhds x.property] with y hy
    rw [h ⟨y,hy⟩]
  have ht : transposeProfile (scalarParameter q)
      (fun y => W y*seed (physicalRate q (!br)) b v y (fullSquarePotential q (coordinates z)))
      (fun y => W y*seed (physicalRate q (!br)) b v y
        (scalarLaplacian (fullSquarePotential q) (coordinates z))) x.val =
    transposeProfile (scalarParameter q)
      (fun y => V y*seed (physicalRate q (!br)) b v y (fullSquarePotential q (coordinates z)))
      (fun y => V y*seed (physicalRate q (!br)) b v y
        (scalarLaplacian (fullSquarePotential q) (coordinates z))) x.val := by
    simp only [transposeProfile,radialGenerator,(he _).deriv_eq,h x]
  rw [ht,h x]
  exact hV a b v x z

/-- Sharp classification on the physical radial interval, retaining every amplitude and onset time. -/
theorem preservesSource_iff (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ)
    (hW : DifferentiableOn ℝ W (Iio 0)) :
    PreservesSource q br W ↔ ∃ c : ℂ, ∀ x : Iio (0:ℝ), W x.val=c*dualWeight x.val := by
  constructor
  · exact source_weight_classification q br W hW
  · rintro ⟨c,hc⟩
    exact preservesSource_congr q br W (fun x => c*dualWeight x) hc
      (preservesSource_const_mul q br c)

/-- The unique local source transpose carries one boundary charge; no radial normalization removes it. -/
theorem preserving_weight_boundary_charge (q : XiZeroCopy) (br : Bool) (W : ℝ → ℂ)
    (hW : DifferentiableOn ℝ W (Iio 0)) (hP : PreservesSource q br W) :
    ∃ c : ℂ, (∀ x : Iio (0:ℝ), W x.val=c*dualWeight x.val) ∧
      ∀ (a : ℂ) (v : ℝ) (z : UpperHalfPlane),
        Tendsto (fun x : ℝ => (radialUnit x:ℂ)^(4 : ℕ)*
          (W x*seed (physicalRate q (!br)) a v x (fullSquarePotential q (coordinates z))))
          (𝓝[<] 0) (𝓝 (c*(a^(2 : ℕ)*timeOnset (2*physicalRate q (!br)) v*
            fullSquarePotential q (coordinates z)))) := by
  obtain ⟨c,hc⟩ := source_weight_classification q br W hW hP
  refine ⟨c,hc,?_⟩
  intro a v z
  apply ((dualSeed_ads_residue q (!br) a v z).const_mul c).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hc ⟨x,hx⟩]
  dsimp only [dualSeed]
  ring

/-- No nonzero local transpose of the actual source can have finite AdS limits at every angular point. -/
theorem not_exists_admitted_source_weight (q : XiZeroCopy) (br : Bool) :
    ¬ ∃ W : ℝ → ℂ, DifferentiableOn ℝ W (Iio 0) ∧ PreservesSource q br W ∧
      (∃ x : Iio (0:ℝ), W x.val ≠ 0) ∧
      ∀ z : UpperHalfPlane, ∃ L : ℂ,
        Tendsto (fun x => W x*seed (physicalRate q (!br)) 1 2 x
          (fullSquarePotential q (coordinates z))) (𝓝[<] 0) (𝓝 L) := by
  rintro ⟨W,hW,hP,⟨x,hx⟩,hA⟩
  obtain ⟨c,hc,hB⟩ := preserving_weight_boundary_charge q br W hW hP
  have hc0 : c ≠ 0 := by intro h; apply hx; rw [hc x,h,zero_mul]
  obtain ⟨X,y,hy,hS⟩ := D4BMNativeFieldMatching.exists_original_scalar_ne_zero q
  let z : UpperHalfPlane := ⟨⟨X,y⟩,hy⟩
  have hQ : fullSquarePotential q (coordinates z) ≠ 0 :=
    mul_ne_zero (by norm_num : (1/2:ℂ)≠0) (mul_ne_zero hS hS)
  have ht : timeOnset (2*physicalRate q (!br)) 2 ≠ 0 := by
    simpa [timeOnset,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2)]
      using Complex.exp_ne_zero (2*physicalRate q (!br)*(2:ℂ))
  obtain ⟨L,hL⟩ := hA z
  have hu : Tendsto (fun x : ℝ => (radialUnit x:ℂ)) (𝓝[<] (0:ℝ)) (𝓝 (0:ℂ)) := by
    have h := ((radialUnit_hasDerivAt 0).continuousAt.tendsto.ofReal).mono_left
      (show 𝓝[<] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa [radialUnit] using h
  have he := tendsto_nhds_unique ((hu.pow 4).mul hL) (hB 1 2 z)
  simp only [zero_pow (by decide : 4≠0),zero_mul,one_pow,one_mul] at he
  exact (mul_ne_zero hc0 (mul_ne_zero ht hQ)) he.symm

/-- A local radial reweighting preserving the full source transpose cannot be a physical
fundamental QNM, even allowing an independent target copy and arbitrary angular normalization. -/
theorem not_exists_physicalQNM_source_weight (q r : XiZeroCopy) (br side outer : Bool) :
    ¬ ∃ (W : ℝ → ℂ) (B : UpperHalfPlane → ℂ),
      DifferentiableOn ℝ W (Iio 0) ∧ PreservesSource q br W ∧
      (∃ x : Iio (0:ℝ), W x.val ≠ 0) ∧
      ∀ (x : Iio (0:ℝ)) (z : UpperHalfPlane),
        W x.val*seed (physicalRate q (!br)) 1 2 x.val (fullSquarePotential q (coordinates z))=
          B z*tortoiseMode outer (physicalFundamentalFrequency r side) (physicalRadialFrequency r) x.val := by
  rintro ⟨W,B,hW,hP,hn,he⟩
  apply not_exists_admitted_source_weight q br
  refine ⟨W,hW,hP,hn,?_⟩
  intro z
  refine ⟨0,?_⟩
  have ht := (physicalFundamentalMode_ads r side outer).const_mul (B z)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (he ⟨x,hx⟩ z).symm


end
end RHTower.D4BMLocalTranspose
