import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCommonRadialSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalRadialModes
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies

/-! Source-derived FE density dual, exact retained spin-two radial flux, and its
AdS mismatch with the original fundamental radial modes. These source identities
retain a boundary port; they do not assert radiative extinction or physical
left-QNM identification of the auxiliary dual. -/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMSourceDensityDual
open D4BMCommonRadialSource D4BMJointSource D4BMModularCore D4BMHorizon
open D4BMGlobalAngularResponse D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Radial density factor dictated by the original complex-bilinear source transpose.
It is an auxiliary adjoint weight, not a redefinition of the literal source. -/
def dualWeight (x : ℝ) : ℂ := (1+(radialUnit x:ℂ))^(5 : ℕ)/(radialUnit x:ℂ)^(4 : ℕ)

/-- The original fixed-onset seed multiplied by the derived radial dual weight. -/
def dualSeed (s a : ℂ) (v x : ℝ) (J : ℂ) : ℂ := dualWeight x*seed s a v x J

/-- Separated profile of the formal transpose in the original radial measure.
The angular input is retained independently, as in `commonSource`. -/
def transposeProfile (lam : ℂ) (F LF : ℝ → ℂ) (x : ℝ) : ℂ :=
  (5*lam-6)/4*F x+(radialUnit x:ℂ)^(2 : ℕ)/8*
    ((4*lam+1)*(lam+2)*F x-(lam+4)*LF x)+
  (4*(radialUnit x:ℂ)-(radialUnit x:ℂ)^(2 : ℕ))/8*((7*lam-2)*F x-2*LF x)+
  (radialUnit x:ℂ)^(2 : ℕ)/8*((7*lam-2)*radialGenerator F x-2*radialGenerator LF x)

private theorem unit_ne_zero (x : Iio (0:ℝ)) : (radialUnit x.val:ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (radialUnit_bounds x.val x.property).1.ne'
private theorem unit_sub_one_ne_zero (x : Iio (0:ℝ)) : (radialUnit x.val:ℂ)-1 ≠ 0 := by
  exact_mod_cast sub_ne_zero.mpr (radialUnit_bounds x.val x.property).2.ne

/-- Exact integrating-factor law, in the original tortoise coordinate. -/
theorem dualWeight_hasDerivAt (x : Iio (0:ℝ)) :
    HasDerivAt dualWeight
      (((radialUnit x.val:ℂ)-1)*(1-4/(radialUnit x.val:ℂ))*dualWeight x.val) x.val := by
  have hu : HasDerivAt (fun y => (radialUnit y:ℂ)) ((radialUnit x.val:ℂ)^(2 : ℕ)-1) x.val := by
    simpa only [Complex.ofReal_sub,Complex.ofReal_pow,Complex.ofReal_one] using!
      (radialUnit_hasDerivAt x.val).ofReal_comp
  apply (((hu.const_add 1).pow 5).div (hu.pow 4) (pow_ne_zero _ (unit_ne_zero x))).congr_deriv
  simp only [dualWeight, Pi.pow_apply]
  field_simp [unit_ne_zero x]
  ring

private theorem seed_derivative (s a : ℂ) (v x : ℝ) (J : ℂ) :
    HasDerivAt (fun y => seed s a v y J)
      (2*s*((radialUnit x:ℂ)-1)*seed s a v x J) x := by
  apply (((sourceAmplitude_hasDerivAt s 0 a 1 x).mul_const
    (timeOnset (2*s) v)).mul_const J).congr_deriv
  dsimp only [seed,amplitudeRate]
  ring

private theorem generator_seed (s a : ℂ) (v : ℝ) (x : Iio (0:ℝ)) (J : ℂ) :
    radialGenerator (fun y => seed s a v y J) x.val=(2*s+3)*seed s a v x.val J := by
  rw [radialGenerator,(seed_derivative s a v x.val J).deriv]
  field_simp [unit_sub_one_ne_zero x]

private theorem generator_dualSeed (s a : ℂ) (v : ℝ) (x : Iio (0:ℝ)) (J : ℂ) :
    radialGenerator (fun y => dualSeed s a v y J) x.val=
      (2*s+4-4/(radialUnit x.val:ℂ))*dualSeed s a v x.val J := by
  have hd : HasDerivAt (fun y => dualSeed s a v y J)
      (((radialUnit x.val:ℂ)-1)*(1-4/(radialUnit x.val:ℂ))*dualWeight x.val*seed s a v x.val J+
        dualWeight x.val*(2*s*((radialUnit x.val:ℂ)-1)*seed s a v x.val J)) x.val :=
    (dualWeight_hasDerivAt x).mul (seed_derivative s a v x.val J)
  rw [radialGenerator,hd.deriv]
  dsimp only [dualSeed]
  field_simp [unit_ne_zero x,unit_sub_one_ne_zero x]
  ring

private def coefficient (lam delta u J LJ : ℂ) : ℂ :=
  (5*lam-6)/4*J+u^(2 : ℕ)/8*((4*lam+1)*(lam+2)*J-(lam+4)*LJ-
    (7*lam-2)*delta*J+2*delta*LJ)

private theorem source_profile (lam s a : ℂ) (v : ℝ) (x : Iio (0:ℝ)) (J LJ : ℂ) :
    commonSource lam (fun y => seed s a v y J) (fun y => seed s a v y LJ) x.val=
      seed s a v x.val 1*coefficient lam (2*s+3) (radialUnit x.val) J LJ := by
  rw [commonSource,generator_seed,generator_seed]
  dsimp only [seed,coefficient]
  ring

private theorem dual_profile (lam s a : ℂ) (v : ℝ) (x : Iio (0:ℝ)) (J LJ : ℂ) :
    transposeProfile lam (fun y => dualSeed (-s-3) a v y J)
      (fun y => dualSeed (-s-3) a v y LJ) x.val=
      dualSeed (-s-3) a v x.val 1*coefficient lam (2*s+3) (radialUnit x.val) J LJ := by
  rw [transposeProfile,generator_dualSeed,generator_dualSeed]
  dsimp only [dualSeed,seed,coefficient]
  field_simp [unit_ne_zero x]
  ring

private theorem opposite_rate (q : XiZeroCopy) (branch : Bool) :
    physicalRate q (!branch) = -physicalRate q branch-3 := by
  cases branch <;> simp only [physicalRate,Bool.not_false,Bool.not_true,Bool.false_eq_true,
    if_false,if_true] <;> ring

/-- The exact density-dual transpose reproduces the opposite literal source coefficient.
All amplitudes and onset factors are retained without division. The angular input is the
actual theta half-square Laplacian, including the full source gradient energy. -/
theorem densityDual_originalForcing (q : XiZeroCopy) (branch : Bool) (a b : ℂ)
    (v : ℝ) (x : Iio (0:ℝ)) (z : UpperHalfPlane) :
    let s := physicalRate q branch;
    let t := physicalRate q (!branch);
    let Q := fullSquarePotential q (coordinates z);
    let LQ := scalarLaplacian (fullSquarePotential q) (coordinates z);
    -2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)*seed s a v x.val 1*
        transposeProfile (scalarParameter q) (fun y => dualSeed t b v y Q)
          (fun y => dualSeed t b v y LQ) x.val =
      dualSeed t b v x.val 1*timeOriginalForcing q branch a (v-x.val) x.val (coordinates z) := by
  dsimp only
  rw [opposite_rate,dual_profile,timeOriginalForcing_common_source,source_profile]
  ring

/-- Exact density factor; it does not make either endpoint current zero. -/
theorem dualWeight_density (x : Iio (0:ℝ)) :
    (radialUnit x.val:ℂ)^(4 : ℕ)*(1+(radialUnit x.val:ℂ))*dualWeight x.val=
      (1+(radialUnit x.val:ℂ))^(6 : ℕ) := by
  unfold dualWeight
  field_simp [unit_ne_zero x]

private theorem seed_continuous (s a : ℂ) (v : ℝ) (J : ℂ) :
    Continuous (fun x => seed s a v x J) :=
  continuous_iff_continuousAt.mpr (fun x => (seed_derivative s a v x J).continuousAt)

/-- The source-derived dual retains an exact fourth-order AdS boundary coefficient. -/
theorem dualSeed_ads_residue (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (z : UpperHalfPlane) :
    Tendsto (fun x : ℝ => (radialUnit x:ℂ)^(4 : ℕ)*
      dualSeed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z)))
      (𝓝[<] 0) (𝓝 (a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        fullSquarePotential q (coordinates z))) := by
  have hu : Continuous (fun x : ℝ => (radialUnit x:ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr (fun x => (radialUnit_hasDerivAt x).continuousAt))
  have hc : Continuous (fun x : ℝ => (1+(radialUnit x:ℂ))^(5 : ℕ)*
      seed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z))) :=
    ((continuous_const.add hu).pow 5).mul
      (seed_continuous (physicalRate q branch) a v (fullSquarePotential q (coordinates z)))
  have h0 : Tendsto (fun x : ℝ => (1+(radialUnit x:ℂ))^(5 : ℕ)*
      seed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z)))
      (𝓝[<] 0) (𝓝 ((1+(radialUnit 0:ℂ))^(5 : ℕ)*
        seed (physicalRate q branch) a v 0 (fullSquarePotential q (coordinates z)))) :=
    hc.continuousAt.tendsto.mono_left inf_le_left
  have he : (fun x : ℝ => (radialUnit x:ℂ)^(4 : ℕ)*
      dualSeed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z)))
      =ᶠ[𝓝[<] 0] (fun x => (1+(radialUnit x:ℂ))^(5 : ℕ)*
        seed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hn := unit_ne_zero ⟨x,hx⟩
    dsimp only [dualSeed,dualWeight]
    field_simp [hn]
  simpa [radialUnit, seed, sourceAmplitude, power] using h0.congr' he.symm


private theorem seed_pair (s a b : ℂ) (v x : ℝ) (J H : ℂ) :
    (1+(radialUnit x:ℂ))^(6 : ℕ)*seed s a v x J*seed (-s-3) b v x H =
      a^(2 : ℕ)*b^(2 : ℕ)*(Real.smoothTransition v:ℂ)^(2 : ℕ)*Complex.exp (-6*(v:ℂ))*J*H := by
  have hn : ((1+radialUnit x:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (radialUnit_add_one_pos x).ne'
  have hp : power (2*s) (1+radialUnit x)*power (2*(-s-3)) (1+radialUnit x)=
      ((1+(radialUnit x:ℂ))^(6 : ℕ))⁻¹ := by
    unfold power
    rw [← Complex.cpow_add _ _ hn,
      show 2*s+2*(-s-3)=-(6:ℂ) by ring, Complex.cpow_neg, Complex.cpow_ofNat]
    push_cast
    rfl
  have he : Complex.exp (2*s*(v:ℂ))*Complex.exp (2*(-s-3)*(v:ℂ))=
      Complex.exp (-6*(v:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp only [seed,sourceAmplitude,timeOnset,zero_mul,Complex.exp_zero,one_mul,mul_one]
  calc
    _ = (1+(radialUnit x:ℂ))^(6 : ℕ)*
        (power (2*s) (1+radialUnit x)*power (2*(-s-3)) (1+radialUnit x))*
        a^(2 : ℕ)*b^(2 : ℕ)*(Real.smoothTransition v:ℂ)^(2 : ℕ)*
        (Complex.exp (2*s*(v:ℂ))*Complex.exp (2*(-s-3)*(v:ℂ)))*J*H := by ring
    _ = _ := by
      rw [hp,he,mul_inv_cancel₀ (pow_ne_zero 6 (by simpa only [Complex.ofReal_add,
        Complex.ofReal_one] using hn)),one_mul]

/-- The common source's angular `K` coefficient, with its Laplacian retained. -/
def sourceAngularK (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  ((7*scalarParameter q-2)*fullSquarePotential q (coordinates z)-
    2*scalarLaplacian (fullSquarePotential q) (coordinates z))/8

/-- The full spin-two polynomial applied to the literal theta half-square. -/
def retainedSpinTwo (q : XiZeroCopy) (z : UpperHalfPlane) : ℂ :=
  -scalarLaplacian (scalarLaplacian (fullSquarePotential q)) (coordinates z)+
    2*scalarLaplacian (fullSquarePotential q) (coordinates z)

/-- Original radial Green density tested against the derived dual spin-two seed.
This definition does not identify that auxiliary test with a physical left-QNM state. -/
def dualRadialFlux (q : XiZeroCopy) (branch : Bool) (a b : ℂ)
    (v x : ℝ) (z : UpperHalfPlane) : ℂ :=
  -(radialUnit x:ℂ)^(4 : ℕ)*(1+(radialUnit x:ℂ))*
    seed (physicalRate q branch) a v x (sourceAngularK q z)*
    dualSeed (physicalRate q (!branch)) b v x (retainedSpinTwo q z)/(z.im:ℂ)^(2 : ℕ)

/-- The density-dual radial flux is radius-independent at the unchanged common clock.
Its surviving endpoint value is explicit; conservation does not assert its vanishing. -/
theorem dualRadialFlux_exact (q : XiZeroCopy) (branch : Bool) (a b : ℂ)
    (v : ℝ) (x : Iio (0:ℝ)) (z : UpperHalfPlane) :
    dualRadialFlux q branch a b v x.val z =
      -a^(2 : ℕ)*b^(2 : ℕ)*(Real.smoothTransition v:ℂ)^(2 : ℕ)*Complex.exp (-6*(v:ℂ))*
        sourceAngularK q z*retainedSpinTwo q z/(z.im:ℂ)^(2 : ℕ) := by
  unfold dualRadialFlux dualSeed
  rw [opposite_rate]
  calc
    _ = -((radialUnit x.val:ℂ)^(4 : ℕ)*(1+(radialUnit x.val:ℂ))*dualWeight x.val*
        seed (physicalRate q branch) a v x.val (sourceAngularK q z)*
        seed (-physicalRate q branch-3) b v x.val (retainedSpinTwo q z))/(z.im:ℂ)^(2 : ℕ) := by ring
    _ = _ := by rw [dualWeight_density,seed_pair]; ring


private theorem fundamental_mode_value (q : XiZeroCopy) (side outer : Bool)
    (x : Iio (0:ℝ)) :
    tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q) x.val =
      power (physicalFundamentalFrequency q side/2) (horizonCoordinate x.val)*
        power (1/2) (1-horizonCoordinate x.val) := by
  have hf : physicalFundamentalFrequency q side=-3/2-Complex.I*physicalRadialFrequency q ∨
      physicalFundamentalFrequency q side=-3/2+Complex.I*physicalRadialFrequency q := by
    rw [physicalFundamentalFrequency_connection_root]
    cases side <;> simp
  cases outer
  · change horizon _ _ _ = _
    rw [horizon_eq_normalizable_fundamental _ _ (physicalFundamentalFrequency_strip q side).1
      hf (horizonCoordinate_interior x.val x.property)]
    exact normalizable_fundamental_value _ _ hf _
  · exact normalizable_fundamental_value _ _ hf _

/-- Both actual fundamental radial normalizations have the admitted zero AdS value. -/
theorem physicalFundamentalMode_ads (q : XiZeroCopy) (side outer : Bool) :
    Tendsto (tortoiseMode outer (physicalFundamentalFrequency q side) (physicalRadialFrequency q))
      (𝓝[<] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hz : Tendsto horizonCoordinate (𝓝[<] (0:ℝ)) (𝓝 (1:ℝ)) :=
    horizonCoordinate_tendsto_boundary.mono_right nhdsWithin_le_nhds
  have hr : Tendsto (fun x : ℝ => 1-horizonCoordinate x) (𝓝[<] (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [sub_self] using
      (show Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[<] (0:ℝ)) (𝓝 (1:ℝ)) from
        tendsto_const_nhds).sub hz
  have h := ((power_tendsto_one (physicalFundamentalFrequency q side/2)).comp hz).mul
    ((power_tendsto_zero (a := (1/2:ℂ)) (by norm_num)).comp hr)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (fundamental_mode_value q side outer ⟨x,hx⟩).symm

/-- Subtracting any constant-normalized actual fundamental radial mode leaves the
complete source-dual pole coefficient. The source and target Xi copies are independent. -/
theorem densityDual_physicalMode_ads_residue (q r : XiZeroCopy) (branch side outer : Bool)
    (a c : ℂ) (v : ℝ) (z : UpperHalfPlane) :
    Tendsto (fun x : ℝ => (radialUnit x:ℂ)^(4 : ℕ)*
      (dualSeed (physicalRate q branch) a v x (fullSquarePotential q (coordinates z))-
        c*tortoiseMode outer (physicalFundamentalFrequency r side) (physicalRadialFrequency r) x))
      (𝓝[<] 0) (𝓝 (a^(2 : ℕ)*timeOnset (2*physicalRate q branch) v*
        fullSquarePotential q (coordinates z))) := by
  have hu : Tendsto (fun x : ℝ => (radialUnit x:ℂ)) (𝓝[<] (0:ℝ)) (𝓝 (0:ℂ)) := by
    have h := ((radialUnit_hasDerivAt 0).continuousAt.tendsto.ofReal).mono_left
      (show 𝓝[<] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa [radialUnit] using h
  have hg := (hu.pow 4).mul ((physicalFundamentalMode_ads r side outer).const_mul c)
  have h := (dualSeed_ads_residue q branch a v z).sub hg
  simp only [zero_pow (by decide : 4 ≠ 0),zero_mul,sub_zero] at h
  apply h.congr'
  filter_upwards [] with x
  ring

end
end RHTower.D4BMSourceDensityDual
