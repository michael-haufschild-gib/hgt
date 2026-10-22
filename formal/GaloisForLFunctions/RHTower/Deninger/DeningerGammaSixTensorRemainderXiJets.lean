import GaloisForLFunctions.RHTower.MobiusThetaStrictTailXiJetRetention

/-!
# Xi jets in the complete Gamma-six tensor remainder

The existing product-measure Hilbert source is internally promoted before
spectral evaluation. Its complete leading-removed tensor has an absolutely
admitted two-variable Fourier--Laplace integral, with both cross terms,
Fourier coordinate normalization and forced half-density retained.

The diagonal multiplier tends to zero but is eventually nonzero. Every Xi
divisor retains its adjacent internal conormal pair; exact successor and
half-density normalization recover a nonzero top-jet limit.

This constructs no Sonin quotient comparison or fixed-reader agreement.
The source-forced normalization is singular and does not prove RH.
-/

open Complex Real MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

-- The physical coordinate is retained in both factor and product integrals.
def mobiusThetaL2FourierLaplaceIntegrand (f : MobiusThetaSourceL2) (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (((2 * Real.pi) * x : ℝ) : ℂ)) * f x

def mobiusThetaL2FourierLaplace (f : MobiusThetaSourceL2) (w : ℂ) : ℂ :=
  ∫ x : ℝ, mobiusThetaL2FourierLaplaceIntegrand f w x

theorem xiThetaInternalJetSourceL2_fourierLaplaceIntegrand_ae (k : ℕ) (w : ℂ) :
    mobiusThetaL2FourierLaplaceIntegrand (xiThetaInternalJetSourceL2 k) w =ᵐ[volume]
      fun x => (2 * Real.pi : ℂ) *
        thetaCuspFourierLaplaceJetIntegrand k w ((2 * Real.pi) * x) := by
  filter_upwards [(xiThetaInternalJetSchwartzSource k).coeFn_toLp (p := 2) (μ := volume)]
    with x hx
  dsimp [mobiusThetaL2FourierLaplaceIntegrand, xiThetaInternalJetSourceL2]
  rw [hx, xiThetaInternalJetSchwartzSource_apply, xiThetaSchwartzSource_apply]
  dsimp [thetaCuspFourierLaplaceJetIntegrand, thetaCuspFourierLaplaceIntegrand]
  push_cast
  ring_nf

theorem integrable_xiThetaInternalJetSourceL2_fourierLaplace
    (k : ℕ) {w : ℂ} (hw : |w.im| < 1) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand (xiThetaInternalJetSourceL2 k) w) := by
  have hi := ((integrable_thetaCuspFourierLaplaceJetIntegrand k hw).comp_mul_left'
    (by positivity : (2 * Real.pi) ≠ 0)).const_mul (2 * Real.pi : ℂ)
  exact hi.congr (xiThetaInternalJetSourceL2_fourierLaplaceIntegrand_ae k w).symm

theorem xiThetaInternalJetSourceL2_fourierLaplace
    (k : ℕ) {w : ℂ} (hw : |w.im| < 1) :
    mobiusThetaL2FourierLaplace (xiThetaInternalJetSourceL2 k) w =
      iteratedDeriv k XiC w := by
  rw [mobiusThetaL2FourierLaplace, integral_congr_ae
    (xiThetaInternalJetSourceL2_fourierLaplaceIntegrand_ae k w), integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left]
  rw [abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  rw [real_smul, ← mul_assoc]
  have hcancel : (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hcancel, one_mul]
  exact (iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k
    (abs_lt.mp hw)).symm

theorem integrable_mobiusThetaInternalJetStrictTailL2_fourierLaplace
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j) w) := by
  have hi := ((integrable_mobiusThetaInternalJetStrictTailFourierLaplaceIntegrand p m k hw hms).comp_mul_left' (by positivity : (2 * Real.pi) ≠ 0)).const_mul (2 * Real.pi : ℂ)
  apply hi.congr
  filter_upwards [mobiusThetaInternalJetStrictTailL2_ae_source p m k] with x hx
  dsimp [mobiusThetaL2FourierLaplaceIntegrand]
  rw [hx]
  ring

/-- Admission and evaluation are kept together when manipulating actual Hilbert sources. -/
theorem mobiusThetaL2FourierLaplace_smul_data
    (f : MobiusThetaSourceL2) (w c : ℂ)
    (hf : Integrable (mobiusThetaL2FourierLaplaceIntegrand f w)) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand (c • f) w) ∧
      mobiusThetaL2FourierLaplace (c • f) w = c * mobiusThetaL2FourierLaplace f w := by
  have hae : mobiusThetaL2FourierLaplaceIntegrand (c • f) w =ᵐ[volume]
      fun x => c * mobiusThetaL2FourierLaplaceIntegrand f w x := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    dsimp [mobiusThetaL2FourierLaplaceIntegrand]
    rw [hx]
    change _ * (c * f x) = _
    ring
  refine ⟨(hf.const_mul c).congr hae.symm, ?_⟩
  rw [mobiusThetaL2FourierLaplace, integral_congr_ae hae, integral_const_mul]
  rfl

theorem mobiusThetaL2FourierLaplace_add_data
    (f g : MobiusThetaSourceL2) (w : ℂ)
    (hf : Integrable (mobiusThetaL2FourierLaplaceIntegrand f w))
    (hg : Integrable (mobiusThetaL2FourierLaplaceIntegrand g w)) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand (f + g) w) ∧
      mobiusThetaL2FourierLaplace (f + g) w =
        mobiusThetaL2FourierLaplace f w + mobiusThetaL2FourierLaplace g w := by
  have hae : mobiusThetaL2FourierLaplaceIntegrand (f + g) w =ᵐ[volume]
      fun x => mobiusThetaL2FourierLaplaceIntegrand f w x +
        mobiusThetaL2FourierLaplaceIntegrand g w x := by
    filter_upwards [Lp.coeFn_add f g] with x hx
    change _ * (f + g : MobiusThetaSourceL2) x = _
    rw [hx]
    exact mul_add _ _ _
  refine ⟨(hf.add hg).congr hae.symm, ?_⟩
  rw [mobiusThetaL2FourierLaplace, integral_congr_ae hae, integral_add hf hg]
  rfl

/-- A genuine product-measure integral on the existing tensor Hilbert space. -/
def deningerGammaSixTensorFourierLaplaceIntegrand
    (F : DeningerGammaSixTensorSourceL2) (w z : ℂ) (xy : ℝ × ℝ) : ℂ :=
  (Complex.exp (-I * w * (((2 * Real.pi) * xy.1 : ℝ) : ℂ)) *
    Complex.exp (-I * z * (((2 * Real.pi) * xy.2 : ℝ) : ℂ))) * F xy

def deningerGammaSixTensorFourierLaplace
    (F : DeningerGammaSixTensorSourceL2) (w z : ℂ) : ℂ :=
  ∫ xy : ℝ × ℝ, deningerGammaSixTensorFourierLaplaceIntegrand F w z xy
    ∂(volume.prod volume)

theorem deningerGammaSixTensorFourierLaplace_product_data
    (f g : MobiusThetaSourceL2) (w z : ℂ)
    (hf : Integrable (mobiusThetaL2FourierLaplaceIntegrand f w))
    (hg : Integrable (mobiusThetaL2FourierLaplaceIntegrand g z)) :
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct f g) w z)
        (volume.prod volume) ∧
      deningerGammaSixTensorFourierLaplace (l2SeparatedProduct f g) w z =
        mobiusThetaL2FourierLaplace f w * mobiusThetaL2FourierLaplace g z := by
  have hae : deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct f g) w z
      =ᵐ[volume.prod volume] fun xy =>
        mobiusThetaL2FourierLaplaceIntegrand f w xy.1 *
          mobiusThetaL2FourierLaplaceIntegrand g z xy.2 := by
    filter_upwards [l2SeparatedProduct_ae f g] with xy hxy
    dsimp [deningerGammaSixTensorFourierLaplaceIntegrand,
      mobiusThetaL2FourierLaplaceIntegrand]
    rw [hxy]
    dsimp [l2SeparatedFun]
    ring
  refine ⟨(hf.mul_prod hg).congr hae.symm, ?_⟩
  rw [deningerGammaSixTensorFourierLaplace, integral_congr_ae hae, integral_prod_mul]
  rfl

theorem deningerGammaSixTensorFourierLaplace_sub_data
    (F G : DeningerGammaSixTensorSourceL2) (w z : ℂ)
    (hF : Integrable (deningerGammaSixTensorFourierLaplaceIntegrand F w z) (volume.prod volume))
    (hG : Integrable (deningerGammaSixTensorFourierLaplaceIntegrand G w z) (volume.prod volume)) :
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand (F - G) w z)
        (volume.prod volume) ∧
      deningerGammaSixTensorFourierLaplace (F - G) w z =
        deningerGammaSixTensorFourierLaplace F w z -
          deningerGammaSixTensorFourierLaplace G w z := by
  have hae : deningerGammaSixTensorFourierLaplaceIntegrand (F - G) w z
      =ᵐ[volume.prod volume] fun xy =>
        deningerGammaSixTensorFourierLaplaceIntegrand F w z xy -
          deningerGammaSixTensorFourierLaplaceIntegrand G w z xy := by
    filter_upwards [Lp.coeFn_sub F G] with xy hxy
    change _ * (F - G : DeningerGammaSixTensorSourceL2) xy = _
    rw [hxy]
    exact mul_sub _ _ _
  refine ⟨(hF.sub hG).congr hae.symm, ?_⟩
  rw [deningerGammaSixTensorFourierLaplace, integral_congr_ae hae, integral_sub hF hG]
  rfl

/-- Internal promotion occurs in each source factor before a spectral point is selected. -/
def deningerGammaSixInternalJetSource (k : ℕ) (m : MobiusHonestDepth) : MobiusThetaSourceL2 :=
  (deningerGammaSixHalfWeight m : ℂ) •
    (xiThetaInternalJetSourceL2 k +
      ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 6 m j)

def deningerGammaSixInternalJetLeading (k : ℕ) (m : MobiusHonestDepth) : MobiusThetaSourceL2 :=
  (deningerGammaSixHalfWeight m : ℂ) • xiThetaInternalJetSourceL2 k

def deningerGammaSixInternalJetTensorRemainder
    (k l : ℕ) (m : MobiusHonestDepth) : DeningerGammaSixTensorSourceL2 :=
  l2SeparatedProduct (deningerGammaSixInternalJetSource k m)
      (deningerGammaSixInternalJetSource l m) -
    l2SeparatedProduct (deningerGammaSixInternalJetLeading k m)
      (deningerGammaSixInternalJetLeading l m)

theorem deningerGammaSixInternalJetSource_zero (m : MobiusHonestDepth) :
    deningerGammaSixInternalJetSource 0 m = deningerGammaSixCountertransportedSource m := by
  have hterm (j : ℕ) : mobiusThetaInternalJetPrimeNormalTailTerm 0 6 m j =
      mobiusThetaPrimeNormalTailTerm 6 m j := by
    rw [mobiusThetaInternalJetPrimeNormalTailTerm, xiThetaInternalJetSourceL2_zero]
    rfl
  rw [deningerGammaSixInternalJetSource, xiThetaInternalJetSourceL2_zero]
  simp_rw [hterm]
  rw [deningerGammaSixCountertransportedSource_eq_leading_add_tail, smul_add]
  rfl

theorem deningerGammaSixInternalJetTensorRemainder_zero (m : MobiusHonestDepth) :
    deningerGammaSixInternalJetTensorRemainder 0 0 m =
      deningerGammaSixSourceTensorRemainder m := by
  rw [deningerGammaSixInternalJetTensorRemainder, deningerGammaSixInternalJetSource_zero]
  simp only [deningerGammaSixInternalJetLeading, xiThetaInternalJetSourceL2_zero]
  rfl

theorem deningerGammaSixInternalJetLeading_fourierLaplace_data
    (k : ℕ) (m : MobiusHonestDepth) {w : ℂ} (hw : |w.im| < 1) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand (deningerGammaSixInternalJetLeading k m) w) ∧
      mobiusThetaL2FourierLaplace (deningerGammaSixInternalJetLeading k m) w =
        (deningerGammaSixHalfWeight m : ℂ) * iteratedDeriv k XiC w := by
  have h := mobiusThetaL2FourierLaplace_smul_data (xiThetaInternalJetSourceL2 k) w
    (deningerGammaSixHalfWeight m : ℂ) (integrable_xiThetaInternalJetSourceL2_fourierLaplace k hw)
  simpa only [deningerGammaSixInternalJetLeading, xiThetaInternalJetSourceL2_fourierLaplace k hw] using h

theorem deningerGammaSixInternalJetSource_fourierLaplace_data
    (k : ℕ) (m : MobiusHonestDepth) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Integrable (mobiusThetaL2FourierLaplaceIntegrand (deningerGammaSixInternalJetSource k m) w) ∧
      mobiusThetaL2FourierLaplace (deningerGammaSixInternalJetSource k m) w =
        (deningerGammaSixHalfWeight m : ℂ) * mobiusThetaPrimeNormalResidualMultiplier 6 m w *
          iteratedDeriv k XiC w := by
  have hadd := mobiusThetaL2FourierLaplace_add_data (xiThetaInternalJetSourceL2 k)
    (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 6 m j) w
    (integrable_xiThetaInternalJetSourceL2_fourierLaplace k hw)
    (integrable_mobiusThetaInternalJetStrictTailL2_fourierLaplace ⟨6, by omega⟩ m k hw hms)
  have h := mobiusThetaL2FourierLaplace_smul_data _ w (deningerGammaSixHalfWeight m : ℂ) hadd.1
  refine ⟨h.1, ?_⟩
  rw [deningerGammaSixInternalJetSource, h.2, hadd.2, xiThetaInternalJetSourceL2_fourierLaplace k hw]
  have htail := mobiusThetaInternalJetStrictTailL2FourierLaplace_landing ⟨6, by omega⟩ m k hw hms
  change mobiusThetaL2FourierLaplace _ w = _ at htail
  rw [htail, mobiusThetaStrictTailMultiplier, moebius_six]
  push_cast
  ring

/-- Both spectral variables and both internal jet orders are retained in the actual tensor integral. -/
theorem deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data
    (k l : ℕ) (m : MobiusHonestDepth) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hmw : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand
      (deningerGammaSixInternalJetTensorRemainder k l m) w z) (volume.prod volume) ∧
    deningerGammaSixTensorFourierLaplace
        (deningerGammaSixInternalJetTensorRemainder k l m) w z =
      (deningerGammaSixHalfWeight m : ℂ) ^ (2 : ℕ) *
        (mobiusThetaPrimeNormalResidualMultiplier 6 m w *
          mobiusThetaPrimeNormalResidualMultiplier 6 m z - 1) *
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) := by
  have hS := deningerGammaSixInternalJetSource_fourierLaplace_data k m hw hmw
  have hT := deningerGammaSixInternalJetSource_fourierLaplace_data l m hz hmz
  have hH := deningerGammaSixInternalJetLeading_fourierLaplace_data k m hw
  have hJ := deningerGammaSixInternalJetLeading_fourierLaplace_data l m hz
  have hprod := deningerGammaSixTensorFourierLaplace_product_data _ _ w z hS.1 hT.1
  have hhead := deningerGammaSixTensorFourierLaplace_product_data _ _ w z hH.1 hJ.1
  have hsub := deningerGammaSixTensorFourierLaplace_sub_data _ _ w z hprod.1 hhead.1
  refine ⟨hsub.1, ?_⟩
  rw [deningerGammaSixInternalJetTensorRemainder, hsub.2, hprod.2, hhead.2,
    hS.2, hT.2, hH.2, hJ.2]
  ring

/-- The three contributions in the literal remainder are separately absolutely admitted. -/
theorem deningerGammaSixInternalJetTensorRemainder_cross_integrable
    (k l : ℕ) (m : MobiusHonestDepth) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hmw : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) :
    let H := deningerGammaSixInternalJetLeading k m
    let J := deningerGammaSixInternalJetLeading l m
    let T := (deningerGammaSixHalfWeight m : ℂ) •
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 6 m j)
    let U := (deningerGammaSixHalfWeight m : ℂ) •
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm l 6 m j)
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct H U) w z)
        (volume.prod volume) ∧
      Integrable (deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct T J) w z)
        (volume.prod volume) ∧
      Integrable (deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct T U) w z)
        (volume.prod volume) := by
  dsimp only
  have hH := (deningerGammaSixInternalJetLeading_fourierLaplace_data k m hw).1
  have hJ := (deningerGammaSixInternalJetLeading_fourierLaplace_data l m hz).1
  have hT := (mobiusThetaL2FourierLaplace_smul_data _ w (deningerGammaSixHalfWeight m : ℂ)
    (integrable_mobiusThetaInternalJetStrictTailL2_fourierLaplace ⟨6, by omega⟩ m k hw hmw)).1
  have hU := (mobiusThetaL2FourierLaplace_smul_data _ z (deningerGammaSixHalfWeight m : ℂ)
    (integrable_mobiusThetaInternalJetStrictTailL2_fourierLaplace ⟨6, by omega⟩ m l hz hmz)).1
  exact ⟨(deningerGammaSixTensorFourierLaplace_product_data _ _ w z hH hU).1,
    (deningerGammaSixTensorFourierLaplace_product_data _ _ w z hT hJ).1,
    (deningerGammaSixTensorFourierLaplace_product_data _ _ w z hT hU).1⟩

/-- The exact two-variable multiplier of the complete tensor remainder. -/
def deningerGammaSixTensorRemainderMultiplier (m : ℕ) (w z : ℂ) : ℂ :=
  mobiusThetaPrimeNormalResidualMultiplier 6 m w *
    mobiusThetaPrimeNormalResidualMultiplier 6 m z - 1

theorem tendsto_mobiusThetaPrimeNormalResidualMultiplier_six
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun m : ℕ => mobiusThetaPrimeNormalResidualMultiplier 6 m w) atTop (nhds 1) := by
  simpa only [moebius_six, Int.cast_one] using
    (tendsto_mobiusThetaPrimeNormalResidualMultiplier (by omega : 0 < 6) hw)

theorem deningerGammaSixTensorRemainderMultiplier_diagonal (m : ℕ) (w : ℂ) :
    deningerGammaSixTensorRemainderMultiplier m w w =
      mobiusThetaStrictTailMultiplier 6 m w *
        (mobiusThetaPrimeNormalResidualMultiplier 6 m w + 1) := by
  unfold deningerGammaSixTensorRemainderMultiplier mobiusThetaStrictTailMultiplier
  rw [moebius_six]
  push_cast
  ring

theorem tendsto_deningerGammaSixTensorRemainderMultiplier_zero
    {w z : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (hz : 0 < (mobiusThetaCenteredParameter z).re) :
    Tendsto (fun m => deningerGammaSixTensorRemainderMultiplier m w z) atTop (nhds 0) := by
  simpa only [deningerGammaSixTensorRemainderMultiplier, one_mul, sub_self] using
    ((tendsto_mobiusThetaPrimeNormalResidualMultiplier_six hw).mul
      (tendsto_mobiusThetaPrimeNormalResidualMultiplier_six hz)).sub_const 1

/-- Keeping both cross terms makes the leading-removed tensor multiplier eventually nonzero. -/
theorem eventually_deningerGammaSixTensorRemainderMultiplier_diagonal_ne_zero
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ m : ℕ in atTop, deningerGammaSixTensorRemainderMultiplier m w w ≠ 0 := by
  have hplus := ((tendsto_mobiusThetaPrimeNormalResidualMultiplier_six hw).add_const 1).eventually_ne (by norm_num : (1 : ℂ) + 1 ≠ 0)
  filter_upwards [eventually_mobiusThetaStrictTailMultiplier_ne_zero ⟨6, by omega⟩ hw,
    hplus] with m hm hp
  rw [deningerGammaSixTensorRemainderMultiplier_diagonal]
  exact mul_ne_zero hm hp

theorem tendsto_deningerGammaSixTensorRemainderMultiplier_normalized
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun m : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ m (mobiusThetaCenteredParameter w) *
        deningerGammaSixTensorRemainderMultiplier m w w) atTop
      (nhds (2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ)))) := by
  have ht := (tendsto_mobiusThetaStrictTailMultiplier_normalized ⟨6, by omega⟩ hw).mul
    ((tendsto_mobiusThetaPrimeNormalResidualMultiplier_six hw).add_const 1)
  convert ht using 1
  · funext m
    rw [deningerGammaSixTensorRemainderMultiplier_diagonal]
    exact (mul_assoc _ _ _).symm
  · congr 1
    ring

def deningerGammaSixInternalJetTensorConormalPair
    (k l : ℕ) (m : MobiusHonestDepth) (w : ℂ) : ℂ × ℂ :=
  (deningerGammaSixTensorFourierLaplace (deningerGammaSixInternalJetTensorRemainder k l m) w w,
    deningerGammaSixTensorFourierLaplace (deningerGammaSixInternalJetTensorRemainder (k + 1) l m) w w)

/-- The actual complete tensor remainder retains every divisor's adjacent internal conormal pair. -/
theorem eventually_deningerGammaSixInternalJetTensorConormalPair_at_divisor
    (rho : XiDivisorSupport) :
    ∀ᶠ n : ℕ in atTop,
      let m : MobiusHonestDepth := ⟨n + 3, by omega⟩
      let w := xiSpectralPointSupport rho
      let q := xiSupportMultiplicity rho
      let c := (deningerGammaSixHalfWeight m : ℂ) ^ (2 : ℕ) *
        deningerGammaSixTensorRemainderMultiplier m w w * (iteratedDeriv q XiC w) ^ (2 : ℕ)
      deningerGammaSixInternalJetTensorConormalPair (q - 1) q m w = (0, c) ∧ c ≠ 0 := by
  have hre : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hd := (tendsto_add_atTop_nat 3).eventually
    (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hre)
  have hn := (tendsto_add_atTop_nat 3).eventually
    (eventually_deningerGammaSixTensorRemainderMultiplier_diagonal_ne_zero hre)
  filter_upwards [hd, hn] with n hm hne
  dsimp only
  have hw := abs_im_xiSpectralPointSupport_lt_one rho
  have hpos := xiSupportMultiplicity_pos rho
  have hpred : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho := Nat.sub_lt hpos (by omega)
  have hs : xiSupportMultiplicity rho - 1 + 1 = xiSupportMultiplicity rho := by omega
  have hzero := iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hpred
  have hweight : (deningerGammaSixHalfWeight ⟨n + 3, by omega⟩ : ℂ) ≠ 0 := by
    exact_mod_cast (deningerGammaSixHalfWeight_pos ⟨n + 3, by omega⟩).ne'
  constructor
  · rw [deningerGammaSixInternalJetTensorConormalPair,
      (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data _ _
        ⟨n + 3, by omega⟩ hw hw hm.2 hm.2).2,
      hs, (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data _ _
        ⟨n + 3, by omega⟩ hw hw hm.2 hm.2).2, hzero, zero_mul, mul_zero]
    simp only [deningerGammaSixTensorRemainderMultiplier, pow_two]
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hweight) hne)
      (pow_ne_zero _ (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))

/-- Restoring both the exact half-density and successor scale recovers a nonzero jet coefficient. -/
theorem tendsto_deningerGammaSixInternalJetTensorRemainder_fourierLaplace_normalized
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hre : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun n : ℕ =>
      let m : MobiusHonestDepth := ⟨n + 3, by omega⟩
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ m (mobiusThetaCenteredParameter w) *
        (((deningerGammaSixHalfWeight m : ℂ) ^ (2 : ℕ))⁻¹ *
          deningerGammaSixTensorFourierLaplace
            (deningerGammaSixInternalJetTensorRemainder k l m) w w)) atTop
      (nhds ((2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w))) := by
  have ht := ((tendsto_deningerGammaSixTensorRemainderMultiplier_normalized hre).comp
    (tendsto_add_atTop_nat 3)).mul_const (iteratedDeriv k XiC w * iteratedDeriv l XiC w)
  apply ht.congr'
  have hd := (tendsto_add_atTop_nat 3).eventually
    (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hre)
  filter_upwards [hd] with n hm
  dsimp only
  rw [(deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l
    ⟨n + 3, by omega⟩ hw hw hm.2 hm.2).2]
  have hweight : (deningerGammaSixHalfWeight ⟨n + 3, by omega⟩ : ℂ) ≠ 0 := by
    exact_mod_cast (deningerGammaSixHalfWeight_pos ⟨n + 3, by omega⟩).ne'
  rw [mul_assoc ((deningerGammaSixHalfWeight ⟨n + 3, by omega⟩ : ℂ) ^ (2 : ℕ)),
    ← mul_assoc (((deningerGammaSixHalfWeight ⟨n + 3, by omega⟩ : ℂ) ^ (2 : ℕ))⁻¹),
    inv_mul_cancel₀ (pow_ne_zero 2 hweight), one_mul]
  exact mul_assoc _ _ _

theorem deningerGammaSixInternalJetTensorRemainder_divisor_normalized_limit_ne_zero
    (rho : XiDivisorSupport) :
    (2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
      (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
        iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) ≠ 0 := by
  have hmu : (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast moebius_mobiusSuccessor_ne_zero 6
  exact mul_ne_zero (mul_ne_zero (by norm_num) hmu)
    (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))

end
end RHTower
