import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixFixedDilationTailReader
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualFourierCoefficient

/-!
# Complete integrand admission and the original fixed-six reader

The complete internal-jet tensor remainder has a summable integrated-norm
majorant after a source-selected depth cutoff. The bound retains both cross
terms, the double arithmetic tail, the physical Jacobian, shell multiplicity,
and the original column flattening. It justifies summing the actual integrands
before evaluating their complete Fourier--Laplace integral.

Every positive spectral real part admits all sufficiently late original
cutoffs. Their actual integral operator has the same normalized fixed-six
boundary limit as the source shell sum. Every Xi divisor retains its original
spectral point, multiplicity, and adjacent zero/nonzero internal-jet pair;
finite diagonal repairs preserve the top response.

No Sonin/Burnol comparison, joint regulator--depth limit, finite-rank repair
claim, or Riemann Hypothesis is asserted.
-/

open Complex Real MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section


/-- Absolute mass of every strict arithmetic coefficient, before cancellation. -/
def mobiusThetaStrictSpectralTailMass (p m : ℕ) (w : ℂ) : ℝ :=
  ∑' j : ℕ, ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖

theorem mobiusThetaStrictSpectralTailMass_nonneg (p m : ℕ) (w : ℂ) :
    0 ≤ mobiusThetaStrictSpectralTailMass p m w := tsum_nonneg (fun _ => norm_nonneg _)

theorem mobiusThetaStrictSpectralTailMass_le_depthRate
    {p m : ℕ} (hp : 0 < p) {w : ℂ}
    (he : (3 / 2 : ℝ) ≤ (m : ℝ) * (mobiusThetaCenteredParameter w).re) :
    mobiusThetaStrictSpectralTailMass p m w ≤
      mobiusThetaSpectralTailConstant p * mobiusThetaSpectralTailDepthRate p m w := by
  have hmajor := (summable_mobiusThetaPrimeNormalSpectralTailMajorant p).mul_left
    (mobiusThetaSpectralTailDepthRate p m w)
  have hs : Summable (fun j : ℕ => ‖mobiusThetaPrimeNormalSpectralTailCoefficient p m w j‖) :=
    hmajor.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_depthRate hp he j)
  calc
    _ ≤ ∑' j : ℕ, mobiusThetaSpectralTailDepthRate p m w *
        mobiusThetaPrimeNormalSpectralTailMajorant p j :=
      hs.tsum_le_tsum (fun j => norm_mobiusThetaPrimeNormalSpectralTailCoefficient_le_depthRate hp he j) hmajor
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

theorem summable_mobiusThetaStrictSpectralTailMass_depth
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Summable (fun m : ℕ => mobiusThetaStrictSpectralTailMass p m w) := by
  have hs := (summable_mobiusThetaSpectralTailDepthRate hp hw).mul_left
    (mobiusThetaSpectralTailConstant p)
  apply hs.of_norm_bounded_eventually_nat
  have he := (tendsto_natCast_atTop_atTop.atTop_mul_const hw).eventually_ge_atTop (3 / 2 : ℝ)
  filter_upwards [he] with m hm
  rw [Real.norm_of_nonneg (mobiusThetaStrictSpectralTailMass_nonneg p m w)]
  exact mobiusThetaStrictSpectralTailMass_le_depthRate hp hm

/-- Original Fourier--Laplace jet norm, with no Xi-value cancellation. -/
def xiThetaInternalJetSpectralMass (k : ℕ) (w : ℂ) : ℝ :=
  ∫ x : ℝ, ‖thetaCuspFourierLaplaceJetIntegrand k w x‖

theorem xiThetaInternalJetSpectralMass_nonneg (k : ℕ) (w : ℂ) :
    0 ≤ xiThetaInternalJetSpectralMass k w := integral_nonneg (fun _ => norm_nonneg _)

/-- The complete strict source is controlled before its integral is evaluated. -/
theorem integral_norm_mobiusThetaInternalJetStrictTail_le
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    (∫ x : ℝ, ‖Complex.exp (-I * w * (x : ℂ)) *
      mobiusThetaInternalJetStrictTailSource k p m x‖) ≤
        mobiusThetaStrictSpectralTailMass p m w * xiThetaInternalJetSpectralMass k w := by
  have hp : 0 < (p : ℕ) := lt_of_lt_of_le Nat.zero_lt_one p.property
  have hm : (m : ℕ) ≠ 0 := by have := m.property; omega
  have hs : Summable (fun j : ℕ => ∫ x : ℝ,
      ‖mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w (j + 1) x‖) :=
    (summable_nat_add_iff 1).2
      (summable_integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp hm k hms)
  have hb := GaloisForLFunctions.HTGeometry.integral_norm_tsum_le_tsum_integral_norm
    (fun j => integrable_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp k m hw (j + 1)) hs
  have he : (fun x : ℝ => Complex.exp (-I * w * (x : ℂ)) *
      mobiusThetaInternalJetStrictTailSource k p m x) =
      fun x => ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w (j + 1) x := by
    funext x
    rw [mobiusThetaInternalJetStrictTailSource, ← tsum_mul_left]
    rfl
  simp_rw [congrFun he]
  simp_rw [integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp,
    mobiusThetaPrimeNormalResidualSpectralCoefficient_succ] at hb
  simpa only [tsum_mul_right, mobiusThetaStrictSpectralTailMass,
    xiThetaInternalJetSpectralMass] using hb

/-- The physical coordinate Jacobian exactly cancels its source normalization. -/
theorem integral_norm_physical_fourier_scaling (F : ℝ → ℂ) :
    (∫ x : ℝ, ‖(2 * Real.pi : ℂ) * F ((2 * Real.pi) * x)‖) =
      ∫ x : ℝ, ‖F x‖ := by
  simp_rw [norm_mul (2 * Real.pi : ℂ)]
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left (fun x : ℝ => ‖F x‖) (2 * Real.pi)]
  rw [abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- The leading source norm in its actual physical Hilbert representative. -/
theorem integral_norm_xiThetaInternalJetSourceL2_fourierLaplace (k : ℕ) (w : ℂ) :
    (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand (xiThetaInternalJetSourceL2 k) w x‖) =
      xiThetaInternalJetSpectralMass k w := by
  rw [integral_congr_ae ((xiThetaInternalJetSourceL2_fourierLaplaceIntegrand_ae k w).mono (fun _ h => congrArg norm h)),
    integral_norm_physical_fourier_scaling]
  rfl

/-- The full Hilbert tail obeys the same uncancelled integrated-norm bound. -/
theorem integral_norm_mobiusThetaInternalJetStrictTailL2_le
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j) w x‖) ≤
      mobiusThetaStrictSpectralTailMass p m w * xiThetaInternalJetSpectralMass k w := by
  have hae : mobiusThetaL2FourierLaplaceIntegrand
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j) w =ᵐ[volume]
      fun x : ℝ => (2 * Real.pi : ℂ) *
        (Complex.exp (-I * w * (((2 * Real.pi) * x : ℝ) : ℂ)) *
          mobiusThetaInternalJetStrictTailSource k p m ((2 * Real.pi) * x)) := by
    filter_upwards [mobiusThetaInternalJetStrictTailL2_ae_source p m k] with x hx
    dsimp [mobiusThetaL2FourierLaplaceIntegrand]
    rw [hx]
    ring
  rw [integral_congr_ae (hae.mono (fun _ h => congrArg norm h)),
    integral_norm_physical_fourier_scaling (fun x : ℝ => Complex.exp (-I * w * (x : ℂ)) *
      mobiusThetaInternalJetStrictTailSource k p m x)]
  exact integral_norm_mobiusThetaInternalJetStrictTail_le p m k hw hms

/-- Integrated norm of a physically scaled source, retaining its actual representative. -/
theorem integral_norm_mobiusThetaL2FourierLaplace_smul
    (f : MobiusThetaSourceL2) (w c : ℂ) :
    (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand (c • f) w x‖) =
      ‖c‖ * ∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand f w x‖ := by
  have hae : mobiusThetaL2FourierLaplaceIntegrand (c • f) w =ᵐ[volume]
      fun x => c * mobiusThetaL2FourierLaplaceIntegrand f w x := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    dsimp [mobiusThetaL2FourierLaplaceIntegrand]
    rw [hx]
    change _ * (c * f x) = _
    ring
  rw [integral_congr_ae (hae.mono (fun _ h => congrArg norm h))]
  simp_rw [norm_mul]
  exact integral_const_mul _ _

/-- Exact integrated tensor norm in the original product measure. -/
theorem integral_norm_deningerGammaSixTensorFourierLaplace_product
    (f g : MobiusThetaSourceL2) (w z : ℂ) :
    (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand
      (l2SeparatedProduct f g) w z xy‖ ∂(volume.prod volume)) =
      (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand f w x‖) *
        (∫ y : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand g z y‖) := by
  have hae : deningerGammaSixTensorFourierLaplaceIntegrand (l2SeparatedProduct f g) w z
      =ᵐ[volume.prod volume] fun xy =>
        mobiusThetaL2FourierLaplaceIntegrand f w xy.1 *
          mobiusThetaL2FourierLaplaceIntegrand g z xy.2 := by
    filter_upwards [l2SeparatedProduct_ae f g] with xy hxy
    dsimp [deningerGammaSixTensorFourierLaplaceIntegrand, mobiusThetaL2FourierLaplaceIntegrand]
    rw [hxy]
    dsimp [l2SeparatedFun]
    ring
  rw [integral_congr_ae (hae.mono (fun _ h => congrArg norm h))]
  simp_rw [norm_mul]
  exact integral_prod_mul (fun x : ℝ => ‖mobiusThetaL2FourierLaplaceIntegrand f w x‖)
    (fun y : ℝ => ‖mobiusThetaL2FourierLaplaceIntegrand g z y‖)

/-- Triangle control of all three admitted tensor contributions. -/
theorem integral_norm_deningerGammaSixTensor_three_sum_le
    (F G H : DeningerGammaSixTensorSourceL2) (w z : ℂ)
    (hF : Integrable (deningerGammaSixTensorFourierLaplaceIntegrand F w z) (volume.prod volume))
    (hG : Integrable (deningerGammaSixTensorFourierLaplaceIntegrand G w z) (volume.prod volume))
    (hH : Integrable (deningerGammaSixTensorFourierLaplaceIntegrand H w z) (volume.prod volume)) :
    (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand (F + G + H) w z xy‖
      ∂(volume.prod volume)) ≤
      (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand F w z xy‖ ∂(volume.prod volume)) +
      (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand G w z xy‖ ∂(volume.prod volume)) +
      (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand H w z xy‖ ∂(volume.prod volume)) := by
  have hae : deningerGammaSixTensorFourierLaplaceIntegrand (F + G + H) w z
      =ᵐ[volume.prod volume] fun xy =>
        deningerGammaSixTensorFourierLaplaceIntegrand F w z xy +
        deningerGammaSixTensorFourierLaplaceIntegrand G w z xy +
        deningerGammaSixTensorFourierLaplaceIntegrand H w z xy := by
    filter_upwards [Lp.coeFn_add (F + G) H, Lp.coeFn_add F G] with xy h1 h2
    dsimp only [deningerGammaSixTensorFourierLaplaceIntegrand]
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2]
    ring
  rw [integral_congr_ae (hae.mono (fun _ h => congrArg norm h))]
  calc
    _ ≤ ∫ xy : ℝ × ℝ,
        ‖deningerGammaSixTensorFourierLaplaceIntegrand F w z xy‖ +
        ‖deningerGammaSixTensorFourierLaplaceIntegrand G w z xy‖ +
        ‖deningerGammaSixTensorFourierLaplaceIntegrand H w z xy‖ ∂(volume.prod volume) := by
      apply integral_mono ((hF.add hG).add hH).norm ((hF.norm.add hG.norm).add hH.norm)
      intro xy
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by
      have hfg := integral_add hF.norm hG.norm
      have hall := integral_add (hF.norm.add hG.norm) hH.norm
      simp only [Pi.add_apply] at hall
      exact hall.trans (by rw [hfg])

def deningerGammaSixInternalJetTail (k : ℕ) (m : MobiusHonestDepth) : MobiusThetaSourceL2 :=
  (deningerGammaSixHalfWeight m : ℂ) •
    (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k 6 m j)

theorem deningerGammaSixInternalJetSource_eq_leading_add_tail (k : ℕ) (m : MobiusHonestDepth) :
    deningerGammaSixInternalJetSource k m =
      deningerGammaSixInternalJetLeading k m + deningerGammaSixInternalJetTail k m := by
  rw [deningerGammaSixInternalJetSource, smul_add]
  rfl

/-- The internal promotion preserves the literal three-term tensor decomposition. -/
theorem deningerGammaSixInternalJetTensorRemainder_eq_three_terms (k l : ℕ) (m : MobiusHonestDepth) :
    deningerGammaSixInternalJetTensorRemainder k l m =
      l2SeparatedProduct (deningerGammaSixInternalJetLeading k m) (deningerGammaSixInternalJetTail l m) +
      l2SeparatedProduct (deningerGammaSixInternalJetTail k m) (deningerGammaSixInternalJetLeading l m) +
      l2SeparatedProduct (deningerGammaSixInternalJetTail k m) (deningerGammaSixInternalJetTail l m) := by
  rw [deningerGammaSixInternalJetTensorRemainder,
    deningerGammaSixInternalJetSource_eq_leading_add_tail,
    deningerGammaSixInternalJetSource_eq_leading_add_tail]
  change (l2SeparatedProductContinuousBilinear (_ + _)) (_ + _) -
    l2SeparatedProduct _ _ = _
  simp only [map_add, add_apply, l2SeparatedProductContinuousBilinear_apply]
  abel

/-- Full uncancelled depth majorant, including both cross terms and the double tail. -/
def deningerGammaSixTensorRemainderNormMajorant (k l m : ℕ) (w z : ℂ) : ℝ :=
  xiThetaInternalJetSpectralMass k w * xiThetaInternalJetSpectralMass l z *
    (mobiusThetaStrictSpectralTailMass 6 m w + mobiusThetaStrictSpectralTailMass 6 m z +
      mobiusThetaStrictSpectralTailMass 6 m w * mobiusThetaStrictSpectralTailMass 6 m z)

theorem deningerGammaSixTensorRemainderNormMajorant_nonneg (k l m : ℕ) (w z : ℂ) :
    0 ≤ deningerGammaSixTensorRemainderNormMajorant k l m w z := by
  unfold deningerGammaSixTensorRemainderNormMajorant
  exact mul_nonneg (mul_nonneg (xiThetaInternalJetSpectralMass_nonneg k w)
    (xiThetaInternalJetSpectralMass_nonneg l z))
    (add_nonneg (add_nonneg (mobiusThetaStrictSpectralTailMass_nonneg 6 m w)
      (mobiusThetaStrictSpectralTailMass_nonneg 6 m z))
      (mul_nonneg (mobiusThetaStrictSpectralTailMass_nonneg 6 m w)
        (mobiusThetaStrictSpectralTailMass_nonneg 6 m z)))

theorem summable_deningerGammaSixTensorRemainderNormMajorant
    (k l : ℕ) {w z : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (hz : 0 < (mobiusThetaCenteredParameter z).re) :
    Summable (fun m : ℕ => deningerGammaSixTensorRemainderNormMajorant k l m w z) := by
  have hW := summable_mobiusThetaStrictSpectralTailMass_depth (by norm_num : 0 < 6) hw
  have hZ := summable_mobiusThetaStrictSpectralTailMass_depth (by norm_num : 0 < 6) hz
  have hprod := (Summable.mul_norm (f := fun m => mobiusThetaStrictSpectralTailMass 6 m w)
    (g := fun m => mobiusThetaStrictSpectralTailMass 6 m z) hW.norm hZ.norm).comp_injective
      (i := fun m : ℕ => (m, m)) (fun a b h => congrArg Prod.fst h)
  simp only [Real.norm_of_nonneg (mul_nonneg (mobiusThetaStrictSpectralTailMass_nonneg 6 _ w)
    (mobiusThetaStrictSpectralTailMass_nonneg 6 _ z))] at hprod
  exact ((hW.add hZ).add hprod).mul_left
    (xiThetaInternalJetSpectralMass k w * xiThetaInternalJetSpectralMass l z)

/-- Integrated norm control of the complete original Hilbert tensor remainder. -/
theorem integral_norm_deningerGammaSixInternalJetTensorRemainder_le
    (k l : ℕ) (m : MobiusHonestDepth) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hmw : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) :
    (∫ xy : ℝ × ℝ, ‖deningerGammaSixTensorFourierLaplaceIntegrand
      (deningerGammaSixInternalJetTensorRemainder k l m) w z xy‖ ∂(volume.prod volume)) ≤
      deningerGammaSixHalfWeight m ^ (2 : ℕ) * deningerGammaSixTensorRemainderNormMajorant k l m w z := by
  let H := deningerGammaSixInternalJetLeading k m
  let J := deningerGammaSixInternalJetLeading l m
  let T := deningerGammaSixInternalJetTail k m
  let U := deningerGammaSixInternalJetTail l m
  have had := deningerGammaSixInternalJetTensorRemainder_cross_integrable k l m hw hz hmw hmz
  have hrough := integral_norm_deningerGammaSixTensor_three_sum_le
    (l2SeparatedProduct H U) (l2SeparatedProduct T J) (l2SeparatedProduct T U) w z had.1 had.2.1 had.2.2
  rw [← deningerGammaSixInternalJetTensorRemainder_eq_three_terms] at hrough
  simp only [integral_norm_deningerGammaSixTensorFourierLaplace_product] at hrough
  have ha : ‖(deningerGammaSixHalfWeight m : ℂ)‖ = deningerGammaSixHalfWeight m := by
    rw [Complex.norm_real, Real.norm_of_nonneg (deningerGammaSixHalfWeight_pos m).le]
  have hH : (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand H w x‖) =
      deningerGammaSixHalfWeight m * xiThetaInternalJetSpectralMass k w := by
    dsimp only [H]
    rw [deningerGammaSixInternalJetLeading, integral_norm_mobiusThetaL2FourierLaplace_smul,
      ha, integral_norm_xiThetaInternalJetSourceL2_fourierLaplace]
  have hJ : (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand J z x‖) =
      deningerGammaSixHalfWeight m * xiThetaInternalJetSpectralMass l z := by
    dsimp only [J]
    rw [deningerGammaSixInternalJetLeading, integral_norm_mobiusThetaL2FourierLaplace_smul,
      ha, integral_norm_xiThetaInternalJetSourceL2_fourierLaplace]
  have hT : (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand T w x‖) ≤
      deningerGammaSixHalfWeight m *
        (mobiusThetaStrictSpectralTailMass 6 m w * xiThetaInternalJetSpectralMass k w) := by
    dsimp only [T]
    rw [deningerGammaSixInternalJetTail, integral_norm_mobiusThetaL2FourierLaplace_smul, ha]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_mobiusThetaInternalJetStrictTailL2_le ⟨6, by omega⟩ m k hw hmw)
      (deningerGammaSixHalfWeight_pos m).le
  have hU : (∫ x : ℝ, ‖mobiusThetaL2FourierLaplaceIntegrand U z x‖) ≤
      deningerGammaSixHalfWeight m *
        (mobiusThetaStrictSpectralTailMass 6 m z * xiThetaInternalJetSpectralMass l z) := by
    dsimp only [U]
    rw [deningerGammaSixInternalJetTail, integral_norm_mobiusThetaL2FourierLaplace_smul, ha]
    exact mul_le_mul_of_nonneg_left
      (integral_norm_mobiusThetaInternalJetStrictTailL2_le ⟨6, by omega⟩ m l hz hmz)
      (deningerGammaSixHalfWeight_pos m).le
  rw [hH, hJ] at hrough
  have h01 := mul_le_mul_of_nonneg_left hU (mul_nonneg (deningerGammaSixHalfWeight_pos m).le
    (xiThetaInternalJetSpectralMass_nonneg k w))
  have h10 := mul_le_mul_of_nonneg_right hT (mul_nonneg (deningerGammaSixHalfWeight_pos m).le
    (xiThetaInternalJetSpectralMass_nonneg l z))
  have h11 := mul_le_mul hT hU (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (deningerGammaSixHalfWeight_pos m).le
      (mul_nonneg (mobiusThetaStrictSpectralTailMass_nonneg 6 m w)
        (xiThetaInternalJetSpectralMass_nonneg k w)))
  exact (hrough.trans (add_le_add (add_le_add h01 h10) h11)).trans_eq (by
    unfold deningerGammaSixTensorRemainderNormMajorant
    ring)


/-- Admission is applied to the source, before any Fourier--Laplace integral. -/
def deningerGammaSixAdmittedRemainderIntegrand
    (k l M : ℕ) (w z : ℂ) (n : ℕ) (xy : ℝ × ℝ) : ℂ := by
  classical
  exact if M ≤ deningerGammaSixShellDepth n ∧
      1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re ∧
      1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter z).re then
    (deningerGammaSixShellFlattening n : ℂ) *
      deningerGammaSixTensorFourierLaplaceIntegrand
        (deningerGammaSixInternalJetTensorRemainder k l (deningerGammaSixShellHonestDepth n)) w z xy
    else 0

theorem integrable_deningerGammaSixAdmittedRemainderIntegrand
    (k l M n : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1) :
    Integrable (deningerGammaSixAdmittedRemainderIntegrand k l M w z n) (volume.prod volume) := by
  classical
  unfold deningerGammaSixAdmittedRemainderIntegrand
  split_ifs with h
  · exact ((deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data
      k l (deningerGammaSixShellHonestDepth n) hw hz h.2.1 h.2.2).1).const_mul _
  · exact integrable_zero _ _ _

set_option maxHeartbeats 1000000 in
/-- The bound retains the original half-density and both arithmetic tails. -/
theorem integral_norm_deningerGammaSixAdmittedRemainderIntegrand_le
    (k l M n : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1) :
    (∫ xy : ℝ × ℝ, ‖deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy‖
      ∂(volume.prod volume)) ≤ deningerGammaSixShellEigenvalue n *
        deningerGammaSixTensorRemainderNormMajorant k l (deningerGammaSixShellDepth n) w z := by
  classical
  unfold deningerGammaSixAdmittedRemainderIntegrand
  split_ifs with h
  · simp_rw [norm_mul]
    rw [integral_const_mul, Complex.norm_real,
      Real.norm_of_nonneg (deningerGammaSixShellFlattening_pos n).le]
    have hbound := mul_le_mul_of_nonneg_left
      (integral_norm_deningerGammaSixInternalJetTensorRemainder_le k l (deningerGammaSixShellHonestDepth n) hw hz h.2.1 h.2.2)
      (deningerGammaSixShellFlattening_pos n).le
    have hsquare : deningerGammaSixHalfWeight (deningerGammaSixShellHonestDepth n) ^ (2 : ℕ) =
        deningerGammaSixShellEigenvalue n := by
      rw [pow_two, deningerGammaSixHalfWeight_sq]
      rfl
    rw [hsquare] at hbound
    have hnonneg : 0 ≤ deningerGammaSixShellEigenvalue n *
        deningerGammaSixTensorRemainderNormMajorant k l (deningerGammaSixShellDepth n) w z :=
      mul_nonneg (by unfold deningerGammaSixShellEigenvalue; positivity)
        (deningerGammaSixTensorRemainderNormMajorant_nonneg k l (deningerGammaSixShellDepth n) w z)
    have hflat := mul_le_mul_of_nonneg_right (deningerGammaSixShellFlattening_bounds n).2 hnonneg
    rw [one_mul] at hflat
    dsimp only [deningerGammaSixShellHonestDepth] at hbound
    exact hbound.trans hflat
  · simp only [norm_zero, integral_zero]
    exact mul_nonneg (by unfold deningerGammaSixShellEigenvalue; positivity)
      (deningerGammaSixTensorRemainderNormMajorant_nonneg k l (deningerGammaSixShellDepth n) w z)

/-- Absolute summability is established at the integrand level, before cancellations. -/
theorem summable_integral_norm_deningerGammaSixAdmittedRemainderIntegrand
    (k l M : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hrz : 0 < (mobiusThetaCenteredParameter z).re) :
    Summable (fun n : ℕ => ∫ xy : ℝ × ℝ,
      ‖deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy‖ ∂(volume.prod volume)) := by
  exact (summable_deningerGammaSixShellEigenvalue_profile
    (fun m => deningerGammaSixTensorRemainderNormMajorant k l m w z)
    (fun m => deningerGammaSixTensorRemainderNormMajorant_nonneg k l m w z)
    (summable_deningerGammaSixTensorRemainderNormMajorant k l hrw hrz)).of_nonneg_of_le
      (fun n => integral_nonneg (fun xy => norm_nonneg _))
      (fun n => integral_norm_deningerGammaSixAdmittedRemainderIntegrand_le k l M n hw hz)

/-- Complete original column sum is an integrable source with a justified exchange. -/
theorem deningerGammaSixAdmittedRemainderIntegrand_tsum_data
    (k l M : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hrz : 0 < (mobiusThetaCenteredParameter z).re) :
    Integrable (fun xy => ∑' n : ℕ, deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy)
        (volume.prod volume) ∧
      (∫ xy : ℝ × ℝ, (∑' n : ℕ, deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy)
        ∂(volume.prod volume)) = ∑' n : ℕ,
          ∫ xy : ℝ × ℝ, deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy ∂(volume.prod volume) := by
  have hi := fun n => integrable_deningerGammaSixAdmittedRemainderIntegrand k l M n hw hz
  have hs := summable_integral_norm_deningerGammaSixAdmittedRemainderIntegrand k l M hw hz hrw hrz
  exact ⟨GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs,
    (integral_tsum_of_summable_integral_norm hi hs).symm⟩

/-- Every positive original spectral real part admits a cofinal set of literal cutoffs. -/
theorem eventually_deningerGammaSixSourceDepth_admitted
    {w z : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (hz : 0 < (mobiusThetaCenteredParameter z).re) :
    ∀ᶠ M : ℕ in atTop, 3 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re ∧
      1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re := by
  have hW := eventually_atTop.1 (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hw)
  have hZ := eventually_atTop.1 (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hz)
  obtain ⟨W, hW⟩ := hW
  obtain ⟨Z, hZ⟩ := hZ
  filter_upwards [eventually_ge_atTop 3, eventually_ge_atTop W, eventually_ge_atTop Z] with M h3 hMW hMZ
  exact ⟨h3, fun m hm => ⟨(hW m (hMW.trans hm)).2, (hZ m (hMZ.trans hm)).2⟩⟩

/-- The admitted source is exactly the original coordinate cutoff once its depths are admitted. -/
theorem deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff
    (k l M : ℕ) (w z : ℂ)
    (had : ∀ m : ℕ, M ≤ m →
      1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re ∧
      1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) (n : ℕ) (xy : ℝ × ℝ) :
    deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy =
      if 6 ^ M ≤ n + 216 then (deningerGammaSixShellFlattening n : ℂ) *
        deningerGammaSixTensorFourierLaplaceIntegrand
          (deningerGammaSixInternalJetTensorRemainder k l (deningerGammaSixShellHonestDepth n)) w z xy
      else 0 := by
  classical
  simp only [deningerGammaSixAdmittedRemainderIntegrand, deningerGammaSixTailCut_iff_depth]
  by_cases h : M ≤ deningerGammaSixShellDepth n
  · rw [if_pos ⟨h, had _ h⟩, if_pos h]
  · rw [if_neg (fun hh => h hh.1), if_neg h]

theorem integral_deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff
    (k l M : ℕ) (w z : ℂ)
    (had : ∀ m : ℕ, M ≤ m →
      1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re ∧
      1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) (n : ℕ) :
    (∫ xy : ℝ × ℝ, deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy ∂(volume.prod volume)) =
      if 6 ^ M ≤ n + 216 then deningerGammaSixIntegralRemainder k l w z n else 0 := by
  simp_rw [deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff k l M w z had]
  split_ifs <;> simp only [integral_zero, integral_const_mul,
    deningerGammaSixIntegralRemainder, deningerGammaSixTensorFourierLaplace]

theorem summable_deningerGammaSixIntegralRemainder_cutoff
    (k l M : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hrz : 0 < (mobiusThetaCenteredParameter z).re)
    (had : ∀ m : ℕ, M ≤ m →
      1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re ∧
      1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Summable (fun n : ℕ => if 6 ^ M ≤ n + 216 then deningerGammaSixIntegralRemainder k l w z n else 0) := by
  have hs : Summable (fun n => ∫ xy : ℝ × ℝ,
      deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy ∂(volume.prod volume)) :=
    (summable_integral_norm_deningerGammaSixAdmittedRemainderIntegrand k l M hw hz hrw hrz).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  simpa only [integral_deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff k l M w z had] using hs


/-- Full tensor evaluation requires only the retained depth's own admission inequalities. -/
theorem deningerGammaSixInternalJetTensor_full_fourierLaplace_data_of_admitted
    (k l : ℕ) (m : MobiusHonestDepth) {w z : ℂ}
    (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hmw : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (m : ℝ) < (mobiusThetaCenteredParameter z).re) :
    Integrable (deningerGammaSixTensorFourierLaplaceIntegrand
      (l2SeparatedProduct (deningerGammaSixInternalJetSource k m)
        (deningerGammaSixInternalJetSource l m)) w z) (volume.prod volume) ∧
    deningerGammaSixTensorFourierLaplace
      (l2SeparatedProduct (deningerGammaSixInternalJetSource k m)
        (deningerGammaSixInternalJetSource l m)) w z =
      (deningerGammaSixHalfWeight m : ℂ) ^ (2 : ℕ) *
        (mobiusThetaPrimeNormalResidualMultiplier 6 m w * mobiusThetaPrimeNormalResidualMultiplier 6 m z) *
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) := by
  have hW := deningerGammaSixInternalJetSource_fourierLaplace_data k m hw hmw
  have hZ := deningerGammaSixInternalJetSource_fourierLaplace_data l m hz hmz
  have hP := deningerGammaSixTensorFourierLaplace_product_data _ _ w z hW.1 hZ.1
  refine ⟨hP.1, ?_⟩
  rw [hP.2, hW.2, hZ.2]
  ring

set_option maxHeartbeats 1000000 in
theorem deningerGammaSixIntegralColumn_decomposition_of_admitted
    (k l : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1) (n : ℕ)
    (hmw : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter z).re) :
    deningerGammaSixIntegralColumn k l w z n =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * ((n : ℂ) + 216)⁻¹ +
        deningerGammaSixIntegralRemainder k l w z n := by
  rw [deningerGammaSixIntegralColumn, deningerGammaSixIntegralRemainder,
    (deningerGammaSixInternalJetTensor_full_fourierLaplace_data_of_admitted k l
      (deningerGammaSixShellHonestDepth n) (w := w) (z := z) hw hz hmw hmz).2,
    (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l
      (deningerGammaSixShellHonestDepth n) (w := w) (z := z) hw hz hmw hmz).2,
    deningerGammaSixShellHalfWeight_sq]
  have hp : (deningerGammaSixShellFlattening n : ℂ) *
      (deningerGammaSixShellEigenvalue n : ℂ) = ((n : ℂ) + 216)⁻¹ := by
    have hh := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
    push_cast at hh
    exact hh
  linear_combination (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * hp

theorem deningerGammaSixIntegralCorrection_tail_of_admitted
    (k l : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1) (n : ℕ)
    (hmw : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hmz : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter z).re) :
    deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩
      (deningerGammaSixIntegralOperator k l w z -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC z) • deningerOrdinaryIntegerReciprocalGreen) =
      deningerGammaSixIntegralRemainder k l w z n := by
  simp only [map_sub, map_smul, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_integralOperator,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
  change deningerGammaSixIntegralNatColumn k l w z (n + 216) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC z) * (((n + 216 : ℕ) : ℂ))⁻¹ = _
  rw [deningerGammaSixIntegralNatColumn, if_pos (by omega : 216 ≤ n + 216), Nat.add_sub_cancel,
    deningerGammaSixIntegralColumn_decomposition_of_admitted k l hw hz n hmw hmz]
  push_cast
  ring

theorem deningerGammaSixIntegralRemainder_eq_shell_multiplier_of_admitted
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1) (n : ℕ)
    (ha : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re) :
    deningerGammaSixIntegralRemainder k l w w n =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        deningerGammaSixTensorRemainderMultiplier (deningerGammaSixShellDepth n) w w *
          (((n + 216 : ℕ) : ℂ))⁻¹ := by
  rw [deningerGammaSixIntegralRemainder,
    (deningerGammaSixInternalJetTensorRemainder_fourierLaplace_data k l (deningerGammaSixShellHonestDepth n) hw hw ha ha).2,
    deningerGammaSixShellHalfWeight_sq]
  dsimp only [deningerGammaSixShellHonestDepth]
  have hf := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
  push_cast at hf ⊢
  unfold deningerGammaSixTensorRemainderMultiplier
  linear_combination ((mobiusThetaPrimeNormalResidualMultiplier 6 (deningerGammaSixShellDepth n) w *
      mobiusThetaPrimeNormalResidualMultiplier 6 (deningerGammaSixShellDepth n) w - 1) *
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w)) * hf

/-- Every original admitted coordinate diagonal equals the integral of its masked source. -/
theorem deningerGammaSixIntegralTailOperator_diagonal_source
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (n : ℕ) :
    deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩
      (deningerGammaSixIntegralTailOperator k l M w) =
      ∫ xy : ℝ × ℝ, deningerGammaSixAdmittedRemainderIntegrand k l M w w n xy ∂(volume.prod volume) := by
  rw [integral_deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff k l M w w
    (fun m hm => ⟨had m hm, had m hm⟩)]
  rw [deningerGammaSixIntegralTailOperator, deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
  change (if 6 ^ M ≤ n + 216 then _ else 0) = _
  split_ifs with hn
  · have ha := had _ ((deningerGammaSixTailCut_iff_depth M n).1 hn)
    exact deningerGammaSixIntegralCorrection_tail_of_admitted k l hw hw n ha ha
  · rfl

theorem deningerGammaSixIntegralTailOperator_summable_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerGammaSixIntegralTailOperator k l M w)) := by
  have hs := summable_deningerGammaSixIntegralRemainder_cutoff k l M hw hw hrw hrw
    (fun m hm => ⟨had m hm, had m hm⟩)
  simp only [deningerGammaSixIntegralTailOperator,
    deningerOrdinaryIntegerDiagonalCoefficient_tailProjection, map_sub, map_smul, smul_eq_mul,
    deningerOrdinaryIntegerDiagonalCoefficient_integralOperator,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen]
  apply (summable_pnat_iff_summable_nat (f := fun a : ℕ => if 6 ^ M ≤ a then
    deningerGammaSixIntegralNatColumn k l w w a -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) * (a : ℂ)⁻¹ else 0)).2
  apply (summable_nat_add_iff 216).1
  refine hs.congr (fun n => ?_)
  split_ifs with hn
  · have ha := had _ ((deningerGammaSixTailCut_iff_depth M n).1 hn)
    rw [deningerGammaSixIntegralNatColumn, if_pos (by omega : 216 ≤ n + 216),
      Nat.add_sub_cancel, deningerGammaSixIntegralColumn_decomposition_of_admitted k l hw hw n ha ha]
    push_cast
    ring
  · rfl

theorem summable_deningerGammaSixIntegralTailTerm_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (deningerGammaSixIntegralTailTerm k l M w) := by
  apply (summable_deningerGammaSixIntegralRemainder_cutoff k l M hw hw hrw hrw
    (fun m hm => ⟨had m hm, had m hm⟩)).norm.of_norm_bounded
  intro n
  unfold deningerGammaSixIntegralTailTerm
  split_ifs <;> simp_all


theorem deningerGammaSixIntegralTailTerm_fiber_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) (m : ℕ) :
    (∑' n : deningerGammaSixDepthFiber m, deningerGammaSixIntegralTailTerm k l M w n) =
      if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        deningerGammaSixTensorRemainderMultiplier m w w *
          (deningerGammaSixDivisibleShellMass (m - 1) : ℂ) else 0 := by
  simp_rw [deningerGammaSixIntegralTailTerm_depth]
  by_cases hMm : M ≤ m
  · simp only [if_pos hMm]
    have hm : 3 ≤ m := hM.trans hMm
    have hfiber : (∑' n : deningerGammaSixDepthFiber m,
        if 6 ∣ (n : ℕ) + 216 then deningerGammaSixIntegralRemainder k l w w n else 0) =
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
          deningerGammaSixTensorRemainderMultiplier m w w *
            ∑' n : deningerGammaSixDepthFiber m,
              if 6 ∣ (n : ℕ) + 216 then (((n : ℕ) + 216 : ℕ) : ℂ)⁻¹ else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have ha : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re := by
        rw [show deningerGammaSixShellDepth n = m from n.property]
        exact had m hMm
      rw [deningerGammaSixIntegralRemainder_eq_shell_multiplier_of_admitted k l hw n ha,
        show deningerGammaSixShellDepth n = m from n.property]
      split_ifs <;> simp
    rw [hfiber]
    congr 1
    rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
    rw [Finset.tsum_subtype' (deningerGammaSixShellCoordinates m)
      (fun n : ℕ => if 6 ∣ n + 216 then (((n + 216 : ℕ) : ℂ))⁻¹ else 0)]
    have hlo := deningerGammaSix_pow_three_le hm
    have hhi := deningerGammaSix_pow_three_le (show 3 ≤ m + 1 by omega)
    have hshift := Finset.sum_Ico_add'
      (fun a : ℕ => if 6 ∣ a then (a : ℂ)⁻¹ else 0)
      (6 ^ m - 216) (6 ^ (m + 1) - 216) (c := 216)
    rw [Nat.sub_add_cancel hlo, Nat.sub_add_cancel hhi] at hshift
    change (∑ n ∈ Finset.Ico (6 ^ m - 216) (6 ^ (m + 1) - 216),
      if 6 ∣ n + 216 then ((n + 216 : ℕ) : ℂ)⁻¹ else 0) = _
    rw [hshift]
    have hreal := congrArg Complex.ofReal (deningerGammaSixDivisibleShellMass_eq_sum m (by omega))
    push_cast at hreal
    simpa only [apply_ite, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero] using hreal
  · simp only [if_neg hMm, tsum_zero]


theorem deningerGammaSixIntegralTailTerm_tsum_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    (∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n) =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        ∑' j : ℕ, deningerGammaSixTensorRemainderMultiplier (M + j) w w *
          (deningerGammaSixDivisibleShellMass (M + j - 1) : ℂ) := by
  have hs := summable_deningerGammaSixIntegralTailTerm_of_admitted k l M hw hrw had
  have hf := hs.hasSum.tsum_fiberwise deningerGammaSixShellDepth
  change HasSum (fun m : ℕ => ∑' n : deningerGammaSixDepthFiber m,
    deningerGammaSixIntegralTailTerm k l M w n)
      (∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n) at hf
  rw [← hf.tsum_eq]
  simp_rw [deningerGammaSixIntegralTailTerm_fiber_of_admitted k l M hw had hM]
  have hinj : Function.Injective (fun j : ℕ => M + j) := fun _ _ h => Nat.add_left_cancel h
  have he := hinj.tsum_eq (f := fun m : ℕ =>
    if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
      deningerGammaSixTensorRemainderMultiplier m w w *
        (deningerGammaSixDivisibleShellMass (m - 1) : ℂ) else 0) (by
          intro m hm
          have hMm : M ≤ m := by
            by_contra h
            exact hm (if_neg h)
          exact ⟨m - M, by change M + (m - M) = m; omega⟩)
  rw [← he]
  simp only [Nat.le_add_right, if_true, mul_assoc, tsum_mul_left]


theorem deningerGammaSixIntegralTailOperator_second_eq_tsum_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 =
        (Real.log 6 : ℂ) * ∑' n : ℕ, deningerGammaSixIntegralTailTerm k l M w n := by
  classical
  let R := deningerGammaSixIntegralOperator k l w w -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen
  let f : PNat → ℂ := fun a => if 6 ^ M ≤ (a : ℕ) ∧ (6 : PNat) ∣ a then
    deningerOrdinaryIntegerDiagonalCoefficient a R else 0
  have hf : deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 = (Real.log 6 : ℂ) * ∑' a : PNat, f a := by
    simp only [deningerOrdinaryIntegerAbelSecondCoefficient, zero_smul, sub_zero,
      deningerGammaSixIntegralTailOperator, deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
    congr 1
    apply tsum_congr
    intro a
    dsimp only [f, R]
    split_ifs <;> simp_all
  rw [hf]
  congr 1
  let g : ℕ → PNat := fun n => ⟨n + 216, by omega⟩
  have hg : Function.Injective g := by
    intro i j h
    have he := congrArg (fun a : PNat => (a : ℕ)) h
    change i + 216 = j + 216 at he
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro a ha
    have hpow : 6 ^ M ≤ (a : ℕ) := by
      by_contra h
      exact ha (by simp only [f, h, false_and, if_false])
    have hlow := deningerGammaSix_pow_three_le hM
    refine ⟨(a : ℕ) - 216, ?_⟩
    apply Subtype.ext
    change (a : ℕ) - 216 + 216 = (a : ℕ)
    exact Nat.sub_add_cancel (hlow.trans hpow)
  rw [← hg.tsum_eq hsupp]
  apply tsum_congr
  intro n
  dsimp only [f, g]
  by_cases hn : 6 ^ M ≤ n + 216
  · have ha := had _ ((deningerGammaSixTailCut_iff_depth M n).1 hn)
    rw [show deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩ R =
      deningerGammaSixIntegralRemainder k l w w n from
        deningerGammaSixIntegralCorrection_tail_of_admitted k l hw hw n ha ha]
    unfold deningerGammaSixIntegralTailTerm
    split_ifs <;> simp_all [PNat.dvd_iff]
  · change (if 6 ^ M ≤ n + 216 ∧ (6 : PNat) ∣ ⟨n + 216, by omega⟩ then _ else 0) = _
    simp only [deningerGammaSixIntegralTailTerm, hn, false_and, if_false]


theorem deningerGammaSixIntegralTailOperator_second_eq_shell_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 =
        deningerGammaSixShellTailBoundary k l M w := by
  rw [deningerGammaSixIntegralTailOperator_second_eq_tsum_of_admitted k l M hw had hM,
    deningerGammaSixIntegralTailTerm_tsum_of_admitted k l M hw hrw had hM,
    deningerGammaSixShellTailBoundary]
  ring


theorem tendsto_deningerGammaSixIntegralTailOperator_second_of_admitted
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    Tendsto (fun ε : ℝ => deningerOrdinaryIntegerAbelDefect ε (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) / (ε : ℂ)^(2 : ℕ))
      (𝓝[>] 0) (𝓝 (deningerGammaSixShellTailBoundary k l M w)) := by
  have h := tendsto_deningerOrdinaryIntegerAbelDefect_second
    (deningerGammaSixIntegralTailOperator k l M w) 0
    (by simpa only [zero_smul, sub_zero] using deningerGammaSixIntegralTailOperator_summable_of_admitted k l M hw hrw had)
    (6 : PNat)
  simpa only [zero_mul, sub_zero,
    deningerGammaSixIntegralTailOperator_second_eq_shell_of_admitted k l M hw hrw had hM] using h

/-- Every ordinary divisibility filter retains the same absolute source admission. -/
theorem deningerGammaSixAdmittedRemainderIntegrand_divisible_tsum_data
    (k l M q : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hrz : 0 < (mobiusThetaCenteredParameter z).re) :
    Summable (fun n : ℕ => ∫ xy : ℝ × ℝ,
      ‖if q ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0‖
        ∂(volume.prod volume)) ∧
    Integrable (fun xy => ∑' n : ℕ,
      if q ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0)
        (volume.prod volume) ∧
      (∫ xy : ℝ × ℝ, (∑' n : ℕ,
        if q ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0)
        ∂(volume.prod volume)) = ∑' n : ℕ,
          ∫ xy : ℝ × ℝ,
            (if q ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0)
            ∂(volume.prod volume) := by
  have hi : ∀ n : ℕ, Integrable (fun xy => if q ∣ n + 216 then
      deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0) (volume.prod volume) := by
    intro n
    split_ifs
    · exact integrable_deningerGammaSixAdmittedRemainderIntegrand k l M n hw hz
    · exact integrable_zero _ _ _
  have hs : Summable (fun n : ℕ => ∫ xy : ℝ × ℝ,
      ‖if q ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0‖
        ∂(volume.prod volume)) := by
    apply (summable_integral_norm_deningerGammaSixAdmittedRemainderIntegrand k l M hw hz hrw hrz).of_nonneg_of_le
      (fun n => integral_nonneg (fun xy => norm_nonneg _))
    intro n
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, integral_zero]
      exact integral_nonneg (fun xy => norm_nonneg _)
  exact ⟨hs, GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs,
    (integral_tsum_of_summable_integral_norm hi hs).symm⟩

/-- The fixed-six readout is an integral of the complete admitted source sum. -/
theorem deningerGammaSixIntegralTailOperator_second_eq_complete_integral
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) (hM : 3 ≤ M) :
    deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 = (Real.log 6 : ℂ) *
        ∫ xy : ℝ × ℝ, (∑' n : ℕ,
          if 6 ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w w n xy else 0)
          ∂(volume.prod volume) := by
  rw [deningerGammaSixIntegralTailOperator_second_eq_tsum_of_admitted k l M hw had hM,
    (deningerGammaSixAdmittedRemainderIntegrand_divisible_tsum_data k l M 6 hw hw hrw hrw).2.2]
  congr 1
  apply tsum_congr
  intro n
  by_cases hq : 6 ∣ n + 216
  · simp only [hq, if_true]
    rw [integral_deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff k l M w w
      (fun m hm => ⟨had m hm, had m hm⟩)]
    simp only [deningerGammaSixIntegralTailTerm, hq, and_true]
  · simp only [hq, if_false, integral_zero, deningerGammaSixIntegralTailTerm, and_false]

/-- At any pair of original Xi divisors the complete source sum is admitted without a location premise. -/
theorem deningerGammaSixAdmittedRemainderIntegrand_tsum_at_divisors
    (k l M : ℕ) (rho sigma : XiDivisorSupport) :
    Integrable (fun xy => ∑' n : ℕ, deningerGammaSixAdmittedRemainderIntegrand k l M
      (xiSpectralPointSupport rho) (xiSpectralPointSupport sigma) n xy) (volume.prod volume) := by
  have hrho : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hsigma : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport sigma)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit sigma).1
  exact (deningerGammaSixAdmittedRemainderIntegrand_tsum_data k l M
    (abs_im_xiSpectralPointSupport_lt_one rho) (abs_im_xiSpectralPointSupport_lt_one sigma) hrho hsigma).1

/-- The original integral operator has the fixed-six normalized limit throughout the positive chamber. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_normalized_positive
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun M : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
          (deningerGammaSixIntegralTailOperator k l M w) 0) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  apply (tendsto_deningerGammaSixShellTailBoundary_normalized k l hrw).congr'
  filter_upwards [eventually_deningerGammaSixSourceDepth_admitted hrw hrw] with M hM
  rw [deningerGammaSixIntegralTailOperator_second_eq_shell_of_admitted k l M hw hrw
    (fun m hm => (hM.2 m hm).1) hM.1]

theorem eventually_deningerGammaSixIntegralTailOperator_second_ne_zero_positive
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hc : iteratedDeriv k XiC w * iteratedDeriv l XiC w ≠ 0) :
    ∀ᶠ M : ℕ in atTop, deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator k l M w) 0 ≠ 0 := by
  have ht := (tendsto_deningerGammaSixIntegralTailOperator_normalized_positive k l hw hrw).eventually_ne
    (deningerGammaSixTailBoundaryLimit_ne_zero k l hrw hc)
  filter_upwards [ht] with M hM
  intro hz
  exact hM (by rw [hz, mul_zero])

/-- Finite diagonal repairs preserve the actual original-anchor limit on the full positive chamber. -/
theorem tendsto_deningerGammaSixIntegral_finite_repair_tail_normalized_positive
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    Tendsto (fun M : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
          (deningerOrdinaryIntegerTailProjection (6 ^ M) *
            ((deningerGammaSixIntegralOperator k l w w + F) -
              (iteratedDeriv k XiC w * iteratedDeriv l XiC w) •
                deningerOrdinaryIntegerReciprocalGreen)) 0) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  have he := eventually_deningerOrdinaryInteger_finite_tail_second_eq
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) F hF
  apply (tendsto_deningerGammaSixIntegralTailOperator_normalized_positive k l hw hrw).congr'
  filter_upwards [he] with M hM
  rw [show (deningerGammaSixIntegralOperator k l w w + F) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen =
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) + F by abel,
    hM]
  rfl

/-- Every Xi divisor keeps its original spectral point and its nonzero top-jet fixed-six response. -/
theorem eventually_deningerGammaSixIntegral_top_fixed_six_all_divisors
    (rho : XiDivisorSupport) :
    ∀ᶠ M : ℕ in atTop, deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
      (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
        (xiSpectralPointSupport rho)) 0 ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  exact eventually_deningerGammaSixIntegralTailOperator_second_ne_zero_positive _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw
    (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))

/-- Finite diagonal repairs cannot kill the actual second boundary limit at any original divisor. -/
theorem eventually_deningerGammaSixIntegral_top_finite_repair_fixed_six_all_divisors
    (rho : XiDivisorSupport)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ¬ Tendsto (fun ε : ℝ =>
      deningerOrdinaryIntegerAbelDefect ε (6 : PNat)
        (deningerOrdinaryIntegerTailProjection (6 ^ M) *
          ((deningerGammaSixIntegralOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
            (xiSpectralPointSupport rho) (xiSpectralPointSupport rho) + F) -
              (iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) *
                iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) •
                  deningerOrdinaryIntegerReciprocalGreen)) / (ε : ℂ)^(2 : ℕ))
      (𝓝[>] 0) (𝓝 0) := by
  let w := xiSpectralPointSupport rho
  let r := xiSupportMultiplicity rho
  let T := deningerGammaSixIntegralOperator r r w w -
    (iteratedDeriv r XiC w * iteratedDeriv r XiC w) • deningerOrdinaryIntegerReciprocalGreen
  have hw := abs_im_xiSpectralPointSupport_lt_one rho
  have hrw : 0 < (mobiusThetaCenteredParameter w).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hc := mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
    (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
  have ht := (tendsto_deningerGammaSixIntegral_finite_repair_tail_normalized_positive r r hw hrw F hF).eventually_ne
    (deningerGammaSixTailBoundaryLimit_ne_zero r r hrw hc)
  filter_upwards [ht, eventually_deningerGammaSixSourceDepth_admitted hrw hrw,
    eventually_deningerOrdinaryInteger_finite_tail_diagonal_zero F hF] with M hM had hFzero
  have hs := deningerGammaSixIntegralTailOperator_summable_of_admitted r r M hw hrw
    (fun m hm => (had.2 m hm).1)
  have hrepair : (deningerGammaSixIntegralOperator r r w w + F) -
      (iteratedDeriv r XiC w * iteratedDeriv r XiC w) • deningerOrdinaryIntegerReciprocalGreen = T + F := by
    dsimp [T]
    abel
  have hsrepair : Summable (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a
      (deningerOrdinaryIntegerTailProjection (6 ^ M) *
        ((deningerGammaSixIntegralOperator r r w w + F) -
          (iteratedDeriv r XiC w * iteratedDeriv r XiC w) • deningerOrdinaryIntegerReciprocalGreen))) := by
    rw [hrepair, mul_add]
    simpa only [map_add, hFzero, add_zero, deningerGammaSixIntegralTailOperator] using hs
  have hlim := tendsto_deningerOrdinaryIntegerAbelDefect_second _ 0
    (by simpa only [zero_smul, sub_zero] using hsrepair) (6 : PNat)
  simp only [zero_mul, sub_zero] at hlim
  intro hz
  have hcoef := tendsto_nhds_unique hlim hz
  exact hM (by rw [hcoef, mul_zero])

/-- The complete cutoff reader retains the adjacent zero/nonzero internal conormal pair. -/
theorem eventually_deningerGammaSixIntegral_adjacent_conormal_pair_all_divisors
    (rho : XiDivisorSupport) :
    ∀ᶠ M : ℕ in atTop,
      deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
        (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho - 1) (xiSupportMultiplicity rho) M
          (xiSpectralPointSupport rho)) 0 = 0 ∧
      deningerOrdinaryIntegerAbelSecondCoefficient (6 : PNat)
        (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
          (xiSpectralPointSupport rho)) 0 ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hr : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho :=
    Nat.sub_lt (xiSupportMultiplicity_pos rho) (by omega)
  have hlower := iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hr
  filter_upwards [eventually_deningerGammaSixSourceDepth_admitted hrw hrw,
    eventually_deningerGammaSixIntegral_top_fixed_six_all_divisors rho] with M had htop
  refine ⟨?_, htop⟩
  rw [deningerGammaSixIntegralTailOperator_second_eq_shell_of_admitted _ _ M
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw (fun m hm => (had.2 m hm).1) had.1]
  simp only [deningerGammaSixShellTailBoundary, hlower, zero_mul, mul_zero]

end
end RHTower
