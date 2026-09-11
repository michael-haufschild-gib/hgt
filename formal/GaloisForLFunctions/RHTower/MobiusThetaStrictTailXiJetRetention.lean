import GaloisForLFunctions.RHTower.DeningerGammaSixFullSourcePrincipalClass
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Xi jets retained by complete strict arithmetic tails

After any finite ordinary-integer head removal, the internally promoted
Möbius--theta tail has an absolutely admitted Fourier--Laplace integral.
Its multiplier tends to zero but is eventually nonzero; exact successor
normalization recovers a nonzero Möbius coefficient. Every Xi divisor's
multiplicity is retained in the adjacent source jets.

The complete Hilbert tail tends strongly to zero, with an exact successor
norm law. An almost-everywhere representative identity, including Fourier
coordinate scaling, identifies its literal integral with the same jet
source. The original pre-tensor Gamma-six tail is included.

This is positive remainder retention, not an RH proof. It constructs no
Sonin quotient comparison, fixed-reader agreement, or tensor-remainder
annihilation. Internal source jets are distinguished from derivatives of
the entire multiplier-times-Xi product.
-/

open Complex Real MeasureTheory Filter Topology
open scoped BigOperators
namespace RHTower
set_option maxHeartbeats 800000
noncomputable section

/-- All ordinary-integer channels strictly beyond the retained label, before evaluation. -/
def mobiusThetaInternalJetStrictTailSource (k p m : ℕ) (x : ℝ) : ℂ :=
  ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m (j + 1) x

def mobiusThetaInternalJetStrictTailFourierLaplace (k p m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetStrictTailSource k p m x

def mobiusThetaStrictTailMultiplier (p m : ℕ) (w : ℂ) : ℂ :=
  mobiusThetaPrimeNormalResidualMultiplier p m w -
    ((ArithmeticFunction.moebius p : ℤ) : ℂ)

theorem mobiusThetaInternalJetStrictTailFourierLaplace_eq
    {p : ℕ} (hp : 0 < p) (k : ℕ) {m : ℕ} (hm : m ≠ 0)
    {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetStrictTailFourierLaplace k p m w =
      mobiusThetaStrictTailMultiplier p m w * iteratedDeriv k XiC w := by
  have hs : Summable (fun j : ℕ => ∫ x : ℝ,
      ‖mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w (j + 1) x‖) :=
    (summable_nat_add_iff 1).2
      (summable_integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp hm k hms)
  unfold mobiusThetaInternalJetStrictTailFourierLaplace mobiusThetaInternalJetStrictTailSource
  have hinter (x : ℝ) : Complex.exp (-I * w * (x : ℂ)) *
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m (j + 1) x) =
      ∑' j : ℕ, mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w (j + 1) x := by
    rw [← tsum_mul_left]
    rfl
  simp_rw [hinter]
  rw [← integral_tsum_of_summable_integral_norm
    (fun j => integrable_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp k m hw (j + 1)) hs]
  simp_rw [integral_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp k m hw,
    mobiusThetaPrimeNormalResidualSpectralCoefficient_succ]
  rw [tsum_mul_right, mobiusThetaStrictTailMultiplier,
    mobiusThetaPrimeNormalResidualMultiplier_eq_asymptoticMultiplier hp hm hms,
    mobiusThetaPrimeNormalAsymptoticMultiplier, add_sub_cancel_left]

theorem tendsto_mobiusThetaStrictTailMultiplier_zero
    {p : ℕ} (hp : 0 < p) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun m => mobiusThetaStrictTailMultiplier p m w) atTop (nhds 0) := by
  simpa only [mobiusThetaStrictTailMultiplier, sub_self] using
    (tendsto_mobiusThetaPrimeNormalResidualMultiplier hp hw).sub_const
      (((ArithmeticFunction.moebius p : ℤ) : ℂ))

theorem mobiusThetaStrictTailMultiplier_successor
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth)
    (w : MobiusSuccessorSpectralPoint m) :
    mobiusThetaSuccessorSpectralNormalizer p m (mobiusThetaCenteredParameter w) *
      mobiusThetaStrictTailMultiplier p m w =
        mobiusThetaPrimeNormalResidualMultiplier (mobiusSuccessor p) m w :=
  mobiusThetaPrimeNormalResidualMultiplier_successor_transport p m w

/-- A strict tail is eventually nonzero after every finite ordinary-integer head removal. -/
theorem eventually_mobiusThetaStrictTailMultiplier_ne_zero
    (p : MobiusPositiveIndex) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    ∀ᶠ m : ℕ in atTop, mobiusThetaStrictTailMultiplier p m w ≠ 0 := by
  have hmu : (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℤ) : ℂ)) ≠ 0 := by
    exact_mod_cast moebius_mobiusSuccessor_ne_zero p
  have hn := (tendsto_mobiusThetaPrimeNormalResidualMultiplier
    (mobiusSuccessor_pos p.property) hw).eventually_ne hmu
  filter_upwards [hn, eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hw,
    eventually_ge_atTop 3] with m hm hd hdepth
  intro hz
  have heq := mobiusThetaStrictTailMultiplier_successor p ⟨m, hdepth⟩ ⟨w, hd.2⟩
  change mobiusThetaSuccessorSpectralNormalizer p m (mobiusThetaCenteredParameter w) *
    mobiusThetaStrictTailMultiplier p m w = _ at heq
  rw [hz, mul_zero] at heq
  exact hm heq.symm

/-- The source-derived normalization recovers the next nonzero Möbius coefficient. -/
theorem tendsto_mobiusThetaStrictTailMultiplier_normalized
    (p : MobiusPositiveIndex) {w : ℂ}
    (hw : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun m : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer p m (mobiusThetaCenteredParameter w) *
        mobiusThetaStrictTailMultiplier p m w) atTop
      (nhds (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℤ) : ℂ))) := by
  apply (tendsto_mobiusThetaPrimeNormalResidualMultiplier
    (mobiusSuccessor_pos p.property) hw).congr'
  filter_upwards [eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hw,
    eventually_ge_atTop 3] with m hm hdepth
  exact (mobiusThetaStrictTailMultiplier_successor p ⟨m, hdepth⟩ ⟨w, hm.2⟩).symm

def mobiusThetaInternalJetStrictTailConormalPair (k p m : ℕ) (w : ℂ) : ℂ × ℂ :=
  (mobiusThetaInternalJetStrictTailFourierLaplace k p m w,
    mobiusThetaInternalJetStrictTailFourierLaplace (k + 1) p m w)

/-- Every finite tail retains arbitrary Xi multiplicity in its actual adjacent internal jets. -/
theorem eventually_mobiusThetaInternalJetStrictTailConormalPair_at_divisor
    (p : MobiusPositiveIndex) (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ in atTop,
      mobiusThetaInternalJetStrictTailConormalPair
          (xiSupportMultiplicity rho - 1) p m (xiSpectralPointSupport rho) =
        (0, mobiusThetaStrictTailMultiplier p m (xiSpectralPointSupport rho) *
          iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)) ∧
      mobiusThetaStrictTailMultiplier p m (xiSpectralPointSupport rho) *
        iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho) ≠ 0 := by
  have hre : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  filter_upwards [eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hre,
    eventually_mobiusThetaStrictTailMultiplier_ne_zero p hre] with m hm hne
  have hp : 0 < (p : ℕ) := lt_of_lt_of_le Nat.zero_lt_one p.property
  have hrpos := xiSupportMultiplicity_pos rho
  have hrpred : xiSupportMultiplicity rho - 1 < xiSupportMultiplicity rho :=
    Nat.sub_lt hrpos (by omega)
  have hzero := iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho hrpred
  have hsucc : xiSupportMultiplicity rho - 1 + 1 = xiSupportMultiplicity rho := by omega
  constructor
  · rw [mobiusThetaInternalJetStrictTailConormalPair,
      mobiusThetaInternalJetStrictTailFourierLaplace_eq hp _ hm.1
        (abs_im_xiSpectralPointSupport_lt_one rho) hm.2,
      hsucc, mobiusThetaInternalJetStrictTailFourierLaplace_eq hp _ hm.1
        (abs_im_xiSpectralPointSupport_lt_one rho) hm.2, hzero, mul_zero]
  · exact mul_ne_zero hne (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)

/-- Complete strict physical tail in the original Hilbert source space. -/
def mobiusThetaStrictTailL2 (p m : ℕ) : MobiusThetaSourceL2 :=
  mobiusThetaPrimeNormalResidual p m -
    (((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaSourceL2

theorem mobiusThetaStrictTailL2_eq_tsum (p m : ℕ) :
    mobiusThetaStrictTailL2 p m = ∑' j : ℕ, mobiusThetaPrimeNormalTailTerm p m j := by
  unfold mobiusThetaStrictTailL2 mobiusThetaPrimeNormalResidual
  abel

theorem tendsto_mobiusThetaStrictTailL2_zero (p : MobiusPositiveIndex) :
    Tendsto (mobiusThetaStrictTailL2 p) atTop (nhds 0) := by
  change Tendsto (fun m => mobiusThetaStrictTailL2 p m) atTop (nhds 0)
  simp_rw [mobiusThetaStrictTailL2_eq_tsum]
  exact tendsto_tsum_mobiusThetaPrimeNormalTailTerm_zero p.property

/-- The same actual successor transport yields an exact norm identity, not just an upper bound. -/
theorem mobiusThetaStrictTailL2_successor_norm
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) :
    ((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) * ‖mobiusThetaStrictTailL2 p m‖ =
      ‖mobiusThetaPrimeNormalResidual (mobiusSuccessor p) m‖ := by
  have h := congrArg norm (mobiusTheta_successor_transport p m)
  rw [mobiusThetaSuccessorBlowup, norm_smul, LinearIsometryEquiv.norm_map,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by
      apply div_pos
      · exact_mod_cast mobiusSuccessor_pos p.property
      · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one p.property) _)] at h
  exact h

/-- The normalized source norm has a forced strictly positive limit. -/
theorem tendsto_mobiusThetaStrictTailL2_normalized_norm
    (p : MobiusPositiveIndex) :
    Tendsto (fun n : ℕ =>
      ((mobiusSuccessor p : ℝ) / p) ^ (((n + 3 : ℕ) : ℝ) / 2) *
        ‖mobiusThetaStrictTailL2 p (n + 3)‖) atTop
      (nhds ‖(((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) • xiThetaSourceL2‖) := by
  have ht := ((tendsto_mobiusThetaPrimeNormalResidual
    (Nat.one_le_iff_ne_zero.mpr (mobiusSuccessor_pos p.property).ne_zero)).comp
      (tendsto_add_atTop_nat 3)).norm
  apply ht.congr'
  exact Filter.Eventually.of_forall (fun n =>
    (mobiusThetaStrictTailL2_successor_norm p ⟨n + 3, by omega⟩).symm)

theorem mobiusThetaStrictTailL2_normalized_limit_pos (p : MobiusPositiveIndex) :
    0 < ‖(((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) • xiThetaSourceL2‖ := by
  apply norm_pos_iff.mpr
  apply smul_ne_zero
  · exact_mod_cast moebius_mobiusSuccessor_ne_zero p
  · exact xiThetaSourceL2_ne_zero

/-- Hilbert-small strict tails remain nonzero at every sufficiently large depth. -/
theorem eventually_mobiusThetaStrictTailL2_ne_zero (p : MobiusPositiveIndex) :
    ∀ᶠ m : ℕ in atTop, mobiusThetaStrictTailL2 p m ≠ 0 := by
  have hlimne : (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) • xiThetaSourceL2 ≠ 0 :=
    norm_pos_iff.mp (mobiusThetaStrictTailL2_normalized_limit_pos p)
  have hn := (tendsto_mobiusThetaPrimeNormalResidual
    (Nat.one_le_iff_ne_zero.mpr (mobiusSuccessor_pos p.property).ne_zero)).eventually_ne hlimne
  filter_upwards [hn, eventually_ge_atTop 3] with m hm hdepth
  intro hz
  have h := mobiusThetaStrictTailL2_successor_norm p ⟨m, hdepth⟩
  rw [hz, norm_zero, mul_zero] at h
  exact hm (norm_eq_zero.mp h.symm)

/-- Exact connection to the complete pre-tensor Gamma-six tail in C20. -/
theorem deningerGammaSixCountertransportedTail_eq_strictTail (m : MobiusHonestDepth) :
    deningerGammaSixCountertransportedTail m =
      (deningerGammaSixHalfWeight m : ℂ) • mobiusThetaStrictTailL2 6 m := by
  rw [mobiusThetaStrictTailL2_eq_tsum]
  rfl

/-- Every internal source jet tends to zero in the physical tail norm. -/
theorem tendsto_mobiusThetaInternalJetStrictTailL2_zero
    (k : ℕ) (p : MobiusPositiveIndex) :
    Tendsto (fun m : ℕ =>
      mobiusThetaInternalJetPrimeNormalResidual k p m -
        (((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaInternalJetSourceL2 k)
      atTop (nhds 0) := by
  simpa only [sub_self] using
    (tendsto_mobiusThetaInternalJetPrimeNormalResidual k p.property).sub_const
      ((((ArithmeticFunction.moebius p : ℝ) : ℂ)) • xiThetaInternalJetSourceL2 k)

/-- Normalized literal strict-tail evaluation recovers the next source's Xi jet. -/
theorem tendsto_mobiusThetaInternalJetStrictTailFourierLaplace_normalized
    (p : MobiusPositiveIndex) (k : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hs : 0 < (mobiusThetaCenteredParameter w).re) :
    Tendsto (fun m : ℕ =>
      mobiusThetaSuccessorSpectralNormalizer p m (mobiusThetaCenteredParameter w) *
        mobiusThetaInternalJetStrictTailFourierLaplace k p m w) atTop
      (nhds ((((ArithmeticFunction.moebius (mobiusSuccessor p) : ℤ) : ℂ)) *
        iteratedDeriv k XiC w)) := by
  apply ((tendsto_mobiusThetaStrictTailMultiplier_normalized p hs).mul_const
    (iteratedDeriv k XiC w)).congr'
  filter_upwards [eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hs]
    with m hm
  rw [mobiusThetaInternalJetStrictTailFourierLaplace_eq
    (lt_of_lt_of_le Nat.zero_lt_one p.property) k hm.1 hw hm.2]
  exact mul_assoc _ _ _

/-- The Hilbert coefficient is exactly the source's half-density Dirichlet coefficient. -/
theorem mobiusThetaPrimeNormalWeight_eq_halfDensityTerm
    {p : ℕ} (hp : 0 < p) (m j : ℕ) :
    (mobiusThetaPrimeNormalWeight p m j : ℂ) =
      (((p : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          ((m : ℂ) / 2) (p + j + 1) := by
  have hn : p + j + 1 ≠ 0 := by omega
  have hpow : ((((p + j + 1 : ℕ) : ℝ) ^ ((m : ℝ) / 2) : ℝ) : ℂ) =
      ((p + j + 1 : ℕ) : ℂ) ^ ((m : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [mobiusThetaPrimeNormalWeight, Real.div_rpow (by positivity) (by positivity),
    LSeries.term_of_ne_zero hn, ← hpow]
  push_cast
  ring_nf

/-- Literal almost-everywhere coordinate bridge between the Hilbert jet tail and its integral source. -/
theorem mobiusThetaInternalJetPrimeNormalTailTerm_ae_source
    {p : ℕ} (hp : 0 < p) (k m j : ℕ) :
    mobiusThetaInternalJetPrimeNormalTailTerm k p m j =ᵐ[volume]
      fun x : ℝ => (2 * Real.pi : ℂ) *
        mobiusThetaInternalJetPrimeNormalResidualSourceTerm k p m (j + 1) ((2 * Real.pi) * x) := by
  let a : ℝ := -((m : ℝ) * Real.log ((p + j + 1 : ℕ) / (p : ℝ))) *
    MellinL2.spectralNormalization
  have hbase := ((xiThetaInternalJetSchwartzSource k).coeFn_toLp (p := 2) (μ := volume)).comp_tendsto
    (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae
  have hshift := Lp.coeFn_compMeasurePreserving (xiThetaInternalJetSourceL2 k)
    (MellinL2.realTranslation_measurePreserving a)
  have hsmul := Lp.coeFn_smul (mobiusThetaPrimeNormalWeight p m j : ℂ)
    (MellinL2.additiveTranslationUnitary a (xiThetaInternalJetSourceL2 k))
  filter_upwards [hbase, hshift, hsmul] with x hx hy hz
  change ((mobiusThetaPrimeNormalWeight p m j : ℂ) •
    MellinL2.additiveTranslationUnitary a (xiThetaInternalJetSourceL2 k)) x = _
  rw [hz]
  change (mobiusThetaPrimeNormalWeight p m j : ℂ) *
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv a)
      (MellinL2.realTranslation_measurePreserving a) (xiThetaInternalJetSourceL2 k) x = _
  rw [hy]
  change (mobiusThetaPrimeNormalWeight p m j : ℂ) *
    (xiThetaInternalJetSourceL2 k) (x + a) = _
  rw [show (xiThetaInternalJetSourceL2 k) (x + a) =
    xiThetaInternalJetSchwartzSource k (x + a) from hx]
  rw [xiThetaInternalJetSchwartzSource_apply, xiThetaSchwartzSource_apply,
    mobiusThetaPrimeNormalWeight_eq_halfDensityTerm hp]
  have hcoord : (2 * Real.pi) * (x + a) =
      (2 * Real.pi) * x - (m : ℝ) *
        (Real.log (p + (j + 1) : ℕ) - Real.log p) := by
    dsimp [a, MellinL2.spectralNormalization]
    rw [Real.log_div (by positivity) (by exact_mod_cast hp.ne')]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
  rw [hcoord, mobiusThetaInternalJetPrimeNormalResidualSourceTerm]
  have hn : p + (j + 1) = p + j + 1 := by omega
  simp only [hn]
  push_cast
  ring_nf

/-- Absolute Hilbert-column admission allows the representative bridge to pass through the whole tail. -/
theorem mobiusThetaInternalJetStrictTailL2_ae_source
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) :
    ((∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j : MobiusThetaSourceL2) : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (2 * Real.pi : ℂ) *
        mobiusThetaInternalJetStrictTailSource k p m ((2 * Real.pi) * x) := by
  have hnorm : Summable (fun j : ℕ => ‖mobiusThetaInternalJetPrimeNormalTailTerm k p m j‖) := by
    exact (summable_mobiusThetaInternalJetPrimeNormalMajorant k p).of_norm_bounded
      (fun j => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_mobiusThetaInternalJetPrimeNormalTailTerm_le_majorant k p.property m.property j)
  have he : ∑' j : ℕ, ‖mobiusThetaInternalJetPrimeNormalTailTerm k p m j‖ₑ ≠ ⊤ := by
    simp only [enorm_eq_nnnorm]
    rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    simpa only [coe_nnnorm] using hnorm
  have hsum := Lp.coeFn_tsum he
  have hall := ae_all_iff.mpr (fun j => mobiusThetaInternalJetPrimeNormalTailTerm_ae_source
    (lt_of_lt_of_le Nat.zero_lt_one p.property) k m j)
  filter_upwards [hsum, hall] with x hx hterm
  rw [hx]
  simp_rw [hterm]
  rw [tsum_mul_left]
  rfl

/-- Evaluation of the actual Hilbert tail, with the Fourier normalization retained explicitly. -/
def mobiusThetaInternalJetStrictTailL2FourierLaplace
    (k p m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (((2 * Real.pi) * x : ℝ) : ℂ)) *
    (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j : MobiusThetaSourceL2) x

/-- Exact same-source integral bridge, including the physical coordinate normalization. -/
theorem mobiusThetaInternalJetStrictTailL2FourierLaplace_eq
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) (w : ℂ) :
    mobiusThetaInternalJetStrictTailL2FourierLaplace k p m w =
      mobiusThetaInternalJetStrictTailFourierLaplace k p m w := by
  let G : ℝ → ℂ := fun x => Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaInternalJetStrictTailSource k p m x
  have hfun : (fun x : ℝ => Complex.exp (-I * w * (((2 * Real.pi) * x : ℝ) : ℂ)) *
      (∑' j : ℕ, mobiusThetaInternalJetPrimeNormalTailTerm k p m j : MobiusThetaSourceL2) x) =ᵐ[volume]
      fun x => (2 * Real.pi : ℂ) * G ((2 * Real.pi) * x) := by
    filter_upwards [mobiusThetaInternalJetStrictTailL2_ae_source p m k] with x hx
    rw [hx]
    dsimp [G]
    ring
  rw [mobiusThetaInternalJetStrictTailL2FourierLaplace, integral_congr_ae hfun,
    integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)]
  rw [abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]
  change (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) • (∫ x : ℝ, G x)) = _
  rw [real_smul]
  have hcancel : (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]
  rfl

/-- The Xi-jet formula is an evaluation of the actual decaying Hilbert tail. -/
theorem mobiusThetaInternalJetStrictTailL2FourierLaplace_landing
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaInternalJetStrictTailL2FourierLaplace k p m w =
      mobiusThetaStrictTailMultiplier p m w * iteratedDeriv k XiC w := by
  rw [mobiusThetaInternalJetStrictTailL2FourierLaplace_eq]
  exact mobiusThetaInternalJetStrictTailFourierLaplace_eq
    (lt_of_lt_of_le Nat.zero_lt_one p.property) k (by have := m.property; omega) hw hms

/-- The whole strict-tail Fourier--Laplace integral is absolutely admitted before evaluation. -/
theorem integrable_mobiusThetaInternalJetStrictTailFourierLaplaceIntegrand
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) (k : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * w * (x : ℂ)) *
      mobiusThetaInternalJetStrictTailSource k p m x) := by
  have hp : 0 < (p : ℕ) := lt_of_lt_of_le Nat.zero_lt_one p.property
  have hm : (m : ℕ) ≠ 0 := by have := m.property; omega
  have hs : Summable (fun j : ℕ => ∫ x : ℝ,
      ‖mobiusThetaInternalJetPrimeNormalResidualIntegrand k p m w (j + 1) x‖) :=
    (summable_nat_add_iff 1).2
      (summable_integral_norm_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp hm k hms)
  have hi := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun j => integrable_mobiusThetaInternalJetPrimeNormalResidualIntegrand hp k m hw (j + 1)) hs
  convert hi using 1
  funext x
  rw [mobiusThetaInternalJetStrictTailSource, ← tsum_mul_left]
  rfl

/-- The unpromoted representative is exactly the original physical strict tail. -/
theorem mobiusThetaStrictTailL2_ae_source
    (p : MobiusPositiveIndex) (m : MobiusHonestDepth) :
    (mobiusThetaStrictTailL2 p m : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => (2 * Real.pi : ℂ) *
        mobiusThetaInternalJetStrictTailSource 0 p m ((2 * Real.pi) * x) := by
  have hterm (j : ℕ) : mobiusThetaInternalJetPrimeNormalTailTerm 0 p m j =
      mobiusThetaPrimeNormalTailTerm p m j := by
    rw [mobiusThetaInternalJetPrimeNormalTailTerm, xiThetaInternalJetSourceL2_zero]
    rfl
  have h := mobiusThetaInternalJetStrictTailL2_ae_source p m 0
  simp_rw [hterm] at h
  rw [mobiusThetaStrictTailL2_eq_tsum]
  exact h

end
end RHTower
