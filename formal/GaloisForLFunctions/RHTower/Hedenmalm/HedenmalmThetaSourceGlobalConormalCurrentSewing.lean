import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport
import GaloisForLFunctions.HTGeometry.L2DependentOperatorFamilyCrossDisjointness
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceFunctionalEquationRootCurrentTransport

/-!
# Global conservative sewing of theta-source conormal currents

Every nonzero theta-source root current is normalized without losing its range or its exact
unnormalized value.  Functional-equation partners are placed in an oriented Hilbert `L²` double,
where reflection is a literal fibrewise unitary involution.  The resulting dependent `ell²` sum
carries one bounded global current, exact single-packet recovery, and the conservation identity
`R D R = Chi D`, with `Chi` equal to the Jordan-depth parity character.
-/

open scoped ENNReal
open Complex MeasureTheory Module.End
open GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Canonical positive normalization of one source conormal current. -/
def thetaConormalNormalization (mu : ThetaNonzeroSpectrum) : ℝ :=
  (1 + ‖thetaSourceConormalCurrentCLM mu‖)⁻¹

theorem thetaConormalNormalization_pos (mu : ThetaNonzeroSpectrum) :
    0 < thetaConormalNormalization mu := by
  unfold thetaConormalNormalization
  positivity

theorem thetaConormalNormalization_ne_zero (mu : ThetaNonzeroSpectrum) :
    thetaConormalNormalization mu ≠ 0 :=
  ne_of_gt (thetaConormalNormalization_pos mu)

/-- Bounded normalization retaining every nonzero local current. -/
def normalizedThetaSourceConormalCurrent (mu : ThetaNonzeroSpectrum) :
    ThetaRootBlock mu →L[ℂ] ThetaRootBlock mu :=
  (thetaConormalNormalization mu : ℂ) • thetaSourceConormalCurrentCLM mu

theorem normalizedThetaSourceConormalCurrent_apply (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    normalizedThetaSourceConormalCurrent mu v =
      (thetaConormalNormalization mu : ℂ) • thetaSourceConormalCurrent mu v := rfl

theorem normalizedThetaSourceConormalCurrent_ne_zero (mu : ThetaNonzeroSpectrum) :
    normalizedThetaSourceConormalCurrent mu ≠ 0 := by
  intro hzero
  apply thetaSourceConormalCurrentCLM_ne_zero mu
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun hzero v
  change (thetaConormalNormalization mu : ℂ) • thetaSourceConormalCurrent mu v = 0 at hv
  exact (smul_eq_zero.mp hv).resolve_left
    (Complex.ofReal_ne_zero.mpr (thetaConormalNormalization_ne_zero mu))

theorem norm_normalizedThetaSourceConormalCurrent_le_one (mu : ThetaNonzeroSpectrum) :
    ‖normalizedThetaSourceConormalCurrent mu‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [normalizedThetaSourceConormalCurrent_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (thetaConormalNormalization_pos mu), one_mul]
  calc
    thetaConormalNormalization mu * ‖thetaSourceConormalCurrent mu v‖ ≤
        thetaConormalNormalization mu *
          (‖thetaSourceConormalCurrentCLM mu‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        ((thetaSourceConormalCurrentCLM mu).le_opNorm v)
        (thetaConormalNormalization_pos mu).le
    _ = (thetaConormalNormalization mu *
        ‖thetaSourceConormalCurrentCLM mu‖) * ‖v‖ := by ring
    _ ≤ ‖v‖ := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (show
          thetaConormalNormalization mu * ‖thetaSourceConormalCurrentCLM mu‖ ≤ 1 by
            unfold thetaConormalNormalization
            rw [inv_mul_le_one₀ (by positivity)]
            linarith [norm_nonneg (thetaSourceConormalCurrentCLM mu)]) (norm_nonneg v))

/-- Normalization preserves the exact recovered eigenline. -/
theorem range_normalizedThetaSourceConormalCurrent (mu : ThetaNonzeroSpectrum) :
    LinearMap.range (normalizedThetaSourceConormalCurrent mu).toLinearMap =
      LinearMap.ker (thetaRootNilpotentPart mu) := by
  change LinearMap.range
      ((thetaConormalNormalization mu : ℂ) • thetaSourceConormalCurrent mu) = _
  rw [LinearMap.range_smul _ _
    (Complex.ofReal_ne_zero.mpr (thetaConormalNormalization_ne_zero mu))]
  exact range_thetaSourceConormalCurrent mu

theorem thetaConormalNormalization_reflection (mu : ThetaNonzeroSpectrum) :
    thetaConormalNormalization (thetaSpectrumNeg mu) = thetaConormalNormalization mu := by
  unfold thetaConormalNormalization
  rw [norm_thetaSourceConormalCurrentCLM_reflection]

/-- Functional-equation character carried by the terminal Jordan current. -/
def thetaDepthCharacter (mu : ThetaNonzeroSpectrum) : ℂ :=
  (-1 : ℂ) ^ (Module.finrank ℂ (ThetaRootBlock mu) - 1)

@[simp] theorem norm_thetaDepthCharacter (mu : ThetaNonzeroSpectrum) :
    ‖thetaDepthCharacter mu‖ = 1 := by
  simp [thetaDepthCharacter]

@[simp] theorem thetaDepthCharacter_reflection (mu : ThetaNonzeroSpectrum) :
    thetaDepthCharacter (thetaSpectrumNeg mu) = thetaDepthCharacter mu := by
  unfold thetaDepthCharacter
  rw [finrank_thetaRootBlock_reflection]

theorem thetaDepthCharacter_at_XiSupport (rho : XiDivisorSupport) :
    thetaDepthCharacter (thetaSpectrumOfXiSupport rho) =
      (-1 : ℂ) ^ (xiSupportMultiplicity rho - 1) := by
  unfold thetaDepthCharacter
  rw [finrank_thetaRootBlock_at_XiSupport]

theorem normalizedThetaSourceConormalCurrent_reflection (mu : ThetaNonzeroSpectrum)
    (v : ThetaRootBlock mu) :
    normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu)
        (thetaRootBlockReflectionLIE mu v) =
      thetaDepthCharacter mu • thetaRootBlockReflectionLIE mu
        (normalizedThetaSourceConormalCurrent mu v) := by
  rw [normalizedThetaSourceConormalCurrent_apply,
    normalizedThetaSourceConormalCurrent_apply,
    thetaConormalNormalization_reflection,
    thetaSourceConormalCurrent_reflection]
  simp only [thetaDepthCharacter, map_smul]
  module

theorem normalizedThetaSourceConormalCurrent_conjugated_reflection
    (mu : ThetaNonzeroSpectrum) (v : ThetaRootBlock mu) :
    (thetaRootBlockReflectionLIE mu).symm
        (normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu)
          (thetaRootBlockReflectionLIE mu v)) =
      thetaDepthCharacter mu • normalizedThetaSourceConormalCurrent mu v := by
  rw [normalizedThetaSourceConormalCurrent_reflection]
  simp

theorem thetaDepthCharacter_sq (mu : ThetaNonzeroSpectrum) :
    thetaDepthCharacter mu * thetaDepthCharacter mu = 1 := by
  unfold thetaDepthCharacter
  rw [← pow_add]
  conv_lhs =>
    rw [show (Module.finrank ℂ (ThetaRootBlock mu) - 1) +
        (Module.finrank ℂ (ThetaRootBlock mu) - 1) =
        2 * (Module.finrank ℂ (ThetaRootBlock mu) - 1) by omega]
  rw [pow_mul]
  norm_num

/-- One oriented functional-equation orbit.  The `L²` double makes reflection internal. -/
abbrev ThetaReflectionPairFiber (mu : ThetaNonzeroSpectrum) :=
  WithLp 2 (ThetaRootBlock mu × ThetaRootBlock (thetaSpectrumNeg mu))

def thetaReflectionPairLIE (mu : ThetaNonzeroSpectrum) :
    ThetaReflectionPairFiber mu ≃ₗᵢ[ℂ] ThetaReflectionPairFiber mu :=
  (LinearIsometryEquiv.withLpProdCongr (p := 2)
      (thetaRootBlockReflectionLIE mu)
      (thetaRootBlockReflectionLIE mu).symm).trans
    (LinearIsometryEquiv.withLpProdComm 2 ℂ
      (ThetaRootBlock (thetaSpectrumNeg mu)) (ThetaRootBlock mu))

@[simp] theorem thetaReflectionPairLIE_apply (mu : ThetaNonzeroSpectrum)
    (p : ThetaReflectionPairFiber mu) :
    thetaReflectionPairLIE mu p =
      WithLp.toLp 2 ((thetaRootBlockReflectionLIE mu).symm p.snd,
        thetaRootBlockReflectionLIE mu p.fst) := rfl

def normalizedThetaReflectionPairCurrentLM (mu : ThetaNonzeroSpectrum) :
    ThetaReflectionPairFiber mu →ₗ[ℂ] ThetaReflectionPairFiber mu where
  toFun p := WithLp.toLp 2
    (normalizedThetaSourceConormalCurrent mu p.fst,
      normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) p.snd)
  map_add' p q := by
    rw [WithLp.ext_iff]
    apply Prod.ext <;> simp
  map_smul' c p := by
    rw [WithLp.ext_iff]
    apply Prod.ext <;> simp

@[simp] theorem normalizedThetaReflectionPairCurrentLM_apply
    (mu : ThetaNonzeroSpectrum) (p : ThetaReflectionPairFiber mu) :
    normalizedThetaReflectionPairCurrentLM mu p = WithLp.toLp 2
      (normalizedThetaSourceConormalCurrent mu p.fst,
        normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) p.snd) := rfl

theorem norm_normalizedThetaReflectionPairCurrentLM_le
    (mu : ThetaNonzeroSpectrum) (p : ThetaReflectionPairFiber mu) :
    ‖normalizedThetaReflectionPairCurrentLM mu p‖ ≤ ‖p‖ := by
  have hfst : ‖normalizedThetaSourceConormalCurrent mu p.fst‖ ≤ ‖p.fst‖ :=
    calc
      _ ≤ ‖normalizedThetaSourceConormalCurrent mu‖ * ‖p.fst‖ :=
        (normalizedThetaSourceConormalCurrent mu).le_opNorm p.fst
      _ ≤ 1 * ‖p.fst‖ := mul_le_mul_of_nonneg_right
        (norm_normalizedThetaSourceConormalCurrent_le_one mu) (norm_nonneg _)
      _ = _ := one_mul _
  have hsnd :
      ‖normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) p.snd‖ ≤ ‖p.snd‖ :=
    calc
      _ ≤ ‖normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu)‖ * ‖p.snd‖ :=
        (normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu)).le_opNorm p.snd
      _ ≤ 1 * ‖p.snd‖ := mul_le_mul_of_nonneg_right
        (norm_normalizedThetaSourceConormalCurrent_le_one (thetaSpectrumNeg mu)) (norm_nonneg _)
      _ = _ := one_mul _
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  simp only [normalizedThetaReflectionPairCurrentLM_apply,
    WithLp.toLp_fst, WithLp.toLp_snd]
  exact add_le_add
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hfst)
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hsnd)

def normalizedThetaReflectionPairCurrent (mu : ThetaNonzeroSpectrum) :
    ThetaReflectionPairFiber mu →L[ℂ] ThetaReflectionPairFiber mu :=
  LinearMap.mkContinuous (normalizedThetaReflectionPairCurrentLM mu) 1
    (fun p => by simpa using norm_normalizedThetaReflectionPairCurrentLM_le mu p)

@[simp] theorem normalizedThetaReflectionPairCurrent_apply
    (mu : ThetaNonzeroSpectrum) (p : ThetaReflectionPairFiber mu) :
    normalizedThetaReflectionPairCurrent mu p = WithLp.toLp 2
      (normalizedThetaSourceConormalCurrent mu p.fst,
        normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) p.snd) := rfl

theorem norm_normalizedThetaReflectionPairCurrent_le_one (mu : ThetaNonzeroSpectrum) :
    ‖normalizedThetaReflectionPairCurrent mu‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  simpa using norm_normalizedThetaReflectionPairCurrentLM_le mu p

/-- Exact local reflection law on an oriented source orbit. -/
theorem normalizedThetaReflectionPairCurrent_covariant
    (mu : ThetaNonzeroSpectrum) (p : ThetaReflectionPairFiber mu) :
    thetaReflectionPairLIE mu
        (normalizedThetaReflectionPairCurrent mu (thetaReflectionPairLIE mu p)) =
      thetaDepthCharacter mu • normalizedThetaReflectionPairCurrent mu p := by
  rw [WithLp.ext_iff]
  apply Prod.ext
  · exact normalizedThetaSourceConormalCurrent_conjugated_reflection mu p.fst
  · have h := normalizedThetaSourceConormalCurrent_reflection mu
        ((thetaRootBlockReflectionLIE mu).symm p.snd)
    rw [(thetaRootBlockReflectionLIE mu).apply_symm_apply] at h
    symm
    calc
      thetaDepthCharacter mu •
          normalizedThetaSourceConormalCurrent (thetaSpectrumNeg mu) p.snd =
          thetaDepthCharacter mu •
            (thetaDepthCharacter mu • thetaRootBlockReflectionLIE mu
              (normalizedThetaSourceConormalCurrent mu
                ((thetaRootBlockReflectionLIE mu).symm p.snd))) := by rw [← h]
      _ = (thetaDepthCharacter mu * thetaDepthCharacter mu) •
            thetaRootBlockReflectionLIE mu
              (normalizedThetaSourceConormalCurrent mu
                ((thetaRootBlockReflectionLIE mu).symm p.snd)) := by rw [smul_smul]
      _ = thetaRootBlockReflectionLIE mu
              (normalizedThetaSourceConormalCurrent mu
                ((thetaRootBlockReflectionLIE mu).symm p.snd)) := by
            rw [thetaDepthCharacter_sq, one_smul]

/-- Global Hilbert formation space containing all oriented nonzero source orbits. -/
abbrev ThetaSourceGlobalConormalSpace :=
  L2DependentSum ThetaNonzeroSpectrum (fun mu => ThetaReflectionPairFiber mu)

/-- Information-neutral global functional-equation action. -/
def thetaSourceGlobalReflection :
    ThetaSourceGlobalConormalSpace →ₗᵢ[ℂ] ThetaSourceGlobalConormalSpace :=
  lpFamilyIsometry (𝕜 := ℂ) (p := 2)
    (E := fun mu => ThetaReflectionPairFiber mu)
    (F := fun mu => ThetaReflectionPairFiber mu) (by norm_num)
    (fun mu => (thetaReflectionPairLIE mu).toLinearIsometry)

@[simp] theorem thetaSourceGlobalReflection_apply
    (f : ThetaSourceGlobalConormalSpace) (mu : ThetaNonzeroSpectrum) :
    thetaSourceGlobalReflection f mu = thetaReflectionPairLIE mu (f mu) := rfl

theorem thetaReflectionPairLIE_involutive (mu : ThetaNonzeroSpectrum)
    (p : ThetaReflectionPairFiber mu) :
    thetaReflectionPairLIE mu (thetaReflectionPairLIE mu p) = p := by
  rw [WithLp.ext_iff]
  apply Prod.ext <;> simp [thetaReflectionPairLIE_apply]

theorem thetaSourceGlobalReflection_involutive (f : ThetaSourceGlobalConormalSpace) :
    thetaSourceGlobalReflection (thetaSourceGlobalReflection f) = f := by
  apply lp.ext
  funext mu
  exact thetaReflectionPairLIE_involutive mu (f mu)

theorem norm_thetaSourceGlobalReflection (f : ThetaSourceGlobalConormalSpace) :
    ‖thetaSourceGlobalReflection f‖ = ‖f‖ :=
  thetaSourceGlobalReflection.norm_map f

/-- One uniformly bounded diagonal current on the complete source-history formation space. -/
def thetaSourceGlobalConormalCurrent :
    ThetaSourceGlobalConormalSpace →L[ℂ] ThetaSourceGlobalConormalSpace :=
  l2DependentDiagonal normalizedThetaReflectionPairCurrent 1 (by norm_num)
    norm_normalizedThetaReflectionPairCurrent_le_one

@[simp] theorem thetaSourceGlobalConormalCurrent_apply
    (f : ThetaSourceGlobalConormalSpace) (mu : ThetaNonzeroSpectrum) :
    thetaSourceGlobalConormalCurrent f mu =
      normalizedThetaReflectionPairCurrent mu (f mu) := rfl

def thetaDepthCharacterLI (mu : ThetaNonzeroSpectrum) :
    ThetaReflectionPairFiber mu →ₗᵢ[ℂ] ThetaReflectionPairFiber mu where
  toFun := fun v => thetaDepthCharacter mu • v
  map_add' v w := smul_add _ _ _
  map_smul' c v := by simp [smul_smul, mul_comm]
  norm_map' v := by
    change ‖thetaDepthCharacter mu • v‖ = ‖v‖
    rw [norm_smul, norm_thetaDepthCharacter, one_mul]

def thetaSourceGlobalDepthCharacter :
    ThetaSourceGlobalConormalSpace →ₗᵢ[ℂ] ThetaSourceGlobalConormalSpace :=
  lpFamilyIsometry (𝕜 := ℂ) (p := 2)
    (E := fun mu => ThetaReflectionPairFiber mu)
    (F := fun mu => ThetaReflectionPairFiber mu) (by norm_num) thetaDepthCharacterLI

@[simp] theorem thetaSourceGlobalDepthCharacter_apply
    (f : ThetaSourceGlobalConormalSpace) (mu : ThetaNonzeroSpectrum) :
    thetaSourceGlobalDepthCharacter f mu = thetaDepthCharacter mu • f mu := rfl

/-- Global functional-equation conservation: reflection changes only the depth character. -/
theorem thetaSourceGlobalConservation (f : ThetaSourceGlobalConormalSpace) :
    thetaSourceGlobalReflection
        (thetaSourceGlobalConormalCurrent (thetaSourceGlobalReflection f)) =
      thetaSourceGlobalDepthCharacter (thetaSourceGlobalConormalCurrent f) := by
  apply lp.ext
  funext mu
  rw [thetaSourceGlobalReflection_apply,
    thetaSourceGlobalConormalCurrent_apply,
    thetaSourceGlobalReflection_apply,
    thetaSourceGlobalDepthCharacter_apply,
    thetaSourceGlobalConormalCurrent_apply]
  exact normalizedThetaReflectionPairCurrent_covariant mu (f mu)

theorem thetaSourceGlobalConormalCurrent_single
    (mu : ThetaNonzeroSpectrum) (v : ThetaReflectionPairFiber mu) :
    thetaSourceGlobalConormalCurrent (l2DependentSingle mu v) =
      l2DependentSingle mu (normalizedThetaReflectionPairCurrent mu v) := by
  classical
  apply lp.ext
  funext j
  rw [thetaSourceGlobalConormalCurrent_apply]
  simp only [l2DependentSingle_apply, lp.single_apply]
  by_cases h : j = mu
  · subst j
    simp
  · rw [Pi.single_eq_of_ne h, map_zero, Pi.single_eq_of_ne h]

/-- Multiplying the recovered normalized coordinate by its known denominator returns the original
unnormalized conormal current exactly. -/
theorem thetaSourceGlobalConormalCurrent_exact_recovery
    (mu : ThetaNonzeroSpectrum) (v : ThetaRootBlock mu) :
    ((1 + ‖thetaSourceConormalCurrentCLM mu‖ : ℝ) : ℂ) •
        (l2DependentCoordinate mu
          (thetaSourceGlobalConormalCurrent (l2DependentSingle mu
            (WithLp.toLp 2 (v, 0))))).fst =
      thetaSourceConormalCurrent mu v := by
  rw [thetaSourceGlobalConormalCurrent_single, l2DependentCoordinate_apply]
  rw [l2DependentSingle_apply, lp.single_apply_self]
  change ((1 + ‖thetaSourceConormalCurrentCLM mu‖ : ℝ) : ℂ) •
      normalizedThetaSourceConormalCurrent mu v = thetaSourceConormalCurrent mu v
  rw [normalizedThetaSourceConormalCurrent_apply, smul_smul]
  rw [show (((1 + ‖thetaSourceConormalCurrentCLM mu‖ : ℝ) : ℂ) *
      (thetaConormalNormalization mu : ℂ)) = 1 by
    rw [← Complex.ofReal_mul]
    norm_cast
    unfold thetaConormalNormalization
    exact mul_inv_cancel₀ (by positivity)]
  simp

/-- Every supplied spectral fibre witnesses nonvanishing of the global current. -/
theorem thetaSourceGlobalConormalCurrent_ne_zero
    (mu : ThetaNonzeroSpectrum) : thetaSourceGlobalConormalCurrent ≠ 0 := by
  intro hzero
  apply normalizedThetaSourceConormalCurrent_ne_zero mu
  apply ContinuousLinearMap.ext
  intro v
  have hsingle := DFunLike.congr_fun hzero
    (l2DependentSingle mu (WithLp.toLp 2 (v, 0)))
  have hcoordinate := congrArg (fun f : ThetaSourceGlobalConormalSpace => (f mu).fst) hsingle
  rw [thetaSourceGlobalConormalCurrent_apply, l2DependentSingle_apply,
    lp.single_apply_self] at hcoordinate
  change normalizedThetaSourceConormalCurrent mu v = 0 at hcoordinate
  exact hcoordinate

end

end RHTower.HedenmalmThetaSource
