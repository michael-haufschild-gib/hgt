import GaloisForLFunctions.RHTower.DeBrangesExplicitGammaGauge
import GaloisForLFunctions.RHTower.L2MellinUnitary
import GaloisForLFunctions.RHTower.HardyTitchmarshEulerConcrete
import GaloisForLFunctions.RHTower.SuzukiPositiveHalfLine
import GaloisForLFunctions.HTGeometry.UnitaryOrbitGeometry
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicExponentialPencil
import GaloisForLFunctions.HTGeometry.MeroExponentialGauge

/-!
# Mellin-dilation hypertranscendental unitary saturation

The odd reciprocal-Gamma phase
`q(z) = Γ(z)⁻¹ - Γ(-z)⁻¹` is entire and hypertranscendental.  Its exponential
phases form a continuum one-parameter group of unimodular zero-free entire HT multipliers.

Multiplication by these phases on the Mellin spectral line, and its conjugates on multiplicative
Haar, even Lebesgue, and literal positive-ray Lebesgue `L²`, commutes with every positive
dilation.  The commuting-unitary orbit infrastructure then gives exact preservation of marked
closed cyclic subspaces, closure membership, approximation distance, cyclicity, and every finite
Gram determinant.  Finally, the DA cancellation theorem shows that a fixed nonzero entire base
has at most one exceptional phase parameter, so every countable marked family is simultaneously
HT outside one countable union.
-/

open Set Complex
open MeasureTheory
open scoped ENNReal InnerProductSpace Differential UnivMeroFieldInstances

namespace GaloisForLFunctions.RHTower

open HTGeometry
open Bottcher
open HTGeometry.FixedModulusRealRootedness
open _root_.HTGeometry

noncomputable section

def mellinOddReciprocalGammaPhase (z : ℂ) : ℂ :=
  reciprocalGammaEntire z - reciprocalGammaEntire (-z)

def mellinOddReciprocalGammaProduct (z : ℂ) : ℂ :=
  z ^ 2 * sincProduct z

theorem analyticOnNhd_mellinOddReciprocalGammaPhase :
    AnalyticOnNhd ℂ mellinOddReciprocalGammaPhase Set.univ := by
  apply analyticOnNhd_reciprocalGammaEntire.sub
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact contDiff_reciprocalGammaEntire.differentiable (by simp) |>.comp (by fun_prop)

theorem analyticOnNhd_mellinOddReciprocalGammaProduct :
    AnalyticOnNhd ℂ mellinOddReciprocalGammaProduct Set.univ := by
  exact analyticOnNhd_id.pow 2 |>.mul analyticOnNhd_sincProduct

theorem differentiallyAlgebraic_mellinOddReciprocalGammaProduct :
    DifferentiallyAlgebraic mellinOddReciprocalGammaProduct := by
  exact differentiallyAlgebraic_mul
    (analyticOnNhd_id.pow 2) analyticOnNhd_sincProduct
    (differentiallyAlgebraic_pow analyticOnNhd_id
      (by simpa using differentiallyAlgebraic_polynomial Polynomial.X) 2)
    differentiallyAlgebraic_sincProduct

theorem reciprocalGammaEntire_mul_neg_eq_mellinOddReciprocalGammaProduct (z : ℂ) :
    reciprocalGammaEntire z * reciprocalGammaEntire (-z) =
      -mellinOddReciprocalGammaProduct z := by
  have href := reciprocalGammaEntire_mul_one_sub (-z)
  have href' : reciprocalGammaEntire (-z) * reciprocalGammaEntire (z + 1) =
      -(Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) := by
    simpa [sub_neg_eq_add, add_comm, mul_neg, Complex.sin_neg, neg_div] using href
  have hrec : reciprocalGammaEntire z = z * reciprocalGammaEntire (z + 1) := by
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  rw [hrec]
  rw [mul_assoc, mul_comm (reciprocalGammaEntire (z + 1)) (reciprocalGammaEntire (-z))]
  rw [href']
  rw [mellinOddReciprocalGammaProduct]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) = z * sincProduct z by
    apply (mul_left_cancel₀ hpi)
    rw [mul_div_cancel₀ _ hpi, ← pi_mul_sincProduct]
    ring]
  ring

theorem hypertranscendental_mellinOddReciprocalGammaPhase :
    Hypertranscendental mellinOddReciprocalGammaPhase := by
  intro hqDA
  apply hypertranscendental_reciprocalGammaEntire
  exact differentiallyAlgebraic_of_quadratic_relation
    analyticOnNhd_reciprocalGammaEntire
    analyticOnNhd_mellinOddReciprocalGammaPhase
    analyticOnNhd_mellinOddReciprocalGammaProduct
    (fun z => by
      rw [mellinOddReciprocalGammaPhase]
      have hp := reciprocalGammaEntire_mul_neg_eq_mellinOddReciprocalGammaProduct z
      calc
        reciprocalGammaEntire z ^ 2 -
              (reciprocalGammaEntire z - reciprocalGammaEntire (-z)) *
                reciprocalGammaEntire z + mellinOddReciprocalGammaProduct z =
            reciprocalGammaEntire z * reciprocalGammaEntire (-z) -
              (-mellinOddReciprocalGammaProduct z) := by ring
        _ = 0 := by rw [hp]; ring)
    hqDA differentiallyAlgebraic_mellinOddReciprocalGammaProduct

@[simp] theorem mellinOddReciprocalGammaPhase_neg (z : ℂ) :
    mellinOddReciprocalGammaPhase (-z) = -mellinOddReciprocalGammaPhase z := by
  simp [mellinOddReciprocalGammaPhase]

theorem mellinOddReciprocalGammaPhase_conj (z : ℂ) :
    mellinOddReciprocalGammaPhase ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (mellinOddReciprocalGammaPhase z) := by
  simp only [mellinOddReciprocalGammaPhase, map_sub]
  rw [← reciprocalGammaEntire_conj z, ← reciprocalGammaEntire_conj (-z)]
  simp

def mellinHTPhase (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (c : ℂ) * mellinOddReciprocalGammaPhase z)

theorem analyticOnNhd_mellinHTPhase (c : ℝ) :
    AnalyticOnNhd ℂ (mellinHTPhase c) Set.univ := by
  exact (analyticOnNhd_const.mul analyticOnNhd_mellinOddReciprocalGammaPhase).cexp

theorem zeroFree_mellinHTPhase (c : ℝ) (z : ℂ) : mellinHTPhase c z ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem mellinHTPhase_zero (z : ℂ) : mellinHTPhase 0 z = 1 := by
  simp [mellinHTPhase]

theorem mellinHTPhase_add (c d : ℝ) (z : ℂ) :
    mellinHTPhase (c + d) z = mellinHTPhase c z * mellinHTPhase d z := by
  rw [mellinHTPhase, mellinHTPhase, mellinHTPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mellinHTPhase_neg_argument (c : ℝ) (z : ℂ) :
    mellinHTPhase c (-z) = (mellinHTPhase c z)⁻¹ := by
  change Complex.exp (Complex.I * (c : ℂ) * mellinOddReciprocalGammaPhase (-z)) =
    (Complex.exp (Complex.I * (c : ℂ) * mellinOddReciprocalGammaPhase z))⁻¹
  rw [mellinOddReciprocalGammaPhase_neg, mul_neg, Complex.exp_neg]

theorem hypertranscendental_mellinHTPhase {c : ℝ} (hc : c ≠ 0) :
    Hypertranscendental (mellinHTPhase c) := by
  have hic : Complex.I * (c : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr hc)
  change Hypertranscendental
    (fun z => Complex.exp (Complex.I * (c : ℂ) * mellinOddReciprocalGammaPhase z))
  exact
    (hypertranscendental_cexp_const_mul_iff
      analyticOnNhd_mellinOddReciprocalGammaPhase hic).2
      hypertranscendental_mellinOddReciprocalGammaPhase

theorem mellinOddReciprocalGammaPhase_real (t : ℝ) :
    (starRingEnd ℂ) (mellinOddReciprocalGammaPhase (t : ℂ)) =
      mellinOddReciprocalGammaPhase (t : ℂ) := by
  rw [← mellinOddReciprocalGammaPhase_conj]
  simp

theorem mellinHTPhase_real_conj (c t : ℝ) :
    (starRingEnd ℂ) (mellinHTPhase c (t : ℂ)) =
      mellinHTPhase c (-(t : ℂ)) := by
  rw [mellinHTPhase, ← Complex.exp_conj, map_mul, map_mul]
  simp [mellinOddReciprocalGammaPhase_real, mellinHTPhase,
    mellinOddReciprocalGammaPhase_neg]

@[simp] theorem norm_mellinHTPhase_real (c t : ℝ) :
    ‖mellinHTPhase c (t : ℂ)‖ = 1 := by
  unfold mellinHTPhase
  rw [Complex.norm_exp]
  have hreal := mellinOddReciprocalGammaPhase_real t
  have him : (mellinOddReciprocalGammaPhase (t : ℂ)).im = 0 := by
    have himEq := congrArg Complex.im hreal
    simp at himEq
    linarith
  simp [mul_re, him]

theorem mellinHTPhase_mul_preserves_spectralReality
    (c : ℝ) {G : ℝ → ℂ}
    (hG : ∀ t, G (-t) = (starRingEnd ℂ) (G t)) (t : ℝ) :
    mellinHTPhase c (-(t : ℂ)) * G (-t) =
      (starRingEnd ℂ) (mellinHTPhase c (t : ℂ) * G t) := by
  rw [hG, map_mul, mellinHTPhase_real_conj]

theorem mellinHTPhase_injective : Function.Injective mellinHTPhase := by
  intro c d hcd
  by_contra hne
  have hdiff : c - d ≠ 0 := sub_ne_zero.mpr hne
  have hfun : mellinHTPhase (c - d) = 1 := by
    funext z
    have hz := congrFun hcd z
    have hdne := zeroFree_mellinHTPhase d z
    have hadd := mellinHTPhase_add (c - d) d z
    rw [sub_add_cancel] at hadd
    apply mul_right_cancel₀ hdne
    simpa using (hadd.symm.trans hz)
  exact hypertranscendental_mellinHTPhase hdiff (by
    rw [hfun]
    change DifferentiallyAlgebraic (fun _ : ℂ => (1 : ℂ))
    exact differentiallyAlgebraic_const 1)

/-- The explicit phase group has exactly continuum cardinality. -/
theorem cardinal_range_mellinHTPhase_eq_continuum :
    Cardinal.mk (Set.range mellinHTPhase) = Cardinal.continuum := by
  rw [Cardinal.mk_range_eq _ mellinHTPhase_injective, Cardinal.mk_real]

/-! Spectral and physical Hilbert-space unitaries. -/

theorem continuous_mellinHTPhase_real (c : ℝ) :
    Continuous (fun t : ℝ => mellinHTPhase c (t : ℂ)) := by
  have hdiff : Differentiable ℂ (mellinHTPhase c) := by
    rw [← Complex.analyticOnNhd_univ_iff_differentiable]
    exact analyticOnNhd_mellinHTPhase c
  exact hdiff.continuous.comp Complex.continuous_ofReal

theorem memLp_mellinHTPhase_mul (c : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    MemLp (fun t : ℝ => mellinHTPhase c (t : ℂ) * f t) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).congr_norm
  · exact (continuous_mellinHTPhase_real c).aestronglyMeasurable.mul (Lp.memLp f).1
  · filter_upwards with t
    simp

def mellinHTPhaseMulAux (c : ℝ) (f : Lp (α := ℝ) ℂ 2) : Lp (α := ℝ) ℂ 2 :=
  (memLp_mellinHTPhase_mul c f).toLp _

theorem mellinHTPhaseMulAux_ae (c : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulAux c f =ᵐ[volume]
      fun t => mellinHTPhase c (t : ℂ) * f t :=
  (memLp_mellinHTPhase_mul c f).coeFn_toLp

def mellinHTPhaseMulLinear (c : ℝ) :
    Lp (α := ℝ) ℂ 2 →ₗ[ℂ] Lp (α := ℝ) ℂ 2 where
  toFun := mellinHTPhaseMulAux c
  map_add' f g := by
    apply Lp.ext
    filter_upwards [mellinHTPhaseMulAux_ae c (f + g),
      mellinHTPhaseMulAux_ae c f, mellinHTPhaseMulAux_ae c g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (mellinHTPhaseMulAux c f) (mellinHTPhaseMulAux c g)]
      with t hfg hf hg hadd hout
    rw [hfg, hout]
    change mellinHTPhase c (t : ℂ) * (f + g : Lp (α := ℝ) ℂ 2) t =
      mellinHTPhaseMulAux c f t + mellinHTPhaseMulAux c g t
    rw [hadd, hf, hg]
    simp only [Pi.add_apply]
    ring
  map_smul' a f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [mellinHTPhaseMulAux_ae c (a • f),
      mellinHTPhaseMulAux_ae c f, Lp.coeFn_smul a f,
      Lp.coeFn_smul a (mellinHTPhaseMulAux c f)] with t haf hf hin hout
    rw [haf, hout]
    change mellinHTPhase c (t : ℂ) * (a • f : Lp (α := ℝ) ℂ 2) t =
      a • mellinHTPhaseMulAux c f t
    rw [hin, hf]
    change mellinHTPhase c (t : ℂ) * (a * f t) =
      a * (mellinHTPhase c (t : ℂ) * f t)
    ring

theorem norm_mellinHTPhaseMulAux (c : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    ‖mellinHTPhaseMulAux c f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (mellinHTPhaseMulAux_ae c f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with t
  simp

def mellinHTPhaseMulIsometry (c : ℝ) :
    Lp (α := ℝ) ℂ 2 →ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 where
  __ := mellinHTPhaseMulLinear c
  norm_map' := norm_mellinHTPhaseMulAux c

theorem mellinHTPhase_neg_parameter_mul (c : ℝ) (z : ℂ) :
    mellinHTPhase (-c) z * mellinHTPhase c z = 1 := by
  have h := mellinHTPhase_add (-c) c z
  simpa using h.symm

/-- Multiplication by the reciprocal-Gamma phase on the Mellin spectral line. -/
def mellinHTPhaseMulUnitary (c : ℝ) :
    Lp (α := ℝ) ℂ 2 ≃ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 where
  __ := mellinHTPhaseMulIsometry c
  invFun := mellinHTPhaseMulAux (-c)
  left_inv f := by
    change mellinHTPhaseMulAux (-c) (mellinHTPhaseMulAux c f) = f
    apply Lp.ext
    filter_upwards [mellinHTPhaseMulAux_ae c f,
      mellinHTPhaseMulAux_ae (-c) (mellinHTPhaseMulAux c f)] with t hf hout
    rw [hout, hf, ← mul_assoc, mellinHTPhase_neg_parameter_mul, one_mul]
  right_inv f := by
    change mellinHTPhaseMulAux c (mellinHTPhaseMulAux (-c) f) = f
    apply Lp.ext
    filter_upwards [mellinHTPhaseMulAux_ae (-c) f,
      mellinHTPhaseMulAux_ae c (mellinHTPhaseMulAux (-c) f)] with t hf hout
    rw [hout, hf]
    have h := mellinHTPhase_neg_parameter_mul c (t : ℂ)
    rw [← mul_assoc, mul_comm (mellinHTPhase c (t : ℂ))
      (mellinHTPhase (-c) (t : ℂ)), h, one_mul]

theorem mellinHTPhaseMulUnitary_ae (c : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulUnitary c f =ᵐ[volume]
      fun t => mellinHTPhase c (t : ℂ) * f t :=
  mellinHTPhaseMulAux_ae c f

theorem mellinHTPhaseMulUnitary_zero (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulUnitary 0 f = f := by
  apply Lp.ext
  filter_upwards [mellinHTPhaseMulUnitary_ae 0 f] with t ht
  rw [ht]
  simp

theorem mellinHTPhaseMulUnitary_add (c d : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulUnitary (c + d) f =
      mellinHTPhaseMulUnitary c (mellinHTPhaseMulUnitary d f) := by
  apply Lp.ext
  filter_upwards [mellinHTPhaseMulUnitary_ae (c + d) f,
    mellinHTPhaseMulUnitary_ae d f,
    mellinHTPhaseMulUnitary_ae c (mellinHTPhaseMulUnitary d f)] with t hout hd hc
  rw [hout, hc, hd, mellinHTPhase_add]
  ring

theorem mellinHTPhaseMulUnitary_commutes_fourierPhase (c a : ℝ)
    (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulUnitary c (_root_.RHTower.MellinL2.fourierPhaseMulUnitary a f) =
      _root_.RHTower.MellinL2.fourierPhaseMulUnitary a (mellinHTPhaseMulUnitary c f) := by
  change mellinHTPhaseMulAux c (_root_.RHTower.MellinL2.fourierPhaseMulAux a f) =
    _root_.RHTower.MellinL2.fourierPhaseMulAux a (mellinHTPhaseMulAux c f)
  apply Lp.ext
  filter_upwards [mellinHTPhaseMulAux_ae c
      (_root_.RHTower.MellinL2.fourierPhaseMulAux a f),
    _root_.RHTower.MellinL2.fourierPhaseMulAux_ae a f,
    _root_.RHTower.MellinL2.fourierPhaseMulAux_ae a (mellinHTPhaseMulAux c f),
    mellinHTPhaseMulAux_ae c f] with t hl hf hr hc
  rw [hl, hf, hr, hc]
  ring

/-- Mellin conjugate of the spectral HT phase. -/
def mellinHTPhysicalUnitary (c : ℝ) :
    Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar ≃ₗᵢ[ℂ]
      Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar :=
  _root_.RHTower.MellinL2.mellinUnitary.trans
    ((mellinHTPhaseMulUnitary c).trans _root_.RHTower.MellinL2.mellinUnitary.symm)

theorem mellinHTPhysicalUnitary_zero
    (f : Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar) :
    mellinHTPhysicalUnitary 0 f = f := by
  unfold mellinHTPhysicalUnitary
  simp only [LinearIsometryEquiv.trans_apply, mellinHTPhaseMulUnitary_zero,
    _root_.RHTower.MellinL2.mellinUnitary.symm_apply_apply]

theorem mellinHTPhysicalUnitary_add (c d : ℝ)
    (f : Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar) :
    mellinHTPhysicalUnitary (c + d) f =
      mellinHTPhysicalUnitary c (mellinHTPhysicalUnitary d f) := by
  apply _root_.RHTower.MellinL2.mellinUnitary.injective
  unfold mellinHTPhysicalUnitary
  simp only [LinearIsometryEquiv.trans_apply,
    _root_.RHTower.MellinL2.mellinUnitary.apply_symm_apply]
  rw [mellinHTPhaseMulUnitary_add]

/-- The physical HT gauge commutes with every positive logarithmic dilation. -/
theorem mellinHTPhysicalUnitary_commutes_positiveScale (c a : ℝ)
    (f : Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar) :
    mellinHTPhysicalUnitary c (_root_.RHTower.MellinL2.positiveScaleUnitary a f) =
      _root_.RHTower.MellinL2.positiveScaleUnitary a (mellinHTPhysicalUnitary c f) := by
  unfold mellinHTPhysicalUnitary
  simp only [LinearIsometryEquiv.trans_apply]
  apply _root_.RHTower.MellinL2.mellinUnitary.injective
  rw [_root_.RHTower.MellinL2.mellinUnitary.apply_symm_apply]
  change mellinHTPhaseMulUnitary c
      (_root_.RHTower.MellinL2.mellinUnitary
        (_root_.RHTower.MellinL2.positiveScaleUnitary a f)) =
    _root_.RHTower.MellinL2.mellinUnitary
      (_root_.RHTower.MellinL2.positiveScaleUnitary a
        (_root_.RHTower.MellinL2.mellinUnitary.symm
          (mellinHTPhaseMulUnitary c (_root_.RHTower.MellinL2.mellinUnitary f))))
  rw [_root_.RHTower.MellinL2.mellin_positiveScale,
    _root_.RHTower.MellinL2.mellin_positiveScale,
    _root_.RHTower.MellinL2.mellinUnitary.apply_symm_apply]
  exact mellinHTPhaseMulUnitary_commutes_fourierPhase c
    (a * _root_.RHTower.MellinL2.spectralNormalization)
    (_root_.RHTower.MellinL2.mellinUnitary f)

/-! Literal normalized `L²((0,∞), dx)` carrier. -/

def mellinHTEvenPhysicalUnitary (c : ℝ) :
    _root_.RHTower.evenSubspace ≃ₗᵢ[ℂ] _root_.RHTower.evenSubspace :=
  _root_.RHTower.archimedeanMellinUnitary.trans
    ((mellinHTPhaseMulUnitary c).trans
      _root_.RHTower.archimedeanMellinUnitary.symm)

theorem mellinHTPhaseMulUnitary_commutes_mellinCharacter (c p : ℝ)
    (f : Lp (α := ℝ) ℂ 2) :
    mellinHTPhaseMulUnitary c
        (_root_.RHTower.MellinL2.mellinCharacterMulUnitary p f) =
      _root_.RHTower.MellinL2.mellinCharacterMulUnitary p
        (mellinHTPhaseMulUnitary c f) :=
  mellinHTPhaseMulUnitary_commutes_fourierPhase c
    (Real.log p * _root_.RHTower.MellinL2.spectralNormalization) f

theorem mellinHTEvenPhysicalUnitary_commutes_evenDilation
    (c p : ℝ) (hp : 0 < p) (f : _root_.RHTower.evenSubspace) :
    mellinHTEvenPhysicalUnitary c (_root_.RHTower.evenDilationUnitary p hp f) =
      _root_.RHTower.evenDilationUnitary p hp (mellinHTEvenPhysicalUnitary c f) := by
  unfold mellinHTEvenPhysicalUnitary
  simp only [LinearIsometryEquiv.trans_apply]
  apply _root_.RHTower.archimedeanMellinUnitary.injective
  rw [_root_.RHTower.archimedeanMellinUnitary.apply_symm_apply,
    _root_.RHTower.archimedeanMellinUnitary_evenDilation,
    _root_.RHTower.archimedeanMellinUnitary_evenDilation,
    _root_.RHTower.archimedeanMellinUnitary.apply_symm_apply]
  exact mellinHTPhaseMulUnitary_commutes_mellinCharacter c p
    (_root_.RHTower.archimedeanMellinUnitary f)

/-- The HT phase on the literal positive-ray Lebesgue `L²` carrier. -/
def mellinHTPositiveRayUnitary (c : ℝ) :
    _root_.RHTower.SuzukiPositiveL2 ≃ₗᵢ[ℂ]
      _root_.RHTower.SuzukiPositiveL2 :=
  _root_.RHTower.suzukiPositiveHalfLineUnitary.symm.trans
    ((mellinHTEvenPhysicalUnitary c).trans
      _root_.RHTower.suzukiPositiveHalfLineUnitary)

/-- Literal normalized positive-ray dilation, transported from `f(x) ↦ p¹ᴵ² f(px)`. -/
def mellinPositiveRayDilationUnitary (p : ℝ) (hp : 0 < p) :
    _root_.RHTower.SuzukiPositiveL2 ≃ₗᵢ[ℂ]
      _root_.RHTower.SuzukiPositiveL2 :=
  _root_.RHTower.suzukiPositiveHalfLineUnitary.symm.trans
    ((_root_.RHTower.evenDilationUnitary p hp).trans
      _root_.RHTower.suzukiPositiveHalfLineUnitary)

theorem mellinHTPositiveRayUnitary_commutes_dilation
    (c p : ℝ) (hp : 0 < p) (f : _root_.RHTower.SuzukiPositiveL2) :
    mellinHTPositiveRayUnitary c (mellinPositiveRayDilationUnitary p hp f) =
      mellinPositiveRayDilationUnitary p hp (mellinHTPositiveRayUnitary c f) := by
  unfold mellinHTPositiveRayUnitary mellinPositiveRayDilationUnitary
  simp only [LinearIsometryEquiv.trans_apply]
  simp only [_root_.RHTower.suzukiPositiveHalfLineUnitary.symm_apply_apply]
  congr 1
  exact mellinHTEvenPhysicalUnitary_commutes_evenDilation c p hp
    (_root_.RHTower.suzukiPositiveHalfLineUnitary.symm f)

/-! Countable simultaneous hypertranscendental saturation. -/

def mellinHTGaugeRepresentative (G : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  G z * mellinHTPhase c z

theorem mellinHTGaugeRepresentative_eq_entireExponentialPencil
    (G : ℂ → ℂ) (c : ℝ) :
    mellinHTGaugeRepresentative G c =
      entireExponentialPencil G mellinOddReciprocalGammaPhase
        (Complex.I * (c : ℂ)) := by
  rfl

theorem analyticOnNhd_mellinHTGaugeRepresentative {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (c : ℝ) :
    AnalyticOnNhd ℂ (mellinHTGaugeRepresentative G c) Set.univ :=
  hG.mul (analyticOnNhd_mellinHTPhase c)

/-- A fixed nonzero entire base has at most one DA representative in the phase orbit. -/
theorem differentiallyAlgebraic_mellinHTGaugeRepresentative_unique
    {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hGne : ∃ z, G z ≠ 0)
    {c d : ℝ}
    (hc : DifferentiallyAlgebraic (mellinHTGaugeRepresentative G c))
    (hd : DifferentiallyAlgebraic (mellinHTGaugeRepresentative G d)) :
    c = d := by
  rw [mellinHTGaugeRepresentative_eq_entireExponentialPencil] at hc hd
  have hparam := differentiallyAlgebraic_entireExponentialPencil_unique
    hG analyticOnNhd_mellinOddReciprocalGammaPhase hGne
    hypertranscendental_mellinOddReciprocalGammaPhase hc hd
  apply ofReal_injective
  apply mul_left_cancel₀ Complex.I_ne_zero
  exact hparam

theorem differentiallyAlgebraic_mellinHTGaugeParameterSet_subsingleton
    {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hGne : ∃ z, G z ≠ 0) :
    {c : ℝ | DifferentiallyAlgebraic (mellinHTGaugeRepresentative G c)}.Subsingleton := by
  intro c hc d hd
  exact differentiallyAlgebraic_mellinHTGaugeRepresentative_unique hG hGne hc hd

/-- For a countable marked family, the union of all DA phase parameters is countable. -/
theorem countable_differentiallyAlgebraic_mellinHTGaugeParameters
    {J : Type*} [Countable J] {G : J → ℂ → ℂ}
    (hG : ∀ j, AnalyticOnNhd ℂ (G j) Set.univ)
    (hGne : ∀ j, ∃ z, G j z ≠ 0) :
    {c : ℝ | ∃ j, DifferentiallyAlgebraic (mellinHTGaugeRepresentative (G j) c)}.Countable := by
  have heq : {c : ℝ | ∃ j, DifferentiallyAlgebraic
      (mellinHTGaugeRepresentative (G j) c)} =
      ⋃ j, {c : ℝ | DifferentiallyAlgebraic
        (mellinHTGaugeRepresentative (G j) c)} := by
    ext c
    simp
  rw [heq]
  exact Set.countable_iUnion fun j =>
    (differentiallyAlgebraic_mellinHTGaugeParameterSet_subsingleton
      (hG j) (hGne j)).countable

/-- Every parameter outside the countable exceptional union simultaneously makes all marked
representatives hypertranscendental. -/
theorem simultaneously_hypertranscendental_mellinHTGaugeRepresentative
    {J : Type*} {G : J → ℂ → ℂ} {c : ℝ}
    (hc : c ∉ {t : ℝ | ∃ j, DifferentiallyAlgebraic
      (mellinHTGaugeRepresentative (G j) t)}) :
    ∀ j, Hypertranscendental (mellinHTGaugeRepresentative (G j) c) := by
  intro j hDA
  exact hc ⟨j, hDA⟩

/-- There is a simultaneous HT parameter for every countable nonzero entire family. -/
theorem exists_simultaneously_hypertranscendental_mellinHTGaugeRepresentative
    {J : Type*} [Countable J] {G : J → ℂ → ℂ}
    (hG : ∀ j, AnalyticOnNhd ℂ (G j) Set.univ)
    (hGne : ∀ j, ∃ z, G j z ≠ 0) :
    ∃ c : ℝ, ∀ j, Hypertranscendental
      (mellinHTGaugeRepresentative (G j) c) := by
  let S : Set ℝ := {c | ∃ j, DifferentiallyAlgebraic
    (mellinHTGaugeRepresentative (G j) c)}
  have hS : S.Countable :=
    countable_differentiallyAlgebraic_mellinHTGaugeParameters hG hGne
  have hex : ∃ c : ℝ, c ∉ S := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have huniv : S = Set.univ := Set.eq_univ_of_forall hcon
    exact Cardinal.not_countable_real (huniv ▸ hS)
  obtain ⟨c, hc⟩ := hex
  exact ⟨c, simultaneously_hypertranscendental_mellinHTGaugeRepresentative hc⟩

/-- If the base is DA, zero is the unique possible DA phase parameter. -/
theorem hypertranscendental_mellinHTGaugeRepresentative_of_base_DA
    {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hGne : ∃ z, G z ≠ 0)
    (hGDA : DifferentiallyAlgebraic G) {c : ℝ} (hc : c ≠ 0) :
    Hypertranscendental (mellinHTGaugeRepresentative G c) := by
  intro hcDA
  have hzero : DifferentiallyAlgebraic (mellinHTGaugeRepresentative G 0) := by
    have heq : mellinHTGaugeRepresentative G 0 = G := by
      funext z
      simp [mellinHTGaugeRepresentative]
    rw [heq]
    exact hGDA
  exact hc (differentiallyAlgebraic_mellinHTGaugeRepresentative_unique
    hG hGne hcDA hzero)

/-! Exact marked dilation-orbit geometry. -/

abbrev MellinPhysicalL2 :=
  Lp ℂ 2 _root_.RHTower.MellinL2.multiplicativeHaar

def mellinPositiveScaleLinearMap (a : ℝ) :
    MellinPhysicalL2 →ₗ[ℂ] MellinPhysicalL2 :=
  (_root_.RHTower.MellinL2.positiveScaleUnitary a).toLinearEquiv.toLinearMap

theorem mellinHTPhysicalUnitary_commutes_positiveScaleLinearMap (c a : ℝ)
    (f : MellinPhysicalL2) :
    mellinHTPhysicalUnitary c (mellinPositiveScaleLinearMap a f) =
      mellinPositiveScaleLinearMap a (mellinHTPhysicalUnitary c f) :=
  mellinHTPhysicalUnitary_commutes_positiveScale c a f

/-- Exact transport `V_c C(g) = C(V_c g)` for arbitrary marked dilation sets. -/
theorem mellinHTPhysicalUnitary_map_markedCyclicSubspace
    {J : Type*} (c : ℝ) (g : J → MellinPhysicalL2) (A : J → Set ℝ) :
    Submodule.map (mellinHTPhysicalUnitary c).toLinearEquiv.toLinearMap
        (markedCyclicSubspace mellinPositiveScaleLinearMap g A) =
      markedCyclicSubspace mellinPositiveScaleLinearMap
        (fun j => mellinHTPhysicalUnitary c (g j)) A :=
  unitary_map_markedCyclicSubspace (mellinHTPhysicalUnitary c)
    mellinPositiveScaleLinearMap g A
    (mellinHTPhysicalUnitary_commutes_positiveScaleLinearMap c)

/-- Exact preservation of approximation distance to arbitrary marked dilation-orbit closures. -/
theorem mellinHTPhysicalUnitary_infDist_markedCyclicSubspace
    {J : Type*} (c : ℝ) (g : J → MellinPhysicalL2) (A : J → Set ℝ)
    (v : MellinPhysicalL2) :
    Metric.infDist (mellinHTPhysicalUnitary c v)
        (markedCyclicSubspace mellinPositiveScaleLinearMap
          (fun j => mellinHTPhysicalUnitary c (g j)) A : Set MellinPhysicalL2) =
      Metric.infDist v
        (markedCyclicSubspace mellinPositiveScaleLinearMap g A : Set MellinPhysicalL2) :=
  unitary_infDist_markedCyclicSubspace (mellinHTPhysicalUnitary c)
    mellinPositiveScaleLinearMap g A
    (mellinHTPhysicalUnitary_commutes_positiveScaleLinearMap c) v

/-- Exact preservation of membership in the marked dilation-orbit closure. -/
theorem mellinHTPhysicalUnitary_mem_markedCyclicSubspace_iff
    {J : Type*} (c : ℝ) (g : J → MellinPhysicalL2) (A : J → Set ℝ)
    (v : MellinPhysicalL2) :
    mellinHTPhysicalUnitary c v ∈
        markedCyclicSubspace mellinPositiveScaleLinearMap
          (fun j => mellinHTPhysicalUnitary c (g j)) A ↔
      v ∈ markedCyclicSubspace mellinPositiveScaleLinearMap g A :=
  unitary_mem_markedCyclicSubspace_iff (mellinHTPhysicalUnitary c)
    mellinPositiveScaleLinearMap g A
    (mellinHTPhysicalUnitary_commutes_positiveScaleLinearMap c) v

/-- Exact preservation of dilation cyclicity. -/
theorem mellinHTPhysicalUnitary_markedCyclicSubspace_eq_top_iff
    {J : Type*} (c : ℝ) (g : J → MellinPhysicalL2) (A : J → Set ℝ) :
    markedCyclicSubspace mellinPositiveScaleLinearMap
        (fun j => mellinHTPhysicalUnitary c (g j)) A = ⊤ ↔
      markedCyclicSubspace mellinPositiveScaleLinearMap g A = ⊤ :=
  unitary_markedCyclicSubspace_eq_top_iff (mellinHTPhysicalUnitary c)
    mellinPositiveScaleLinearMap g A
    (mellinHTPhysicalUnitary_commutes_positiveScaleLinearMap c)

/-- Every finite Gram determinant, including those of arbitrary finite linear combinations of
marked orbit vectors, is invariant. -/
theorem mellinHTPhysicalUnitary_gramDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (v : ι → MellinPhysicalL2) :
    Matrix.det (fun i j => inner ℂ
      (mellinHTPhysicalUnitary c (v i)) (mellinHTPhysicalUnitary c (v j))) =
      Matrix.det (fun i j => inner ℂ (v i) (v j)) :=
  unitary_gramDeterminant (mellinHTPhysicalUnitary c) v

/-! Marked orbit geometry on the literal positive-ray Lebesgue carrier. -/

def mellinPositiveRayDilationLinearMap
    (p : _root_.RHTower.MellinL2.PosReal) :
    _root_.RHTower.SuzukiPositiveL2 →ₗ[ℂ] _root_.RHTower.SuzukiPositiveL2 :=
  (mellinPositiveRayDilationUnitary p p.property).toLinearEquiv.toLinearMap

theorem mellinHTPositiveRayUnitary_commutes_dilationLinearMap
    (c : ℝ) (p : _root_.RHTower.MellinL2.PosReal)
    (f : _root_.RHTower.SuzukiPositiveL2) :
    mellinHTPositiveRayUnitary c (mellinPositiveRayDilationLinearMap p f) =
      mellinPositiveRayDilationLinearMap p (mellinHTPositiveRayUnitary c f) :=
  mellinHTPositiveRayUnitary_commutes_dilation c p p.property f

/-- Literal `L²((0,∞),dx)` form of `V_c C(g)=C(V_cg)`. -/
theorem mellinHTPositiveRayUnitary_map_markedCyclicSubspace
    {J : Type*} (c : ℝ) (g : J → _root_.RHTower.SuzukiPositiveL2)
    (A : J → Set _root_.RHTower.MellinL2.PosReal) :
    Submodule.map (mellinHTPositiveRayUnitary c).toLinearEquiv.toLinearMap
        (markedCyclicSubspace mellinPositiveRayDilationLinearMap g A) =
      markedCyclicSubspace mellinPositiveRayDilationLinearMap
        (fun j => mellinHTPositiveRayUnitary c (g j)) A :=
  unitary_map_markedCyclicSubspace (mellinHTPositiveRayUnitary c)
    mellinPositiveRayDilationLinearMap g A
    (mellinHTPositiveRayUnitary_commutes_dilationLinearMap c)

/-- Literal positive-ray approximation distances are invariant. -/
theorem mellinHTPositiveRayUnitary_infDist_markedCyclicSubspace
    {J : Type*} (c : ℝ) (g : J → _root_.RHTower.SuzukiPositiveL2)
    (A : J → Set _root_.RHTower.MellinL2.PosReal)
    (v : _root_.RHTower.SuzukiPositiveL2) :
    Metric.infDist (mellinHTPositiveRayUnitary c v)
        (markedCyclicSubspace mellinPositiveRayDilationLinearMap
          (fun j => mellinHTPositiveRayUnitary c (g j)) A :
            Set _root_.RHTower.SuzukiPositiveL2) =
      Metric.infDist v
        (markedCyclicSubspace mellinPositiveRayDilationLinearMap g A :
          Set _root_.RHTower.SuzukiPositiveL2) :=
  unitary_infDist_markedCyclicSubspace (mellinHTPositiveRayUnitary c)
    mellinPositiveRayDilationLinearMap g A
    (mellinHTPositiveRayUnitary_commutes_dilationLinearMap c) v

/-- Literal positive-ray closure membership is invariant. -/
theorem mellinHTPositiveRayUnitary_mem_markedCyclicSubspace_iff
    {J : Type*} (c : ℝ) (g : J → _root_.RHTower.SuzukiPositiveL2)
    (A : J → Set _root_.RHTower.MellinL2.PosReal)
    (v : _root_.RHTower.SuzukiPositiveL2) :
    mellinHTPositiveRayUnitary c v ∈
        markedCyclicSubspace mellinPositiveRayDilationLinearMap
          (fun j => mellinHTPositiveRayUnitary c (g j)) A ↔
      v ∈ markedCyclicSubspace mellinPositiveRayDilationLinearMap g A :=
  unitary_mem_markedCyclicSubspace_iff (mellinHTPositiveRayUnitary c)
    mellinPositiveRayDilationLinearMap g A
    (mellinHTPositiveRayUnitary_commutes_dilationLinearMap c) v

/-- Literal positive-ray dilation cyclicity is invariant. -/
theorem mellinHTPositiveRayUnitary_markedCyclicSubspace_eq_top_iff
    {J : Type*} (c : ℝ) (g : J → _root_.RHTower.SuzukiPositiveL2)
    (A : J → Set _root_.RHTower.MellinL2.PosReal) :
    markedCyclicSubspace mellinPositiveRayDilationLinearMap
        (fun j => mellinHTPositiveRayUnitary c (g j)) A = ⊤ ↔
      markedCyclicSubspace mellinPositiveRayDilationLinearMap g A = ⊤ :=
  unitary_markedCyclicSubspace_eq_top_iff (mellinHTPositiveRayUnitary c)
    mellinPositiveRayDilationLinearMap g A
    (mellinHTPositiveRayUnitary_commutes_dilationLinearMap c)

/-- Every finite positive-ray Gram determinant is invariant. -/
theorem mellinHTPositiveRayUnitary_gramDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (v : ι → _root_.RHTower.SuzukiPositiveL2) :
    Matrix.det (fun i j => inner ℂ
      (mellinHTPositiveRayUnitary c (v i))
      (mellinHTPositiveRayUnitary c (v j))) =
      Matrix.det (fun i j => inner ℂ (v i) (v j)) :=
  unitary_gramDeterminant (mellinHTPositiveRayUnitary c) v

/-! Exact saturation of arbitrary global meromorphic representatives. -/

def mellinHTPhaseMero (c : ℝ) : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (mellinHTPhase c) (analyticOnNhd_mellinHTPhase c)

theorem mellinHTPhaseMero_ne_zero (c : ℝ) : mellinHTPhaseMero c ≠ 0 := by
  unfold mellinHTPhaseMero mellinHTPhase
  exact analyticMeroElement_exp_ne_zero
    (fun z => Complex.I * (c : ℂ) * mellinOddReciprocalGammaPhase z)
    (analyticOnNhd_const.mul analyticOnNhd_mellinOddReciprocalGammaPhase)

theorem mellinHTPhaseMero_add (c d : ℝ) :
    mellinHTPhaseMero (c + d) = mellinHTPhaseMero c * mellinHTPhaseMero d := by
  unfold mellinHTPhaseMero
  rw [← analyticMeroElement_mul]
  apply analyticMeroElement_congr
  funext z
  exact mellinHTPhase_add c d z

@[simp] theorem mellinHTPhaseMero_zero : mellinHTPhaseMero 0 = 1 := by
  unfold mellinHTPhaseMero
  calc
    analyticMeroElement (mellinHTPhase 0) (analyticOnNhd_mellinHTPhase 0) =
        analyticMeroElement (fun _ : ℂ => 1) analyticOnNhd_const := by
      apply analyticMeroElement_congr
      funext z
      simp
    _ = 1 := by rw [analyticMeroElement_const]; simp

theorem mellinHTPhaseMero_div (c d : ℝ) :
    mellinHTPhaseMero c / mellinHTPhaseMero d = mellinHTPhaseMero (c - d) := by
  apply (div_eq_iff (mellinHTPhaseMero_ne_zero d)).2
  rw [← mellinHTPhaseMero_add, sub_add_cancel]

theorem hypertranscendentalOver_mellinHTPhaseMero {c : ℝ} (hc : c ≠ 0) :
    HypertranscendentalOver (RatFunc ℂ) (mellinHTPhaseMero c) := by
  intro hDA
  apply hypertranscendental_mellinHTPhase hc
  exact differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement
    (analyticOnNhd_mellinHTPhase c) hDA

def mellinHTMeromorphicGaugeRepresentative
    (G : meroField (Set.univ : Set ℂ)) (c : ℝ) :
    meroField (Set.univ : Set ℂ) :=
  G * mellinHTPhaseMero c

theorem differentialAlgebraicOver_mellinHTMeromorphicGaugeRepresentative_unique
    {G : meroField (Set.univ : Set ℂ)} (hGne : G ≠ 0) {c d : ℝ}
    (hc : DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative G c))
    (hd : DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative G d)) :
    c = d := by
  by_contra hcd
  have hdiff : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have hquot : DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative G c /
        mellinHTMeromorphicGaugeRepresentative G d) :=
    differentialAlgebraicOver_div hc hd
  have heq : mellinHTMeromorphicGaugeRepresentative G c /
      mellinHTMeromorphicGaugeRepresentative G d = mellinHTPhaseMero (c - d) := by
    unfold mellinHTMeromorphicGaugeRepresentative
    rw [mul_div_mul_left _ _ hGne, mellinHTPhaseMero_div]
  rw [heq] at hquot
  exact hypertranscendentalOver_mellinHTPhaseMero hdiff hquot

theorem differentialAlgebraicOver_mellinHTMeromorphicGaugeParameterSet_subsingleton
    {G : meroField (Set.univ : Set ℂ)} (hGne : G ≠ 0) :
    {c : ℝ | DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative G c)}.Subsingleton := by
  intro c hc d hd
  exact differentialAlgebraicOver_mellinHTMeromorphicGaugeRepresentative_unique
    hGne hc hd

theorem countable_differentialAlgebraicOver_mellinHTMeromorphicGaugeParameters
    {J : Type*} [Countable J]
    {G : J → meroField (Set.univ : Set ℂ)} (hGne : ∀ j, G j ≠ 0) :
    {c : ℝ | ∃ j, DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative (G j) c)}.Countable := by
  have heq : {c : ℝ | ∃ j, DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative (G j) c)} =
      ⋃ j, {c : ℝ | DifferentialAlgebraicOver (RatFunc ℂ)
        (mellinHTMeromorphicGaugeRepresentative (G j) c)} := by
    ext c
    simp
  rw [heq]
  exact Set.countable_iUnion fun j =>
    (differentialAlgebraicOver_mellinHTMeromorphicGaugeParameterSet_subsingleton
      (hGne j)).countable

theorem simultaneously_hypertranscendentalOver_mellinHTMeromorphicGaugeRepresentative
    {J : Type*} {G : J → meroField (Set.univ : Set ℂ)} {c : ℝ}
    (hc : c ∉ {t : ℝ | ∃ j, DifferentialAlgebraicOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative (G j) t)}) :
    ∀ j, HypertranscendentalOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative (G j) c) := by
  intro j hDA
  exact hc ⟨j, hDA⟩

theorem exists_simultaneously_hypertranscendentalOver_mellinHTMeromorphicGaugeRepresentative
    {J : Type*} [Countable J]
    {G : J → meroField (Set.univ : Set ℂ)} (hGne : ∀ j, G j ≠ 0) :
    ∃ c : ℝ, ∀ j, HypertranscendentalOver (RatFunc ℂ)
      (mellinHTMeromorphicGaugeRepresentative (G j) c) := by
  let S : Set ℝ := {c | ∃ j, DifferentialAlgebraicOver (RatFunc ℂ)
    (mellinHTMeromorphicGaugeRepresentative (G j) c)}
  have hS : S.Countable :=
    countable_differentialAlgebraicOver_mellinHTMeromorphicGaugeParameters hGne
  have hex : ∃ c : ℝ, c ∉ S := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have huniv : S = Set.univ := Set.eq_univ_of_forall hcon
    exact Cardinal.not_countable_real (huniv ▸ hS)
  obtain ⟨c, hc⟩ := hex
  exact ⟨c,
    simultaneously_hypertranscendentalOver_mellinHTMeromorphicGaugeRepresentative hc⟩

/-- **Mellin-dilation HT unitary saturation, capstone.**  For every countable family of nonzero
global meromorphic representatives and every marked positive-dilation Hilbert problem, one phase
simultaneously makes all representatives HT while preserving the exact closed cyclic subspace,
approximation distance, closure membership, cyclicity, and every prescribed finite Gram
determinant on literal `L²((0,∞),dx)`. -/
theorem exists_mellinHTPositiveRayUnitary_saturation
    {K : Type*} [Countable K]
    {G : K → meroField (Set.univ : Set ℂ)} (hGne : ∀ k, G k ≠ 0)
    {J ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : J → _root_.RHTower.SuzukiPositiveL2)
    (A : J → Set _root_.RHTower.MellinL2.PosReal)
    (v : _root_.RHTower.SuzukiPositiveL2)
    (w : ι → _root_.RHTower.SuzukiPositiveL2) :
    ∃ c : ℝ,
      (∀ k, HypertranscendentalOver (RatFunc ℂ)
        (mellinHTMeromorphicGaugeRepresentative (G k) c)) ∧
      Submodule.map (mellinHTPositiveRayUnitary c).toLinearEquiv.toLinearMap
          (markedCyclicSubspace mellinPositiveRayDilationLinearMap g A) =
        markedCyclicSubspace mellinPositiveRayDilationLinearMap
          (fun j => mellinHTPositiveRayUnitary c (g j)) A ∧
      Metric.infDist (mellinHTPositiveRayUnitary c v)
          (markedCyclicSubspace mellinPositiveRayDilationLinearMap
            (fun j => mellinHTPositiveRayUnitary c (g j)) A :
              Set _root_.RHTower.SuzukiPositiveL2) =
        Metric.infDist v
          (markedCyclicSubspace mellinPositiveRayDilationLinearMap g A :
            Set _root_.RHTower.SuzukiPositiveL2) ∧
      (mellinHTPositiveRayUnitary c v ∈
          markedCyclicSubspace mellinPositiveRayDilationLinearMap
            (fun j => mellinHTPositiveRayUnitary c (g j)) A ↔
        v ∈ markedCyclicSubspace mellinPositiveRayDilationLinearMap g A) ∧
      (markedCyclicSubspace mellinPositiveRayDilationLinearMap
          (fun j => mellinHTPositiveRayUnitary c (g j)) A = ⊤ ↔
        markedCyclicSubspace mellinPositiveRayDilationLinearMap g A = ⊤) ∧
      Matrix.det (fun i j => inner ℂ
          (mellinHTPositiveRayUnitary c (w i))
          (mellinHTPositiveRayUnitary c (w j))) =
        Matrix.det (fun i j => inner ℂ (w i) (w j)) := by
  obtain ⟨c, hc⟩ :=
    exists_simultaneously_hypertranscendentalOver_mellinHTMeromorphicGaugeRepresentative hGne
  exact ⟨c, hc,
    mellinHTPositiveRayUnitary_map_markedCyclicSubspace c g A,
    mellinHTPositiveRayUnitary_infDist_markedCyclicSubspace c g A v,
    mellinHTPositiveRayUnitary_mem_markedCyclicSubspace_iff c g A v,
    mellinHTPositiveRayUnitary_markedCyclicSubspace_eq_top_iff c g A,
    mellinHTPositiveRayUnitary_gramDeterminant c w⟩

end
end GaloisForLFunctions.RHTower
