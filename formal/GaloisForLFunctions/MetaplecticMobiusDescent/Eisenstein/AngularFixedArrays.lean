import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularFiniteReflection
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularPhaseIdeals

/-!
# Fixed-array geometry of angular reflection

The reflected angular series has the same squarefree–cube frequencies and radial scales.
Its normalized coefficient is the fixed cusp array multiplied by the higher-jet unit phase
and the opposite angular frequency phase.
-/

open Complex MeasureTheory Set
open scoped BigOperators Classical ContDiff ComplexConjugate MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss CompletedDyadic
open GaloisForLFunctions.FamilyContinuationTheory
noncomputable section
local notation "Eis" => Eisenstein.O

def SourceCuspDatum.angularSmoothedKernel (d:SourceCuspDatum) (k : ℕ) (W:ℝ→ℂ) (X:ℝ) : ℂ :=
  (d.jetMultiplier (6 * k)*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
    ∑'n:Eis,(conj (elemPsiSix n) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint n)*
      angularPaperKernel k (Vstar W)
        (X*sourceCuspRadialLength n/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

private lemma thetaBesselScale_sq : thetaBesselScale ^ 2 = (1 / 27 : ℝ) := by
  rw [thetaBesselScale, thetaFrequencyScale, norm_div, norm_one, norm_mul,
    Complex.norm_ofNat, div_pow, mul_pow, norm_ringComplex_traceLambda_sq]
  norm_num

lemma SourceCuspDatum.smoothingScale_explicit (d : SourceCuspDatum) (X : ℝ) :
    d.smoothingScale X = X / (27 * (sourceCuspScale d.index) ^ 2 * d.heightScale ^ 2) := by
  have h0 : sourceCuspRadialScale 0 = thetaBesselScale := by
    simp only [sourceCuspRadialScale, sourceCuspScale, Matrix.cons_val_zero, div_one]
  rw [SourceCuspDatum.smoothingScale, h0, sourceCuspRadialScale, div_pow]
  simp only [thetaBesselScale_sq]
  field_simp [(sourceCuspScale_pos d.index).ne', d.heightScale_pos.ne']

lemma SourceCuspDatum.angularSmoothingMultiplier_normalization (d : SourceCuspDatum) (k : ℕ) :
    d.angularSmoothingMultiplier k =
      d.jetMultiplier (6 * k) * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2 := by
  rw [SourceCuspDatum.angularSmoothingMultiplier, sourceCuspRadialScale_ratio,
    Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

lemma SourceCuspDatum.angularSmoothedKernel_eq_reflected_series
    (d : SourceCuspDatum) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) :
    d.angularSmoothedKernel k W X = d.angularSmoothingMultiplier k *
      ∑' h : O, (conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h) *
        angularPaperKernel k (Vstar W) (d.smoothingScale X * sourceCuspRadialLength h) := by
  rw [SourceCuspDatum.angularSmoothedKernel, d.angularSmoothingMultiplier_normalization]
  congr 1
  apply tsum_congr
  intro h
  rw [d.smoothingScale_explicit]
  congr 2
  ring

/-- The fixed-array kernel is the exact reflected kernel of the actual completed sum. -/
theorem completedT_angular_finite_cusp_kernel (k : ℕ) (c : O) (hc : c ≠ 0)
    [Fintype (O ⧸ Ideal.span {9 * c})] (Ψ : (O ⧸ Ideal.span {c}) →* ℂ)
    (d : (O ⧸ Ideal.span {9 * c}) → SourceCuspDatum)
    (hd : ∀ i, (d i).point = thetaFourierTranslation (9 * c) i)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    completedT (angularSourceTwist k
      (Ψ.comp (Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom)) W X =
      thetaDerivativeScalar⁻¹ * ∑ i,
        finiteAdditiveFourierCoeff (residueTraceQuotientChar 1 (9 * c) (mul_ne_zero (by norm_num) hc))
          (finiteThetaTwist c Ψ) i * (d i).angularSmoothedKernel k W X := by
  simp_rw [SourceCuspDatum.angularSmoothedKernel_eq_reflected_series]
  exact completedT_angular_finite_cusp_reflection k c hc Ψ d hd W a b ha hs hW X hX

lemma SourceCuspDatum.angularSmoothedKernel_full_index (d:SourceCuspDatum) (k : ℕ) (W:ℝ→ℂ) (X:ℝ) :
    d.angularSmoothedKernel k W X=
      (d.jetMultiplier (6 * k)*(d.heightScale:ℂ)*(sourceCuspScale d.index:ℂ)^2)*
        ∑'p:ThetaFullIndex,(conj (elemPsiSix (thetaFullFrequency p)) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p))*
          angularPaperKernel k (Vstar W)
            (X*sourceCuspRadialLength (thetaFullFrequency p)/
              (27*(sourceCuspScale d.index)^2*d.heightScale^2)) := by
  rw [SourceCuspDatum.angularSmoothedKernel]
  congr 1
  exact angularSourceCusp_tsum_full_index k d.index d.dualPoint
    (fun h=>angularPaperKernel k (Vstar W)
      (X*sourceCuspRadialLength h/(27*(sourceCuspScale d.index)^2*d.heightScale^2)))


lemma SourceCuspDatum.angularSmoothedKernel_full_index_norm_summable
    (d:SourceCuspDatum) (k : ℕ) (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    Summable (fun p:ThetaFullIndex=>
      ‖(conj (elemPsiSix (thetaFullFrequency p)) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p))*
        angularPaperKernel k (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/
            (27*(sourceCuspScale d.index)^2*d.heightScale^2))‖) := by
  have hsum := angularSourceZ_weighted_summable k d.index d.dualPoint
  have hs:=angularPaperKernel_weighted_norm_summable sourceCuspRadialLength sourceCuspRadialLength_pos
    (fun h => conj (elemPsiSix h) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint h)
    hsum k
    (Vstar W) v0 v1 hv0 (Vstar_support W v0 v1 hWs) (Vstar_contDiff W v0 v1 hv0 hWs hW)
    (X/(27*(sourceCuspScale d.index)^2*d.heightScale^2))
    (by have := sourceCuspScale_pos d.index; have := d.heightScale_pos; positivity)
  have hp:=hs.comp_injective thetaFullFrequency_injective
  apply hp.congr
  intro p
  exact congrArg (fun y:ℝ=>‖(conj (elemPsiSix (thetaFullFrequency p)) ^ k * sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p))*
    angularPaperKernel k (Vstar W) y‖)
    (by ring :
      X/(27*(sourceCuspScale d.index)^2*d.heightScale^2)*sourceCuspRadialLength (thetaFullFrequency p)=
        X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale d.index)^2*d.heightScale^2))

lemma SourceCuspDatum.angular_unit_phase_norm (d : SourceCuspDatum) (k : ℕ) :
    ‖d.jetMultiplier (6 * k) * (d.heightScale : ℂ)‖ = 1 := by
  rw [norm_mul, d.jetMultiplier_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos d.heightScale_pos, inv_mul_cancel₀ d.heightScale_pos.ne']

/-- Higher jets change only the two unit phases in the normalized fixed-array coefficient. -/
theorem SourceCuspDatum.angularSmoothedFullCoefficient_normalization
    (d : SourceCuspDatum) (k : ℕ) (p : ThetaFullIndex) :
    (d.jetMultiplier (6 * k) * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2) *
      (conj (elemPsiSix (thetaFullFrequency p)) ^ k *
        sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)) =
    (fixedRadialCoefficientScalar * (d.jetMultiplier (6 * k) * (d.heightScale : ℂ))) *
      (conj (elemPsiSix (thetaFullFrequency p)) ^ k *
        (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
          angularFactor (thetaFullFrequency p) *
          tracePhase (-cuspFrequency (thetaFullFrequency p) *
            (d.dualPoint / (sourceCuspScale d.index : ℂ))))) /
      ((ramifiedScale 1 completedRamifiedStep p.2.1 *
        Real.sqrt (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) : ℝ) : ℂ) := by
  have hn := d.smoothedFullCoefficient_normalization p
  simp only [d.jetMultiplier_six_mul]
  calc
    _ = ((-conj (d.matrix 1 0) / d.matrix 1 0) ^ (6 * k) *
        conj (elemPsiSix (thetaFullFrequency p)) ^ k) *
      ((d.multiplier * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2) *
        sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p)) := by ring
    _ = _ := by rw [hn]; ring

lemma SourceCuspDatum.angularSmoothedFullCoefficient_norm_le
    (d : SourceCuspDatum) (k : ℕ) (p : ThetaFullIndex) :
    ‖(d.jetMultiplier (6 * k) * (d.heightScale : ℂ) * (sourceCuspScale d.index : ℂ) ^ 2) *
      (conj (elemPsiSix (thetaFullFrequency p)) ^ k *
        sourceCuspRadialCoefficient d.index d.dualPoint (thetaFullFrequency p))‖ ≤
    ‖fixedRadialCoefficientScalar‖ /
      (ramifiedScale 1 completedRamifiedStep p.2.1 *
        Real.sqrt (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ)) := by
  have hp : ‖conj (elemPsiSix (thetaFullFrequency p)) ^ k‖ ≤ 1 := by
    rw [norm_pow, Complex.norm_conj]
    exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one _)
  have ha : ‖fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
      angularFactor (thetaFullFrequency p) *
      tracePhase (-cuspFrequency (thetaFullFrequency p) *
        (d.dualPoint / (sourceCuspScale d.index : ℂ)))‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_angularFactor _ (thetaFullFrequency_ne_zero p),
      tracePhase_norm, mul_one, mul_one]
    exact fixedConjugateCuspArray_norm_le_one _ _ _ _ _
  rw [d.angularSmoothedFullCoefficient_normalization, norm_div, norm_mul,
    norm_mul, d.angular_unit_phase_norm, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (thetaFullIndex_denominator_pos p).le]
  apply div_le_div_of_nonneg_right _ (thetaFullIndex_denominator_pos p).le
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [norm_mul]
  exact (mul_le_mul hp ha (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem SourceCuspDatum.angularSmoothedKernel_fixed_array
    (d : SourceCuspDatum) (k : ℕ) (W : ℝ → ℂ) (X : ℝ) :
    d.angularSmoothedKernel k W X =
      (fixedRadialCoefficientScalar * (d.jetMultiplier (6 * k) * (d.heightScale : ℂ))) *
        ∑' p : ThetaFullIndex,
          ((conj (elemPsiSix (thetaFullFrequency p)) ^ k *
            (fixedConjugateCuspArray d.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val *
              angularFactor (thetaFullFrequency p) *
              tracePhase (-cuspFrequency (thetaFullFrequency p) *
                (d.dualPoint / (sourceCuspScale d.index : ℂ))))) /
            ((ramifiedScale 1 completedRamifiedStep p.2.1 *
              Real.sqrt (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) : ℝ) : ℂ)) *
          angularPaperKernel k (Vstar W)
            ((X / (27 * (sourceCuspScale d.index) ^ 2 * d.heightScale ^ 2)) *
              (ramifiedScale 1 completedRamifiedStep p.2.1) ^ 3 *
              (Ideal.absNorm p.2.2.1.val : ℝ) * (Ideal.absNorm p.2.2.2.val : ℝ) ^ 3) := by
  rw [d.angularSmoothedKernel_full_index, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [← mul_assoc, d.angularSmoothedFullCoefficient_normalization,
    sourceCusp_full_index_kernel_argument]
  ring


theorem sum_angularSmoothedKernel_common_cusp (k : ℕ) {ι:Type*} [Fintype ι]
    (d:ι→SourceCuspDatum) (w:ι→ℂ) (j:Fin 3) (Q:ℝ)
    (hj:∀i,(d i).index=j) (hQ:∀i,(d i).heightScale=Q)
    (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑i,w i*(d i).angularSmoothedKernel k W X)=fixedRadialCoefficientScalar*
      ∑'p:ThetaFullIndex,
        ((conj (elemPsiSix (thetaFullFrequency p)) ^ k *
          (fixedConjugateCuspArray j p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
            angularFactor (thetaFullFrequency p)))/
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        angularPaperKernel k (Vstar W)
          (X*sourceCuspRadialLength (thetaFullFrequency p)/(27*(sourceCuspScale j)^2*Q^2))*
        (∑i,w i*((d i).jetMultiplier (6 * k)*(Q:ℂ))*
          tracePhase (-cuspFrequency (thetaFullFrequency p)*
            ((d i).dualPoint/(sourceCuspScale j:ℂ)))) := by
  let F:ι→ThetaFullIndex→ℂ:=fun i p=>w i*
    ((d i).jetMultiplier (6 * k)*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
    ((conj (elemPsiSix (thetaFullFrequency p)) ^ k * sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p))*
      angularPaperKernel k (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)))
  have hs (i:ι):Summable (F i):=by
    exact ((d i).angularSmoothedKernel_full_index_norm_summable k W a b ha hsupp hW X hX).of_norm.mul_left _
  have he (i:ι):w i*(d i).angularSmoothedKernel k W X=∑'p,F i p := by
    rw [(d i).angularSmoothedKernel_full_index]
    simp only [F,tsum_mul_left]
    ring
  simp_rw [he]
  rw [←Summable.tsum_finsetSum (fun i _=>hs i),←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn:=(d i).angularSmoothedFullCoefficient_normalization k p
  dsimp only [F]
  calc
    _=w i*(((d i).jetMultiplier (6 * k)*((d i).heightScale:ℂ)*(sourceCuspScale (d i).index:ℂ)^2)*
      (conj (elemPsiSix (thetaFullFrequency p)) ^ k * sourceCuspRadialCoefficient (d i).index (d i).dualPoint (thetaFullFrequency p)))*
      angularPaperKernel k (Vstar W)
        (X*sourceCuspRadialLength (thetaFullFrequency p)/
          (27*(sourceCuspScale (d i).index)^2*(d i).heightScale^2)):=by ring
    _=_:=by rw [hn,hj i,hQ i]; ring


namespace FixedCuspShape
variable {H : SL(2, Eis)} (s : FixedCuspShape H)
theorem sum_angularSmoothedKernel_integral_phase (k : ℕ) {ι:Type*} [Fintype ι]
    (g:ι → rationalExtension) (c:Eis) (hc:c≠0) (hC:∀v,((g v:SL(2,Eis))*H) 1 0=c)
    (w:ι→ℂ) (W:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hsupp:Function.support W⊆Set.Icc a b)
    (hW:ContDiff ℝ ∞ W) (X:ℝ) (hX:0<X) :
    (∑v,w v*(s.datum (g v) (by rw [hC v];exact hc)).angularSmoothedKernel k W X)=
      fixedRadialCoefficientScalar*(s.stratumShapeFactor c*elemPsiSix c^(2*k))*
      ∑'p:ThetaFullIndex,
        (conj (elemPsiSix (thetaFullFrequency p))^k * s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val /
          ((ramifiedScale 1 completedRamifiedStep p.2.1*
            Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ))*
        angularPaperKernel k (Vstar W)
          ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
            (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
            (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)*
        (∑v,w v*star (extendedComplexCharacter (g v))*
          tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
            (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/
              ringComplex c)) := by
  let d:ι→SourceCuspDatum:=fun v=>s.datum (g v) (by rw [hC v];exact hc)
  have hindex:∀v,(d v).index=s.index:=fun _=>rfl
  have hheight:∀v,(d v).heightScale=(Ideal.absNorm (Ideal.span {c}):ℝ):=by
    intro v
    dsimp only [d]
    rw [s.datum_heightScale,hC v,ringComplex_norm_sq_eq_absNorm_span]
  have he:=sum_angularSmoothedKernel_common_cusp k d w s.index (Ideal.absNorm (Ideal.span {c}):ℝ)
    hindex hheight W a b ha hsupp hW X hX
  rw [he]
  conv_rhs => rw [mul_assoc]
  apply congrArg (fun z:ℂ=>fixedRadialCoefficientScalar*z)
  rw [←tsum_mul_left]
  apply tsum_congr
  intro p
  rw [sourceCusp_full_index_kernel_argument p s.index (Ideal.absNorm (Ideal.span {c}):ℝ) X]
  let A:ℂ:=fixedConjugateCuspArray s.index p.1 p.2.1 p.2.2.1.val p.2.2.2.val*
    angularFactor (thetaFullFrequency p)
  let B:ℂ:=s.amplitude p.1 p.2.1 p.2.2.1.val p.2.2.2.val
  let lengthScale:ι→ℂ:=fun v=>w v*((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
    tracePhase (-cuspFrequency (thetaFullFrequency p)*((d v).dualPoint/(sourceCuspScale s.index:ℂ)))
  let R:ι→ℂ:=fun v=>w v*star (extendedComplexCharacter (g v))*
    tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
      (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/ringComplex c)
  have hs:A*(∑v,lengthScale v)=s.stratumShapeFactor c*B*(∑v,R v):=by
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [lengthScale,R]
    calc
      _=w v*(((d v).multiplier*((Ideal.absNorm (Ideal.span {c}):ℝ):ℂ))*
          (A*tracePhase (-cuspFrequency (thetaFullFrequency p)*
            ((d v).dualPoint/(sourceCuspScale s.index:ℂ))))):=by ring
      _=w v*((s.stratumShapeFactor c*star (extendedComplexCharacter (g v)))*
          (B*tracePhase (-(ringComplex (((g v:SL(2,Eis))*H) 1 1)*
            (ringComplex (sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency p))/(ringComplex traceLambda)^4))/ringComplex c))):=by
        rw [s.datum_common_row_factor (g v) c hc (hC v),s.datum_integral_phase (g v) c hc (hC v) p]
      _=_:=by ring
  let D:ℂ:=((ramifiedScale 1 completedRamifiedStep p.2.1*
    Real.sqrt (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ):ℝ):ℂ)
  let K:ℂ:=angularPaperKernel k (Vstar W)
    ((X/(27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep p.2.1)^3*
      (Ideal.absNorm p.2.2.1.val:ℝ)*(Ideal.absNorm p.2.2.2.val:ℝ)^3)
  have hjet (v : ι) : (d v).jetMultiplier (6*k) = (d v).multiplier * elemPsiSix c^(2*k) := by
    dsimp only [d]
    rw [s.datum_jetMultiplier_six_mul]
    exact congrArg (fun z : Eis => (d v).multiplier * elemPsiSix z^(2*k)) (hC v)
  have hsum : (∑ v, w v * ((d v).jetMultiplier (6*k) *
      ((Ideal.absNorm (Ideal.span {c}) : ℝ) : ℂ)) *
      tracePhase (-cuspFrequency (thetaFullFrequency p) * ((d v).dualPoint / (sourceCuspScale s.index : ℂ)))) =
      elemPsiSix c^(2*k) * ∑ v, lengthScale v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hjet v]
    dsimp only [lengthScale]
    ring
  rw [hsum]
  change (conj (elemPsiSix (thetaFullFrequency p))^k*A)/D*K*
    (elemPsiSix c^(2*k)*(∑v,lengthScale v)) =
    (s.stratumShapeFactor c*elemPsiSix c^(2*k))*
      ((conj (elemPsiSix (thetaFullFrequency p))^k*B)/D*K*(∑v,R v))
  calc
    _=elemPsiSix c^(2*k)*conj (elemPsiSix (thetaFullFrequency p))^k*
        ((A*(∑v,lengthScale v))/D*K) := by ring
    _=_ := by rw [hs]; ring

end FixedCuspShape

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
