import GaloisForLFunctions.HTGeometry.CoordinateEinsteinMixedVariations
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic

/-!
# Complex Einstein variations and their real restriction

The actual rational Einstein contraction commutes with scalar extension. Its locally holomorphic
second and third variations are therefore identified with the real variations by derivative
uniqueness after restriction of scalars, retaining all spatial jet coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff
noncomputable section

namespace CoordinateMetricTwoJet

variable {d : ℕ} {K L : Type*} [Field K] [Field L]

/-- Apply a scalar field homomorphism to every entry of the complete metric two-jet. -/
def mapScalars (f : K →+* L) (J : CoordinateMetricTwoJet d K) : CoordinateMetricTwoJet d L :=
  ⟨J.metric.map f, fun k => (J.first k).map f, fun k l => (J.second k l).map f⟩

private theorem mapScalars_inverse (f : K →+* L) (A : Matrix (Fin d) (Fin d) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  ext i j
  have hdet := f.map_det A
  have hadj := congrArg (fun M => M i j) (f.map_adjugate A)
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hdet hadj
  simp only [Matrix.inv_def, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv']
  rw [← hdet, map_mul, map_inv₀, hadj]

private theorem mapScalars_christoffel (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (u i j : Fin d) : (mapScalars f J).christoffel u i j = f (J.christoffel u i j) := by
  simp [christoffel, mapScalars, mapScalars_inverse, map_ofNat]

private theorem mapScalars_inverseDerivative (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (k i j : Fin d) : (mapScalars f J).inverseDerivative k i j = f (J.inverseDerivative k i j) := by
  simp [inverseDerivative, mapScalars, mapScalars_inverse, Matrix.mul_apply]

private theorem mapScalars_christoffelDerivative (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (k u i j : Fin d) :
    (mapScalars f J).christoffelDerivative k u i j = f (J.christoffelDerivative k u i j) := by
  simp only [christoffelDerivative, mapScalars_inverseDerivative]
  simp [mapScalars, mapScalars_inverse, map_ofNat]

private theorem mapScalars_riemann (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (u i k l : Fin d) : (mapScalars f J).riemann u i k l = f (J.riemann u i k l) := by
  simp [riemann, mapScalars_christoffelDerivative, mapScalars_christoffel]

private theorem mapScalars_ricci (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (i j : Fin d) : (mapScalars f J).ricci i j = f (J.ricci i j) := by
  simp [ricci, mapScalars_riemann]

private theorem mapScalars_scalar (f : K →+* L) (J : CoordinateMetricTwoJet d K) :
    (mapScalars f J).scalar = f J.scalar := by
  simp only [scalar, mapScalars_ricci]
  simp [mapScalars, mapScalars_inverse]

/-- The literal Einstein contraction commutes with every scalar field homomorphism. -/
theorem mapScalars_einstein (f : K →+* L) (J : CoordinateMetricTwoJet d K)
    (i j : Fin d) : (mapScalars f J).einstein i j = f (J.einstein i j) := by
  simp only [einstein, mapScalars_ricci, mapScalars_scalar]
  simp [mapScalars, map_ofNat]

end CoordinateMetricTwoJet

private theorem complex_contDiff_matrix_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} {n : ℕ∞ω} {A : E → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i j, ContDiff ℂ n fun x => A x i j) :
    ContDiff ℂ n fun x => (A x).det := by
  have heq : (fun x => (A x).det) =
      fun x => ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℂ) * ∏ i, A x (σ i) i := by
    funext x
    exact Matrix.det_apply' (A x)
  rw [heq]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA (σ i) i)

private theorem complex_contDiff_matrix_adjugate_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {d : ℕ} {n : ℕ∞ω} {A : E → Matrix (Fin d) (Fin d) ℂ}
    (hA : ∀ i j, ContDiff ℂ n fun x => A x i j) (i j : Fin d) :
    ContDiff ℂ n fun x => (A x).adjugate i j := by
  have heq : (fun x => (A x).adjugate i j) =
      fun x => ((A x).updateRow j (Pi.single i 1)).det := by
    funext x
    exact Matrix.adjugate_apply (A x) i j
  rw [heq]
  apply complex_contDiff_matrix_det
  intro k l
  by_cases hk : k = j
  · simpa [Matrix.updateRow_apply, hk] using
      (contDiff_const : ContDiff ℂ n (fun _ : E => (Pi.single i (1 : ℂ) : Fin d → ℂ) l))
  · simpa [Matrix.updateRow_apply, hk] using hA k l

/-- Normed coordinates for the complete metric two-jet, including every ordered spatial partial. -/
abbrev ComplexMetricTwoJetSpace (d : ℕ) :=
  (Fin d → Fin d → ℂ) ×
    (Fin d → Fin d → Fin d → ℂ) ×
    (Fin d → Fin d → Fin d → Fin d → ℂ)

namespace ComplexCoordinateMetricTwoJet

variable {d : ℕ} {n : ℕ∞ω}

/-- The complete jet in its normed product coordinates. -/
def toSpace (J : CoordinateMetricTwoJet d ℂ) : ComplexMetricTwoJetSpace d :=
  (J.metric, J.first, J.second)

/-- Decode normed product coordinates without imposing additional jet constraints. -/
def ofSpace (q : ComplexMetricTwoJetSpace d) : CoordinateMetricTwoJet d ℂ :=
  ⟨q.1, q.2.1, q.2.2⟩

@[simp] theorem ofSpace_toSpace (J : CoordinateMetricTwoJet d ℂ) :
    ofSpace (toSpace J) = J := rfl

@[simp] theorem toSpace_ofSpace (q : ComplexMetricTwoJetSpace d) :
    toSpace (ofSpace q) = q := rfl

private theorem smooth_metric (i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ofSpace q).metric i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.1 i j)
  fun_prop

private theorem smooth_first (k i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ofSpace q).first k i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.2.1 k i j)
  fun_prop

private theorem smooth_second (k l i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ofSpace q).second k l i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.2.2 k l i j)
  fun_prop

private theorem smoothAt_inverse (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (fun r : ComplexMetricTwoJetSpace d => (ofSpace r).metric⁻¹ i j) q := by
  have heq : (fun r : ComplexMetricTwoJetSpace d => (ofSpace r).metric⁻¹ i j) =
      fun r => ((ofSpace r).metric.det)⁻¹ * (ofSpace r).metric.adjugate i j := by
    funext r
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact ((complex_contDiff_matrix_det smooth_metric).contDiffAt.inv hq).mul
    (complex_contDiff_matrix_adjugate_apply smooth_metric i j).contDiffAt

private theorem smoothAt_inverseDerivative (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k i j : Fin d) : ContDiffAt ℂ n (fun r => (ofSpace r).inverseDerivative k i j) q := by
  simp only [CoordinateMetricTwoJet.inverseDerivative, Matrix.neg_apply, Matrix.mul_apply]
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro m _
    exact (smoothAt_inverse q hq i m).mul (smooth_first k m l).contDiffAt
  · exact smoothAt_inverse q hq l j

private theorem smoothAt_christoffel (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (u i j : Fin d) : ContDiffAt ℂ n (fun r => (ofSpace r).christoffel u i j) q := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact (smoothAt_inverse q hq u m).mul
    (((smooth_first i m j).contDiffAt.add (smooth_first j m i).contDiffAt).sub
      (smooth_first m i j).contDiffAt)

private theorem smoothAt_christoffelDerivative (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k u i j : Fin d) : ContDiffAt ℂ n (fun r => (ofSpace r).christoffelDerivative k u i j) q := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact ((smoothAt_inverseDerivative q hq k u m).mul
    (((smooth_first i m j).contDiffAt.add (smooth_first j m i).contDiffAt).sub
      (smooth_first m i j).contDiffAt)).add
    ((smoothAt_inverse q hq u m).mul
      (((smooth_second k i m j).contDiffAt.add (smooth_second k j m i).contDiffAt).sub
        (smooth_second k m i j).contDiffAt))

private theorem smoothAt_riemann (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (u i k l : Fin d) : ContDiffAt ℂ n (fun r => (ofSpace r).riemann u i k l) q := by
  apply ContDiffAt.add
    ((smoothAt_christoffelDerivative q hq k u l i).sub
      (smoothAt_christoffelDerivative q hq l u k i))
  apply ContDiffAt.sum
  intro m _
  exact ((smoothAt_christoffel q hq u k m).mul (smoothAt_christoffel q hq m l i)).sub
    ((smoothAt_christoffel q hq u l m).mul (smoothAt_christoffel q hq m k i))

private theorem smoothAt_ricci (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (fun r => (ofSpace r).ricci i j) q := by
  exact ContDiffAt.sum fun u _ => smoothAt_riemann q hq u i u j

private theorem smoothAt_scalar (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0) :
    ContDiffAt ℂ n (fun r => (ofSpace r).scalar) q := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (smoothAt_inverse q hq i j).mul (smoothAt_ricci q hq i j)

/-- Literal coordinate Einstein curvature as a scalar function on complete jet coordinates. -/
def einsteinComponent (i j : Fin d) (q : ComplexMetricTwoJetSpace d) : ℂ :=
  (ofSpace q).einstein i j

/-- All orders of local smoothness follow from the actual rational curvature contraction. -/
theorem contDiffAt_einsteinComponent (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (einsteinComponent i j) q := by
  exact (smoothAt_ricci q hq i j).sub
    ((contDiffAt_const.mul (smoothAt_scalar q hq)).mul (smooth_metric i j).contDiffAt)

/-- The actual second Einstein variation, bilinear in complete jet perturbations. -/
def secondVariation (q : ComplexMetricTwoJetSpace d) (i j : Fin d) :
    ComplexMetricTwoJetSpace d →L[ℂ] ComplexMetricTwoJetSpace d →L[ℂ] ℂ :=
  fderiv ℂ (fderiv ℂ (einsteinComponent i j)) q

/-- The actual third Einstein variation, trilinear in complete jet perturbations. -/
def thirdVariation (q : ComplexMetricTwoJetSpace d) (i j : Fin d) :
    ComplexMetricTwoJetSpace d →L[ℂ] ComplexMetricTwoJetSpace d →L[ℂ] ComplexMetricTwoJetSpace d →L[ℂ] ℂ :=
  fderiv ℂ (fun r => secondVariation r i j) q

/-- The actual Einstein Hessian is symmetric at every nondegenerate background. -/
theorem secondVariation_symm (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v : ComplexMetricTwoJetSpace d) :
    secondVariation q i j u v = secondVariation q i j v u :=
  ((contDiffAt_einsteinComponent (n := 3) q hq i j).isSymmSndFDerivAt (by norm_num)) u v

/-- The first two third-variation slots commute by local Hessian symmetry of the derivative. -/
theorem thirdVariation_symm_left (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : ComplexMetricTwoJetSpace d) :
    thirdVariation q i j u v w = thirdVariation q i j v u w := by
  have h := (contDiffAt_einsteinComponent (n := 3) q hq i j).fderiv_right (m := 2) (by norm_num)
  exact congrArg (fun L => L w) ((h.isSymmSndFDerivAt (by norm_num)) u v)

/-- The final two third-variation slots commute by differentiating local Hessian symmetry. -/
theorem thirdVariation_symm_right (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : ComplexMetricTwoJetSpace d) :
    thirdVariation q i j u v w = thirdVariation q i j u w v := by
  have hA := contDiffAt_einsteinComponent (n := 3) q hq i j
  have h1 : HasFDerivAt (fun r => secondVariation r i j) (thirdVariation q i j) q :=
    (((hA.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have step : ∀ a b : ComplexMetricTwoJetSpace d,
      HasFDerivAt (fun r => secondVariation r i j a b)
        (((thirdVariation q i j).flip a).flip b) q := by
    intro a b
    simpa using (h1.clm_apply (hasFDerivAt_const a q)).clm_apply (hasFDerivAt_const b q)
  have heq : (fun r => secondVariation r i j v w) =ᶠ[nhds q]
      fun r => secondVariation r i j w v := by
    filter_upwards [hA.eventually (by simp)] with r hr
    exact (hr.isSymmSndFDerivAt (by norm_num)) v w
  have h := ((step v w).congr_of_eventuallyEq heq.symm).unique (step w v)
  exact congrArg (fun L => L u) h


/-- Entrywise real inclusion of the complete jet, as a real continuous linear map. -/
def realInclusion : MetricTwoJetSpace d →L[ℝ] ComplexMetricTwoJetSpace d where
  toFun q := (fun i j => (q.1 i j : ℂ), fun k i j => (q.2.1 k i j : ℂ),
    fun k l i j => (q.2.2 k l i j : ℂ))
  map_add' q r := by ext <;> simp
  map_smul' t q := by ext <;> simp
  cont := by fun_prop

/-- Scalar extension preserves the literal Einstein component, including its inverse terms. -/
theorem einsteinComponent_real (q : MetricTwoJetSpace d) (i j : Fin d) :
    einsteinComponent i j (realInclusion q) =
      (CoordinateMetricTwoJet.einsteinComponent i j q : ℂ) :=
  CoordinateMetricTwoJet.mapScalars_einstein Complex.ofRealHom
    (CoordinateMetricTwoJet.ofSpace q) i j

private theorem realInclusion_det_ne_zero (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0) :
    Matrix.det (realInclusion q).1 ≠ 0 := by
  have hd : ((Matrix.det q.1 : ℝ) : ℂ) = Matrix.det (realInclusion q).1 :=
    Complex.ofRealHom.map_det q.1
  rw [← hd]
  exact_mod_cast hq

private theorem real_nondegenerate_eventually (q : MetricTwoJetSpace d)
    (hq : Matrix.det q.1 ≠ 0) : ∀ᶠ r in nhds q, Matrix.det r.1 ≠ 0 := by
  have hc : Continuous (fun r : MetricTwoJetSpace d => Matrix.det r.1) :=
    (contDiff_matrix_det (n := 0) (fun i j => by fun_prop)).continuous
  exact hc.continuousAt.eventually_ne hq

private theorem derivative_real_compatibility
    {f : MetricTwoJetSpace d → ℝ} {F : ComplexMetricTwoJetSpace d → ℂ}
    {q : MetricTwoJetSpace d} {df : MetricTwoJetSpace d →L[ℝ] ℝ}
    {dF : ComplexMetricTwoJetSpace d →L[ℂ] ℂ}
    (hf : HasFDerivAt f df q) (hF : HasFDerivAt F dF (realInclusion q))
    (heq : (fun r => F (realInclusion r)) =ᶠ[nhds q] fun r => (f r : ℂ))
    (u : MetricTwoJetSpace d) : dF (realInclusion u) = (df u : ℂ) := by
  have h₁ := (hF.restrictScalars ℝ).comp q realInclusion.hasFDerivAt
  have h₂ := Complex.ofRealCLM.hasFDerivAt.comp q hf
  have h := (h₁.congr_of_eventuallyEq heq.symm).unique h₂
  exact congrArg (fun L => L u) h

/-- The first complex variation restricts to the first real variation. -/
theorem firstVariation_real (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u : MetricTwoJetSpace d) :
    fderiv ℂ (einsteinComponent i j) (realInclusion q) (realInclusion u) =
      (fderiv ℝ (CoordinateMetricTwoJet.einsteinComponent i j) q u : ℂ) := by
  apply derivative_real_compatibility
  · exact ((CoordinateMetricTwoJet.contDiffAt_einsteinComponent (n := 3) q hq i j).differentiableAt
      (by norm_num)).hasFDerivAt
  · exact ((contDiffAt_einsteinComponent (n := 3) (realInclusion q)
      (realInclusion_det_ne_zero q hq) i j).differentiableAt (by norm_num)).hasFDerivAt
  · exact Filter.Eventually.of_forall (fun r => einsteinComponent_real r i j)

/-- The actual complex bilinear Einstein form agrees with the real one on real input slots. -/
theorem secondVariation_real (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v : MetricTwoJetSpace d) :
    secondVariation (realInclusion q) i j (realInclusion u) (realInclusion v) =
      (CoordinateMetricTwoJet.secondVariation q i j u v : ℂ) := by
  have hr := (CoordinateMetricTwoJet.contDiffAt_einsteinComponent (n := 3) q hq i j).fderiv_right
    (m := 2) (by norm_num)
  have hc := (contDiffAt_einsteinComponent (n := 3) (realInclusion q)
    (realInclusion_det_ne_zero q hq) i j).fderiv_right (m := 2) (by norm_num)
  have hdr := ((hr.differentiableAt (by norm_num)).hasFDerivAt).clm_apply (hasFDerivAt_const v q)
  have hdc := ((hc.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hasFDerivAt_const (realInclusion v) (realInclusion q))
  have heq : (fun r => fderiv ℂ (einsteinComponent i j) (realInclusion r) (realInclusion v))
      =ᶠ[nhds q] fun r => (fderiv ℝ (CoordinateMetricTwoJet.einsteinComponent i j) r v : ℂ) := by
    filter_upwards [real_nondegenerate_eventually q hq] with r hr
    exact firstVariation_real r hr i j v
  simpa [secondVariation, CoordinateMetricTwoJet.secondVariation] using
    derivative_real_compatibility hdr hdc heq u

/-- The actual complex trilinear Einstein form agrees with the real one on real input slots. -/
theorem thirdVariation_real (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : MetricTwoJetSpace d) :
    thirdVariation (realInclusion q) i j (realInclusion u) (realInclusion v) (realInclusion w) =
      (CoordinateMetricTwoJet.thirdVariation q i j u v w : ℂ) := by
  have hr := ((CoordinateMetricTwoJet.contDiffAt_einsteinComponent (n := 3) q hq i j).fderiv_right
    (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hc := ((contDiffAt_einsteinComponent (n := 3) (realInclusion q)
    (realInclusion_det_ne_zero q hq) i j).fderiv_right (m := 2)
      (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hdr := (((hr.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hasFDerivAt_const v q)).clm_apply (hasFDerivAt_const w q)
  have hdc := (((hc.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hasFDerivAt_const (realInclusion v) (realInclusion q))).clm_apply
      (hasFDerivAt_const (realInclusion w) (realInclusion q))
  have heq : (fun r => secondVariation (realInclusion r) i j (realInclusion v) (realInclusion w))
      =ᶠ[nhds q] fun r => (CoordinateMetricTwoJet.secondVariation r i j v w : ℂ) := by
    filter_upwards [real_nondegenerate_eventually q hq] with r hr
    exact secondVariation_real r hr i j v w
  simpa [thirdVariation, secondVariation, CoordinateMetricTwoJet.thirdVariation,
    CoordinateMetricTwoJet.secondVariation] using derivative_real_compatibility hdr hdc heq u

/-- Entrywise real part of the complete complex metric two-jet. -/
def realPart (q : ComplexMetricTwoJetSpace d) : MetricTwoJetSpace d :=
  (fun i j => (q.1 i j).re, fun k i j => (q.2.1 k i j).re,
    fun k l i j => (q.2.2 k l i j).re)

/-- Entrywise imaginary part of the complete complex metric two-jet. -/
def imagPart (q : ComplexMetricTwoJetSpace d) : MetricTwoJetSpace d :=
  (fun i j => (q.1 i j).im, fun k i j => (q.2.1 k i j).im,
    fun k l i j => (q.2.2 k l i j).im)

/-- Real jet inclusions span the complete complex jet space. -/
theorem real_imag_decomposition (q : ComplexMetricTwoJetSpace d) :
    q = realInclusion (realPart q) + Complex.I • realInclusion (imagPart q) := by
  ext <;> simp [realPart, imagPart, realInclusion, Complex.ext_iff]

/-- The constructed complex Hessian is the unique complex bilinear extension of the real one. -/
theorem secondVariation_unique_extension (q : MetricTwoJetSpace d)
    (hq : Matrix.det q.1 ≠ 0) (i j : Fin d)
    (B : ComplexMetricTwoJetSpace d →L[ℂ] ComplexMetricTwoJetSpace d →L[ℂ] ℂ)
    (hB : ∀ u v : MetricTwoJetSpace d, B (realInclusion u) (realInclusion v) =
      (CoordinateMetricTwoJet.secondVariation q i j u v : ℂ)) :
    B = secondVariation (realInclusion q) i j := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  rw [real_imag_decomposition u, real_imag_decomposition v]
  simp only [map_add, map_smul, add_apply, smul_apply, hB, secondVariation_real q hq]

/-- The constructed complex third variation is the unique complex trilinear extension. -/
theorem thirdVariation_unique_extension (q : MetricTwoJetSpace d)
    (hq : Matrix.det q.1 ≠ 0) (i j : Fin d)
    (C : ComplexMetricTwoJetSpace d →L[ℂ] ComplexMetricTwoJetSpace d →L[ℂ]
      ComplexMetricTwoJetSpace d →L[ℂ] ℂ)
    (hC : ∀ u v w : MetricTwoJetSpace d,
      C (realInclusion u) (realInclusion v) (realInclusion w) =
        (CoordinateMetricTwoJet.thirdVariation q i j u v w : ℂ)) :
    C = thirdVariation (realInclusion q) i j := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [real_imag_decomposition u, real_imag_decomposition v, real_imag_decomposition w]
  simp only [map_add, map_smul, add_apply, smul_apply, hC, thirdVariation_real q hq]

/-- Actual complex quadratic evaluation reduces to four real mixed evaluations. -/
theorem secondVariation_real_imag (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v : ComplexMetricTwoJetSpace d) :
    secondVariation (realInclusion q) i j u v =
      (CoordinateMetricTwoJet.secondVariation q i j (realPart u) (realPart v) : ℂ) -
      (CoordinateMetricTwoJet.secondVariation q i j (imagPart u) (imagPart v) : ℂ) +
      Complex.I * ((CoordinateMetricTwoJet.secondVariation q i j (realPart u) (imagPart v) : ℂ) +
        (CoordinateMetricTwoJet.secondVariation q i j (imagPart u) (realPart v) : ℂ)) := by
  conv_lhs => rw [real_imag_decomposition u, real_imag_decomposition v]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, secondVariation_real q hq]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Actual complex cubic evaluation reduces to eight real mixed evaluations. -/
theorem thirdVariation_real_imag (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : ComplexMetricTwoJetSpace d) :
    thirdVariation (realInclusion q) i j u v w =
      (CoordinateMetricTwoJet.thirdVariation q i j (realPart u) (realPart v) (realPart w) : ℂ) -
      (CoordinateMetricTwoJet.thirdVariation q i j (realPart u) (imagPart v) (imagPart w) : ℂ) -
      (CoordinateMetricTwoJet.thirdVariation q i j (imagPart u) (realPart v) (imagPart w) : ℂ) -
      (CoordinateMetricTwoJet.thirdVariation q i j (imagPart u) (imagPart v) (realPart w) : ℂ) +
      Complex.I * (
        (CoordinateMetricTwoJet.thirdVariation q i j (realPart u) (realPart v) (imagPart w) : ℂ) +
        (CoordinateMetricTwoJet.thirdVariation q i j (realPart u) (imagPart v) (realPart w) : ℂ) +
        (CoordinateMetricTwoJet.thirdVariation q i j (imagPart u) (realPart v) (realPart w) : ℂ) -
        (CoordinateMetricTwoJet.thirdVariation q i j (imagPart u) (imagPart v) (imagPart w) : ℂ)) := by
  conv_lhs => rw [real_imag_decomposition u, real_imag_decomposition v, real_imag_decomposition w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, thirdVariation_real q hq]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The complex direct `++-` source has the same proved permutation factor as the real source. -/
theorem thirdVariation_plusPlusMinus (q : ComplexMetricTwoJetSpace d)
    (hq : Matrix.det q.1 ≠ 0) (i j : Fin d) (p m : ComplexMetricTwoJetSpace d) :
    (thirdVariation q i j p p m + thirdVariation q i j p m p +
      thirdVariation q i j m p p) / 6 = thirdVariation q i j p p m / 2 := by
  rw [thirdVariation_symm_left q hq i j m p p,
    thirdVariation_symm_right q hq i j p m p]
  ring

end ComplexCoordinateMetricTwoJet
end
end GaloisForLFunctions.HTGeometry
