import GaloisForLFunctions.HTGeometry.CoordinateEinsteinAffineCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual mixed second and third variations of coordinate Einstein curvature

The complete metric two-jet is represented by a normed product of its three arrays. The literal
Einstein contraction is smooth locally at every nondegenerate metric. Its iterated Fréchet
derivatives therefore give actual multilinear variations, with symmetry proved locally.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff
noncomputable section

/-- Normed coordinates for the complete metric two-jet, including every ordered spatial partial. -/
abbrev MetricTwoJetSpace (d : ℕ) :=
  (Fin d → Fin d → ℝ) ×
    (Fin d → Fin d → Fin d → ℝ) ×
    (Fin d → Fin d → Fin d → Fin d → ℝ)

namespace CoordinateMetricTwoJet

variable {d : ℕ} {n : ℕ∞ω}

/-- The complete jet in its normed product coordinates. -/
def toSpace (J : CoordinateMetricTwoJet d ℝ) : MetricTwoJetSpace d :=
  (J.metric, J.first, J.second)

/-- Decode normed product coordinates without imposing additional jet constraints. -/
def ofSpace (q : MetricTwoJetSpace d) : CoordinateMetricTwoJet d ℝ :=
  ⟨q.1, q.2.1, q.2.2⟩

@[simp] theorem ofSpace_toSpace (J : CoordinateMetricTwoJet d ℝ) :
    ofSpace J.toSpace = J := rfl

@[simp] theorem toSpace_ofSpace (q : MetricTwoJetSpace d) :
    (ofSpace q).toSpace = q := rfl

/-- Affine product coordinates coincide with the literal affine metric two-jet. -/
theorem ofSpace_affine (J K : CoordinateMetricTwoJet d ℝ) (t : ℝ) :
    ofSpace (J.toSpace + t • K.toSpace) = affinePerturbation J K t := rfl

private theorem smooth_metric (i j : Fin d) :
    ContDiff ℝ n (fun q : MetricTwoJetSpace d => (ofSpace q).metric i j) := by
  change ContDiff ℝ n (fun q : MetricTwoJetSpace d => q.1 i j)
  fun_prop

private theorem smooth_first (k i j : Fin d) :
    ContDiff ℝ n (fun q : MetricTwoJetSpace d => (ofSpace q).first k i j) := by
  change ContDiff ℝ n (fun q : MetricTwoJetSpace d => q.2.1 k i j)
  fun_prop

private theorem smooth_second (k l i j : Fin d) :
    ContDiff ℝ n (fun q : MetricTwoJetSpace d => (ofSpace q).second k l i j) := by
  change ContDiff ℝ n (fun q : MetricTwoJetSpace d => q.2.2 k l i j)
  fun_prop

private theorem smoothAt_inverse (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℝ n (fun r : MetricTwoJetSpace d => (ofSpace r).metric⁻¹ i j) q := by
  have heq : (fun r : MetricTwoJetSpace d => (ofSpace r).metric⁻¹ i j) =
      fun r => ((ofSpace r).metric.det)⁻¹ * (ofSpace r).metric.adjugate i j := by
    funext r
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact ((contDiff_matrix_det smooth_metric).contDiffAt.inv hq).mul
    (contDiff_matrix_adjugate_apply smooth_metric i j).contDiffAt

private theorem smoothAt_inverseDerivative (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k i j : Fin d) : ContDiffAt ℝ n (fun r => (ofSpace r).inverseDerivative k i j) q := by
  simp only [inverseDerivative, Matrix.neg_apply, Matrix.mul_apply]
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro m _
    exact (smoothAt_inverse q hq i m).mul (smooth_first k m l).contDiffAt
  · exact smoothAt_inverse q hq l j

private theorem smoothAt_christoffel (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (u i j : Fin d) : ContDiffAt ℝ n (fun r => (ofSpace r).christoffel u i j) q := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact (smoothAt_inverse q hq u m).mul
    (((smooth_first i m j).contDiffAt.add (smooth_first j m i).contDiffAt).sub
      (smooth_first m i j).contDiffAt)

private theorem smoothAt_christoffelDerivative (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k u i j : Fin d) : ContDiffAt ℝ n (fun r => (ofSpace r).christoffelDerivative k u i j) q := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact ((smoothAt_inverseDerivative q hq k u m).mul
    (((smooth_first i m j).contDiffAt.add (smooth_first j m i).contDiffAt).sub
      (smooth_first m i j).contDiffAt)).add
    ((smoothAt_inverse q hq u m).mul
      (((smooth_second k i m j).contDiffAt.add (smooth_second k j m i).contDiffAt).sub
        (smooth_second k m i j).contDiffAt))

private theorem smoothAt_riemann (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (u i k l : Fin d) : ContDiffAt ℝ n (fun r => (ofSpace r).riemann u i k l) q := by
  apply ContDiffAt.add
    ((smoothAt_christoffelDerivative q hq k u l i).sub
      (smoothAt_christoffelDerivative q hq l u k i))
  apply ContDiffAt.sum
  intro m _
  exact ((smoothAt_christoffel q hq u k m).mul (smoothAt_christoffel q hq m l i)).sub
    ((smoothAt_christoffel q hq u l m).mul (smoothAt_christoffel q hq m k i))

private theorem smoothAt_ricci (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℝ n (fun r => (ofSpace r).ricci i j) q := by
  exact ContDiffAt.sum fun u _ => smoothAt_riemann q hq u i u j

private theorem smoothAt_scalar (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0) :
    ContDiffAt ℝ n (fun r => (ofSpace r).scalar) q := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (smoothAt_inverse q hq i j).mul (smoothAt_ricci q hq i j)

/-- Literal coordinate Einstein curvature as a scalar function on complete jet coordinates. -/
def einsteinComponent (i j : Fin d) (q : MetricTwoJetSpace d) : ℝ :=
  (ofSpace q).einstein i j

/-- All orders of local smoothness follow from the actual rational curvature contraction. -/
theorem contDiffAt_einsteinComponent (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℝ n (einsteinComponent i j) q := by
  exact (smoothAt_ricci q hq i j).sub
    ((contDiffAt_const.mul (smoothAt_scalar q hq)).mul (smooth_metric i j).contDiffAt)

/-- The actual second Einstein variation, bilinear in complete jet perturbations. -/
def secondVariation (q : MetricTwoJetSpace d) (i j : Fin d) :
    MetricTwoJetSpace d →L[ℝ] MetricTwoJetSpace d →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (einsteinComponent i j)) q

/-- The actual third Einstein variation, trilinear in complete jet perturbations. -/
def thirdVariation (q : MetricTwoJetSpace d) (i j : Fin d) :
    MetricTwoJetSpace d →L[ℝ] MetricTwoJetSpace d →L[ℝ] MetricTwoJetSpace d →L[ℝ] ℝ :=
  fderiv ℝ (fun r => secondVariation r i j) q

/-- The actual Einstein Hessian is symmetric at every nondegenerate background. -/
theorem secondVariation_symm (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v : MetricTwoJetSpace d) :
    secondVariation q i j u v = secondVariation q i j v u :=
  ((contDiffAt_einsteinComponent (n := 3) q hq i j).isSymmSndFDerivAt (by norm_num)) u v

/-- The first two third-variation slots commute by local Hessian symmetry of the derivative. -/
theorem thirdVariation_symm_left (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : MetricTwoJetSpace d) :
    thirdVariation q i j u v w = thirdVariation q i j v u w := by
  have h := (contDiffAt_einsteinComponent (n := 3) q hq i j).fderiv_right (m := 2) (by norm_num)
  exact congrArg (fun L => L w) ((h.isSymmSndFDerivAt (by norm_num)) u v)

/-- The final two third-variation slots commute by differentiating local Hessian symmetry. -/
theorem thirdVariation_symm_right (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (u v w : MetricTwoJetSpace d) :
    thirdVariation q i j u v w = thirdVariation q i j u w v := by
  have hA := contDiffAt_einsteinComponent (n := 3) q hq i j
  have h1 : HasFDerivAt (fun r => secondVariation r i j) (thirdVariation q i j) q :=
    (((hA.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have step : ∀ a b : MetricTwoJetSpace d,
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

private theorem affineLine_hasDerivAt (J K : CoordinateMetricTwoJet d ℝ) (t : ℝ) :
    HasDerivAt (fun s => J.toSpace + s • K.toSpace) K.toSpace t := by
  simpa using ((hasDerivAt_id t).smul_const K.toSpace).const_add J.toSpace

/-- A derivative certificate for the actual multilinear variations along an affine jet line. -/
private def variationCurve (J K : CoordinateMetricTwoJet d ℝ) (i j : Fin d) :
    CubicDerivativeCurve (affineNondegenerateDomain J K) where
  value := fun t => einsteinComponent i j (J.toSpace + t • K.toSpace)
  first := fun t => fderiv ℝ (einsteinComponent i j) (J.toSpace + t • K.toSpace) K.toSpace
  second := fun t => secondVariation (J.toSpace + t • K.toSpace) i j K.toSpace K.toSpace
  third := fun t => thirdVariation (J.toSpace + t • K.toSpace) i j K.toSpace K.toSpace K.toSpace
  has_first := by
    intro t ht
    have h := contDiffAt_einsteinComponent (n := 3) (J.toSpace + t • K.toSpace) ht i j
    exact (h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (affineLine_hasDerivAt J K t)
  has_second := by
    intro t ht
    have h := (contDiffAt_einsteinComponent (n := 3) (J.toSpace + t • K.toSpace) ht i j).fderiv_right (m := 2) (by norm_num)
    have hd := (h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (affineLine_hasDerivAt J K t)
    simpa [secondVariation] using hd.clm_apply (hasDerivAt_const t K.toSpace)
  has_third := by
    intro t ht
    have h := ((contDiffAt_einsteinComponent (n := 3) (J.toSpace + t • K.toSpace) ht i j).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
    have hd := (h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
      (affineLine_hasDerivAt J K t)
    simpa [thirdVariation, secondVariation] using
      (hd.clm_apply (hasDerivAt_const t K.toSpace)).clm_apply (hasDerivAt_const t K.toSpace)

/-- The actual bilinear form recovers the previously constructed finite quadratic coefficient. -/
theorem secondVariation_diagonal (J K : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    secondVariation J.toSpace i j K.toSpace K.toSpace / 2 =
      affineEinsteinQuadraticCoefficient J K i j := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by
    simpa [affineNondegenerateDomain] using hJ
  have hd := (variationCurve J K i j).iteratedDeriv_two_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (variationCurve J K i j).value =
      fun t => (affinePerturbation J K t).einstein i j := by
    funext t
    exact congrArg (fun L => L.einstein i j) (ofSpace_affine J K t)
  rw [heq] at hd
  rw [affineEinsteinQuadraticCoefficient_eq_iteratedDeriv J K hJ i j, hd]
  simp [variationCurve]

/-- The actual trilinear form recovers the previously constructed finite cubic coefficient. -/
theorem thirdVariation_diagonal (J K : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) :
    thirdVariation J.toSpace i j K.toSpace K.toSpace K.toSpace / 6 =
      affineEinsteinCubicCoefficient J K i j := by
  have ht : (0 : ℝ) ∈ affineNondegenerateDomain J K := by
    simpa [affineNondegenerateDomain] using hJ
  have hd := (variationCurve J K i j).iteratedDeriv_three_value
    (isOpen_affineNondegenerateDomain J K) ht
  have heq : (variationCurve J K i j).value =
      fun t => (affinePerturbation J K t).einstein i j := by
    funext t
    exact congrArg (fun L => L.einstein i j) (ofSpace_affine J K t)
  rw [heq] at hd
  rw [affineEinsteinCubicCoefficient_eq_iteratedDeriv J K hJ i j, hd]
  simp [variationCurve]

/-- Exact quadratic two-mode expansion of the actual Einstein variation. -/
theorem secondVariation_twoMode (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (p m : MetricTwoJetSpace d) (x y : ℝ) :
    secondVariation q i j (x • p + y • m) (x • p + y • m) / 2 =
      x ^ 2 * (secondVariation q i j p p / 2) +
      x * y * secondVariation q i j p m +
      y ^ 2 * (secondVariation q i j m m / 2) := by
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [secondVariation_symm q hq i j m p]
  ring

/-- Cubic two-mode extraction retains all slot permutations before any symmetry is used. -/
theorem thirdVariation_twoMode_permutations (q : MetricTwoJetSpace d)
    (i j : Fin d) (p m : MetricTwoJetSpace d) (x y : ℝ) :
    thirdVariation q i j (x • p + y • m) (x • p + y • m) (x • p + y • m) / 6 =
      x ^ 3 * (thirdVariation q i j p p p / 6) +
      x ^ 2 * y * ((thirdVariation q i j p p m + thirdVariation q i j p m p +
        thirdVariation q i j m p p) / 6) +
      x * y ^ 2 * ((thirdVariation q i j p m m + thirdVariation q i j m p m +
        thirdVariation q i j m m p) / 6) +
      y ^ 3 * (thirdVariation q i j m m m / 6) := by
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- Proved symmetry identifies the actual direct `++-` source with half of `C(p,p,m)`. -/
theorem thirdVariation_plusPlusMinus (q : MetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) (p m : MetricTwoJetSpace d) :
    (thirdVariation q i j p p m + thirdVariation q i j p m p +
      thirdVariation q i j m p p) / 6 = thirdVariation q i j p p m / 2 := by
  rw [thirdVariation_symm_left q hq i j m p p,
    thirdVariation_symm_right q hq i j p m p]
  ring

/-- Complete symmetric cubic two-mode expansion of the literal Einstein coefficient. -/
theorem affineEinsteinCubicCoefficient_twoMode (J : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) (p m : MetricTwoJetSpace d) (x y : ℝ) :
    affineEinsteinCubicCoefficient J (ofSpace (x • p + y • m)) i j =
      x ^ 3 * affineEinsteinCubicCoefficient J (ofSpace p) i j +
      x ^ 2 * y * (thirdVariation J.toSpace i j p p m / 2) +
      x * y ^ 2 * (thirdVariation J.toSpace i j p m m / 2) +
      y ^ 3 * affineEinsteinCubicCoefficient J (ofSpace m) i j := by
  rw [← thirdVariation_diagonal J (ofSpace (x • p + y • m)) hJ i j,
    ← thirdVariation_diagonal J (ofSpace p) hJ i j,
    ← thirdVariation_diagonal J (ofSpace m) hJ i j]
  simp only [toSpace_ofSpace]
  rw [thirdVariation_twoMode_permutations, thirdVariation_plusPlusMinus J.toSpace hJ]
  rw [thirdVariation_symm_left J.toSpace hJ i j m p m,
    thirdVariation_symm_right J.toSpace hJ i j m m p,
    thirdVariation_symm_left J.toSpace hJ i j m p m]
  ring

/-- The actual direct mixed cubic source is recovered from three explicit finite coefficients. -/
theorem thirdVariation_plusPlusMinus_polarization (J : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) (p m : MetricTwoJetSpace d) :
    thirdVariation J.toSpace i j p p m / 2 =
      (affineEinsteinCubicCoefficient J (ofSpace (p + m)) i j -
        affineEinsteinCubicCoefficient J (ofSpace (p - m)) i j -
        2 * affineEinsteinCubicCoefficient J (ofSpace m) i j) / 2 := by
  have hp := affineEinsteinCubicCoefficient_twoMode J hJ i j p m 1 1
  have hm := affineEinsteinCubicCoefficient_twoMode J hJ i j p m 1 (-1)
  simp only [one_smul, neg_smul, one_pow, one_mul, mul_one, mul_neg,
    sub_eq_add_neg] at hp hm ⊢
  rw [hp, hm]
  ring

/-- The actual mixed quadratic source is obtained by polarizing the finite diagonal formula. -/
theorem secondVariation_polarization (J : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) (p m : MetricTwoJetSpace d) :
    secondVariation J.toSpace i j p m =
      affineEinsteinQuadraticCoefficient J (ofSpace (p + m)) i j -
        affineEinsteinQuadraticCoefficient J (ofSpace p) i j -
        affineEinsteinQuadraticCoefficient J (ofSpace m) i j := by
  rw [← secondVariation_diagonal J (ofSpace (p + m)) hJ i j,
    ← secondVariation_diagonal J (ofSpace p) hJ i j,
    ← secondVariation_diagonal J (ofSpace m) hJ i j]
  simp only [toSpace_ofSpace]
  have h := secondVariation_twoMode J.toSpace hJ i j p m 1 1
  simp only [one_smul, one_pow, one_mul] at h
  rw [h]
  ring

/-- Full cubic polarization recovers every mixed slot from the explicit finite coefficient. -/
theorem thirdVariation_polarization (J : CoordinateMetricTwoJet d ℝ)
    (hJ : J.metric.det ≠ 0) (i j : Fin d) (u v w : MetricTwoJetSpace d) :
    thirdVariation J.toSpace i j u v w =
      affineEinsteinCubicCoefficient J (ofSpace (u + v + w)) i j -
        affineEinsteinCubicCoefficient J (ofSpace (u + v)) i j -
        affineEinsteinCubicCoefficient J (ofSpace (u + w)) i j -
        affineEinsteinCubicCoefficient J (ofSpace (v + w)) i j +
        affineEinsteinCubicCoefficient J (ofSpace u) i j +
        affineEinsteinCubicCoefficient J (ofSpace v) i j +
        affineEinsteinCubicCoefficient J (ofSpace w) i j := by
  have hc (r : MetricTwoJetSpace d) :
      affineEinsteinCubicCoefficient J (ofSpace r) i j =
        thirdVariation J.toSpace i j r r r / 6 := by
    simpa only [toSpace_ofSpace] using (thirdVariation_diagonal J (ofSpace r) hJ i j).symm
  have h₁ := thirdVariation_symm_right J.toSpace hJ i j u w v
  have h₂ := thirdVariation_symm_left J.toSpace hJ i j v u w
  have h₃ := (thirdVariation_symm_right J.toSpace hJ i j v w u).trans h₂
  have h₄ := (thirdVariation_symm_left J.toSpace hJ i j w u v).trans h₁
  have h₅ := (thirdVariation_symm_left J.toSpace hJ i j w v u).trans h₃
  simp only [hc, map_add, add_apply, h₁, h₂, h₃, h₄, h₅]
  ring

end CoordinateMetricTwoJet
end
end GaloisForLFunctions.HTGeometry
