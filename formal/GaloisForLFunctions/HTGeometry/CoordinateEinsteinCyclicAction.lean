import GaloisForLFunctions.HTGeometry.CoordinateEinsteinActionVariation

set_option autoImplicit false

/-!
# Cyclic Einstein--Hilbert variation with its original boundary divergence

A fixed three-parameter family of complete metric jets retains the changing determinant
weight, both inverse metrics in the test contraction, and the full connection-current
divergence. The cyclicity defect of the paired Einstein source is exactly the boundary
cyclicity defect. Their difference is the negative third variation of the original action.
No field equation, flux cancellation, or causal boundary condition is assumed.
-/

open Complex Filter Topology
open scoped ContDiff BigOperators
namespace GaloisForLFunctions.HTGeometry.EinsteinCyclicVariation
open CoordinateMetricTwoJet CoordinateMetricTwoJet.Linearization
open ComplexCoordinateMetricTwoJet EinsteinActionBoundary MetricPathDensity
noncomputable section
variable {d : ℕ} {n : ℕ∞ω}
local notation "Jet" => CoordinateMetricTwoJet d ℂ
local notation "Param" => Fin 3 → ℂ
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

private theorem smooth_metric (i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace q).metric i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.1 i j)
  fun_prop

private theorem smooth_first (k i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace q).first k i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.2.1 k i j)
  fun_prop

private theorem smooth_second (k l i j : Fin d) :
    ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace q).second k l i j) := by
  change ContDiff ℂ n (fun q : ComplexMetricTwoJetSpace d => q.2.2 k l i j)
  fun_prop

private theorem smoothAt_inverse (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (fun r : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace r).metric⁻¹ i j) q := by
  have heq : (fun r : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace r).metric⁻¹ i j) =
      fun r => ((ComplexCoordinateMetricTwoJet.ofSpace r).metric.det)⁻¹ * (ComplexCoordinateMetricTwoJet.ofSpace r).metric.adjugate i j := by
    funext r
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact ((complex_contDiff_matrix_det smooth_metric).contDiffAt.inv hq).mul
    (complex_contDiff_matrix_adjugate_apply smooth_metric i j).contDiffAt

private theorem smoothAt_inverseDerivative (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k i j : Fin d) : ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).inverseDerivative k i j) q := by
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
    (u i j : Fin d) : ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).christoffel u i j) q := by
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact (smoothAt_inverse q hq u m).mul
    (((smooth_first i m j).contDiffAt.add (smooth_first j m i).contDiffAt).sub
      (smooth_first m i j).contDiffAt)

private theorem smoothAt_christoffelDerivative (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (k u i j : Fin d) : ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).christoffelDerivative k u i j) q := by
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
    (u i k l : Fin d) : ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).riemann u i k l) q := by
  apply ContDiffAt.add
    ((smoothAt_christoffelDerivative q hq k u l i).sub
      (smoothAt_christoffelDerivative q hq l u k i))
  apply ContDiffAt.sum
  intro m _
  exact ((smoothAt_christoffel q hq u k m).mul (smoothAt_christoffel q hq m l i)).sub
    ((smoothAt_christoffel q hq u l m).mul (smoothAt_christoffel q hq m k i))

private theorem smoothAt_ricci (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).ricci i j) q := by
  exact ContDiffAt.sum fun u _ => smoothAt_riemann q hq u i u j

private theorem smoothAt_scalar (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0) :
    ContDiffAt ℂ n (fun r => (ComplexCoordinateMetricTwoJet.ofSpace r).scalar) q := by
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    (smoothAt_inverse q hq i j).mul (smoothAt_ricci q hq i j)


/-- The original complete jet under three independent affine variations. -/
def family (J : Jet) (U : Fin 3 → Jet) (a : Param) : Jet :=
  ComplexCoordinateMetricTwoJet.ofSpace (ComplexCoordinateMetricTwoJet.toSpace J + ∑ k, a k • ComplexCoordinateMetricTwoJet.toSpace (U k))

private theorem family_zero (J : Jet) (U : Fin 3 → Jet) : family J U 0 = J := by
  simp [family]

private theorem family_smooth (J : Jet) (U : Fin 3 → Jet) :
    ContDiff ℂ n (fun a => ComplexCoordinateMetricTwoJet.toSpace (family J U a)) := by
  simp only [family, ComplexCoordinateMetricTwoJet.toSpace_ofSpace]
  fun_prop

private theorem family_line (J : Jet) (U : Fin 3 → Jet) (a : Param)
    (k : Fin 3) (t : ℂ) :
    family J U (a + t • Pi.single k 1) = affine (family J U a) (U k) t := by
  have haff : ComplexCoordinateMetricTwoJet.toSpace (affine (family J U a) (U k) t) =
      ComplexCoordinateMetricTwoJet.toSpace (family J U a) + t • ComplexCoordinateMetricTwoJet.toSpace (U k) := rfl
  have hh : ComplexCoordinateMetricTwoJet.toSpace (family J U (a + t • Pi.single k (1:ℂ))) =
      ComplexCoordinateMetricTwoJet.toSpace (affine (family J U a) (U k) t) := by
    rw [haff]
    simp only [family, ComplexCoordinateMetricTwoJet.toSpace_ofSpace,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
    simp only [mul_smul, ← Finset.smul_sum]
    simp [Pi.single_apply, add_assoc]
  simpa only [ComplexCoordinateMetricTwoJet.ofSpace_toSpace] using
    congrArg ComplexCoordinateMetricTwoJet.ofSpace hh

/-- Relative determinant density, with one fixed reference metric. -/
def weight (J : Jet) (U : Fin 3 → Jet) (a : Param) : ℂ :=
  Complex.exp (Complex.log ((family J U a).metric.det / J.metric.det) / 2)

/-- The actual Einstein--Hilbert scalar density of this metric family. -/
def density (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (a : Param) : ℂ :=
  weight J U a * ((family J U a).scalar - 2 * Λ)

private theorem family_det_smooth (J : Jet) (U : Fin 3 → Jet) :
    ContDiff ℂ n (fun a => (family J U a).metric.det) := by
  apply complex_contDiff_matrix_det
  intro i j
  change ContDiff ℂ n (fun a => (ComplexCoordinateMetricTwoJet.toSpace (family J U a)).1 i j)
  fun_prop

private theorem weight_smooth (J : Jet) (U : Fin 3 → Jet) (a : Param)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane) :
    ContDiffAt ℂ n (weight J U) a := by
  exact (((Complex.contDiffAt_log ha).comp a
    ((family_det_smooth J U).contDiffAt.div_const J.metric.det)).div_const 2).cexp

private theorem density_smooth (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (a : Param)
    (hdet : (family J U a).metric.det ≠ 0)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane) :
    ContDiffAt ℂ n (density J U Λ) a := by
  exact (weight_smooth J U a ha).mul
    (((smoothAt_scalar (ComplexCoordinateMetricTwoJet.toSpace (family J U a)) hdet).comp a
      (family_smooth J U).contDiffAt).sub contDiffAt_const)

private theorem weight_line (J : Jet) (U : Fin 3 → Jet) (a : Param) (k : Fin 3)
    (hJ : J.metric.det ≠ 0) (hdet : (family J U a).metric.det ≠ 0)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane) :
    HasDerivAt (fun t : ℂ => weight J U (a + t • Pi.single k 1))
      (weight J U a * (((family J U a).metric⁻¹ * (U k).metric).trace / 2)) 0 := by
  let G := (family J U a).metric
  have hg : G.det ≠ 0 := hdet
  have hd := (determinant_hasDerivAt G (U k).metric 0 0).div_const J.metric.det
  have he : path G (U k).metric 0 0 0 = G := by simp [path]
  have hl := (Complex.hasDerivAt_log (by simpa only [he] using ha)).comp 0 hd
  have hh := (hl.div_const 2).cexp
  convert! hh using 1
  · funext t
    simp only [weight, family_line, affine, path, smul_zero, add_zero, G, Function.comp_apply]
  · simp only [Function.comp_apply, he, determinantSlope_eq_det_mul_trace G (U k).metric hg]
    dsimp [weight, G]
    field_simp

/-- The original raised Einstein residual, including the varying determinant density. -/
def bulk (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (k : Fin 3) (a : Param) : ℂ :=
  weight J U a * ∑ i, ∑ j,
    ((family J U a).metric⁻¹ * (U k).metric * ((family J U a).metric⁻¹).transpose) i j *
      ((family J U a).einstein i j + Λ * (family J U a).metric i j)

/-- Full connection-current divergence with the same varying determinant density. -/
def boundary (J : Jet) (U : Fin 3 → Jet) (k : Fin 3) (a : Param) : ℂ :=
  weight J U a * divergence (family J U a) (U k)

private theorem density_direction (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hJ : J.metric.det ≠ 0) (a : Param) (k : Fin 3)
    (hdet : (family J U a).metric.det ≠ 0)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane)
    (hs : (family J U a).metric.transpose = (family J U a).metric)
    (hf : ∀ l i j, (family J U a).first l i j = (family J U a).first l j i) :
    fderiv ℂ (density J U Λ) a (Pi.single k 1) =
      -bulk J U Λ k a + boundary J U k a := by
  have hw := weight_line J U a k hJ hdet ha
  have hscalar := (scalar_hasDerivAt (family J U a) (U k) hdet).sub_const (2*Λ)
  have hline : HasDerivAt (fun t : ℂ => density J U Λ (a + t • Pi.single k 1))
      (weight J U a *
        ((((family J U a).metric⁻¹ * (U k).metric).trace / 2) *
          ((family J U a).scalar - 2*Λ) + Linearization.scalar (family J U a) (U k))) 0 := by
    convert! hw.mul hscalar using 1
    · funext t
      simp only [density, family_line, Pi.mul_apply]
    · simp only [affine_zero, sub_eq_add_neg, zero_smul, add_zero]
      ring
  have haction := densityPath_first_variation (family J U a) (U k) Λ hdet hs hf
  rw [(densityPath_hasDerivAt (family J U a) (U k) Λ hdet).deriv] at haction
  rw [haction] at hline
  have hparam : HasDerivAt (fun t : ℂ => a + t • Pi.single k 1) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const (Pi.single k (1:ℂ))).const_add a
  have hdiff := (density_smooth (n := 1) J U Λ a hdet ha).differentiableAt (by norm_num)
  have hda : HasFDerivAt (density J U Λ) (fderiv ℂ (density J U Λ) a)
      (a + (0:ℂ) • Pi.single k 1) := by
    simpa only [zero_smul, add_zero] using hdiff.hasFDerivAt
  have hd := hda.comp_hasDerivAt 0 hparam
  have h := hd.unique hline
  simpa only [bulk, boundary, mul_add, mul_neg] using h


/-- Coordinate derivative in the independent metric-variation parameters. -/
def parameterDeriv (f : Param → ℂ) (k : Fin 3) (a : Param) : ℂ :=
  fderiv ℂ f a (Pi.single k 1)

private theorem partial_smooth {f : Param → ℂ} {a : Param} {m : ℕ}
    (hf : ContDiffAt ℂ (m+1) f a) (k : Fin 3) :
    ContDiffAt ℂ m (parameterDeriv f k) a := by
  exact (hf.fderiv_right (m := m) (by norm_num)).clm_apply contDiffAt_const

private theorem partial_congr {f g : Param → ℂ} {a : Param}
    (h : f =ᶠ[𝓝 a] g) (k : Fin 3) : parameterDeriv f k =ᶠ[𝓝 a] parameterDeriv g k := by
  have hh : fderiv ℂ f =ᶠ[𝓝 a] fderiv ℂ g := h.fderiv
  filter_upwards [hh] with x hx
  exact congrArg (fun L => L (Pi.single k 1)) hx

private theorem partial_comm {f : Param → ℂ} {a : Param}
    (hf : ContDiffAt ℂ 3 f a) (j k : Fin 3) :
    parameterDeriv (parameterDeriv f k) j a = parameterDeriv (parameterDeriv f j) k a := by
  have hD := ((hf.fderiv_right (m := 2) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hp (v : Fin 3) := hD.clm_apply (hasFDerivAt_const (Pi.single v (1:ℂ)) a)
  have hj := (hp j).fderiv
  have hk := (hp k).fderiv
  change fderiv ℂ (fun x => fderiv ℂ f x (Pi.single k 1)) a (Pi.single j 1) =
    fderiv ℂ (fun x => fderiv ℂ f x (Pi.single j 1)) a (Pi.single k 1)
  rw [hj, hk]
  simpa using (hf.isSymmSndFDerivAt (by norm_num)) (Pi.single j 1) (Pi.single k 1)

private theorem partial_add {f g : Param → ℂ} {a : Param}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) (k : Fin 3) :
    parameterDeriv (fun x => f x + g x) k a = parameterDeriv f k a + parameterDeriv g k a := by
  simpa only [parameterDeriv, add_apply] using
    congrArg (fun L => L (Pi.single k 1)) (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv

private theorem partial2_add {f g : Param → ℂ} {a : Param}
    (hf : ContDiffAt ℂ 3 f a) (hg : ContDiffAt ℂ 3 g a) (i j : Fin 3) :
    parameterDeriv (parameterDeriv (fun x => f x + g x) j) i a =
      parameterDeriv (parameterDeriv f j) i a + parameterDeriv (parameterDeriv g j) i a := by
  have he : parameterDeriv (fun x => f x + g x) j =ᶠ[𝓝 a]
      fun x => parameterDeriv f j x + parameterDeriv g j x := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with x hfx hgx
    exact partial_add (hfx.differentiableAt (by norm_num))
      (hgx.differentiableAt (by norm_num)) j
  rw [(partial_congr he i).eq_of_nhds]
  exact partial_add ((partial_smooth (m := 2) hf j).differentiableAt (by norm_num))
    ((partial_smooth (m := 2) hg j).differentiableAt (by norm_num)) i

private theorem family_symm (J : Jet) (U : Fin 3 → Jet)
    (hJ : ∀ i j, J.metric i j = J.metric j i)
    (hU : ∀ k i j, (U k).metric i j = (U k).metric j i) (a : Param) :
    (family J U a).metric.transpose = (family J U a).metric := by
  ext i j
  simp only [family, ComplexCoordinateMetricTwoJet.ofSpace, Matrix.transpose_apply, Prod.fst_add,
    Prod.fst_sum, Prod.smul_fst, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply congrArg₂ (· + ·) (hJ j i)
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun z : ℂ => a k * z) (hU k j i)

private theorem family_first_symm (J : Jet) (U : Fin 3 → Jet)
    (hJ : ∀ l i j, J.first l i j = J.first l j i)
    (hU : ∀ k l i j, (U k).first l i j = (U k).first l j i) (a : Param) :
    ∀ l i j, (family J U a).first l i j = (family J U a).first l j i := by
  intro l i j
  simp only [family, ComplexCoordinateMetricTwoJet.ofSpace, Prod.snd_add, Prod.snd_sum, Prod.smul_snd,
    Prod.fst_add, Prod.fst_sum, Prod.smul_fst,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply congrArg₂ (· + ·) (hJ l i j)
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun z : ℂ => a k * z) (hU k l i j)

private theorem good_ne_zero (J : Jet) (U : Fin 3 → Jet) (a : Param)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane) :
    (family J U a).metric.det ≠ 0 := by
  intro hz
  apply Complex.slitPlane_ne_zero ha
  rw [hz, zero_div]

private theorem good_eventually (J : Jet) (U : Fin 3 → Jet) (hJ : J.metric.det ≠ 0) :
    ∀ᶠ a in 𝓝 (0 : Param), (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane := by
  have hc := ((family_det_smooth (n := 1) J U).continuous.continuousAt (x := (0:Param))).div_const J.metric.det
  apply hc.eventually
  apply Complex.isOpen_slitPlane.mem_nhds
  simpa only [family_zero, div_self hJ] using Complex.one_mem_slitPlane

private theorem bulk_smooth (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (k : Fin 3) (a : Param)
    (hdet : (family J U a).metric.det ≠ 0)
    (ha : (family J U a).metric.det / J.metric.det ∈ Complex.slitPlane) :
    ContDiffAt ℂ n (bulk J U Λ k) a := by
  have hsp := (family_smooth (n := n) J U).contDiffAt (x := a)
  have hi (i j : Fin d) : ContDiffAt ℂ n (fun b => (family J U b).metric⁻¹ i j) a := by
    simpa only [Function.comp_def, ComplexCoordinateMetricTwoJet.ofSpace_toSpace] using
      (smoothAt_inverse (n := n) (ComplexCoordinateMetricTwoJet.toSpace (family J U a)) hdet i j).comp a hsp
  have hm (i j : Fin d) : ContDiffAt ℂ n (fun b => (family J U b).metric i j) a :=
    (smooth_metric i j).contDiffAt.comp a hsp
  have he (i j : Fin d) : ContDiffAt ℂ n (fun b => (family J U b).einstein i j) a := by
    simpa only [Function.comp_def, ComplexCoordinateMetricTwoJet.einsteinComponent, ComplexCoordinateMetricTwoJet.ofSpace_toSpace] using
      (contDiffAt_einsteinComponent (n := n) (ComplexCoordinateMetricTwoJet.toSpace (family J U a)) hdet i j).comp a hsp
  apply (weight_smooth J U a ha).mul
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul _ ((he i j).add (contDiffAt_const.mul (hm i j)))
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro l _
  apply ContDiffAt.mul _ (hi j l)
  apply ContDiffAt.sum
  intro m _
  exact (hi i m).mul contDiffAt_const

/-- The second variation of the original boundary divergence retains both the third
Einstein--Hilbert variation and the second variation of the paired Einstein residual. -/
private theorem boundary_second_eq (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0)
    (hs : ∀ i j, J.metric i j = J.metric j i)
    (hf : ∀ l i j, J.first l i j = J.first l j i)
    (hUs : ∀ k i j, (U k).metric i j = (U k).metric j i)
    (hUf : ∀ k l i j, (U k).first l i j = (U k).first l j i)
    (i j k : Fin 3) :
    parameterDeriv (parameterDeriv (boundary J U k) j) i 0 =
      parameterDeriv (parameterDeriv (parameterDeriv (density J U Λ) k) j) i 0 +
        parameterDeriv (parameterDeriv (bulk J U Λ k) j) i 0 := by
  have hgood := good_eventually J U hdet
  have hzero : (family J U 0).metric.det / J.metric.det ∈ Complex.slitPlane :=
    hgood.self_of_nhds
  have hdensity : ContDiffAt ℂ 4 (density J U Λ) 0 :=
    density_smooth J U Λ 0 (good_ne_zero J U 0 hzero) hzero
  have hbulk (v : Fin 3) : ContDiffAt ℂ 3 (bulk J U Λ v) 0 :=
    bulk_smooth J U Λ v 0 (good_ne_zero J U 0 hzero) hzero
  have hbalance (v : Fin 3) : boundary J U v =ᶠ[𝓝 (0:Param)]
      fun a => parameterDeriv (density J U Λ) v a + bulk J U Λ v a := by
    filter_upwards [hgood] with a ha
    have h := density_direction J U Λ hdet a v (good_ne_zero J U a ha) ha
      (family_symm J U hs hUs a) (family_first_symm J U hf hUf a)
    change parameterDeriv (density J U Λ) v a = _ at h
    linear_combination -h
  have hb (v w : Fin 3) :
      parameterDeriv (parameterDeriv (boundary J U v) w) i 0 =
        parameterDeriv (parameterDeriv (parameterDeriv (density J U Λ) v) w) i 0 +
          parameterDeriv (parameterDeriv (bulk J U Λ v) w) i 0 := by
    rw [(partial_congr (partial_congr (hbalance v) w) i).eq_of_nhds]
    exact partial2_add (partial_smooth (m := 3) hdensity v) (hbulk v) i w
  exact hb k j

/-- The exact cyclicity defect of the original volume-weighted Einstein source
is its original boundary-divergence defect. No field or boundary equation is assumed. -/
theorem paired_cyclicity_defect (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0)
    (hs : ∀ i j, J.metric i j = J.metric j i)
    (hf : ∀ l i j, J.first l i j = J.first l j i)
    (hUs : ∀ k i j, (U k).metric i j = (U k).metric j i)
    (hUf : ∀ k l i j, (U k).first l i j = (U k).first l j i)
    (i j k : Fin 3) :
    parameterDeriv (parameterDeriv (bulk J U Λ k) j) i 0 -
        parameterDeriv (parameterDeriv (bulk J U Λ j) k) i 0 =
      parameterDeriv (parameterDeriv (boundary J U k) j) i 0 -
        parameterDeriv (parameterDeriv (boundary J U j) k) i 0 := by
  have hgood := good_eventually J U hdet
  have hc : parameterDeriv (parameterDeriv (density J U Λ) k) j =ᶠ[𝓝 (0:Param)]
      parameterDeriv (parameterDeriv (density J U Λ) j) k := by
    filter_upwards [hgood] with a ha
    exact partial_comm (density_smooth (n := 3) J U Λ a
      (good_ne_zero J U a ha) ha) j k
  have hcomm := (partial_congr hc i).eq_of_nhds
  rw [boundary_second_eq J U Λ hdet hs hf hUs hUf i j k,
    boundary_second_eq J U Λ hdet hs hf hUs hUf i k j, hcomm]
  ring

/-- The cubic variation retains both the original bulk source and its boundary divergence. -/
def cubicAction (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (i j k : Fin 3) : ℂ :=
  parameterDeriv (parameterDeriv (bulk J U Λ k) j) i 0 -
    parameterDeriv (parameterDeriv (boundary J U k) j) i 0

/-- Exact identification with the third variation of the original Einstein--Hilbert density. -/
theorem cubicAction_eq_density_third (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0)
    (hs : ∀ i j, J.metric i j = J.metric j i)
    (hf : ∀ l i j, J.first l i j = J.first l j i)
    (hUs : ∀ k i j, (U k).metric i j = (U k).metric j i)
    (hUf : ∀ k l i j, (U k).first l i j = (U k).first l j i)
    (i j k : Fin 3) :
    cubicAction J U Λ i j k =
      -parameterDeriv (parameterDeriv (parameterDeriv (density J U Λ) k) j) i 0 := by
  unfold cubicAction
  rw [boundary_second_eq J U Λ hdet hs hf hUs hUf i j k]
  ring

/-- The retained bulk-and-boundary cubic variation is cyclic without a vanishing-flux premise. -/
theorem cubicAction_cyclic (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0)
    (hs : ∀ i j, J.metric i j = J.metric j i)
    (hf : ∀ l i j, J.first l i j = J.first l j i)
    (hUs : ∀ k i j, (U k).metric i j = (U k).metric j i)
    (hUf : ∀ k l i j, (U k).first l i j = (U k).first l j i)
    (i j k : Fin 3) :
    cubicAction J U Λ i j k = cubicAction J U Λ i k j := by
  have h := paired_cyclicity_defect J U Λ hdet hs hf hUs hUf i j k
  unfold cubicAction
  linear_combination h

end
end GaloisForLFunctions.HTGeometry.EinsteinCyclicVariation

