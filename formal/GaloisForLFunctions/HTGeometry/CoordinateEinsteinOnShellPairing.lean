import GaloisForLFunctions.HTGeometry.CoordinateEinsteinCyclicAction

set_option autoImplicit false

/-!
# Original quadratic Einstein pairing from the on-shell residual

The complete three-parameter cosmological source has the actual Einstein Hessian as
its mixed second derivative. For a vacuum background and original linearized solutions,
differentiating the volume-weighted raised test produces no extra quadratic terms:
each such term multiplies a vanishing zeroth or first residual. The resulting equality
identifies the quadratic source in the previously proved cyclic action identity.
Boundary divergence and global causal admission are not discarded.
-/
open Complex Filter Topology
open scoped ContDiff BigOperators
namespace GaloisForLFunctions.HTGeometry.EinsteinOnShellPairing
open EinsteinCyclicVariation
noncomputable section
local notation "Param" => Fin 3 → ℂ

private theorem pd_smooth {f : Param → ℂ} {a : Param} {m : ℕ}
    (hf : ContDiffAt ℂ (m+1) f a) (k : Fin 3) :
    ContDiffAt ℂ m (parameterDeriv f k) a := by
  exact (hf.fderiv_right (m := m) (by norm_num)).clm_apply contDiffAt_const

private theorem pd_congr {f g : Param → ℂ} {a : Param}
    (h : f =ᶠ[𝓝 a] g) (k : Fin 3) :
    parameterDeriv f k =ᶠ[𝓝 a] parameterDeriv g k := by
  filter_upwards [h.fderiv (𝕜 := ℂ)] with x hx
  exact congrArg (fun L => L (Pi.single k 1)) hx

private theorem pd_mul {f g : Param → ℂ} {a : Param}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) (k : Fin 3) :
    parameterDeriv (fun x => f x * g x) k a =
      f a * parameterDeriv g k a + g a * parameterDeriv f k a := by
  simpa [parameterDeriv] using congrArg (fun L => L (Pi.single k 1))
    (hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv

private theorem pd_add {f g : Param → ℂ} {a : Param}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) (k : Fin 3) :
    parameterDeriv (fun x => f x + g x) k a =
      parameterDeriv f k a + parameterDeriv g k a := by
  simpa only [parameterDeriv, add_apply] using
    congrArg (fun L => L (Pi.single k 1)) (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv

/-- The second variation of a weighted residual freezes the weight exactly when its
zeroth and relevant first residuals vanish. -/
theorem weighted_second_of_residual_zero {f g : Param → ℂ}
    (hf : ContDiffAt ℂ 3 f 0) (hg : ContDiffAt ℂ 3 g 0)
    (i j : Fin 3) (hg0 : g 0 = 0)
    (hgi : parameterDeriv g i 0 = 0) (hgj : parameterDeriv g j 0 = 0) :
    parameterDeriv (parameterDeriv (fun x => f x * g x) j) i 0 =
      f 0 * parameterDeriv (parameterDeriv g j) i 0 := by
  have he : parameterDeriv (fun x => f x * g x) j =ᶠ[𝓝 (0:Param)]
      fun x => f x * parameterDeriv g j x + g x * parameterDeriv f j x := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with x hfx hgx
    exact pd_mul (hfx.differentiableAt (by norm_num))
      (hgx.differentiableAt (by norm_num)) j
  rw [(pd_congr he i).eq_of_nhds]
  have hdf := hf.differentiableAt (by norm_num)
  have hdg := hg.differentiableAt (by norm_num)
  have hdpf := (pd_smooth (m := 2) hf j).differentiableAt (by norm_num)
  have hdpg := (pd_smooth (m := 2) hg j).differentiableAt (by norm_num)
  have hA : DifferentiableAt ℂ (fun x => f x * parameterDeriv g j x) 0 :=
    (hdf.hasFDerivAt.fun_mul hdpg.hasFDerivAt).differentiableAt
  have hB : DifferentiableAt ℂ (fun x => g x * parameterDeriv f j x) 0 :=
    (hdg.hasFDerivAt.fun_mul hdpf.hasFDerivAt).differentiableAt
  rw [pd_add hA hB i, pd_mul hdf hdpg i, pd_mul hdg hdpf i, hg0, hgi, hgj]
  ring

open ComplexCoordinateMetricTwoJet
variable {d : ℕ} {n : ℕ∞ω}
local notation "Jet" => CoordinateMetricTwoJet d ℂ

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

private theorem smoothAt_inverse (q : ComplexMetricTwoJetSpace d) (hq : Matrix.det q.1 ≠ 0)
    (i j : Fin d) : ContDiffAt ℂ n (fun r : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace r).metric⁻¹ i j) q := by
  have heq : (fun r : ComplexMetricTwoJetSpace d => (ComplexCoordinateMetricTwoJet.ofSpace r).metric⁻¹ i j) =
      fun r => ((ComplexCoordinateMetricTwoJet.ofSpace r).metric.det)⁻¹ * (ComplexCoordinateMetricTwoJet.ofSpace r).metric.adjugate i j := by
    funext r
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [heq]
  exact ((complex_contDiff_matrix_det smooth_metric).contDiffAt.inv hq).mul
    (complex_contDiff_matrix_adjugate_apply smooth_metric i j).contDiffAt

private theorem family_zero (J : Jet) (U : Fin 3 → Jet) : family J U 0 = J := by
  simp [family]

private theorem family_smooth (J : Jet) (U : Fin 3 → Jet) :
    ContDiff ℂ n (fun a => ComplexCoordinateMetricTwoJet.toSpace (family J U a)) := by
  simp only [family, ComplexCoordinateMetricTwoJet.toSpace_ofSpace]
  fun_prop

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


/-- All three complete metric-jet directions, as one fixed continuous linear map. -/
def variationMap (U : Fin 3 → Jet) : Param →L[ℂ] ComplexMetricTwoJetSpace d where
  toFun a := ∑ k, a k • toSpace (U k)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z a := by simp [smul_smul, Finset.smul_sum]
  cont := by fun_prop

private theorem variationMap_single (U : Fin 3 → Jet) (k : Fin 3) :
    variationMap U (Pi.single k 1) = toSpace (U k) := by
  simp [variationMap, Pi.single_apply]

private theorem coordinates_hasFDerivAt (J : Jet) (U : Fin 3 → Jet) (a : Param) :
    HasFDerivAt (fun x => toSpace (family J U x)) (variationMap U) a := by
  change HasFDerivAt (fun x => toSpace J + variationMap U x) (variationMap U) a
  exact (variationMap U).hasFDerivAt.const_add (toSpace J)

/-- The original cosmological Einstein residual of the complete three-parameter family. -/
def residual (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (r s : Fin d) (a : Param) : ℂ :=
  (family J U a).einstein r s + Λ * (family J U a).metric r s

private theorem residual_smooth (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (r s : Fin d) (a : Param) (hdet : (family J U a).metric.det ≠ 0) :
    ContDiffAt ℂ n (residual J U Λ r s) a := by
  have hsp := (family_smooth (n := n) J U).contDiffAt (x := a)
  have he := (contDiffAt_einsteinComponent (n := n) (toSpace (family J U a)) hdet r s).comp a hsp
  have hm := (smooth_metric (n := n) r s).contDiffAt.comp a hsp
  change ContDiffAt ℂ n (fun x => (family J U x).einstein r s + Λ * (family J U x).metric r s) a
  have he' : ContDiffAt ℂ n (fun x => (family J U x).einstein r s) a := by
    simpa only [Function.comp_def, einsteinComponent, ofSpace_toSpace] using he
  have hm' : ContDiffAt ℂ n (fun x => (family J U x).metric r s) a := by
    simpa only [Function.comp_def, ofSpace_toSpace] using hm
  exact he'.add (contDiffAt_const.mul hm')

/-- First source derivative in any original jet direction, including the cosmological term. -/
theorem residual_first (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (r s : Fin d) (a : Param) (hdet : (family J U a).metric.det ≠ 0) (k : Fin 3) :
    parameterDeriv (residual J U Λ r s) k a =
      fderiv ℂ (einsteinComponent r s) (toSpace (family J U a)) (toSpace (U k)) +
        Λ * (U k).metric r s := by
  have hc := coordinates_hasFDerivAt J U a
  have hm := hasFDerivAt_pi'.mp (hasFDerivAt_pi'.mp hc.fst r) s
  have hE := contDiffAt_einsteinComponent (n := 1) (toSpace (family J U a)) hdet r s
  have he := (hE.differentiableAt (by norm_num)).hasFDerivAt.comp a hc
  have hr := he.fun_add (hm.const_mul Λ)
  change HasFDerivAt (residual J U Λ r s) _ a at hr
  have hd := congrArg (fun L => L (Pi.single k 1)) hr.fderiv
  simpa [parameterDeriv, ContinuousLinearMap.comp_apply, variationMap_single, toSpace] using hd

/-- Mixed source derivatives are the actual Einstein Hessian; the affine cosmological term
has zero second derivative. -/
theorem residual_second (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0) (r s : Fin d) (i j : Fin 3) :
    parameterDeriv (parameterDeriv (residual J U Λ r s) j) i 0 =
      secondVariation (toSpace J) r s (toSpace (U i)) (toSpace (U j)) := by
  have hgood := good_eventually J U hdet
  have he : parameterDeriv (residual J U Λ r s) j =ᶠ[𝓝 (0:Param)]
      fun a => fderiv ℂ (einsteinComponent r s) (toSpace (family J U a)) (toSpace (U j)) +
        Λ * (U j).metric r s := by
    filter_upwards [hgood] with a ha
    exact residual_first J U Λ r s a (good_ne_zero J U a ha) j
  have hE := contDiffAt_einsteinComponent (n := 3) (toSpace J) hdet r s
  have hD := (hE.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hD0 : HasFDerivAt (fderiv ℂ (einsteinComponent r s))
      (secondVariation (toSpace J) r s) (toSpace (family J U 0)) := by
    simpa only [family_zero, secondVariation] using hD.hasFDerivAt
  have hh := ((hD0.comp 0 (coordinates_hasFDerivAt J U 0)).clm_apply
    (hasFDerivAt_const (toSpace (U j)) (0:Param))).add_const (Λ * (U j).metric r s)
  change HasFDerivAt (fun a => fderiv ℂ (einsteinComponent r s)
    (toSpace (family J U a)) (toSpace (U j)) + Λ * (U j).metric r s) _ 0 at hh
  rw [(pd_congr he i).eq_of_nhds]
  have hd := congrArg (fun L => L (Pi.single i 1)) hh.fderiv
  simpa [parameterDeriv, ContinuousLinearMap.comp_apply, variationMap_single] using hd

/-- Original varying volume and inverse metrics in the covariant test contraction. -/
def testCoefficient (J : Jet) (U : Fin 3 → Jet) (k : Fin 3) (r s : Fin d) (a : Param) : ℂ :=
  weight J U a * ((family J U a).metric⁻¹ * (U k).metric *
    ((family J U a).metric⁻¹).transpose) r s

private theorem testCoefficient_smooth (J : Jet) (U : Fin 3 → Jet)
    (hdet : J.metric.det ≠ 0) (k : Fin 3) (r s : Fin d) :
    ContDiffAt ℂ n (testCoefficient J U k r s) 0 := by
  have ha := (good_eventually J U hdet).self_of_nhds
  have hsp := (family_smooth (n := n) J U).contDiffAt (x := (0:Param))
  have hi (v w : Fin d) : ContDiffAt ℂ n (fun a => (family J U a).metric⁻¹ v w) 0 := by
    simpa only [Function.comp_def, ofSpace_toSpace] using
      (smoothAt_inverse (n := n) (toSpace (family J U 0))
        (good_ne_zero J U 0 ha) v w).comp 0 hsp
  apply (weight_smooth J U 0 ha).mul
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiffAt.sum
  intro v _
  apply ContDiffAt.mul _ (hi s v)
  apply ContDiffAt.sum
  intro w _
  exact (hi r w).mul contDiffAt_const

private theorem testCoefficient_zero (J : Jet) (U : Fin 3 → Jet)
    (hdet : J.metric.det ≠ 0) (k : Fin 3) (r s : Fin d) :
    testCoefficient J U k r s 0 = (J.metric⁻¹ * (U k).metric * (J.metric⁻¹).transpose) r s := by
  simp [testCoefficient, weight, family_zero, hdet]

private theorem pd_sum {ι : Type*} [Fintype ι] {F : ι → Param → ℂ} {a : Param}
    (hF : ∀ v, DifferentiableAt ℂ (F v) a) (k : Fin 3) :
    parameterDeriv (fun x => ∑ v, F v x) k a = ∑ v, parameterDeriv (F v) k a := by
  have hh := (HasFDerivAt.fun_sum (u := Finset.univ) (fun v _ => (hF v).hasFDerivAt)).fderiv
  simpa only [parameterDeriv, sum_apply] using congrArg (fun L => L (Pi.single k 1)) hh

private theorem pd2_sum {ι : Type*} [Fintype ι] {F : ι → Param → ℂ}
    (hF : ∀ v, ContDiffAt ℂ 3 (F v) 0) (i j : Fin 3) :
    parameterDeriv (parameterDeriv (fun x => ∑ v, F v x) j) i 0 =
      ∑ v, parameterDeriv (parameterDeriv (F v) j) i 0 := by
  have ha : ∀ᶠ x in 𝓝 (0:Param), ∀ v, ContDiffAt ℂ 3 (F v) x :=
    Filter.eventually_all.mpr fun v => (hF v).eventually (by norm_num)
  have he : parameterDeriv (fun x => ∑ v, F v x) j =ᶠ[𝓝 (0:Param)]
      fun x => ∑ v, parameterDeriv (F v) j x := by
    filter_upwards [ha] with x hx
    exact pd_sum (fun v => (hx v).differentiableAt (by norm_num)) j
  rw [(pd_congr he i).eq_of_nhds]
  exact pd_sum (fun v => (pd_smooth (m := 2) (hF v) j).differentiableAt (by norm_num)) i

private theorem bulk_eq_sum (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ) (k : Fin 3) :
    bulk J U Λ k = fun a => ∑ r, ∑ s,
      testCoefficient J U k r s a * residual J U Λ r s a := by
  funext a
  simp [bulk, testCoefficient, residual, Finset.mul_sum, mul_assoc]

/-- On-shell reduction of the ORIGINAL volume-weighted source pairing to the actual
Einstein Hessian. All changing-test terms are discharged by the original residual equations. -/
theorem bulk_second_eq_hessian (J : Jet) (U : Fin 3 → Jet) (Λ : ℂ)
    (hdet : J.metric.det ≠ 0)
    (hzero : ∀ r s, J.einstein r s + Λ * J.metric r s = 0)
    (hfirst : ∀ k r s, CoordinateMetricTwoJet.Linearization.cosmological J (U k) Λ r s = 0)
    (i j k : Fin 3) :
    parameterDeriv (parameterDeriv (bulk J U Λ k) j) i 0 =
      ∑ r, ∑ s, (J.metric⁻¹ * (U k).metric * (J.metric⁻¹).transpose) r s *
        secondVariation (toSpace J) r s (toSpace (U i)) (toSpace (U j)) := by
  have h0 : (family J U 0).metric.det ≠ 0 := by simpa only [family_zero] using hdet
  have hg (r s : Fin d) : ContDiffAt ℂ 3 (residual J U Λ r s) 0 :=
    residual_smooth J U Λ r s 0 h0
  have hg0 (r s : Fin d) : residual J U Λ r s 0 = 0 := by
    simpa only [residual, family_zero] using hzero r s
  have hg1 (v : Fin 3) (r s : Fin d) : parameterDeriv (residual J U Λ r s) v 0 = 0 := by
    rw [residual_first J U Λ r s 0 h0 v, family_zero,
      ← CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv J (U v) hdet r s]
    exact hfirst v r s
  have hp (r s : Fin d) : ContDiffAt ℂ 3
      (fun a => testCoefficient J U k r s a * residual J U Λ r s a) 0 :=
    (testCoefficient_smooth J U hdet k r s).mul (hg r s)
  rw [bulk_eq_sum, pd2_sum (fun r => ContDiffAt.sum (fun s _ => hp r s))]
  apply Finset.sum_congr rfl
  intro r _
  rw [pd2_sum (fun s => hp r s)]
  apply Finset.sum_congr rfl
  intro s _
  rw [weighted_second_of_residual_zero (testCoefficient_smooth J U hdet k r s)
      (hg r s) i j (hg0 r s) (hg1 i r s) (hg1 j r s),
    testCoefficient_zero J U hdet k r s, residual_second J U Λ hdet r s i j]

end
end GaloisForLFunctions.HTGeometry.EinsteinOnShellPairing
