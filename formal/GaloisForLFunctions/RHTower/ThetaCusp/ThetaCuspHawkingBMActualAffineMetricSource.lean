import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBackgroundMetricTwoJet

/-!
# Actual affine metric source on the proved BM background

The perturbation is an actual complex tensor field on the real coordinate chart. Taking its
complete coordinate two-jet commutes with affine field variation. This identifies the literal
cosmological source with the previously derived Einstein function on complete jet coordinates.

A three-step complex derivative chain proves its quadratic and direct cubic coefficients,
including the fixed cosmological term. The full covariant KI reconstruction is connected by
its proved field-to-jet equality. Second- and third-order corrections to the metric family,
nonlinear gauge completion, and physical causal boundary projection remain separate.
-/

namespace RHTower.D4BMActualMetricSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction ComplexCoordinateMetricTwoJet
open Filter Topology
noncomputable section

/-- Complex perturbation tensor as an actual field on the real coordinate chart. -/
abbrev MetricField := (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ

/-- The literal affine perturbation of the proved BM background. -/
def perturbedMetric (h : MetricField) (ε : ℂ) : MetricField :=
  fun x => metric (x 1) (x 3) + ε • h x

/-- The actual cosmological Einstein source of the perturbed field's complete coordinate jet. -/
def source (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) (ε : ℂ) : ℂ :=
  let J := ofMetricField (perturbedMetric h ε) p.val
  J.einstein i j - 3 * J.metric i j

/-- Coordinates of the actual background jet. -/
def backgroundSpace (p : ExteriorPoint) : ComplexMetricTwoJetSpace 4 := toSpace (actualJet p)

/-- Coordinates of the actual perturbation jet, with no prescribed derivative arrays. -/
def fieldSpace (p : ExteriorPoint) (h : MetricField) : ComplexMetricTwoJetSpace 4 :=
  toSpace (ofMetricField h p.val)

/-- Taking the complete field jet commutes with the actual affine metric perturbation. -/
theorem perturbedMetric_jet (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (ε : ℂ) :
    toSpace (ofMetricField (perturbedMetric h ε) p.val) =
      backgroundSpace p + ε • fieldSpace p h := by
  have hs (i j : Fin 4) :
      ScalarTwoJet.ofField (fun x : Fin 4 → ℝ => metric (x 1) (x 3) i j + ε * h x i j) p.val =
        ScalarTwoJet.add (ScalarTwoJet.ofField (fun x => metric (x 1) (x 3) i j) p.val)
          (ScalarTwoJet.mul (ScalarTwoJet.constant ε) (ScalarTwoJet.ofField (fun x => h x i j) p.val)) := by
    rw [ScalarTwoJet.ofField_add (exterior_metric_contDiffAt p i j)
      (contDiffAt_const.mul (hh i j)),
      ScalarTwoJet.ofField_mul contDiffAt_const (hh i j), ScalarTwoJet.ofField_constant]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k i j
      change (ScalarTwoJet.ofField (fun x : Fin 4 → ℝ => metric (x 1) (x 3) i j + ε * h x i j) p.val).first k = _
      rw [hs]
      simp [ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.constant,
        backgroundSpace, fieldSpace, toSpace, actualJet, ofMetricField]
      rfl
    · funext k l i j
      change (ScalarTwoJet.ofField (fun x : Fin 4 → ℝ => metric (x 1) (x 3) i j + ε * h x i j) p.val).second k l = _
      rw [hs]
      simp [ScalarTwoJet.add, ScalarTwoJet.mul, ScalarTwoJet.constant,
        backgroundSpace, fieldSpace, toSpace, actualJet, ofMetricField]
      rfl

/-- Exact identification of the literal field source with the derived Einstein function on jet space. -/
theorem source_eq (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4) (ε : ℂ) :
    source p h i j ε = einsteinComponent i j (backgroundSpace p + ε • fieldSpace p h) -
      3 * (backgroundSpace p + ε • fieldSpace p h).1 i j := by
  change einsteinComponent i j (toSpace (ofMetricField (perturbedMetric h ε) p.val)) -
    3 * (toSpace (ofMetricField (perturbedMetric h ε) p.val)).1 i j = _
  rw [perturbedMetric_jet p h hh]

/-- Zeroth-order source vanishes because the actual reference metric solves the vacuum equation. -/
theorem source_zero (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) :
    source p h i j 0 = 0 := by
  have heq : perturbedMetric h 0 = fun x => metric (x 1) (x 3) := by
    funext x
    simp [perturbedMetric]
  unfold source
  rw [heq]
  exact exterior_vacuum p i j

private abbrev line (p : ExteriorPoint) (h : MetricField) (ε : ℂ) : ComplexMetricTwoJetSpace 4 :=
  backgroundSpace p + ε • fieldSpace p h

/-- Admissible complex amplitudes are determined by the actual perturbed metric determinant. -/
def amplitudeDomain (p : ExteriorPoint) (h : MetricField) : Set ℂ :=
  {ε | Matrix.det (line p h ε).1 ≠ 0}

private theorem amplitudeDomain_open (p : ExteriorPoint) (h : MetricField) :
    IsOpen (amplitudeDomain p h) := by
  have hc : Continuous (fun ε : ℂ => Matrix.det (line p h ε).1) := by
    simp only [Matrix.det_apply']
    fun_prop
  exact (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).preimage hc

private theorem zero_mem_amplitudeDomain (p : ExteriorPoint) (h : MetricField) :
    (0 : ℂ) ∈ amplitudeDomain p h := by
  simp only [amplitudeDomain, Set.mem_setOf_eq, line, zero_smul, add_zero]
  change (metric (p.val 1) (p.val 3)).det ≠ 0
  exact exterior_metric_det_ne_zero p

private theorem line_hasDerivAt (p : ExteriorPoint) (h : MetricField) (ε : ℂ) :
    HasDerivAt (line p h) (fieldSpace p h) ε := by
  simpa only [line, id_eq, one_smul] using
    ((hasDerivAt_id ε).smul_const (fieldSpace p h)).const_add (backgroundSpace p)

private abbrev first (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) (ε : ℂ) : ℂ :=
  fderiv ℂ (einsteinComponent i j) (line p h ε) (fieldSpace p h) - 3 * (fieldSpace p h).1 i j

private abbrev second (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) (ε : ℂ) : ℂ :=
  secondVariation (line p h ε) i j (fieldSpace p h) (fieldSpace p h)

private abbrev third (p : ExteriorPoint) (h : MetricField) (i j : Fin 4) (ε : ℂ) : ℂ :=
  thirdVariation (line p h ε) i j (fieldSpace p h) (fieldSpace p h) (fieldSpace p h)

private theorem source_has_first (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4)
    (ε : ℂ) (hε : ε ∈ amplitudeDomain p h) :
    HasDerivAt (source p h i j) (first p h i j ε) ε := by
  have hs := contDiffAt_einsteinComponent (n := 3) (line p h ε) hε i j
  have hE := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ε (line_hasDerivAt p h ε)
  have hG : HasDerivAt (fun z : ℂ => (line p h z).1 i j) ((fieldSpace p h).1 i j) ε := by
    change HasDerivAt (fun z : ℂ => (backgroundSpace p).1 i j + z * (fieldSpace p h).1 i j)
      ((fieldSpace p h).1 i j) ε
    convert! ((hasDerivAt_id ε).mul_const ((fieldSpace p h).1 i j)).const_add
      ((backgroundSpace p).1 i j) using 1
    simp
  have heq : source p h i j = fun z => einsteinComponent i j (line p h z) - 3 * (line p h z).1 i j := by
    funext z
    exact source_eq p h hh i j z
  rw [heq]
  exact hE.sub (hG.const_mul 3)

private theorem source_has_second (p : ExteriorPoint) (h : MetricField) (i j : Fin 4)
    (ε : ℂ) (hε : ε ∈ amplitudeDomain p h) :
    HasDerivAt (first p h i j) (second p h i j ε) ε := by
  have hs := (contDiffAt_einsteinComponent (n := 3) (line p h ε) hε i j).fderiv_right (m := 2) (by norm_num)
  have hd := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ε (line_hasDerivAt p h ε)
  convert! (hd.clm_apply (hasDerivAt_const ε (fieldSpace p h))).sub_const
    (3 * (fieldSpace p h).1 i j) using 1
  simp [second, secondVariation]

private theorem source_has_third (p : ExteriorPoint) (h : MetricField) (i j : Fin 4)
    (ε : ℂ) (hε : ε ∈ amplitudeDomain p h) :
    HasDerivAt (second p h i j) (third p h i j ε) ε := by
  have hs := ((contDiffAt_einsteinComponent (n := 3) (line p h ε) hε i j).fderiv_right
    (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  have hd := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ε (line_hasDerivAt p h ε)
  convert! (hd.clm_apply (hasDerivAt_const ε (fieldSpace p h))).clm_apply
    (hasDerivAt_const ε (fieldSpace p h)) using 1
  simp [third, secondVariation, thirdVariation]

private theorem source_iteratedDeriv_two_at (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4)
    {ε : ℂ} (hε : ε ∈ amplitudeDomain p h) :
    iteratedDeriv 2 (source p h i j) ε = second p h i j ε := by
  have heq : deriv (source p h i j) =ᶠ[𝓝 ε] first p h i j := by
    filter_upwards [(amplitudeDomain_open p h).mem_nhds hε] with z hz
    exact (source_has_first p h hh i j z hz).deriv
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    heq.deriv_eq, (source_has_second p h i j ε hε).deriv]

/-- Actual quadratic coefficient of the literal cosmological field source. -/
theorem source_quadratic (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 2 (source p h i j) 0 / 2 =
      secondVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) / 2 := by
  rw [source_iteratedDeriv_two_at p h hh i j (zero_mem_amplitudeDomain p h)]
  simp [second, line]

/-- Actual direct cubic coefficient of the literal cosmological field source. Contributions
from second- and third-order corrections to the field are not part of this affine path. -/
theorem source_cubic (p : ExteriorPoint) (h : MetricField)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val) (i j : Fin 4) :
    iteratedDeriv 3 (source p h i j) 0 / 6 =
      thirdVariation (backgroundSpace p) i j (fieldSpace p h) (fieldSpace p h) (fieldSpace p h) / 6 := by
  have heq : iteratedDeriv 2 (source p h i j) =ᶠ[𝓝 (0 : ℂ)] second p h i j := by
    filter_upwards [(amplitudeDomain_open p h).mem_nhds (zero_mem_amplitudeDomain p h)] with z hz
    exact source_iteratedDeriv_two_at p h hh i j hz
  rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, heq.deriv_eq,
    (source_has_third p h i j 0 (zero_mem_amplitudeDomain p h)).deriv]
  simp [third, line]

private theorem reconstructedField_contDiffAt (p : ExteriorPoint) (omega kSq : ℂ)
    (a : Primitive → (Fin 4 → ℝ) → ℂ)
    (ha : ∀ b, ContDiffAt ℝ 2 (a b) p.val)
    (hr : a .radius p.val ≠ 0) (hf : (a .radius p.val)^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => covariantMetric omega kSq (fun b => a b x) i j) p.val := by
  have hs := ((covariantMetricExpression omega kSq i j).eval_jet_correct ha
    (covariantMetricExpression_regular omega kSq (fun b => a b p.val) hr hf i j)).1
  have heq : (fun x => (covariantMetricExpression omega kSq i j).eval (fun b => a b x)) =
      fun x => covariantMetric omega kSq (fun b => a b x) i j := by
    funext x
    exact covariantMetricExpression_eval omega kSq (fun b => a b x) i j
  rw [heq] at hs
  exact hs

/-- Both direct source coefficients for the full covariant KI reconstruction are evaluations
of the actual Einstein variations on its proved full metric jet. All coordinate derivatives
enter through the literal reconstruction; no independent source tensor is supplied. -/
theorem reconstructed_source_coefficients (p : ExteriorPoint) (omega kSq : ℂ)
    (a : Primitive → (Fin 4 → ℝ) → ℂ)
    (ha : ∀ b, ContDiffAt ℝ 2 (a b) p.val)
    (hr : a .radius p.val ≠ 0) (hf : (a .radius p.val)^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    let h : MetricField := fun x => covariantMetric omega kSq (fun b => a b x)
    let u := toSpace (metricJet omega kSq (fun b => ScalarTwoJet.ofField (a b) p.val))
    (iteratedDeriv 2 (source p h i j) 0 / 2 = secondVariation (backgroundSpace p) i j u u / 2) ∧
    (iteratedDeriv 3 (source p h i j) 0 / 6 = thirdVariation (backgroundSpace p) i j u u u / 6) := by
  let h : MetricField := fun x => covariantMetric omega kSq (fun b => a b x)
  let u := toSpace (metricJet omega kSq (fun b => ScalarTwoJet.ofField (a b) p.val))
  have hu : fieldSpace p h = u :=
    congrArg toSpace (metricJet_correct omega kSq ha hr hf).symm
  have hh : ∀ i j, ContDiffAt ℝ 2 (fun x => h x i j) p.val :=
    reconstructedField_contDiffAt p omega kSq a ha hr hf
  change (iteratedDeriv 2 (source p h i j) 0 / 2 = secondVariation (backgroundSpace p) i j u u / 2) ∧
    (iteratedDeriv 3 (source p h i j) 0 / 6 = thirdVariation (backgroundSpace p) i j u u u / 6)
  rw [source_quadratic p h hh, source_cubic p h hh, hu]
  exact ⟨rfl,rfl⟩

end
end RHTower.D4BMActualMetricSource
