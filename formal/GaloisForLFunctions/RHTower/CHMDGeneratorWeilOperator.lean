import GaloisForLFunctions.RHTower.CHMDPointwiseGenerator

/-!
# The explicit generator of the arithmetic form in resolvent coordinates

On a compact `C²` profile `v` with source `f = Θv`, the complete jump image minus the polar rate
is the pole-free Weil operator applied to `f`:

`J v(y) − cosh(y/2) v(y) = 𝒲₀ f(y) := −(γ + log π) f(y)
   + ∫_0^∞ [2ν(u) f(y) − ω(u)(f(y+u) + f(y−u))] du − Σ_n Λ(n) n^{−1/2} (f(y + log n) + f(y − log n))`.

This is the pointwise harmonic identity of `Θ` transported along `v`. The generator image
`G v = 𝒲₀(Θv)/cosh(·/2)` is bounded, hence a vector of the theta–cosh mass space, and for every
vector `q` of the completed graph the signed pairing is `⟨G v, q⟩_μ`. In resolvent coordinates
`R(v) = v/2 − R(G v)/2`: the arithmetic resolvent acts on compact tests through the explicit
integro-difference operator `𝒲₀`, and `‖(R − 1/2) v‖ ≤ ‖G v‖/2`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump ThetaSourceWard

/-- The pole-free Weil operator on a real source. -/
def weilOp (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  -2 * archConstantReal * f y +
    (∫ u in Ioi (0 : ℝ), 2 * archDiagonalDensity u * f y - archLevyDensity u * (f (y + u) + f (y - u))) -
    ∑' n : ℕ, vonMangoldtAtom n * (f (y + Real.log n) + f (y - Real.log n))

/-- The archimedean integrand of `𝒲₀(Θv)` is the symmetrized kernel integrand scaled by `v` plus
the weighted jump. -/
theorem archIntegrand_eq (v : ℝ → ℝ) (y u : ℝ) :
    2 * archDiagonalDensity u * phiDoobTest v y -
      archLevyDensity u * (phiDoobTest v (y + u) + phiDoobTest v (y - u)) =
      v y * symArchTerm y u + archLevyDensity u * symJump v u y := by
  unfold phiDoobTest symArchTerm symJump
  ring

theorem integrableOn_archJump {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (y : ℝ) : IntegrableOn (fun t => archLevyDensity t * symJump v t y) (Ioi 0) := by
  obtain ⟨L, hL⟩ := compact_source_lipschitz hv hvc
  obtain ⟨C, hC0, hC⟩ := exists_theta_bound
  refine (integrableOn_archMoment.const_mul (2 * C * L)).mono' ?_ ?_
  · exact (measurable_archLevyDensity.mul
      (continuous_symJump_left hv.continuous y).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht')]
    have hs := abs_symJump_le_lipschitz hL hC t y
    rw [abs_of_pos ht'] at hs
    calc archLevyDensity t * |symJump v t y| ≤ archLevyDensity t * (2 * C * L * t) :=
          mul_le_mul_of_nonneg_left hs (archLevyDensity_pos ht').le
      _ = 2 * C * L * (archLevyDensity t * t) := by ring

theorem integrableOn_archIntegrand {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (y : ℝ) : IntegrableOn (fun u => 2 * archDiagonalDensity u * phiDoobTest v y -
      archLevyDensity u * (phiDoobTest v (y + u) + phiDoobTest v (y - u))) (Ioi 0) := by
  have h : IntegrableOn ((fun u => v y * symArchTerm y u) +
      fun t => archLevyDensity t * symJump v t y) (Ioi 0) :=
    ((integrableOn_symArchTerm y).const_mul (v y)).add (integrableOn_archJump hv hvc y)
  refine MeasureTheory.IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [archIntegrand_eq]

theorem summable_source_shift {v : ℝ → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    (y : ℝ) : Summable fun n : ℕ => vonMangoldtAtom n *
      (phiDoobTest v (y + Real.log n) + phiDoobTest v (y - Real.log n)) := by
  obtain ⟨M, hM⟩ := compact_source_thetaBound (f := phiDoobTest v)
    (continuous_riemannKernelReal.mul hv) (hasCompactSupport_phiDoobTest hvc)
  have hM0 : 0 ≤ M := by
    by_contra hneg
    rw [not_le] at hneg
    have h1 := hM 0
    have h2 := mul_neg_of_neg_of_pos hneg (riemannKernelReal_pos 0)
    linarith [abs_nonneg (phiDoobTest v 0)]
  refine ((summable_primeKernelSum y).mul_left M).of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
  have ha := vonMangoldtAtom_nonneg n
  calc vonMangoldtAtom n * |phiDoobTest v (y + Real.log n) + phiDoobTest v (y - Real.log n)|
      ≤ vonMangoldtAtom n * (|phiDoobTest v (y + Real.log n)| + |phiDoobTest v (y - Real.log n)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) ha
    _ ≤ vonMangoldtAtom n * (M * riemannKernelReal (y + Real.log n) +
          M * riemannKernelReal (y - Real.log n)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hM _) (hM _)) ha
    _ = M * (vonMangoldtAtom n * (riemannKernelReal (y + Real.log n) +
          riemannKernelReal (y - Real.log n))) := by ring

/-- **The jump image is the polar rate plus the pole-free Weil operator of the source.** -/
theorem genTotal_eq_weilOp {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (y : ℝ) :
    genTotal v y - Real.cosh (y / 2) * v y = weilOp (phiDoobTest v) y := by
  have hA : genArch v y = (∫ u in Ioi (0 : ℝ), 2 * archDiagonalDensity u * phiDoobTest v y -
      archLevyDensity u * (phiDoobTest v (y + u) + phiDoobTest v (y - u))) -
      v y * ∫ u in Ioi (0 : ℝ), symArchTerm y u := by
    unfold genArch
    rw [← integral_const_mul, ← integral_sub (integrableOn_archIntegrand hv hvc y)
      ((integrableOn_symArchTerm y).const_mul (v y))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [archIntegrand_eq]
    ring
  have hP : genPrime v y = v y * primeKernelSum y -
      ∑' n : ℕ, vonMangoldtAtom n * (phiDoobTest v (y + Real.log n) + phiDoobTest v (y - Real.log n)) := by
    unfold genPrime primeKernelSum
    rw [← tsum_mul_left, ← (summable_primeKernelSum y |>.mul_left (v y)).tsum_sub
      (summable_source_shift hv.continuous hvc y)]
    apply tsum_congr
    intro n
    unfold symJump phiDoobTest
    ring
  unfold genTotal weilOp
  rw [hA, hP, theta_harmonic_identity y]
  unfold phiDoobTest
  ring

/-! ## The generator image -/

/-- The generator image `G v = J v / cosh(·/2) − v`. -/
def genImage (v : ℝ → ℝ) (y : ℝ) : ℝ := genTotal v y / Real.cosh (y / 2) - v y

theorem genImage_eq_weilOp {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (y : ℝ) :
    genImage v y = weilOp (phiDoobTest v) y / Real.cosh (y / 2) := by
  unfold genImage
  rw [← genTotal_eq_weilOp hv hvc y]
  field_simp [(Real.cosh_pos (y / 2)).ne']

theorem measurable_genImage {v : ℝ → ℝ} (hv : Continuous v) : Measurable (genImage v) :=
  ((measurable_genTotal hv).div (Real.continuous_cosh.comp (continuous_id.div_const 2)).measurable).sub
    hv.measurable

/-- The pole-free Weil operator of a compact source grows at most like the polar rate. -/
theorem exists_weilOp_bound {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |weilOp (phiDoobTest v) y| ≤ K * (1 + Real.cosh (y / 2)) := by
  obtain ⟨M, hM⟩ := hvc.exists_bound_of_continuous hv.continuous
  have hM' : ∀ x, |v x| ≤ M := fun x => by simpa only [Real.norm_eq_abs] using hM x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  obtain ⟨KA, hKA0, hKA⟩ := exists_genArch_bound hv hvc
  obtain ⟨KP₀, hKP₀⟩ := exists_primeKernelSum_bound
  set KP : ℝ := |KP₀| with hKPdef
  have hKP0 : 0 ≤ KP := abs_nonneg _
  have hKP : ∀ y, primeKernelSum y ≤ Real.cosh (y / 2) + KP := fun y =>
    (hKP₀ y).trans (by linarith [le_abs_self KP₀])
  refine ⟨KA + 2 * M * KP + 3 * M, by positivity, fun y => ?_⟩
  rw [← genTotal_eq_weilOp hv hvc y]
  have h1 := hKA y
  have h2 := (abs_genPrime_le hM' y).trans (mul_le_mul_of_nonneg_left (hKP y) (by positivity))
  have h3 : |Real.cosh (y / 2) * v y| ≤ M * Real.cosh (y / 2) := by
    rw [abs_mul, abs_of_pos (Real.cosh_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM' y) (Real.cosh_pos _).le
  have hc1 := Real.one_le_cosh (y / 2)
  unfold genTotal
  calc |genArch v y + genPrime v y - Real.cosh (y / 2) * v y|
      ≤ |genArch v y| + |genPrime v y| + |Real.cosh (y / 2) * v y| := by
        refine (abs_sub _ _).trans ?_
        linarith [abs_add_le (genArch v y) (genPrime v y)]
    _ ≤ KA + 2 * M * (Real.cosh (y / 2) + KP) + M * Real.cosh (y / 2) := by linarith
    _ ≤ (KA + 2 * M * KP + 3 * M) * (1 + Real.cosh (y / 2)) := by
        nlinarith [mul_nonneg hKA0 (by linarith : (0 : ℝ) ≤ Real.cosh (y / 2)),
          mul_nonneg (mul_nonneg hM0 hKP0) (by linarith : (0 : ℝ) ≤ Real.cosh (y / 2))]

theorem exists_genImage_bound {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∃ K : ℝ, ∀ y, |genImage v y| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := exists_weilOp_bound hv hvc
  refine ⟨2 * K, fun y => ?_⟩
  rw [genImage_eq_weilOp hv hvc, abs_div, abs_of_pos (Real.cosh_pos _), div_le_iff₀ (Real.cosh_pos _)]
  have := Real.one_le_cosh (y / 2)
  nlinarith [hK y]

theorem memLp_genImage {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    MemLp (genImage v) 2 massMeasure := by
  obtain ⟨K, hK⟩ := exists_genImage_bound hv hvc
  exact MemLp.of_bound (measurable_genImage hv.continuous).aestronglyMeasurable K
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hK y)

/-- The generator image as a vector of the theta–cosh mass space. -/
def genImageL (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) : MassSpace :=
  (memLp_genImage hv hvc).toLp (genImage v)

/-! ## The signed pairing on compact tests -/

theorem inner_source_compactLift {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ⟪(compactLift v hv hvc).val.fst, (compactLift w hw hwc).val.fst⟫_ℝ =
      ∫ y, v y * w y ∂massMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactLift_source_ae v hv hvc, compactLift_source_ae w hw hwc] with y h1 h2
  change inner ℝ ((compactLift v hv hvc).val.fst y) ((compactLift w hw hwc).val.fst y) = _
  rw [h1, h2]
  simp [mul_comm]

theorem integrable_weight_genTotal {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    Integrable fun y => w y * riemannKernelReal y * genTotal v y := by
  refine ((integrable_weight_genArch hv hvc hw hwc).add
    (integrable_weight_genPrime hv.continuous hvc hw hwc)).congr (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, genTotal]
  ring

/-- **The signed pairing of two compact tests is the mass pairing of one with the generator image
of the other.** -/
theorem sourcePair_compactLift_eq {v w : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    sourcePair (compactLift v hv hvc) (compactLift w hw hwc) =
      ∫ y, genImage v y * w y ∂massMeasure := by
  change ⟪(compactLift v hv hvc).val.snd, (compactLift w hw hwc).val.snd⟫_ℝ -
    ⟪(compactLift v hv hvc).val.fst, (compactLift w hw hwc).val.fst⟫_ℝ = _
  rw [inner_edge_compactLift hv hvc hw hwc, inner_source_compactLift hv hvc hw hwc, integral_mass,
    integral_mass]
  have hvw : Integrable fun y => massDensity y * (v y * w y) :=
    (continuous_massDensity.mul (hv.continuous.mul hw.continuous)).integrable_of_hasCompactSupport
      (hwc.mul_left.mul_left)
  rw [← integral_sub (integrable_weight_genTotal hv hvc hw.continuous hwc) hvw]
  congr 1
  funext y
  unfold genImage massDensity
  field_simp [(Real.cosh_pos (y / 2)).ne']

/-- **Extension to the whole completed graph.** -/
theorem sourcePair_compactLift {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (q : SourceGraph) :
    sourcePair (compactLift v hv hvc) q = ⟪genImageL v hv hvc, q.val.fst⟫_ℝ := by
  have hc1 : Continuous (fun q : SourceGraph => sourcePair (compactLift v hv hvc) q) :=
    continuous_sourcePair.comp (continuous_const.prodMk continuous_id)
  have hc2 : Continuous (fun q : SourceGraph => ⟪genImageL v hv hvc, q.val.fst⟫_ℝ) :=
    continuous_const.inner sourceMap.continuous
  have he : (fun q : SourceGraph => sourcePair (compactLift v hv hvc) q) =
      fun q => ⟪genImageL v hv hvc, q.val.fst⟫_ℝ := by
    apply Continuous.ext_on dense_compactTests hc1 hc2
    rintro q ⟨w, hw, hwc, rfl⟩
    dsimp only
    rw [sourcePair_compactLift_eq hv hvc hw hwc, real_inner_comm]
    unfold genImageL
    rw [inner_toLp_right]
    apply integral_congr_ae
    filter_upwards [compactLift_source_ae w hw hwc] with y hy
    rw [hy, mul_comm]
  exact congrFun he q

/-! ## Resolvent coordinates -/

theorem inner_smul_graph (c : ℝ) (p q : SourceGraph) : ⟪c • p, q⟫_ℝ = c * ⟪p, q⟫_ℝ := by
  rw [graph_inner, graph_inner]
  change ⟪c • p.val.fst, q.val.fst⟫_ℝ + ⟪c • p.val.snd, q.val.snd⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_left]
  ring

theorem inner_sub_graph (p p' q : SourceGraph) : ⟪p - p', q⟫_ℝ = ⟪p, q⟫_ℝ - ⟪p', q⟫_ℝ := by
  rw [graph_inner, graph_inner, graph_inner]
  change ⟪p.val.fst - p'.val.fst, q.val.fst⟫_ℝ + ⟪p.val.snd - p'.val.snd, q.val.snd⟫_ℝ = _
  rw [inner_sub_left, inner_sub_left]
  ring

/-- The Riesz lift of a compact source is half the lift minus half the Riesz lift of its generator
image. -/
theorem rieszLift_compactLift_source {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    rieszLift (compactLift v hv hvc).val.fst =
      (1 / 2 : ℝ) • compactLift v hv hvc - (1 / 2 : ℝ) • rieszLift (genImageL v hv hvc) := by
  apply rieszLift_unique
  intro q
  rw [inner_sub_graph, inner_smul_graph, inner_smul_graph, inner_rieszLift, graph_inner]
  have h := sourcePair_compactLift hv hvc q
  change ⟪(compactLift v hv hvc).val.snd, q.val.snd⟫_ℝ -
    ⟪(compactLift v hv hvc).val.fst, q.val.fst⟫_ℝ = _ at h
  linarith

/-- **The arithmetic resolvent on compact tests.** -/
theorem resolvent_compactLift_source {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    resolvent (compactLift v hv hvc).val.fst =
      (1 / 2 : ℝ) • (compactLift v hv hvc).val.fst - (1 / 2 : ℝ) • resolvent (genImageL v hv hvc) := by
  rw [resolvent_apply, rieszLift_compactLift_source, resolvent_apply]
  rfl

/-- The resolvent defect at the threshold is controlled by the generator image. -/
theorem norm_resolvent_sub_half_le {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ‖resolvent (compactLift v hv hvc).val.fst - (1 / 2 : ℝ) • (compactLift v hv hvc).val.fst‖ ≤
      (1 / 2 : ℝ) * ‖genImageL v hv hvc‖ := by
  rw [resolvent_compactLift_source]
  have h : (1 / 2 : ℝ) • (compactLift v hv hvc).val.fst - (1 / 2 : ℝ) • resolvent (genImageL v hv hvc) -
      (1 / 2 : ℝ) • (compactLift v hv hvc).val.fst = -((1 / 2 : ℝ) • resolvent (genImageL v hv hvc)) := by
    abel
  rw [h, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ‖resolvent (genImageL v hv hvc)‖ ≤ ‖resolvent‖ * ‖genImageL v hv hvc‖ :=
        resolvent.le_opNorm _
    _ ≤ 1 * ‖genImageL v hv hvc‖ := mul_le_mul_of_nonneg_right norm_resolvent_le (norm_nonneg _)
    _ = ‖genImageL v hv hvc‖ := one_mul _

end RHTower.CHMDPolar
