import GaloisForLFunctions.RHTower.CHMDBirmanSchwingerBound

/-!
# The reflection symmetry of the arithmetic Doob graph

Riemann's kernel `Θ` is even, so the theta–cosh mass `μ = Θ cosh(x/2) dx` is invariant under
`x ↦ −x`, and the edge measure of the arithmetic Doob graph (archimedean edges `(t, x)` with weight
`ω(t)Θ(x)Θ(x+t)` and prime edges `(log n, x)` with weight `Λ(n)n^{−1/2}Θ(x)Θ(x+log n)`) is invariant
under the edge reflection `(t, x) ↦ (t, −x − t)`, which sends the jump from `x` to `x+t` to the jump
from `−x−t` to `−x`. Composition with these reflections defines an isometric involution `J` of the
mass space and of the completed graph, compatible with the source projection, and the arithmetic
resolvent commutes with it: `R(Jw) = J(Rw)`.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ENNReal
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Invariance of weighted measures -/

/-- A measure-preserving map that fixes the density preserves the weighted measure. -/
theorem measurePreserving_withDensity_of_invariant {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {σ : α → α} (hσ : MeasurePreserving σ μ μ) {w : α → ℝ≥0∞} (hw : Measurable w)
    (hinv : ∀ x, w (σ x) = w x) : MeasurePreserving σ (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hσ.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hσ.measurable hs, withDensity_apply _ (hσ.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator (hσ.measurable hs), ← lintegral_indicator hs,
    ← hσ.lintegral_comp (hw.indicator hs)]
  congr 1
  funext x
  by_cases h : σ x ∈ s
  · rw [Set.indicator_of_mem (show x ∈ σ ⁻¹' s from h), Set.indicator_of_mem h, hinv]
  · rw [Set.indicator_of_notMem (show x ∉ σ ⁻¹' s from h), Set.indicator_of_notMem h]

theorem measurePreserving_neg_volume : MeasurePreserving (fun x : ℝ => -x) volume volume :=
  ⟨measurable_neg, Measure.map_neg_eq_self volume⟩

theorem measurePreserving_neg_sub_volume (c : ℝ) :
    MeasurePreserving (fun x : ℝ => -x - c) volume volume := by
  have h : (fun x : ℝ => -x - c) = (fun x : ℝ => -x) ∘ (fun x : ℝ => x + c) := by
    funext x
    simp only [Function.comp]
    ring
  rw [h]
  exact measurePreserving_neg_volume.comp (measurePreserving_add_right volume c)

/-- The theta–cosh mass is reflection invariant. -/
theorem measurePreserving_neg_mass : MeasurePreserving (fun x : ℝ => -x) massMeasure massMeasure := by
  unfold massMeasure
  refine measurePreserving_withDensity_of_invariant measurePreserving_neg_volume
    (ENNReal.measurable_ofReal.comp continuous_massDensity.measurable) fun x => ?_
  simp only [massDensity_neg]

/-! ## The edge reflection -/

/-- The edge reflection `(t, x) ↦ (t, −x − t)`. -/
def edgeReflect (e : ℝ × ℝ) : ℝ × ℝ := (e.1, -e.2 - e.1)

theorem measurable_edgeReflect : Measurable edgeReflect := by
  unfold edgeReflect
  fun_prop

theorem edgeReflect_edgeReflect (e : ℝ × ℝ) : edgeReflect (edgeReflect e) = e := by
  unfold edgeReflect
  ext
  · rfl
  · simp only
    ring

theorem left_edgeReflect (e : ℝ × ℝ) : left (edgeReflect e) = -right e := by
  simp only [left, right, edgeReflect]
  ring

theorem right_edgeReflect (e : ℝ × ℝ) : right (edgeReflect e) = -left e := by
  simp only [left, right, edgeReflect]
  ring

theorem measurePreserving_edgeReflect_archBase :
    MeasurePreserving edgeReflect archBase archBase := by
  unfold archBase
  have h := MeasurePreserving.skew_product (MeasurePreserving.id (volume.restrict (Ioi (0 : ℝ))))
    (g := fun t x : ℝ => -x - t) (μc := volume) (μd := volume)
    (by fun_prop : Measurable (Function.uncurry fun t x : ℝ => -x - t))
    (Eventually.of_forall fun t => (measurePreserving_neg_sub_volume t).map_eq)
  exact h

theorem archWeight_edgeReflect (e : ℝ × ℝ) : archWeight (edgeReflect e) = archWeight e := by
  unfold archWeight edgeReflect
  simp only
  rw [show -e.2 - e.1 + e.1 = -e.2 by ring, show -e.2 - e.1 = -(e.2 + e.1) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
  ring

theorem measurePreserving_edgeReflect_arch : MeasurePreserving edgeReflect archMeasure archMeasure := by
  unfold archMeasure
  exact measurePreserving_withDensity_of_invariant measurePreserving_edgeReflect_archBase
    (ENNReal.measurable_ofReal.comp measurable_archWeight) fun e => by rw [archWeight_edgeReflect]

theorem continuous_primeWeight (n : ℕ) : Continuous (primeWeight n) := by
  unfold primeWeight
  exact (continuous_const.mul continuous_riemannKernelReal).mul
    (continuous_riemannKernelReal.comp (continuous_id.add continuous_const))

theorem primeWeight_reflect (n : ℕ) (x : ℝ) : primeWeight n (-x - Real.log n) = primeWeight n x := by
  unfold primeWeight
  rw [show -x - Real.log n + Real.log n = -x by ring, show -x - Real.log n = -(x + Real.log n) by ring,
    WeilExcess.riemannKernelReal_neg, WeilExcess.riemannKernelReal_neg]
  ring

theorem measurePreserving_primeReflect (n : ℕ) :
    MeasurePreserving (fun x : ℝ => -x - Real.log n)
      (volume.withDensity fun x => ENNReal.ofReal (primeWeight n x))
      (volume.withDensity fun x => ENNReal.ofReal (primeWeight n x)) :=
  measurePreserving_withDensity_of_invariant (measurePreserving_neg_sub_volume _)
    (ENNReal.measurable_ofReal.comp (continuous_primeWeight n).measurable)
    fun x => by rw [primeWeight_reflect]

theorem map_edgeReflect_primeMeasure (n : ℕ) :
    Measure.map edgeReflect (primeMeasure n) = primeMeasure n := by
  unfold primeMeasure
  rw [Measure.map_map measurable_edgeReflect measurable_prodMk_left]
  have h : edgeReflect ∘ (fun x : ℝ => (Real.log n, x)) =
      (fun x : ℝ => (Real.log n, x)) ∘ (fun x : ℝ => -x - Real.log n) := by
    funext x
    simp [edgeReflect]
  rw [h, ← Measure.map_map measurable_prodMk_left (by fun_prop),
    (measurePreserving_primeReflect n).map_eq]

/-- The edge measure of the arithmetic Doob graph is reflection invariant. -/
theorem measurePreserving_edgeReflect_edge : MeasurePreserving edgeReflect edgeMeasure edgeMeasure := by
  refine ⟨measurable_edgeReflect, ?_⟩
  unfold edgeMeasure
  rw [Measure.map_add _ _ measurable_edgeReflect, measurePreserving_edgeReflect_arch.map_eq,
    Measure.map_sum measurable_edgeReflect.aemeasurable]
  congr 1
  exact congrArg Measure.sum (funext map_edgeReflect_primeMeasure)

/-! ## The reflection operators -/

/-- Reflection on the mass space. -/
def reflectMass : MassSpace →ₗᵢ[ℝ] MassSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => -x) measurePreserving_neg_mass

/-- Reflection on the edge space. -/
def reflectEdge : Lp ℝ 2 edgeMeasure →ₗᵢ[ℝ] Lp ℝ 2 edgeMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ edgeReflect measurePreserving_edgeReflect_edge

theorem reflectMass_coeFn (f : MassSpace) :
    (reflectMass f : ℝ → ℝ) =ᵐ[massMeasure] fun x => f (-x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_neg_mass

theorem reflectEdge_coeFn (g : Lp ℝ 2 edgeMeasure) :
    (reflectEdge g : ℝ × ℝ → ℝ) =ᵐ[edgeMeasure] fun e => g (edgeReflect e) :=
  Lp.coeFn_compMeasurePreserving g measurePreserving_edgeReflect_edge

theorem reflectMass_reflectMass (f : MassSpace) : reflectMass (reflectMass f) = f := by
  rw [Lp.ext_iff]
  have h1 := reflectMass_coeFn (reflectMass f)
  have h2 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp (reflectMass_coeFn f)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1]
  simp only [Function.comp] at hx2
  rw [hx2, neg_neg]

theorem inner_reflectMass (f g : MassSpace) : ⟪reflectMass f, g⟫_ℝ = ⟪f, reflectMass g⟫_ℝ := by
  have h := reflectMass.inner_map_map (reflectMass f) g
  rw [reflectMass_reflectMass] at h
  exact h.symm

/-! ## The graph reflection -/

theorem reflect_mem_graph (p : SourceGraph) :
    WithLp.toLp 2 (reflectMass p.val.fst, -reflectEdge p.val.snd) ∈
      graph massMeasure edgeMeasure left right nonsingular_left nonsingular_right := by
  have hp := p.property
  have hpσ := measurePreserving_edgeReflect_edge.quasiMeasurePreserving.ae hp
  have hl := nonsingular_left.ae (reflectMass_coeFn p.val.fst)
  have hr := nonsingular_right.ae (reflectMass_coeFn p.val.fst)
  have hE := reflectEdge_coeFn p.val.snd
  have hneg := Lp.coeFn_neg (reflectEdge p.val.snd)
  filter_upwards [hpσ, hl, hr, hE, hneg] with e h1 h2 h3 h4 h5
  change (-reflectEdge p.val.snd) e = (reflectMass p.val.fst) (left e) - (reflectMass p.val.fst) (right e)
  rw [h5, Pi.neg_apply, h4, h1, left_edgeReflect, right_edgeReflect, h2, h3]
  ring

/-- Reflection on the completed graph. -/
def reflectGraph (p : SourceGraph) : SourceGraph :=
  ⟨WithLp.toLp 2 (reflectMass p.val.fst, -reflectEdge p.val.snd), reflect_mem_graph p⟩

theorem reflectGraph_fst (p : SourceGraph) : (reflectGraph p).val.fst = reflectMass p.val.fst := rfl

theorem reflectGraph_snd (p : SourceGraph) : (reflectGraph p).val.snd = -reflectEdge p.val.snd := rfl

theorem reflectGraph_reflectGraph (p : SourceGraph) : reflectGraph (reflectGraph p) = p := by
  apply source_projection_injective
  show (reflectGraph (reflectGraph p)).val.fst = p.val.fst
  rw [reflectGraph_fst, reflectGraph_fst, reflectMass_reflectMass]

theorem reflectGraph_add (p q : SourceGraph) :
    reflectGraph (p + q) = reflectGraph p + reflectGraph q := by
  apply source_projection_injective
  show (reflectGraph (p + q)).val.fst = (reflectGraph p + reflectGraph q).val.fst
  rw [reflectGraph_fst]
  change reflectMass (p.val.fst + q.val.fst) = reflectMass p.val.fst + reflectMass q.val.fst
  exact map_add _ _ _

theorem reflectGraph_smul (c : ℝ) (p : SourceGraph) : reflectGraph (c • p) = c • reflectGraph p := by
  apply source_projection_injective
  show (reflectGraph (c • p)).val.fst = (c • reflectGraph p).val.fst
  rw [reflectGraph_fst]
  change reflectMass (c • p.val.fst) = c • reflectMass p.val.fst
  exact map_smul _ _ _

theorem norm_reflectGraph (p : SourceGraph) : ‖reflectGraph p‖ = ‖p‖ := by
  have h1 := graph_norm_sq (reflectGraph p)
  have h2 := graph_norm_sq p
  rw [reflectGraph_fst, reflectGraph_snd, norm_neg, LinearIsometry.norm_map,
    LinearIsometry.norm_map] at h1
  have h3 : ‖reflectGraph p‖ ^ 2 = ‖p‖ ^ 2 := by rw [h1, h2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3

/-- The graph reflection as a linear isometry. -/
def reflectGraphₗᵢ : SourceGraph →ₗᵢ[ℝ] SourceGraph where
  toFun := reflectGraph
  map_add' := reflectGraph_add
  map_smul' := reflectGraph_smul
  norm_map' := norm_reflectGraph

theorem reflectGraphₗᵢ_apply (p : SourceGraph) : reflectGraphₗᵢ p = reflectGraph p := rfl

theorem inner_reflectGraph (p q : SourceGraph) : ⟪reflectGraph p, q⟫_ℝ = ⟪p, reflectGraph q⟫_ℝ := by
  have h := reflectGraphₗᵢ.inner_map_map (reflectGraph p) q
  rw [reflectGraphₗᵢ_apply, reflectGraphₗᵢ_apply, reflectGraph_reflectGraph] at h
  exact h.symm

theorem continuous_reflectGraph : Continuous reflectGraph := reflectGraphₗᵢ.continuous

/-! ## The resolvent commutes with reflection -/

theorem rieszLift_reflectMass (w : MassSpace) :
    rieszLift (reflectMass w) = reflectGraph (rieszLift w) := by
  apply rieszLift_unique
  intro q
  rw [inner_reflectGraph, inner_rieszLift, reflectGraph_fst, ← inner_reflectMass]

/-- **The arithmetic resolvent commutes with reflection.** -/
theorem resolvent_reflectMass (w : MassSpace) :
    resolvent (reflectMass w) = reflectMass (resolvent w) := by
  rw [resolvent_apply, resolvent_apply, rieszLift_reflectMass, reflectGraph_fst]

/-! ## Reflection of compact tests -/

theorem reflectGraph_compactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    reflectGraph (compactLift v hv hvc) =
      compactLift (fun x => v (-x)) (hv.comp contDiff_neg) (hvc.comp_homeomorph (Homeomorph.neg ℝ)) := by
  apply source_projection_injective
  show (reflectGraph (compactLift v hv hvc)).val.fst = (compactLift (fun x => v (-x)) _ _).val.fst
  rw [reflectGraph_fst, Lp.ext_iff]
  have h1 := reflectMass_coeFn (compactLift v hv hvc).val.fst
  have h2 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp (compactLift_source_ae v hv hvc)
  have h3 := compactLift_source_ae (fun x => v (-x)) (hv.comp contDiff_neg)
    (hvc.comp_homeomorph (Homeomorph.neg ℝ))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [Function.comp] at hx2
  rw [hx1, hx2, hx3]

end RHTower.CHMDPolar
