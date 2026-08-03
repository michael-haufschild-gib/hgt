import GaloisForLFunctions.HTGeometry.BohrOrbitHaarLaw

/-!
# The boundary of a background perturbed by an exponential carrier

Translating an exponential carrier is the same as rotating its phases: `A (z + t)` is the carrier
with amplitudes `a_i e^{i omega_i t}`, which is the point of the phase hull at flow time `t`.  So an
orbit built from a background `S` plus a fixed multiple of the carrier differs from the corresponding
hull point by `S (z + t) - c` alone.

If the background collapses to the constant `c` uniformly on compact subsets of the upper half plane
as the shift leaves every compact set of times, the orbit is therefore asymptotic to the hull along
the phase flow.  Its closure is then the orbit together with the whole boundary family, and every
uniformly continuous observable of the orbit has the Haar mean of the boundary as its limiting time
average.
-/

open Filter MeasureTheory Set Topology

namespace GaloisForLFunctions

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*}

/-! ## Uniform closeness on compact sets -/

/-- A pair of families of continuous maps which is uniformly close on every compact set converges in
the uniformity of compact convergence. -/
theorem tendsto_uniformity_continuousMap {α β γ : Type*} [TopologicalSpace α]
    [PseudoMetricSpace β] {l : Filter γ} {F G : γ → C(α, β)}
    (h : ∀ K : Set α, IsCompact K → ∀ ε > 0, ∀ᶠ t in l, ∀ x ∈ K, dist (F t x) (G t x) < ε) :
    Tendsto (fun t => (F t, G t)) l (uniformity C(α, β)) := by
  rw [ContinuousMap.hasBasis_compactConvergenceUniformity.tendsto_right_iff]
  rintro ⟨K, V⟩ ⟨hK, hV⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hV
  filter_upwards [h K hK ε hε] with t ht
  exact fun x hx => hsub (ht x hx)

/-! ## Translating the carrier rotates its phases -/

theorem cexpChar_add (omega : ℝ) (z w : ℂ) :
    cexpChar omega (z + w) = cexpChar omega z * cexpChar omega w := by
  rw [cexpChar, cexpChar, cexpChar, ← Complex.exp_add]
  ring_nf

/-- **Translation is phase rotation.**  Shifting the argument of an exponential carrier multiplies
each amplitude by the character of the shift. -/
theorem cexpSeriesCarrier_add {a : ι → ℂ} {omega : ι → ℝ} (z w : ℂ) :
    cexpSeriesCarrier a omega (z + w)
      = cexpSeriesCarrier (fun i => a i * cexpChar (omega i) w) omega z := by
  rw [cexpSeriesCarrier, cexpSeriesCarrier]
  congr 1
  funext i
  rw [cexpChar_add]
  ring

/-- The phase flow read in the circle group is the character of the shift. -/
theorem circlePhaseFlow_coe (omega : ι → ℝ) (t : ℝ) (i : ι) :
    ((circlePhaseFlow omega t i : Circle) : ℂ) = cexpChar (omega i) (t : ℂ) := by
  rw [circlePhaseFlow, AddCircle.homeomorphCircle_apply, clockPhasePoint,
    AddCircle.toCircle_apply_mk, Circle.coe_exp, cexpChar]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The hull point at flow time is the translate of the carrier.** -/
theorem bohrHullMap_circlePhaseFlow {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (t : ℝ) (z : ℂ) :
    bohrHullMap a omega h (circlePhaseFlow omega t) z = cexpSeriesCarrier a omega (z + t) := by
  rw [bohrHullMap_apply, cexpSeriesCarrier_add]
  congr 1
  funext i
  rw [circlePhaseFlow_coe]

/-! ## The perturbed orbit on the upper half plane -/

/-- The open upper half plane, as a topological space. -/
abbrev UpperPlane : Type := ↥{z : ℂ | 0 < z.im}

theorem upperPlane_add_ofReal (z : UpperPlane) (t : ℝ) : 0 < ((z : ℂ) + (t : ℂ)).im := by
  have hz : 0 < (z : ℂ).im := z.2
  simpa using hz

/-- The boundary family of a perturbed orbit: a constant plus a scaled phase hull, read on the
upper half plane. -/
def perturbedBoundary {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (c eps : ℂ) (lam : ι → Circle) : C(UpperPlane, ℂ) :=
  ⟨fun z => c + eps * bohrHullMap a omega h lam (z : ℂ),
    continuous_const.add
      (continuous_const.mul ((bohrHullMap a omega h lam).continuous.comp continuous_subtype_val))⟩

theorem perturbedBoundary_apply {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (c eps : ℂ) (lam : ι → Circle) (z : UpperPlane) :
    perturbedBoundary h c eps lam z = c + eps * bohrHullMap a omega h lam (z : ℂ) := rfl

/-- The boundary family is continuous in the phase. -/
theorem continuous_perturbedBoundary {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (c eps : ℂ) :
    Continuous (perturbedBoundary h c eps) := by
  rw [continuous_iff_continuousAt]
  intro lam₀
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hKim : IsCompact ((fun z : UpperPlane => (z : ℂ)) '' K) :=
    hK.image continuous_subtype_val
  have hbase := (continuous_bohrHullMap h).continuousAt (x := lam₀)
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hbase
  have hδ : 0 < ε / (‖eps‖ + 1) := by positivity
  have huc := hbase _ hKim
  rw [Metric.tendstoUniformlyOn_iff] at huc
  filter_upwards [huc _ hδ] with lam hlam z hz
  have hzim : (z : ℂ) ∈ (fun z : UpperPlane => (z : ℂ)) '' K := ⟨z, hz, rfl⟩
  have hd := hlam _ hzim
  rw [perturbedBoundary_apply, perturbedBoundary_apply, Complex.dist_eq]
  have hrw : c + eps * bohrHullMap a omega h lam₀ (z : ℂ)
      - (c + eps * bohrHullMap a omega h lam (z : ℂ))
      = eps * (bohrHullMap a omega h lam₀ (z : ℂ) - bohrHullMap a omega h lam (z : ℂ)) := by
    ring
  rw [hrw, norm_mul]
  rw [Complex.dist_eq] at hd
  calc ‖eps‖ * ‖bohrHullMap a omega h lam₀ (z : ℂ) - bohrHullMap a omega h lam (z : ℂ)‖
      ≤ ‖eps‖ * (ε / (‖eps‖ + 1)) := by
        exact mul_le_mul_of_nonneg_left hd.le (norm_nonneg _)
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg eps, hε]

/-- The orbit of a background perturbed by a fixed multiple of an exponential carrier. -/
def perturbedOrbit {a : ι → ℂ} {omega : ι → ℝ} (h : ExpSeriesNormallySummable a omega)
    (S : ℂ → ℂ) (hS : ContinuousOn S {z : ℂ | 0 < z.im}) (eps : ℂ) (t : ℝ) :
    C(UpperPlane, ℂ) :=
  ⟨fun z => S ((z : ℂ) + (t : ℂ)) + eps * cexpSeriesCarrier a omega ((z : ℂ) + (t : ℂ)), by
    refine Continuous.add ?_ ?_
    · refine ContinuousOn.comp_continuous hS
        (continuous_subtype_val.add continuous_const) fun z => ?_
      exact upperPlane_add_ofReal z t
    · exact continuous_const.mul
        (((differentiable_cexpSeriesCarrier h).continuous).comp
          (continuous_subtype_val.add continuous_const))⟩

theorem perturbedOrbit_apply {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (S : ℂ → ℂ)
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) (eps : ℂ) (t : ℝ) (z : UpperPlane) :
    perturbedOrbit h S hS eps t z
      = S ((z : ℂ) + (t : ℂ)) + eps * cexpSeriesCarrier a omega ((z : ℂ) + (t : ℂ)) := rfl

/-- **The orbit is asymptotic to the boundary family along the phase flow.**  The carrier parts
agree exactly, so the two differ by the collapse of the background alone. -/
theorem tendsto_uniformity_perturbedOrbit {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) {c eps : ℂ} {l : Filter ℝ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) l K) :
    Tendsto (fun t => (perturbedBoundary h c eps (circlePhaseFlow omega t),
      perturbedOrbit h S hS eps t)) l (uniformity C(UpperPlane, ℂ)) := by
  refine tendsto_uniformity_continuousMap fun K hK ε hε => ?_
  have hKim : IsCompact ((fun z : UpperPlane => (z : ℂ)) '' K) :=
    hK.image continuous_subtype_val
  have hKpos : ∀ z ∈ (fun z : UpperPlane => (z : ℂ)) '' K, 0 < z.im := by
    rintro z ⟨w, _, rfl⟩
    exact w.2
  have huc := hcollapse _ hKim hKpos
  rw [Metric.tendstoUniformlyOn_iff] at huc
  filter_upwards [huc ε hε] with t ht z hz
  have hzim : (z : ℂ) ∈ (fun z : UpperPlane => (z : ℂ)) '' K := ⟨z, hz, rfl⟩
  have hd := ht _ hzim
  rw [perturbedBoundary_apply, perturbedOrbit_apply, bohrHullMap_circlePhaseFlow]
  rw [Complex.dist_eq]
  have hrw : c + eps * cexpSeriesCarrier a omega ((z : ℂ) + (t : ℂ))
      - (S ((z : ℂ) + (t : ℂ)) + eps * cexpSeriesCarrier a omega ((z : ℂ) + (t : ℂ)))
      = c - S ((z : ℂ) + (t : ℂ)) := by ring
  rw [hrw]
  rw [Complex.dist_eq] at hd
  exact hd

/-! ## The closure and the limiting law -/

/-- Continuity of the orbit in the shift parameter. -/
theorem continuous_perturbedOrbit {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) (eps : ℂ) :
    Continuous (perturbedOrbit h S hS eps) := by
  have hcoe : Continuous fun p : ℝ × UpperPlane => (p.2 : ℂ) + (p.1 : ℂ) :=
    (continuous_subtype_val.comp continuous_snd).add
      (Complex.continuous_ofReal.comp continuous_fst)
  have hmem : ∀ p : ℝ × UpperPlane, (p.2 : ℂ) + (p.1 : ℂ) ∈ {z : ℂ | 0 < z.im} := by
    intro p
    exact upperPlane_add_ofReal p.2 p.1
  have hF : Continuous fun p : ℝ × UpperPlane =>
      S ((p.2 : ℂ) + (p.1 : ℂ)) + eps * cexpSeriesCarrier a omega ((p.2 : ℂ) + (p.1 : ℂ)) := by
    refine Continuous.add ?_ ?_
    · exact hS.comp_continuous hcoe hmem
    · exact continuous_const.mul
        (((differentiable_cexpSeriesCarrier h).continuous).comp hcoe)
  have heq : perturbedOrbit h S hS eps = ContinuousMap.curry ⟨_, hF⟩ := by
    funext t
    ext z
    rfl
  rw [heq]
  exact (ContinuousMap.curry ⟨_, hF⟩).continuous

/-- **The closure of a perturbed orbit is the orbit together with the whole boundary.**  Equation
(12) for a background collapsing to a constant. -/
theorem closure_range_perturbedOrbit {a : ι → ℂ} {omega : ι → ℝ} [Countable ι] [DecidableEq ι]
    (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) {c eps : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K) :
    closure (Set.range (perturbedOrbit h S hS eps))
      = Set.range (perturbedOrbit h S hS eps) ∪ Set.range (perturbedBoundary h c eps) :=
  closure_range_eq_union_range (continuous_perturbedBoundary h c eps)
    (continuous_perturbedOrbit h hS eps)
    (dense_forwardOrbit_circlePhaseFlow hindep)
    (tendsto_uniformity_perturbedOrbit h hS hcollapse)

/-- **The Haar limiting law of a perturbed orbit.**  Every uniformly continuous observable of the
orbit has the Haar mean of the boundary family as its limiting time average.  This is equation (16).
-/
theorem tendsto_windowAverage_perturbedOrbit {a : ι → ℂ} {omega : ι → ℝ}
    [Countable ι] [DecidableEq ι] (h : ExpSeriesNormallySummable a omega)
    (hindep : RationallyIndependentSequence omega) {S : ℂ → ℂ}
    (hS : ContinuousOn S {z : ℂ | 0 < z.im}) {c eps : ℂ}
    (hcollapse : ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 0 < z.im) →
      TendstoUniformlyOn (fun (t : ℝ) (z : ℂ) => S (z + (t : ℂ))) (fun _ => c) (cocompact ℝ) K)
    {test : C(UpperPlane, ℂ) → ℂ} (htest : UniformContinuous test) :
    Tendsto (windowAverage fun t => test (perturbedOrbit h S hS eps t)) atTop
      (nhds (∫ x, test (perturbedBoundary h c eps
        (unitTorusHomeomorphCircles ι x)) ∂(torusHaar ι))) := by
  have hcont : Continuous fun lam : ι → Circle => test (perturbedBoundary h c eps lam) :=
    htest.continuous.comp (continuous_perturbedBoundary h c eps)
  refine tendsto_windowAverage_haar_circlePhaseFlow hindep ⟨_, hcont⟩
    (htest.continuous.comp (continuous_perturbedOrbit h hS eps)) ?_
  have hasym := tendsto_uniformity_perturbedOrbit h hS hcollapse (omega := omega) (eps := eps)
  have hpair : Tendsto (fun t => (test (perturbedBoundary h c eps (circlePhaseFlow omega t)),
      test (perturbedOrbit h S hS eps t))) (cocompact ℝ) (uniformity ℂ) :=
    Filter.Tendsto.comp htest hasym
  have hatTop : (atTop : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hev := hpair (Metric.dist_mem_uniformity hε)
  filter_upwards [hatTop hev] with t ht
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at ht
  rw [Complex.dist_eq] at ht
  show ‖test (perturbedOrbit h S hS eps t)
    - test (perturbedBoundary h c eps (circlePhaseFlow omega t))‖ < ε
  rw [norm_sub_rev]
  exact ht

end

end GaloisForLFunctions
