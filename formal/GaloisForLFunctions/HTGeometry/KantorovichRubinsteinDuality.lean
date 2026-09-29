import GaloisForLFunctions.HTGeometry.CompactMomentDeterminacy
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Kantorovich–Rubinstein duality on a compact metric space

For Borel probability measures `μ, ν` on a compact metric space `X`, the first Wasserstein
distance

`W₁(μ, ν) = inf { ∫ d(x, y) dπ(x, y) : π a coupling of μ and ν }`

equals the Lipschitz dual value `sup { ∫ f dμ - ∫ f dν : Lip f ≤ 1 }`, and the infimum is attained.

The inequality `sup ≤ inf` integrates `f x - f y ≤ d(x, y)` against a coupling.  For the converse
let `N(φ) = inf { ∫ a dμ + ∫ b dν : φ(x, y) ≤ a(x) + b(y) }` on `C(X × X)`.  It is sublinear, so
the Hahn–Banach theorem extends the functional `t d ↦ -t N(-d)` on the line through the cost `d` to
a linear functional `Λ ≤ N` on `C(X × X)`.  Domination by `N` makes `Λ` positive with marginals
`μ` and `ν`; the Riesz–Markov–Kakutani theorem turns it into a coupling `π` with
`∫ d dπ = -N(-d)`.  For every feasible pair `-d ≤ a ⊕ b` the `d`-transform
`h(x) = inf_y (d(x, y) + b(y))` is `1`-Lipschitz with `-a ≤ h ≤ b`, so `-N(-d)` is at most the
Lipschitz dual value.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction CompactlySupported

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Coupling

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- `π` is a coupling of `μ` and `ν`: its two marginals are `μ` and `ν`. -/
def IsCoupling (μ ν : Measure X) (π : Measure (X × X)) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- The first Wasserstein distance `W₁(μ, ν) = inf_π ∫ d(x, y) dπ` over couplings. -/
def wassersteinOne (μ ν : Measure X) : ℝ :=
  ⨅ π : {π : Measure (X × X) // IsCoupling μ ν π}, ∫ p, dist p.1 p.2 ∂(π : Measure (X × X))

/-- The Lipschitz dual value `sup_{Lip f ≤ 1} (∫ f dμ - ∫ f dν)`. -/
def lipschitzDual (μ ν : Measure X) : ℝ :=
  ⨆ f : {f : X → ℝ // LipschitzWith 1 f}, (∫ x, (f : X → ℝ) x ∂μ - ∫ x, (f : X → ℝ) x ∂ν)

variable [CompactSpace X] [BorelSpace X] {μ ν : Measure X} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
theorem isCoupling_prod : IsCoupling μ ν (μ.prod ν) := by
  refine ⟨?_, ?_⟩ <;> simp

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure ν] in
theorem IsCoupling.isProbabilityMeasure {π : Measure (X × X)} (hπ : IsCoupling μ ν π) :
    IsProbabilityMeasure π := by
  constructor
  have h := congrArg (fun m : Measure X => m univ) hπ.1
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
    measure_univ] at h
  exact h

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] in
theorem IsCoupling.integral_fst [TopologicalSpace X] [OpensMeasurableSpace X]
    {π : Measure (X × X)} (hπ : IsCoupling μ ν π) {f : X → ℝ} (hf : Continuous f) :
    ∫ p, f p.1 ∂π = ∫ x, f x ∂μ := by
  rw [← hπ.1, integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] in
theorem IsCoupling.integral_snd [TopologicalSpace X] [OpensMeasurableSpace X]
    {π : Measure (X × X)} (hπ : IsCoupling μ ν π) {f : X → ℝ} (hf : Continuous f) :
    ∫ p, f p.2 ∂π = ∫ x, f x ∂ν := by
  rw [← hπ.2, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem integral_dist_nonneg (π : Measure (X × X)) : 0 ≤ ∫ p, dist p.1 p.2 ∂π :=
  integral_nonneg fun _ => dist_nonneg

omit [IsProbabilityMeasure ν] in
/-- Every coupling bounds every `1`-Lipschitz integral gap. -/
theorem integral_sub_le_of_isCoupling {π : Measure (X × X)} (hπ : IsCoupling μ ν π)
    {f : X → ℝ} (hf : LipschitzWith 1 f) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ ∫ p, dist p.1 p.2 ∂π := by
  haveI := hπ.isProbabilityMeasure
  have i1 : Integrable (fun p : X × X => f p.1) π :=
    integrable_of_continuous π (hf.continuous.comp continuous_fst)
  have i2 : Integrable (fun p : X × X => f p.2) π :=
    integrable_of_continuous π (hf.continuous.comp continuous_snd)
  rw [← hπ.integral_fst hf.continuous, ← hπ.integral_snd hf.continuous, ← integral_sub i1 i2]
  refine integral_mono (integrable_of_continuous
    π ((hf.continuous.comp continuous_fst).sub (hf.continuous.comp continuous_snd)))
    (integrable_of_continuous π continuous_dist) fun p => ?_
  have h := hf.dist_le_mul p.1 p.2
  rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
  exact (le_abs_self _).trans h

theorem bddAbove_lipschitzDual :
    BddAbove (range fun f : {f : X → ℝ // LipschitzWith 1 f} =>
      ∫ x, (f : X → ℝ) x ∂μ - ∫ x, (f : X → ℝ) x ∂ν) :=
  ⟨∫ p, dist p.1 p.2 ∂(μ.prod ν), by
    rintro _ ⟨f, rfl⟩
    exact integral_sub_le_of_isCoupling isCoupling_prod f.2⟩

theorem le_lipschitzDual {f : X → ℝ} (hf : LipschitzWith 1 f) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ lipschitzDual μ ν :=
  le_ciSup (f := fun f : {f : X → ℝ // LipschitzWith 1 f} =>
    ∫ x, (f : X → ℝ) x ∂μ - ∫ x, (f : X → ℝ) x ∂ν) bddAbove_lipschitzDual ⟨f, hf⟩

omit [IsProbabilityMeasure ν] in
theorem lipschitzDual_le_integral {π : Measure (X × X)} (hπ : IsCoupling μ ν π) :
    lipschitzDual μ ν ≤ ∫ p, dist p.1 p.2 ∂π := by
  haveI : Nonempty {f : X → ℝ // LipschitzWith 1 f} :=
    ⟨⟨fun _ => 0, (LipschitzWith.const 0).weaken zero_le_one⟩⟩
  exact ciSup_le fun f => integral_sub_le_of_isCoupling hπ f.2

omit [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem wassersteinOne_le_integral {π : Measure (X × X)} (hπ : IsCoupling μ ν π) :
    wassersteinOne μ ν ≤ ∫ p, dist p.1 p.2 ∂π :=
  ciInf_le (f := fun π : {π : Measure (X × X) // IsCoupling μ ν π} =>
    ∫ p, dist p.1 p.2 ∂(π : Measure (X × X)))
    ⟨0, by rintro _ ⟨π, rfl⟩; exact integral_dist_nonneg _⟩ ⟨π, hπ⟩

/-- The easy half of the duality: `sup_{Lip f ≤ 1} (∫ f dμ - ∫ f dν) ≤ W₁(μ, ν)`. -/
theorem lipschitzDual_le_wassersteinOne : lipschitzDual μ ν ≤ wassersteinOne μ ν := by
  haveI : Nonempty {π : Measure (X × X) // IsCoupling μ ν π} := ⟨⟨_, isCoupling_prod⟩⟩
  exact le_ciInf fun π => lipschitzDual_le_integral π.2

end Coupling

/-! ## The sublinear upper functional -/

section Upper

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The values `∫ a dμ + ∫ b dν` of pairs with `φ(x, y) ≤ a(x) + b(y)`. -/
def dominatingValues (φ : C(X × X, ℝ)) : Set ℝ :=
  {r | ∃ a b : C(X, ℝ), (∀ x y, φ (x, y) ≤ a x + b y) ∧ ∫ x, a x ∂μ + ∫ y, b y ∂ν = r}

/-- `N(φ) = inf { ∫ a dμ + ∫ b dν : φ ≤ a ⊕ b }`. -/
def dominatingBound (φ : C(X × X, ℝ)) : ℝ := sInf (dominatingValues μ ν φ)

variable {μ ν}

omit [IsProbabilityMeasure ν] in
theorem integral_le_of_dominated {π : Measure (X × X)} (hπ : IsCoupling μ ν π)
    {φ : C(X × X, ℝ)} {a b : C(X, ℝ)} (h : ∀ x y, φ (x, y) ≤ a x + b y) :
    ∫ p, φ p ∂π ≤ ∫ x, a x ∂μ + ∫ y, b y ∂ν := by
  haveI := hπ.isProbabilityMeasure
  have i1 : Integrable (fun p : X × X => a p.1) π :=
    integrable_of_continuous π (a.continuous.comp continuous_fst)
  have i2 : Integrable (fun p : X × X => b p.2) π :=
    integrable_of_continuous π (b.continuous.comp continuous_snd)
  rw [← hπ.integral_fst a.continuous, ← hπ.integral_snd b.continuous, ← integral_add i1 i2]
  exact integral_mono (integrable_of_continuous π φ.continuous)
    (integrable_of_continuous π ((a.continuous.comp continuous_fst).add
      (b.continuous.comp continuous_snd))) fun p => h p.1 p.2

omit [BorelSpace X] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem dominatingValues_nonempty (φ : C(X × X, ℝ)) : (dominatingValues μ ν φ).Nonempty :=
  ⟨_, ContinuousMap.const X ‖φ‖, 0, fun x y => by
    simpa using (le_abs_self _).trans (φ.norm_coe_le_norm (x, y)), rfl⟩

theorem bddBelow_dominatingValues (φ : C(X × X, ℝ)) : BddBelow (dominatingValues μ ν φ) :=
  ⟨∫ p, φ p ∂(μ.prod ν), by
    rintro _ ⟨a, b, h, rfl⟩
    exact integral_le_of_dominated isCoupling_prod h⟩

omit [IsProbabilityMeasure ν] in
theorem integral_le_dominatingBound {π : Measure (X × X)} (hπ : IsCoupling μ ν π)
    (φ : C(X × X, ℝ)) : ∫ p, φ p ∂π ≤ dominatingBound μ ν φ :=
  le_csInf (dominatingValues_nonempty φ) fun _ ⟨_, _, h, hr⟩ => hr ▸ integral_le_of_dominated hπ h

theorem dominatingBound_le {φ : C(X × X, ℝ)} {a b : C(X, ℝ)} (h : ∀ x y, φ (x, y) ≤ a x + b y) :
    dominatingBound μ ν φ ≤ ∫ x, a x ∂μ + ∫ y, b y ∂ν :=
  csInf_le (bddBelow_dominatingValues φ) ⟨a, b, h, rfl⟩

theorem dominatingBound_zero : dominatingBound μ ν 0 = 0 := by
  refine le_antisymm ?_ ?_
  · simpa using dominatingBound_le (μ := μ) (ν := ν) (φ := 0) (a := 0) (b := 0) (by simp)
  · simpa using integral_le_dominatingBound (isCoupling_prod (μ := μ) (ν := ν)) 0

theorem dominatingBound_nonpos {φ : C(X × X, ℝ)} (hφ : ∀ p, φ p ≤ 0) :
    dominatingBound μ ν φ ≤ 0 := by
  simpa using dominatingBound_le (μ := μ) (ν := ν) (a := 0) (b := 0)
    (by simpa using fun x y => hφ (x, y))

theorem dominatingBound_smul_le {c : ℝ} (hc : 0 < c) (φ : C(X × X, ℝ)) :
    dominatingBound μ ν (c • φ) ≤ c * dominatingBound μ ν φ := by
  rw [← div_le_iff₀' hc]
  refine le_csInf (dominatingValues_nonempty φ) ?_
  rintro _ ⟨a, b, h, rfl⟩
  rw [div_le_iff₀' hc]
  have h' : ∀ x y, (c • φ) (x, y) ≤ (c • a) x + (c • b) y := fun x y => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    nlinarith [h x y]
  refine (dominatingBound_le h').trans (le_of_eq ?_)
  simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
  ring

theorem dominatingBound_smul {c : ℝ} (hc : 0 < c) (φ : C(X × X, ℝ)) :
    dominatingBound μ ν (c • φ) = c * dominatingBound μ ν φ := by
  refine le_antisymm (dominatingBound_smul_le hc φ) ?_
  have h := dominatingBound_smul_le (μ := μ) (ν := ν) (inv_pos.mpr hc) (c • φ)
  rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  rwa [← le_div_iff₀' hc, div_eq_inv_mul]

theorem dominatingBound_add (φ ψ : C(X × X, ℝ)) :
    dominatingBound μ ν (φ + ψ) ≤ dominatingBound μ ν φ + dominatingBound μ ν ψ := by
  have key : ∀ r ∈ dominatingValues μ ν φ, ∀ s ∈ dominatingValues μ ν ψ,
      dominatingBound μ ν (φ + ψ) ≤ r + s := by
    rintro _ ⟨a, b, h, rfl⟩ _ ⟨a', b', h', rfl⟩
    have h'' : ∀ x y, (φ + ψ) (x, y) ≤ (a + a') x + (b + b') y := fun x y => by
      simp only [ContinuousMap.add_apply]
      linarith [h x y, h' x y]
    refine (dominatingBound_le h'').trans (le_of_eq ?_)
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_of_continuous μ a.continuous)
        (integrable_of_continuous μ a'.continuous),
      integral_add (integrable_of_continuous ν b.continuous)
        (integrable_of_continuous ν b'.continuous)]
    ring
  have h1 : ∀ s ∈ dominatingValues μ ν ψ,
      dominatingBound μ ν (φ + ψ) - s ≤ dominatingBound μ ν φ := fun s hs =>
    le_csInf (dominatingValues_nonempty φ) fun r hr => by linarith [key r hr s hs]
  have h2 : dominatingBound μ ν (φ + ψ) - dominatingBound μ ν φ ≤ dominatingBound μ ν ψ :=
    le_csInf (dominatingValues_nonempty ψ) fun s hs => by linarith [h1 s hs]
  linarith

end Upper

/-! ## The dual inequality -/

section Dual

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The cost `d(x, y)` as a continuous function on `X × X`. -/
def distCost (X : Type*) [MetricSpace X] : C(X × X, ℝ) := ⟨fun p => dist p.1 p.2, continuous_dist⟩

/-- The `d`-transform bound: `-N(-d)` is at most the Lipschitz dual value. -/
theorem neg_dominatingBound_neg_distCost_le :
    -dominatingBound μ ν (-distCost X) ≤ lipschitzDual μ ν := by
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := μ)
    rw [univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  rw [neg_le]
  refine le_csInf (dominatingValues_nonempty _) ?_
  rintro _ ⟨a, b, h, rfl⟩
  have hbdd : ∀ x, BddBelow (range fun y => dist x y + b y) := fun x =>
    ⟨-‖b‖, by
      rintro _ ⟨y, rfl⟩
      have := neg_abs_le (b y)
      have := (b.norm_coe_le_norm y)
      rw [Real.norm_eq_abs] at this
      linarith [dist_nonneg (x := x) (y := y)]⟩
  set t : X → ℝ := fun x => ⨅ y, (dist x y + b y) with ht
  have hLip : LipschitzWith 1 t := LipschitzWith.of_le_add fun x x' => by
    have : t x - dist x x' ≤ t x' := le_ciInf fun y => by
      have h1 := ciInf_le (hbdd x) y
      linarith [dist_triangle x x' y]
    linarith
  have hlow : ∀ x, -a x ≤ t x := fun x => le_ciInf fun y => by
    have := h x y
    simp only [distCost, ContinuousMap.neg_apply, ContinuousMap.coe_mk] at this
    linarith
  have hup : ∀ y, t y ≤ b y := fun y => by
    have := ciInf_le (hbdd y) y
    simpa using this
  have hdual := le_lipschitzDual (μ := μ) (ν := ν) hLip
  have hia : ∫ x, -a x ∂μ ≤ ∫ x, t x ∂μ :=
    integral_mono (integrable_of_continuous μ a.continuous.neg)
      (integrable_of_continuous μ hLip.continuous) hlow
  have hib : ∫ y, t y ∂ν ≤ ∫ y, b y ∂ν :=
    integral_mono (integrable_of_continuous ν hLip.continuous)
      (integrable_of_continuous ν b.continuous) hup
  rw [integral_neg] at hia
  linarith

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem dominatingBound_neg_distCost_add :
    ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      0 ≤ dominatingBound μ ν (distCost X) + dominatingBound μ ν (-distCost X) := by
  intro _ _
  have h := dominatingBound_add (μ := μ) (ν := ν) (distCost X) (-distCost X)
  rw [add_neg_cancel, dominatingBound_zero] at h
  exact h

/-- **Hahn–Banach coupling.**  There is a coupling `π` of `μ` and `ν` with
`∫ d dπ ≤ sup_{Lip f ≤ 1} (∫ f dμ - ∫ f dν)`. -/
theorem exists_isCoupling_integral_le_lipschitzDual :
    ∃ π : Measure (X × X), IsCoupling μ ν π ∧ ∫ p, dist p.1 p.2 ∂π ≤ lipschitzDual μ ν := by
  set N := dominatingBound μ ν with hN
  set D := distCost X with hD
  set y : ℝ := -N (-D) with hy
  have hH : ∀ c : ℝ, c • D = 0 → c • y = 0 := by
    intro c hc
    rcases smul_eq_zero.mp hc with h | h
    · simp [h]
    · simp [hy, h, hN, dominatingBound_zero]
  set ℓ := LinearPMap.mkSpanSingleton' (σ := RingHom.id ℝ) D y hH with hℓ
  have hℓapp : ∀ (c : ℝ) (h : c • D ∈ ℓ.domain), ℓ ⟨c • D, h⟩ = c * y := fun c h =>
    LinearPMap.mkSpanSingleton'_apply (σ := RingHom.id ℝ) D y hH c h
  have hℓN : ∀ z : ℓ.domain, ℓ z ≤ N z := by
    rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [hℓapp]
    show c * y ≤ N (c • D)
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have : c • D = (-c) • (-D) := by rw [neg_smul_neg]
      rw [this, hN, dominatingBound_smul (neg_pos.mpr hc), hy]
      ring_nf
      exact le_rfl
    · simp [hN, dominatingBound_zero]
    · rw [hN, dominatingBound_smul hc, hy]
      have := dominatingBound_neg_distCost_add (μ := μ) (ν := ν)
      nlinarith
  obtain ⟨g, hgℓ, hgN⟩ := exists_extension_of_le_sublinear ℓ N
    (fun c hc φ => dominatingBound_smul hc φ) dominatingBound_add hℓN
  have hgD : g D = y := by
    have hmem : D ∈ ℓ.domain := Submodule.mem_span_singleton_self D
    rw [show D = ((⟨D, hmem⟩ : ℓ.domain) : C(X × X, ℝ)) from rfl, hgℓ]
    exact LinearPMap.mkSpanSingleton'_apply_self (σ := RingHom.id ℝ) D y hH hmem
  have hpos : ∀ φ : C(X × X, ℝ), 0 ≤ φ → 0 ≤ g φ := by
    intro φ hφ
    have h1 := hgN (-φ)
    have h2 : N (-φ) ≤ 0 := dominatingBound_nonpos fun p => by
      simpa using hφ p
    rw [map_neg] at h1
    linarith
  have hfst : ∀ a : C(X, ℝ), g (a.comp ContinuousMap.fst) = ∫ x, a x ∂μ := by
    intro a
    have h1 := (hgN (a.comp ContinuousMap.fst)).trans
      (dominatingBound_le (a := a) (b := 0) fun x y => by simp)
    have h2 := (hgN (-(a.comp ContinuousMap.fst))).trans
      (dominatingBound_le (a := -a) (b := 0) fun x y => by simp)
    rw [map_neg] at h2
    simp only [ContinuousMap.zero_apply, integral_zero, add_zero, ContinuousMap.neg_apply,
      integral_neg] at h1 h2
    linarith
  have hsnd : ∀ b : C(X, ℝ), g (b.comp ContinuousMap.snd) = ∫ y, b y ∂ν := by
    intro b
    have h1 := (hgN (b.comp ContinuousMap.snd)).trans
      (dominatingBound_le (a := 0) (b := b) fun x y => by simp)
    have h2 := (hgN (-(b.comp ContinuousMap.snd))).trans
      (dominatingBound_le (a := 0) (b := -b) fun x y => by simp)
    rw [map_neg] at h2
    simp only [ContinuousMap.zero_apply, integral_zero, zero_add, ContinuousMap.neg_apply,
      integral_neg] at h1 h2
    linarith
  let toC : C_c(X × X, ℝ) →ₗ[ℝ] C(X × X, ℝ) :=
    { toFun := fun f => (f : C(X × X, ℝ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Λ : C_c(X × X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (g ∘ₗ toC) fun f hf =>
    hpos (f : C(X × X, ℝ)) hf
  set π := RealRMK.rieszMeasure Λ with hπdef
  have hint : ∀ φ : C(X × X, ℝ), ∫ p, φ p ∂π = g φ := fun φ =>
    RealRMK.integral_rieszMeasure Λ (CompactlySupportedContinuousMap.continuousMapEquiv φ)
  have hmarg : ∀ (m : Measure X) [IsFiniteMeasure m] (e : C(X × X, X)), Measurable e →
      (∀ f : C(X, ℝ), g (f.comp e) = ∫ x, f x ∂m) → π.map e = m := by
    intro m _ e hem he
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hem.aemeasurable f.continuous.aestronglyMeasurable]
    exact (hint (f.toContinuousMap.comp e)).trans (he f.toContinuousMap)
  refine ⟨π, ⟨hmarg μ ContinuousMap.fst measurable_fst hfst,
    hmarg ν ContinuousMap.snd measurable_snd hsnd⟩, ?_⟩
  have hcost : ∫ p, dist p.1 p.2 ∂π = y := (hint D).trans hgD
  rw [hcost, hy]
  exact neg_dominatingBound_neg_distCost_le

/-- **Kantorovich–Rubinstein duality.**  `W₁(μ, ν) = sup_{Lip f ≤ 1} (∫ f dμ - ∫ f dν)`. -/
theorem wassersteinOne_eq_lipschitzDual : wassersteinOne μ ν = lipschitzDual μ ν := by
  obtain ⟨π, hπ, hle⟩ := exists_isCoupling_integral_le_lipschitzDual (μ := μ) (ν := ν)
  exact le_antisymm ((wassersteinOne_le_integral hπ).trans hle) lipschitzDual_le_wassersteinOne

/-- The infimum defining `W₁(μ, ν)` is attained. -/
theorem exists_isCoupling_integral_eq_wassersteinOne :
    ∃ π : Measure (X × X), IsCoupling μ ν π ∧ ∫ p, dist p.1 p.2 ∂π = wassersteinOne μ ν := by
  obtain ⟨π, hπ, hle⟩ := exists_isCoupling_integral_le_lipschitzDual (μ := μ) (ν := ν)
  refine ⟨π, hπ, le_antisymm ?_ (wassersteinOne_le_integral hπ)⟩
  rw [wassersteinOne_eq_lipschitzDual]
  exact hle

/-- An `L`-Lipschitz integral gap is at most `L W₁(μ, ν)`. -/
theorem abs_integral_sub_le_mul_wassersteinOne {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ L * wassersteinOne μ ν := by
  obtain ⟨π, hπ, hπW⟩ := exists_isCoupling_integral_eq_wassersteinOne (μ := μ) (ν := ν)
  haveI := hπ.isProbabilityMeasure
  have i1 : Integrable (fun p : X × X => f p.1) π :=
    integrable_of_continuous π (hf.continuous.comp continuous_fst)
  have i2 : Integrable (fun p : X × X => f p.2) π :=
    integrable_of_continuous π (hf.continuous.comp continuous_snd)
  rw [← hπ.integral_fst hf.continuous, ← hπ.integral_snd hf.continuous, ← integral_sub i1 i2,
    ← hπW, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs
    ((integrable_of_continuous π continuous_dist).const_mul _) fun p => ?_)
  have h := hf.dist_le_mul p.1 p.2
  rwa [Real.dist_eq] at h

end Dual

end GaloisForLFunctions.HTGeometry
