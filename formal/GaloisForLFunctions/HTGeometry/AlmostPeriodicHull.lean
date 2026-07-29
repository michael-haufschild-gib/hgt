import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bohr almost-periodic functions and their translation hull

Mathlib has no theory of (Bohr / uniformly) almost-periodic functions.  This file builds it from the
ground up, working in the complete metric space `ℝ →ᵇ ℂ` of bounded continuous functions with the
supremum distance — the setting in which the card's finite-phase theorem (§5, eq. 8–9) requires a
*compact* translation hull.

A bounded continuous `f` is **Bohr almost periodic** when its orbit under real translation is
relatively compact for the sup metric (Bochner's criterion).  Its **hull** is the closure of that
orbit; almost periodicity makes the hull a compact metric space carrying a translation action.  This
is the object whose Pontryagin dual is the Bohr frequency group in the finite-phase argument.

This file establishes the foundational layer: translation is an isometric additive action, the hull
is compact, contains `f`, is closed, and is translation invariant.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open BoundedContinuousFunction Metric

/-- Translation of a bounded continuous function on `ℝ`: `(bcfTranslate t f) s = f (s + t)`. -/
noncomputable def bcfTranslate (t : ℝ) (f : ℝ →ᵇ ℂ) : ℝ →ᵇ ℂ :=
  f.compContinuous ⟨fun s => s + t, by fun_prop⟩

@[simp]
theorem bcfTranslate_apply (t : ℝ) (f : ℝ →ᵇ ℂ) (s : ℝ) :
    bcfTranslate t f s = f (s + t) := rfl

@[simp]
theorem bcfTranslate_zero (f : ℝ →ᵇ ℂ) : bcfTranslate 0 f = f := by
  ext s; simp

/-- Translation is an additive action: `bcfTranslate s (bcfTranslate t f) = bcfTranslate (s+t) f`. -/
theorem bcfTranslate_bcfTranslate (s t : ℝ) (f : ℝ →ᵇ ℂ) :
    bcfTranslate s (bcfTranslate t f) = bcfTranslate (s + t) f := by
  ext u; simp [add_assoc]

/-- Translation preserves the supremum distance: it is an isometry of `ℝ →ᵇ ℂ`. -/
theorem dist_bcfTranslate (t : ℝ) (f g : ℝ →ᵇ ℂ) :
    dist (bcfTranslate t f) (bcfTranslate t g) = dist f g := by
  apply le_antisymm
  · refine (dist_le dist_nonneg).2 (fun s => ?_)
    simpa using dist_coe_le_dist (s + t)
  · refine (dist_le dist_nonneg).2 (fun s => ?_)
    have := dist_coe_le_dist (f := bcfTranslate t f) (g := bcfTranslate t g) (s - t)
    simpa using this

/-- The isometry packaging of translation. -/
theorem isometry_bcfTranslate (t : ℝ) : Isometry (bcfTranslate t) :=
  Isometry.of_dist_eq (fun f g => dist_bcfTranslate t f g)

/-- The translation orbit of `f`. -/
noncomputable def bcfOrbit (f : ℝ →ᵇ ℂ) : Set (ℝ →ᵇ ℂ) :=
  Set.range (fun t : ℝ => bcfTranslate t f)

/-- **Bohr almost periodicity** (Bochner's criterion): the translation orbit is relatively compact
for the supremum metric. -/
def IsBohrAP (f : ℝ →ᵇ ℂ) : Prop :=
  IsCompact (closure (bcfOrbit f))

/-- The **translation hull** of `f`: the closure of its translation orbit. -/
noncomputable def bohrHull (f : ℝ →ᵇ ℂ) : Set (ℝ →ᵇ ℂ) :=
  closure (bcfOrbit f)

/-- The hull of an almost-periodic function is compact. -/
theorem bohrHull_isCompact {f : ℝ →ᵇ ℂ} (hf : IsBohrAP f) : IsCompact (bohrHull f) := hf

/-- The hull is closed. -/
theorem isClosed_bohrHull (f : ℝ →ᵇ ℂ) : IsClosed (bohrHull f) := isClosed_closure

/-- `f` itself lies in its hull (it is the `t = 0` translate). -/
theorem self_mem_bohrHull (f : ℝ →ᵇ ℂ) : f ∈ bohrHull f :=
  subset_closure ⟨0, by simp⟩

/-- Every orbit point lies in the hull. -/
theorem bcfTranslate_mem_bohrHull (t : ℝ) (f : ℝ →ᵇ ℂ) : bcfTranslate t f ∈ bohrHull f :=
  subset_closure ⟨t, rfl⟩

/-- The orbit is translation invariant: translating an orbit point stays in the orbit. -/
theorem bcfTranslate_bcfOrbit_subset (t : ℝ) (f : ℝ →ᵇ ℂ) :
    bcfTranslate t '' bcfOrbit f ⊆ bcfOrbit f := by
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨s + t, by rw [bcfTranslate_bcfTranslate, add_comm s t]⟩

/-- The translation orbit is preserved exactly by every real translation. -/
theorem bcfTranslate_bcfOrbit (t : ℝ) (f : ℝ →ᵇ ℂ) :
    bcfTranslate t '' bcfOrbit f = bcfOrbit f := by
  apply Set.Subset.antisymm (bcfTranslate_bcfOrbit_subset t f)
  intro g hg
  refine ⟨bcfTranslate (-t) g, ?_, ?_⟩
  · exact bcfTranslate_bcfOrbit_subset (-t) f ⟨g, hg, rfl⟩
  · rw [bcfTranslate_bcfTranslate]
    simp

/-- The hull is translation invariant: translation maps the hull into itself.  This uses continuity
(isometry) of translation together with invariance of the orbit. -/
theorem bcfTranslate_bohrHull_subset (t : ℝ) (f : ℝ →ᵇ ℂ) :
    bcfTranslate t '' bohrHull f ⊆ bohrHull f := by
  have hcont : Continuous (bcfTranslate t) := (isometry_bcfTranslate t).continuous
  calc bcfTranslate t '' bohrHull f
      = bcfTranslate t '' closure (bcfOrbit f) := rfl
    _ ⊆ closure (bcfTranslate t '' bcfOrbit f) := image_closure_subset_closure_image hcont
    _ ⊆ closure (bcfOrbit f) := closure_mono (bcfTranslate_bcfOrbit_subset t f)

/-- The translation hull is preserved exactly by every real translation.  Thus the one-sided
invariance above is an actual additive group action on the hull. -/
theorem bcfTranslate_bohrHull (t : ℝ) (f : ℝ →ᵇ ℂ) :
    bcfTranslate t '' bohrHull f = bohrHull f := by
  apply Set.Subset.antisymm (bcfTranslate_bohrHull_subset t f)
  intro g hg
  refine ⟨bcfTranslate (-t) g, ?_, ?_⟩
  · exact bcfTranslate_bohrHull_subset (-t) f ⟨g, hg, rfl⟩
  · rw [bcfTranslate_bcfTranslate]
    simp

/-- **Bohr recurrence (arbitrarily large approximate return times).**  If `f` is Bohr almost
periodic, then for every `ε > 0` and every bound `N` there is a real time `t ≥ N` whose translate of
`f` is within `ε` of `f`.  This is the mechanism (Bochner's compactness argument) that supplies the
diagonal return times `T_l → +∞` with `f(· + T_l) → f` used in the recurrence-collapse step of the
finite-phase theorem (§5, eq. 28). -/
theorem bohrAP_exists_large_return {f : ℝ →ᵇ ℂ} (hf : IsBohrAP f)
    {ε : ℝ} (hε : 0 < ε) (N : ℝ) :
    ∃ t : ℝ, N ≤ t ∧ dist (bcfTranslate t f) f < ε := by
  -- The integer-time orbit lies in the compact hull, so it has a convergent (Cauchy) subsequence.
  obtain ⟨g, _, φ, hφ, hconv⟩ :=
    (bohrHull_isCompact hf).tendsto_subseq (fun n : ℕ => bcfTranslate_mem_bohrHull (n : ℝ) f)
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨K, hK⟩ := hcauchy ε hε
  -- pick a gap of length at least `N`
  set m : ℕ := max 1 ⌈N⌉₊ with hm
  have hgap : φ K + m ≤ φ (K + m) := by
    have step : ∀ i, φ K + i ≤ φ (K + i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
          have hlt : φ (K + i) < φ (K + i + 1) := hφ (by omega)
          have heq : K + (i + 1) = K + i + 1 := by omega
          rw [heq]
          omega
    exact step m
  have hmN : N ≤ (m : ℝ) := by
    have h1 : (⌈N⌉₊ : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast le_max_right 1 ⌈N⌉₊
    exact (Nat.le_ceil N).trans h1
  refine ⟨(φ (K + m) : ℝ) - (φ K : ℝ), ?_, ?_⟩
  · have : (m : ℝ) ≤ (φ (K + m) : ℝ) - (φ K : ℝ) := by
      have : (φ K : ℝ) + (m : ℝ) ≤ (φ (K + m) : ℝ) := by exact_mod_cast hgap
      linarith
    linarith
  · have hiso : dist (bcfTranslate ((φ (K + m) : ℝ) - (φ K : ℝ)) f) f
        = dist (bcfTranslate ((φ (K + m) : ℕ) : ℝ) f) (bcfTranslate ((φ K : ℕ) : ℝ) f) := by
      rw [← dist_bcfTranslate ((φ K : ℕ) : ℝ), bcfTranslate_bcfTranslate]
      congr 2
      ring
    rw [hiso]
    exact hK (K + m) (by omega) K (le_refl K)

/-- **Bohr return sequence.**  Every Bohr almost-periodic `f` admits return times `T_l → +∞` along
which its translates converge to `f` uniformly (`f(· + T_l) → f` in the sup metric).  This is exactly
the diagonal return sequence (eq. 28) feeding `recurrence_collapse_to_autonomous`. -/
theorem bohrAP_return_seq {f : ℝ →ᵇ ℂ} (hf : IsBohrAP f) :
    ∃ T : ℕ → ℝ, Filter.Tendsto T Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun l => bcfTranslate (T l) f) Filter.atTop (nhds f) := by
  choose T hT1 hT2 using
    fun l : ℕ => bohrAP_exists_large_return hf (by positivity : (0 : ℝ) < 1 / (l + 1)) (l : ℝ)
  refine ⟨T, Filter.tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun l => dist_nonneg) (fun l => (hT2 l).le) ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Point-value return (eq. 28).**  For a Bohr almost-periodic `f` and any base point `s`, there
are return times `T_l → +∞` along which the translated values converge, `f(s + T_l) → f(s)`.  This is
the concrete convergence consumed by the recurrence-collapse step at each sample point. -/
theorem bohrAP_pointValue_return {f : ℝ →ᵇ ℂ} (hf : IsBohrAP f) (s : ℝ) :
    ∃ T : ℕ → ℝ, Filter.Tendsto T Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun l => f (s + T l)) Filter.atTop (nhds (f s)) := by
  obtain ⟨T, hT, hconv⟩ := bohrAP_return_seq hf
  refine ⟨T, hT, ?_⟩
  have hcont : Continuous (fun g : ℝ →ᵇ ℂ => g s) :=
    continuous_eval_const s
  have hev := (hcont.tendsto f).comp hconv
  simpa only [Function.comp_def, bcfTranslate_apply] using hev

end GaloisForLFunctions
