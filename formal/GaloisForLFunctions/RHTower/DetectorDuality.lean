import Mathlib.Analysis.InnerProductSpace.Dual
import GaloisForLFunctions.RHTower.VanishingCostRCLike
import GaloisForLFunctions.RHTower.DistancePositivity

/-!
# The distance to a span is exactly a detector problem

`VanishingCostRCLike` computes the distance from a vector to the hyperplane annihilated by a single
functional, and the Nyman--Beurling lane uses it as a *lower* bound: a vector orthogonal to every
generator but not to the target certifies a positive distance.  This file shows that the method loses
nothing.

For a family `S` in a complete inner product space and a target `x`,

`dist(x, span S) = ‖P_{(span S)ᗮ} x‖ = max { ‖⟪w,x⟫‖ : w ⟂ S, ‖w‖ ≤ 1 }`,

the maximum being attained by the normalised component of `x` orthogonal to the span.  Hence

* `infDist_span_eq_norm_starProjection_orthogonal` — the distance is the norm of the orthogonal
  component;
* `exists_detector_norm_inner_eq_infDist_span` — some unit vector orthogonal to the family pairs with
  the target *exactly* at the distance;
* `infDist_span_eq_zero_iff`, `mem_topologicalClosure_span_iff` — approximability is equivalent to the
  nonexistence of a separating detector, and `topologicalClosure_span_eq_top_iff` — totality is the
  nonexistence of any nonzero annihilator;
* `forall_dual_eq_zero_iff_forall_inner_eq_zero`, `mem_topologicalClosure_span_iff_forall_dual` — the
  Riesz bridge to the functional form, which makes the Hahn--Banach criteria of `DenseSpanDuality` and
  `HTGeometry.DenseOfVanishingDual` sharp over a complete inner product space: there the vanishing-dual
  condition is necessary as well as sufficient.

For the Báez-Duarte lane this converts the approximation problem into a rigidity problem about the
orthogonal complement of the generators:

* `bdDist_eq_norm_starProjection` — every Báez-Duarte distance is the norm of a projection;
* `riemannHypothesis_of_forall_orthogonal_bdGen` — **if every element of the carrier orthogonal to all
  generators is orthogonal to `1/u`, the Riemann hypothesis holds**;
* `riemannHypothesis_of_detector_bound` — the quantitative form: if the pairing of unit annihilators of
  the first `N` generators with the target can be made uniformly small, the Riemann hypothesis holds.

`inner_bdDetector_bdGen` computes `⟪bdDetector (1−ρ), bdGen θ⟫ = −(θ^ρ − θ)·ζ(ρ)/ρ` for `½ < Re ρ < 1`, so
each zero of `ζ` in that strip produces an annihilator separating the target from the whole family.
Duality turns the criterion around: the target is approximable precisely when *no* annihilator separates,
so the lower-bound method of `BaezDuarteL2Carrier` is not a weaker substitute for the truth — it is the
truth, and what remains is to exclude separating annihilators.
-/

open MeasureTheory Set Complex Metric Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

section General

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A vector is orthogonal to the span of a set iff it is orthogonal to every member of the set. -/
theorem mem_orthogonal_span_iff (S : Set H) (w : H) :
    w ∈ (Submodule.span 𝕜 S)ᗮ ↔ ∀ s ∈ S, inner 𝕜 w s = 0 := by
  rw [Submodule.mem_orthogonal']
  refine ⟨fun h s hs => h s (Submodule.subset_span hs), fun h u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add a b _ _ iha ihb => rw [inner_add_right, iha, ihb, add_zero]
  | smul c a _ iha => rw [inner_smul_right, iha, mul_zero]

omit [CompleteSpace H] in
/-- **The detector lower bound, for a whole family.**  A vector orthogonal to every member of the family
bounds the distance from the target to the span from below. -/
theorem norm_inner_le_norm_mul_infDist_span (S : Set H) (x w : H)
    (hw : ∀ s ∈ S, inner 𝕜 w s = 0) :
    ‖inner 𝕜 w x‖ ≤ ‖w‖ * Metric.infDist x (Submodule.span 𝕜 S : Set H) := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
    have hwperp : w ∈ (Submodule.span 𝕜 S)ᗮ := (mem_orthogonal_span_iff S w).2 hw
    rw [mul_comm, ← div_le_iff₀ hwpos]
    refine (Metric.le_infDist ⟨0, Submodule.zero_mem _⟩).2 ?_
    intro g hg
    rw [dist_eq_norm]
    exact dist_innerKer_ge w x hne
      ((Submodule.mem_orthogonal' _ _).1 hwperp g (SetLike.mem_coe.1 hg))

/-- The component of `x` orthogonal to a subspace pairs with `x` at its own squared norm. -/
theorem inner_starProjection_orthogonal_self (K : Submodule 𝕜 H) (x : H) :
    inner 𝕜 (Kᗮ.starProjection x) x = ((‖Kᗮ.starProjection x‖ ^ (2 : ℕ) : ℝ) : 𝕜) := by
  have hPmem : Kᗮ.starProjection x ∈ Kᗮ := Submodule.starProjection_apply_mem _ x
  have hsub : x - Kᗮ.starProjection x ∈ Kᗮᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hz : inner 𝕜 (Kᗮ.starProjection x) (x - Kᗮ.starProjection x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hPmem hsub
  have hsplit : inner 𝕜 (Kᗮ.starProjection x) x
      = inner 𝕜 (Kᗮ.starProjection x) (Kᗮ.starProjection x)
        + inner 𝕜 (Kᗮ.starProjection x) (x - Kᗮ.starProjection x) := by
    rw [inner_sub_right]; ring
  rw [hsplit, hz, add_zero, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- **The duality law.**  The distance from a vector to the span of a family is the norm of its component
orthogonal to that span. -/
theorem infDist_span_eq_norm_starProjection_orthogonal (S : Set H) (x : H) :
    Metric.infDist x (Submodule.span 𝕜 S : Set H)
      = ‖(Submodule.span 𝕜 S)ᗮ.starProjection x‖ := by
  set K := Submodule.span 𝕜 S with hKdef
  set P := Kᗮ.starProjection x with hPdef
  have hPmem : P ∈ Kᗮ := Submodule.starProjection_apply_mem _ x
  have hsub : x - P ∈ Kᗮᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hclos : x - P ∈ K.topologicalClosure := by
    rwa [Submodule.orthogonal_orthogonal_eq_closure] at hsub
  refine le_antisymm ?_ ?_
  · have h1 : Metric.infDist x (K.topologicalClosure : Set H) ≤ ‖P‖ := by
      have h := Metric.infDist_le_dist_of_mem (x := x) (SetLike.mem_coe.2 hclos)
      rwa [dist_eq_norm, sub_sub_cancel] at h
    rwa [Submodule.topologicalClosure_coe, Metric.infDist_closure] at h1
  · rcases eq_or_ne P 0 with h0 | hne
    · rw [h0, norm_zero]
      exact Metric.infDist_nonneg
    · have hppos : 0 < ‖P‖ := norm_pos_iff.mpr hne
      have hbound := norm_inner_le_norm_mul_infDist_span S x P
        ((mem_orthogonal_span_iff S P).1 hPmem)
      rw [inner_starProjection_orthogonal_self K x, RCLike.norm_ofReal,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖P‖ ^ (2 : ℕ)), sq] at hbound
      exact le_of_mul_le_mul_left hbound hppos

/-- **The bound is attained.**  Some vector orthogonal to the family, of norm at most one, pairs with the
target exactly at the distance: the detector method is exact. -/
theorem exists_detector_norm_inner_eq_infDist_span (S : Set H) (x : H) :
    ∃ w : H, (∀ s ∈ S, inner 𝕜 w s = 0) ∧ ‖w‖ ≤ 1 ∧
      ‖inner 𝕜 w x‖ = Metric.infDist x (Submodule.span 𝕜 S : Set H) := by
  set K := Submodule.span 𝕜 S with hKdef
  set P := Kᗮ.starProjection x with hPdef
  have hPmem : P ∈ Kᗮ := Submodule.starProjection_apply_mem _ x
  have hperp : ∀ s ∈ S, inner 𝕜 P s = 0 := (mem_orthogonal_span_iff S P).1 hPmem
  have hdual : Metric.infDist x (K : Set H) = ‖P‖ :=
    infDist_span_eq_norm_starProjection_orthogonal S x
  rcases eq_or_ne P 0 with h0 | hne
  · refine ⟨0, by simp, by simp, ?_⟩
    rw [hdual, h0, norm_zero, inner_zero_left, norm_zero]
  · have hppos : 0 < ‖P‖ := norm_pos_iff.mpr hne
    have hcne : ((‖P‖⁻¹ : ℝ) : 𝕜) ≠ 0 := by
      simp only [ne_eq, RCLike.ofReal_eq_zero, inv_eq_zero]
      exact ne_of_gt hppos
    refine ⟨((‖P‖⁻¹ : ℝ) : 𝕜) • P, ?_, ?_, ?_⟩
    · intro s hs
      rw [inner_smul_left, hperp s hs, mul_zero]
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity : (0 : ℝ) < ‖P‖⁻¹),
        inv_mul_cancel₀ (ne_of_gt hppos)]
    · rw [inner_smul_left, inner_starProjection_orthogonal_self K x, RCLike.conj_ofReal,
        norm_mul, RCLike.norm_ofReal, RCLike.norm_ofReal,
        abs_of_pos (by positivity : (0 : ℝ) < ‖P‖⁻¹),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖P‖ ^ (2 : ℕ)), hdual, sq, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hppos), one_mul]

/-- **Approximability is the nonexistence of a detector.** -/
theorem infDist_span_eq_zero_iff (S : Set H) (x : H) :
    Metric.infDist x (Submodule.span 𝕜 S : Set H) = 0
      ↔ ∀ w : H, (∀ s ∈ S, inner 𝕜 w s = 0) → inner 𝕜 w x = 0 := by
  refine ⟨fun h w hw => ?_, fun h => ?_⟩
  · have hb := norm_inner_le_norm_mul_infDist_span S x w hw
    rw [h, mul_zero] at hb
    exact norm_eq_zero.1 (le_antisymm hb (norm_nonneg _))
  · obtain ⟨w, hw, -, heq⟩ := exists_detector_norm_inner_eq_infDist_span (𝕜 := 𝕜) S x
    rw [← heq, h w hw, norm_zero]

/-- **Membership in a topological closure, dually.**  A vector lies in the closure of a subspace iff every
vector orthogonal to the subspace is orthogonal to it. -/
theorem mem_topologicalClosure_iff (K : Submodule 𝕜 H) (x : H) :
    x ∈ K.topologicalClosure ↔ ∀ w ∈ Kᗮ, inner 𝕜 w x = 0 := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]

/-- **Density, dually.**  A subspace is dense iff no nonzero vector is orthogonal to it. -/
theorem topologicalClosure_eq_top_iff (K : Submodule 𝕜 H) :
    K.topologicalClosure = ⊤ ↔ ∀ w ∈ Kᗮ, w = 0 := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  refine ⟨fun h w hw => ?_, fun h => ?_⟩
  · have hmem : w ∈ Kᗮᗮ := h ▸ Submodule.mem_top
    exact inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hw hmem)
  · have hbot : Kᗮ = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      exact (Submodule.mem_bot 𝕜).2 (h w hw)
    rw [hbot, Submodule.bot_orthogonal_eq_top]

/-- **Membership in the closed span, dually.**  A vector lies in the closure of the span iff every vector
orthogonal to the family is orthogonal to it. -/
theorem mem_topologicalClosure_span_iff (S : Set H) (x : H) :
    x ∈ (Submodule.span 𝕜 S).topologicalClosure
      ↔ ∀ w : H, (∀ s ∈ S, inner 𝕜 w s = 0) → inner 𝕜 w x = 0 := by
  rw [mem_topologicalClosure_iff]
  exact ⟨fun h w hw => h w ((mem_orthogonal_span_iff S w).2 hw),
    fun h w hw => h w ((mem_orthogonal_span_iff S w).1 hw)⟩

/-- **Totality, dually.**  The span of a family is dense iff no nonzero vector is orthogonal to every
member of the family. -/
theorem topologicalClosure_span_eq_top_iff (S : Set H) :
    (Submodule.span 𝕜 S).topologicalClosure = ⊤
      ↔ ∀ w : H, (∀ s ∈ S, inner 𝕜 w s = 0) → w = 0 := by
  rw [topologicalClosure_eq_top_iff]
  exact ⟨fun h w hw => h w ((mem_orthogonal_span_iff S w).2 hw),
    fun h w hw => h w ((mem_orthogonal_span_iff S w).1 hw)⟩

/-- **The Riesz bridge.**  Annihilation by continuous functionals and annihilation by vectors are the same
condition: every functional is an inner product against a vector. -/
theorem forall_dual_eq_zero_iff_forall_inner_eq_zero {I : Type*} (v : I → H) (x : H) :
    (∀ L : H →L[𝕜] 𝕜, (∀ i, L (v i) = 0) → L x = 0)
      ↔ ∀ w : H, (∀ i, inner 𝕜 w (v i) = 0) → inner 𝕜 w x = 0 := by
  refine ⟨fun h w hw => h (innerSL 𝕜 w) hw, fun h L hL => ?_⟩
  have hrep : ∀ y : H, inner 𝕜 ((InnerProductSpace.toDual 𝕜 H).symm L) y = L y :=
    fun y => InnerProductSpace.toDual_symm_apply
  rw [← hrep x]
  exact h _ (fun i => (hrep (v i)).trans (hL i))

/-- **The Hahn--Banach density criterion is sharp in a Hilbert space.**  `DenseSpanDuality` proves the
sufficiency of the vanishing-dual condition for an arbitrary normed space; over a complete inner product
space it is also necessary. -/
theorem mem_topologicalClosure_span_iff_forall_dual {I : Type*} (v : I → H) (x : H) :
    x ∈ (Submodule.span 𝕜 (Set.range v)).topologicalClosure
      ↔ ∀ L : H →L[𝕜] 𝕜, (∀ i, L (v i) = 0) → L x = 0 := by
  rw [forall_dual_eq_zero_iff_forall_inner_eq_zero, mem_topologicalClosure_span_iff]
  simp only [Set.forall_mem_range]

/-- The range form of the vanishing criterion, as an indexed family. -/
theorem infDist_range_span_eq_zero_iff {I : Type*} (v : I → H) (x : H) :
    Metric.infDist x (Submodule.span 𝕜 (Set.range v) : Set H) = 0
      ↔ ∀ w : H, (∀ i, inner 𝕜 w (v i) = 0) → inner 𝕜 w x = 0 := by
  rw [infDist_span_eq_zero_iff]
  simp only [Set.forall_mem_range]

/-- The range form of attainment, as an indexed family. -/
theorem exists_detector_norm_inner_eq_infDist_range {I : Type*} (v : I → H) (x : H) :
    ∃ w : H, (∀ i, inner 𝕜 w (v i) = 0) ∧ ‖w‖ ≤ 1 ∧
      ‖inner 𝕜 w x‖ = Metric.infDist x (Submodule.span 𝕜 (Set.range v) : Set H) := by
  obtain ⟨w, hw, hnorm, heq⟩ := exists_detector_norm_inner_eq_infDist_span (𝕜 := 𝕜) (Set.range v) x
  exact ⟨w, fun i => hw (v i) ⟨i, rfl⟩, hnorm, heq⟩

/-- **The exact mass split.**  The squared distance to the span and the squared norm of the component in
the closed span `Kᗮᗮ` add up to the squared norm of the target. -/
theorem infDist_span_sq_add_norm_sq_starProjection (S : Set H) (x : H) :
    Metric.infDist x (Submodule.span 𝕜 S : Set H) ^ (2 : ℕ)
      + ‖(Submodule.span 𝕜 S)ᗮᗮ.starProjection x‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) := by
  rw [infDist_span_eq_norm_starProjection_orthogonal]
  exact (Submodule.norm_sq_eq_add_norm_sq_starProjection x (Submodule.span 𝕜 S)ᗮ).symm

end General

/-! ## The Báez-Duarte lane -/

/-- **Every Báez-Duarte distance is the norm of a projection.**  `d(θ)` is the norm of the component of
`1_{(0,1]}` orthogonal to the span of the generators. -/
theorem bdDist_eq_norm_starProjection {I : Type*} (θ : I → ℝ) :
    bdDist θ
      = ‖(Submodule.span ℂ (Set.range fun i : I => bdGen (θ i)))ᗮ.starProjection bdTarget‖ :=
  infDist_span_eq_norm_starProjection_orthogonal _ _

/-- **The exact explained-mass identity.**  The target is a unit vector, so the squared Báez-Duarte
distance is exactly the mass of `1/u` that the generators fail to explain. -/
theorem bdDist_sq_add_explained_mass {I : Type*} (θ : I → ℝ) :
    bdDist θ ^ (2 : ℕ)
      + ‖(Submodule.span ℂ (Set.range fun i : I => bdGen (θ i)))ᗮᗮ.starProjection bdTarget‖ ^ (2 : ℕ)
        = 1 := by
  have h := infDist_span_sq_add_norm_sq_starProjection (𝕜 := ℂ)
    (Set.range fun i : I => bdGen (θ i)) bdTarget
  rwa [norm_bdTarget, one_pow] at h

/-- **The best detector realises the Báez-Duarte distance.**  There is a carrier element of norm at most
one, orthogonal to every generator, whose pairing with the target is exactly the distance. -/
theorem exists_bdDetector_norm_inner_eq_bdDist {I : Type*} (θ : I → ℝ) :
    ∃ w : BDCarrier, (∀ i, inner ℂ w (bdGen (θ i)) = 0) ∧ ‖w‖ ≤ 1 ∧
      ‖inner ℂ w bdTarget‖ = bdDist θ :=
  exists_detector_norm_inner_eq_infDist_range _ _

/-- **The distance vanishes exactly when no detector separates the target from the generators.** -/
theorem bdDist_eq_zero_iff {I : Type*} (θ : I → ℝ) :
    bdDist θ = 0
      ↔ ∀ w : BDCarrier, (∀ i, inner ℂ w (bdGen (θ i)) = 0) → inner ℂ w bdTarget = 0 :=
  infDist_range_span_eq_zero_iff _ _

/-- **The detector criterion for the Riemann hypothesis.**  If every element of the carrier orthogonal to
all the generators `({θᵢu} − θᵢ{u})/u` is orthogonal to `1/u`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_orthogonal_bdGen {I : Type*} (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    (h : ∀ w : BDCarrier, (∀ i, inner ℂ w (bdGen (θ i)) = 0) → inner ℂ w bdTarget = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_bdDist_eq_zero θ hθ ((bdDist_eq_zero_iff θ).2 h)

/-- The discrete system: a unit annihilator of the first `N` generators pairs with the target at most at
the distance `d_N`, and some annihilator attains it. -/
theorem bdDistDiscrete_eq_sup_detector (N : ℕ) :
    (∀ w : BDCarrier, (∀ n < N, inner ℂ w (bdGen (bdDiscrete n)) = 0) → ‖w‖ ≤ 1 →
        ‖inner ℂ w bdTarget‖ ≤ bdDistDiscrete N) ∧
      ∃ w : BDCarrier, (∀ n < N, inner ℂ w (bdGen (bdDiscrete n)) = 0) ∧ ‖w‖ ≤ 1 ∧
        ‖inner ℂ w bdTarget‖ = bdDistDiscrete N := by
  constructor
  · intro w hw hnorm
    have hb := norm_inner_le_norm_mul_infDist_span
      (Set.range fun i : {x // x ∈ Finset.range N} => bdGen (bdDiscrete i.1)) bdTarget w
      (by
        rintro _ ⟨i, rfl⟩
        exact hw i.1 (Finset.mem_range.1 i.2))
    calc ‖inner ℂ w bdTarget‖ ≤ ‖w‖ * bdDistDiscrete N := hb
      _ ≤ 1 * bdDistDiscrete N := by
          exact mul_le_mul_of_nonneg_right hnorm (bdDist_nonneg _)
      _ = bdDistDiscrete N := one_mul _
  · obtain ⟨w, hw, hnorm, heq⟩ :=
      exists_bdDetector_norm_inner_eq_bdDist (fun i : {x // x ∈ Finset.range N} => bdDiscrete i.1)
    exact ⟨w, fun n hn => hw ⟨n, Finset.mem_range.2 hn⟩, hnorm, heq⟩

/-- **A separating detector exists at every finite level.**  Since `bdDistDiscrete_pos` gives a positive
distance for every `N`, duality produces a carrier element orthogonal to the first `N` generators whose
pairing with the target is nonzero: the finite-section problem always carries an obstruction, so the
criterion can only be met in the limit. -/
theorem exists_bdDetector_inner_ne_zero (N : ℕ) :
    ∃ w : BDCarrier, (∀ n < N, inner ℂ w (bdGen (bdDiscrete n)) = 0) ∧ ‖w‖ ≤ 1 ∧
      inner ℂ w bdTarget ≠ 0 := by
  obtain ⟨w, hw, hnorm, heq⟩ := (bdDistDiscrete_eq_sup_detector N).2
  refine ⟨w, hw, hnorm, fun h => ?_⟩
  rw [h, norm_zero] at heq
  exact absurd heq.symm (ne_of_gt (bdDistDiscrete_pos N))

/-- **The quantitative detector criterion.**  If for every `ε > 0` some finite section has the property
that all its unit annihilators pair with the target below `ε`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_detector_bound
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ w : BDCarrier,
      (∀ n < N, inner ℂ w (bdGen (bdDiscrete n)) = 0) → ‖w‖ ≤ 1 →
        ‖inner ℂ w bdTarget‖ ≤ ε) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_bdDist_eq_zero bdDiscrete bdDiscrete_mem ?_
  have hle : ∀ ε : ℝ, 0 < ε → bdDist bdDiscrete ≤ 0 + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    obtain ⟨w, hw, hnorm, heq⟩ := (bdDistDiscrete_eq_sup_detector N).2
    have hsec : bdDist bdDiscrete ≤ bdDistDiscrete N := by
      refine bdDist_mono _ _ ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
    rw [zero_add]
    calc bdDist bdDiscrete ≤ bdDistDiscrete N := hsec
      _ = ‖inner ℂ w bdTarget‖ := heq.symm
      _ ≤ ε := hN w hw hnorm
  exact le_antisymm (le_of_forall_pos_le_add hle) (bdDist_nonneg _)

end RHTower

end
