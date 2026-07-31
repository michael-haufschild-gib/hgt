import GaloisForLFunctions.HTGeometry.BohrBochnerEquivalence
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The Bohr hull of an almost-periodic function is a compact abelian group

The translation distance of a bounded continuous function `f`,

`d_f(s, t) = sup_x ‖f (x + s) - f (x + t)‖`,

is a translation-invariant pseudometric on the additive group `ℝ`.  Its Hausdorff completion is
therefore an abelian topological group, and it is compact exactly when the translation orbit of `f`
is totally bounded, i.e. exactly when `f` is Bohr almost periodic.

This file constructs that group.  The line maps into it by a dense additive homomorphism, and `f`
itself, being `1`-Lipschitz for the translation distance, extends to a continuous function on the
hull.  The hull is the phase carrier of `f`: its characters are the Bohr frequencies.
-/

open Filter Topology Metric

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- Translation of a bounded continuous function on the line. -/
def translateBC (u : ℝ) (f : ℝ →ᵇ E) : ℝ →ᵇ E :=
  f.compContinuous ⟨fun x => x + u, continuous_id.add continuous_const⟩

@[simp] theorem translateBC_apply (u : ℝ) (f : ℝ →ᵇ E) (x : ℝ) :
    translateBC u f x = f (x + u) := rfl

theorem translateBC_zero (f : ℝ →ᵇ E) : translateBC 0 f = f := by
  ext x
  simp

theorem translateBC_add (a b : ℝ) (f : ℝ →ᵇ E) :
    translateBC (a + b) f = translateBC b (translateBC a f) := by
  ext x
  show f (x + (a + b)) = f (x + b + a)
  congr 1
  ring

/-- Translation acts by isometries. -/
theorem dist_translateBC (u : ℝ) (f g : ℝ →ᵇ E) :
    dist (translateBC u f) (translateBC u g) = dist f g := by
  refine le_antisymm ?_ ?_
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun x => ?_
    simpa using BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) (x + u)
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun x => ?_
    have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := translateBC u f) (g := translateBC u g) (x - u)
    simpa using h

/-- The real line carrying the uniform translation distance of `f`. -/
def BohrLine (_f : ℝ →ᵇ E) : Type := ℝ

namespace BohrLine

instance (f : ℝ →ᵇ E) : AddCommGroup (BohrLine f) := inferInstanceAs (AddCommGroup ℝ)

/-- The underlying real number of a point of the Bohr line. -/
def val {f : ℝ →ᵇ E} (t : BohrLine f) : ℝ := t

/-- A real number viewed as a point of the Bohr line. -/
def of (f : ℝ →ᵇ E) (t : ℝ) : BohrLine f := t

@[simp] theorem val_of (f : ℝ →ᵇ E) (t : ℝ) : (of f t).val = t := rfl

@[simp] theorem of_val {f : ℝ →ᵇ E} (t : BohrLine f) : of f t.val = t := rfl

theorem val_add {f : ℝ →ᵇ E} (s t : BohrLine f) : (s + t).val = s.val + t.val := rfl

theorem of_add (f : ℝ →ᵇ E) (s t : ℝ) : of f (s + t) = of f s + of f t := rfl

instance (f : ℝ →ᵇ E) : PseudoMetricSpace (BohrLine f) :=
  PseudoMetricSpace.induced (fun t : BohrLine f => translateBC t.val f) inferInstance

theorem dist_eq {f : ℝ →ᵇ E} (s t : BohrLine f) :
    dist s t = dist (translateBC s.val f) (translateBC t.val f) := rfl

/-- The translation distance is invariant. -/
theorem dist_add_right {f : ℝ →ᵇ E} (s t u : BohrLine f) :
    dist (s + u) (t + u) = dist s t := by
  show dist (translateBC (s.val + u.val) f) (translateBC (t.val + u.val) f)
    = dist (translateBC s.val f) (translateBC t.val f)
  rw [translateBC_add, translateBC_add, dist_translateBC]

theorem dist_neg {f : ℝ →ᵇ E} (s t : BohrLine f) : dist (-s) (-t) = dist s t := by
  have h := dist_add_right (-s) (-t) (s + t)
  have h1 : (-s) + (s + t) = t := by abel
  have h2 : (-t) + (s + t) = s := by abel
  rw [h1, h2] at h
  rw [← h, dist_comm]

theorem dist_sub_left {f : ℝ →ᵇ E} (s t u : BohrLine f) :
    dist (u - s) (u - t) = dist s t := by
  have h : dist ((-s) + u) ((-t) + u) = dist (-s) (-t) := dist_add_right (-s) (-t) u
  rw [dist_neg] at h
  have e1 : (-s) + u = u - s := by abel
  have e2 : (-t) + u = u - t := by abel
  rw [e1, e2] at h
  exact h

instance (f : ℝ →ᵇ E) : IsUniformAddGroup (BohrLine f) := by
  refine ⟨?_⟩
  have hlip : LipschitzWith 2 (fun p : BohrLine f × BohrLine f => p.1 - p.2) := by
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    have h1 : dist (p.1 - p.2) (q.1 - p.2) = dist p.1 q.1 := by
      have := dist_add_right p.1 q.1 (-p.2)
      have e1 : p.1 + -p.2 = p.1 - p.2 := by abel
      have e2 : q.1 + -p.2 = q.1 - p.2 := by abel
      rwa [e1, e2] at this
    have h2 : dist (q.1 - p.2) (q.1 - q.2) = dist p.2 q.2 := dist_sub_left p.2 q.2 q.1
    have hmax1 : dist p.1 q.1 ≤ dist p q := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    have hmax2 : dist p.2 q.2 ≤ dist p q := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    have htri : dist (p.1 - p.2) (q.1 - q.2)
        ≤ dist (p.1 - p.2) (q.1 - p.2) + dist (q.1 - p.2) (q.1 - q.2) := dist_triangle _ _ _
    rw [h1, h2] at htri
    have : dist p.1 q.1 + dist p.2 q.2 ≤ 2 * dist p q := by linarith
    calc dist (p.1 - p.2) (q.1 - q.2) ≤ dist p.1 q.1 + dist p.2 q.2 := htri
      _ ≤ 2 * dist p q := this
      _ = ((2 : NNReal) : ℝ) * dist p q := by norm_num
  exact hlip.uniformContinuous

/-- The Bohr line of an almost-periodic function is totally bounded: this is Bochner's criterion. -/
theorem totallyBounded_univ {f : ℝ →ᵇ E} (h : HasTotallyBoundedOrbit (fun x => f x)) :
    TotallyBounded (Set.univ : Set (BohrLine f)) := by
  refine Metric.totallyBounded_iff.mpr fun ε hε => ?_
  obtain ⟨S, _, hS⟩ := h (ε / 2) (by linarith)
  refine ⟨(fun t : ℝ => of f t) '' S, S.finite_toSet.image _, ?_⟩
  intro a _
  obtain ⟨s, hsS, hs⟩ := hS a.val
  refine Set.mem_iUnion₂.mpr ⟨of f s, Set.mem_image_of_mem _ hsS, ?_⟩
  have hle : dist a (of f s) ≤ ε / 2 := by
    show dist (translateBC a.val f) (translateBC s f) ≤ ε / 2
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun x => ?_
    have := hs x
    rwa [dist_eq_norm, translateBC_apply, translateBC_apply]
  exact Metric.mem_ball.mpr (lt_of_le_of_lt hle (by linarith))

/-- Evaluation at the origin is `1`-Lipschitz for the translation distance. -/
theorem uniformContinuous_eval (f : ℝ →ᵇ E) :
    UniformContinuous (fun t : BohrLine f => f t.val) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).uniformContinuous
  have h := BoundedContinuousFunction.dist_coe_le_dist
    (f := translateBC s.val f) (g := translateBC t.val f) 0
  simpa [dist_eq] using h

end BohrLine

/-- The Bohr hull group of a bounded continuous function: the Hausdorff completion of the line for
the translation distance of `f`. -/
abbrev BohrHull (f : ℝ →ᵇ E) : Type := UniformSpace.Completion (BohrLine f)

/-- The canonical dense homomorphism of the line into its Bohr hull. -/
def bohrIota (f : ℝ →ᵇ E) (t : ℝ) : BohrHull f := ((BohrLine.of f t : BohrLine f) : BohrHull f)

theorem bohrIota_add (f : ℝ →ᵇ E) (s t : ℝ) :
    bohrIota f (s + t) = bohrIota f s + bohrIota f t := by
  show ((BohrLine.of f (s + t) : BohrLine f) : BohrHull f)
    = ((BohrLine.of f s : BohrLine f) : BohrHull f) + ((BohrLine.of f t : BohrLine f) : BohrHull f)
  rw [BohrLine.of_add, UniformSpace.Completion.coe_add]

@[simp] theorem bohrIota_zero (f : ℝ →ᵇ E) : bohrIota f 0 = 0 :=
  UniformSpace.Completion.coe_zero

/-- If `f` is uniformly continuous then the ordinary uniformity of the line refines its translation
uniformity. -/
theorem uniformContinuous_bohrLine_of {f : ℝ →ᵇ E} (hf : UniformContinuous (fun x => f x)) :
    UniformContinuous (BohrLine.of f) := by
  refine Metric.uniformContinuous_iff.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hf (ε := ε / 2) (by linarith)
  refine ⟨δ, hδ, fun {s t} hst => ?_⟩
  have hle : dist (BohrLine.of f s) (BohrLine.of f t) ≤ ε / 2 := by
    show dist (translateBC s f) (translateBC t f) ≤ ε / 2
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun x => ?_
    have hxd : dist (x + s) (x + t) < δ := by
      simpa [Real.dist_eq, add_sub_add_left_eq_sub] using hst
    exact le_of_lt (by simpa using hδf hxd)
  exact lt_of_le_of_lt hle (by linarith)

theorem uniformContinuous_bohrIota {f : ℝ →ᵇ E} (hf : UniformContinuous (fun x => f x)) :
    UniformContinuous (bohrIota f) :=
  (UniformSpace.Completion.uniformContinuous_coe _).comp (uniformContinuous_bohrLine_of hf)

theorem continuous_bohrIota {f : ℝ →ᵇ E} (hf : UniformContinuous (fun x => f x)) :
    Continuous (bohrIota f) :=
  (uniformContinuous_bohrIota hf).continuous

theorem denseRange_bohrIota (f : ℝ →ᵇ E) : DenseRange (bohrIota f) := by
  have h : Set.range (bohrIota f) = Set.range (fun t : BohrLine f => (t : BohrHull f)) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨BohrLine.of f t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.val, rfl⟩
  have := UniformSpace.Completion.denseRange_coe (α := BohrLine f)
  rw [DenseRange, h]
  exact this

/-- The Bohr hull is compact when the translation orbit of `f` is totally bounded. -/
theorem compactSpace_bohrHull {f : ℝ →ᵇ E} (h : HasTotallyBoundedOrbit (fun x => f x)) :
    CompactSpace (BohrHull f) := by
  rw [← isCompact_univ_iff]
  refine isCompact_iff_totallyBounded_isComplete.mpr ⟨?_, complete_univ⟩
  have htb : TotallyBounded ((fun t : BohrLine f => (t : BohrHull f)) '' Set.univ) :=
    (BohrLine.totallyBounded_univ h).image (UniformSpace.Completion.uniformContinuous_coe _)
  have hcl : (Set.univ : Set (BohrHull f))
      = closure (Set.range (fun t : BohrLine f => (t : BohrHull f))) :=
    (UniformSpace.Completion.denseRange_coe (α := BohrLine f)).closure_range.symm
  rw [hcl]
  rw [Set.image_univ] at htb
  exact htb.closure

/-- The extension of `f` to its Bohr hull. -/
def bohrEval (f : ℝ →ᵇ E) : BohrHull f → E :=
  UniformSpace.Completion.extension (fun t : BohrLine f => f t.val)

@[simp] theorem bohrEval_bohrIota (f : ℝ →ᵇ E) (t : ℝ) : bohrEval f (bohrIota f t) = f t :=
  UniformSpace.Completion.extension_coe (BohrLine.uniformContinuous_eval f) (BohrLine.of f t)

section Complete

variable [CompleteSpace E]

theorem uniformContinuous_bohrEval (f : ℝ →ᵇ E) : UniformContinuous (bohrEval f) :=
  UniformSpace.Completion.uniformContinuous_extension

theorem continuous_bohrEval (f : ℝ →ᵇ E) : Continuous (bohrEval f) :=
  (uniformContinuous_bohrEval f).continuous

end Complete

end

end GaloisForLFunctions
