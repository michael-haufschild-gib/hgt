import GaloisForLFunctions.HTGeometry.ShilovLocalBoundaryIdeal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Complex.Basic

/-!
# The commutative model of a boundary ideal

The metric boundary condition of `ShilovLocalBoundaryIdeal.lean` is the abstract form of a
classical notion.  This module identifies the two in the commutative model, where the ambient
algebra is `C(X, ℂ)` on a compact Hausdorff space and the ideals are vanishing ideals of closed
sets: for a closed `F ⊆ X`,

```text
the vanishing ideal of F is a boundary ideal for S  ↔  F computes the sup-norm of every s ∈ S.
```

One direction is the sup-norm bound.  The other is Urysohn's lemma: if some `s ∈ S` exceeds on `X`
a bound it obeys on `F`, then a continuous function equal to `1` on `F` and to `0` where `‖s‖` is
large cuts `s` down below its own norm while staying in the vanishing ideal, contradicting the
boundary condition.

This is the model case behind the `C^*`-envelope computation `C_e^*(A(K)) = C(ext K)`, and it
shows the abstract definition is not a weakening: it specialises exactly to boundaries of function
systems.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

section Commutative

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The ideal of continuous functions vanishing on a set. -/
def vanishingIdeal (F : Set X) : Submodule ℂ C(X, ℂ) where
  carrier := {f | ∀ x ∈ F, f x = 0}
  add_mem' {f g} hf hg := fun x hx => by
    simp only [ContinuousMap.add_apply, hf x hx, hg x hx, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' c f hf := fun x hx => by
    simp only [ContinuousMap.smul_apply, hf x hx, smul_zero]

omit [CompactSpace X] [T2Space X] in
@[simp]
theorem mem_vanishingIdeal {F : Set X} {f : C(X, ℂ)} :
    f ∈ vanishingIdeal F ↔ ∀ x ∈ F, f x = 0 := Iff.rfl

/-- `F` is a boundary for `S` when every bound valid on `F` is a global bound. -/
def IsBoundarySet (S : Submodule ℂ C(X, ℂ)) (F : Set X) : Prop :=
  ∀ s ∈ S, ∀ r : ℝ, 0 ≤ r → (∀ x ∈ F, ‖s x‖ ≤ r) → ‖s‖ ≤ r

omit [T2Space X] in
/-- A boundary set gives a boundary ideal: subtracting a function that vanishes on `F` cannot
shorten an element of `S`, because `F` already sees its whole norm. -/
theorem isBoundaryIdeal_of_isBoundarySet {S : Submodule ℂ C(X, ℂ)} {F : Set X}
    (h : IsBoundarySet S F) : IsBoundaryIdeal S (vanishingIdeal F) := by
  intro s hs j hj
  refine h s hs ‖s - j‖ (norm_nonneg _) fun x hx => ?_
  have hval : (s - j) x = s x := by
    simp only [ContinuousMap.sub_apply, hj x hx, sub_zero]
  rw [← hval]
  exact ContinuousMap.norm_coe_le_norm (s - j) x

/-- A boundary ideal of vanishing type comes from a boundary set.  Urysohn's lemma produces the
cutting function. -/
theorem isBoundarySet_of_isBoundaryIdeal {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (h : IsBoundaryIdeal S (vanishingIdeal F)) : IsBoundarySet S F := by
  intro s hs r hr0 hr
  by_contra hcon
  have hlt : r < ‖s‖ := not_le.mp hcon
  set c : ℝ := (r + ‖s‖) / 2 with hc
  have hrc : r < c := by rw [hc]; linarith
  have hcs : c < ‖s‖ := by rw [hc]; linarith
  have hc0 : 0 ≤ c := le_trans hr0 hrc.le
  have hK : IsClosed {x : X | c ≤ ‖s x‖} :=
    isClosed_le continuous_const (s.continuous.norm)
  have hdisj : Disjoint {x : X | c ≤ ‖s x‖} F := by
    rw [Set.disjoint_left]
    intro x hx hxF
    have h1 : ‖s x‖ ≤ r := hr x hxF
    have h2 : c ≤ ‖s x‖ := hx
    linarith
  obtain ⟨φ, hφK, hφF, hφmem⟩ := exists_continuous_zero_one_of_isClosed hK hF hdisj
  set ψ : C(X, ℂ) :=
    { toFun := fun x => ((1 - φ x : ℝ) : ℂ) * s x
      continuous_toFun :=
        (Complex.continuous_ofReal.comp (continuous_const.sub φ.continuous)).mul
          s.continuous } with hψ
  have hψmem : ψ ∈ vanishingIdeal F := by
    intro x hx
    have : φ x = 1 := hφF hx
    simp only [hψ, ContinuousMap.coe_mk, this, sub_self, Complex.ofReal_zero, zero_mul]
  have hsub : ∀ x : X, (s - ψ) x = ((φ x : ℝ) : ℂ) * s x := by
    intro x
    simp only [hψ, ContinuousMap.sub_apply, ContinuousMap.coe_mk, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  have hbound : ‖s - ψ‖ ≤ c := by
    rw [ContinuousMap.norm_le _ hc0]
    intro x
    rw [hsub x, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases le_or_gt c ‖s x‖ with hx | hx
    · have : φ x = 0 := hφK hx
      simp [this]
      exact hc0
    · have h1 : |φ x| ≤ 1 := by
        have := hφmem x
        rw [abs_le]
        exact ⟨by linarith [this.1], this.2⟩
      have h2 : (0 : ℝ) ≤ ‖s x‖ := norm_nonneg _
      nlinarith [h1, h2, hx]
  have := h s hs ψ hψmem
  linarith

/-- **The commutative model.**  For a closed set in a compact Hausdorff space, its vanishing ideal
is a boundary ideal for `S` exactly when the set is a boundary for `S`. -/
theorem isBoundaryIdeal_vanishingIdeal_iff (S : Submodule ℂ C(X, ℂ)) {F : Set X}
    (hF : IsClosed F) :
    IsBoundaryIdeal S (vanishingIdeal F) ↔ IsBoundarySet S F :=
  ⟨isBoundarySet_of_isBoundaryIdeal hF, isBoundaryIdeal_of_isBoundarySet⟩

omit [T2Space X] in
/-- Boundary sets are upward closed, matching the downward closure of boundary ideals. -/
theorem IsBoundarySet.mono {S : Submodule ℂ C(X, ℂ)} {F G : Set X} (h : IsBoundarySet S F)
    (hFG : F ⊆ G) : IsBoundarySet S G :=
  fun s hs r hr0 hbound => h s hs r hr0 fun x hx => hbound x (hFG hx)

omit [T2Space X] in
/-- The whole space is a boundary. -/
theorem isBoundarySet_univ (S : Submodule ℂ C(X, ℂ)) : IsBoundarySet S Set.univ := by
  intro s _ r hr0 hbound
  rw [ContinuousMap.norm_le _ hr0]
  exact fun x => hbound x (Set.mem_univ x)

/-! ## Joins and peak points -/

omit [CompactSpace X] [T2Space X] in
/-- The join of two vanishing ideals sits inside the vanishing ideal of the intersection. -/
theorem vanishingIdeal_sup_le (F G : Set X) :
    vanishingIdeal F ⊔ vanishingIdeal G ≤ vanishingIdeal (F ∩ G) := by
  refine sup_le ?_ ?_ <;> intro f hf x hx
  · exact hf x hx.1
  · exact hf x hx.2

omit [T2Space X] in
/-- **Join-closure in the commutative model reduces to intersection-closure of boundaries.**  If
the intersection of two boundary sets is again a boundary set, the join of their vanishing ideals
is a boundary ideal. -/
theorem isBoundaryIdeal_sup_of_isBoundarySet_inter {S : Submodule ℂ C(X, ℂ)} {F G : Set X}
    (h : IsBoundarySet S (F ∩ G)) :
    IsBoundaryIdeal S (vanishingIdeal F ⊔ vanishingIdeal G) :=
  (isBoundaryIdeal_of_isBoundarySet h).mono (vanishingIdeal_sup_le F G)

/-- `x` is a peak point of `S` when some nonzero element of `S` is strictly smaller everywhere
else. -/
def IsPeakPoint (S : Submodule ℂ C(X, ℂ)) (x : X) : Prop :=
  ∃ s ∈ S, 0 < ‖s‖ ∧ ∀ y : X, y ≠ x → ‖s y‖ < ‖s‖

omit [T2Space X] in
/-- **Every boundary contains every peak point.**  A peaking function is strictly smaller off its
peak, so a closed boundary missing the peak would bound it below its own norm. -/
theorem IsBoundarySet.peakPoint_mem {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (hb : IsBoundarySet S F) {x : X} (hx : IsPeakPoint S x) : x ∈ F := by
  obtain ⟨s, hs, hpos, hpeak⟩ := hx
  by_contra hxF
  rcases F.eq_empty_or_nonempty with rfl | hne
  · have hzero := hb s hs 0 le_rfl (by simp)
    linarith
  · obtain ⟨y₀, hy₀F, hy₀max⟩ :=
      hF.isCompact.exists_isMaxOn hne (s.continuous.norm.continuousOn)
    have hlt : ‖s y₀‖ < ‖s‖ := hpeak y₀ fun h => hxF (h ▸ hy₀F)
    have hbound : ∀ y ∈ F, ‖s y‖ ≤ ‖s y₀‖ := fun y hy => hy₀max hy
    have hle := hb s hs ‖s y₀‖ (norm_nonneg _) hbound
    linarith

omit [T2Space X] in
/-- Every closed boundary contains the closure of the peak points.  This is the lower half of the
Shilov boundary: the peak points are forced, and what remains open is whether their closure is
itself a boundary. -/
theorem closure_setOf_isPeakPoint_subset {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (hb : IsBoundarySet S F) : closure {x : X | IsPeakPoint S x} ⊆ F :=
  hF.closure_subset_iff.mpr fun _ hx => hb.peakPoint_mem hF hx

/-! ## Minimal boundaries -/

omit [T2Space X] in
/-- **Directed intersections of closed boundaries are boundaries.**  If some `s ∈ S` exceeded the
bound obeyed on the intersection, every member of the family would carry a nonempty compact set on
which `‖s‖` stays large; compactness then places a point of the intersection there. -/
theorem isBoundarySet_sInter_of_directed {S : Submodule ℂ C(X, ℂ)} {𝓒 : Set (Set X)}
    (hne : 𝓒.Nonempty) (hdir : DirectedOn (· ⊇ ·) 𝓒)
    (hclosed : ∀ F ∈ 𝓒, IsClosed F) (hb : ∀ F ∈ 𝓒, IsBoundarySet S F) :
    IsBoundarySet S (⋂₀ 𝓒) := by
  intro s hs r hr0 hr
  by_contra hcon
  have hlt : r < ‖s‖ := not_le.mp hcon
  set r' : ℝ := (r + ‖s‖) / 2 with hr'
  have hrr' : r < r' := by rw [hr']; linarith
  have hr's : r' < ‖s‖ := by rw [hr']; linarith
  have hr'0 : 0 ≤ r' := le_trans hr0 hrr'.le
  set T : Set X := {y : X | r' ≤ ‖s y‖} with hT
  have hTclosed : IsClosed T := isClosed_le continuous_const s.continuous.norm
  set 𝓚 : Set (Set X) := (fun F => F ∩ T) '' 𝓒 with h𝓚
  have hKclosed : ∀ K ∈ 𝓚, IsClosed K := by
    rintro K ⟨F, hF, rfl⟩
    exact (hclosed F hF).inter hTclosed
  have hKne : ∀ K ∈ 𝓚, K.Nonempty := by
    rintro K ⟨F, hF, rfl⟩
    by_contra hempty
    have hbound : ∀ y ∈ F, ‖s y‖ ≤ r' := by
      intro y hy
      by_contra hy'
      exact hempty ⟨y, hy, (not_le.mp hy').le⟩
    have := hb F hF s hs r' hr'0 hbound
    linarith
  have hKdir : DirectedOn (· ⊇ ·) 𝓚 := by
    rintro K₁ ⟨F₁, hF₁, rfl⟩ K₂ ⟨F₂, hF₂, rfl⟩
    obtain ⟨F₃, hF₃, h₁, h₂⟩ := hdir F₁ hF₁ F₂ hF₂
    exact ⟨F₃ ∩ T, ⟨F₃, hF₃, rfl⟩, Set.inter_subset_inter_left T h₁,
      Set.inter_subset_inter_left T h₂⟩
  obtain ⟨F₀, hF₀⟩ := hne
  haveI : Nonempty ↑𝓚 := ⟨⟨F₀ ∩ T, ⟨F₀, hF₀, rfl⟩⟩⟩
  obtain ⟨y, hy⟩ := IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    hKdir hKne (fun K hK => (hKclosed K hK).isCompact) hKclosed
  have hyInter : y ∈ ⋂₀ 𝓒 := by
    rw [Set.mem_sInter]
    intro F hF
    exact (Set.mem_sInter.mp hy _ ⟨F, hF, rfl⟩).1
  have hylarge : r' ≤ ‖s y‖ := (Set.mem_sInter.mp hy _ ⟨F₀, hF₀, rfl⟩).2
  have := hr y hyInter
  linarith

omit [T2Space X] in
/-- **A minimal closed boundary exists.**  Zorn's lemma applies downwards because chains of closed
boundaries intersect to closed boundaries.  Shilov's theorem is the further statement that the
minimal one is unique; that needs the algebra structure and is not proved here. -/
theorem exists_minimal_isBoundarySet (S : Submodule ℂ C(X, ℂ)) :
    ∃ F : Set X, Minimal (fun G : Set X => IsClosed G ∧ IsBoundarySet S G) F := by
  refine zorn_superset {G : Set X | IsClosed G ∧ IsBoundarySet S G} fun c hc hchain => ?_
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨Set.univ, ⟨isClosed_univ, isBoundarySet_univ S⟩,
      fun s hs => absurd hs (Set.notMem_empty s)⟩
  · have hdir : DirectedOn (· ⊇ ·) c := by
      intro F₁ h₁ F₂ h₂
      rcases hchain.total h₁ h₂ with h | h
      · exact ⟨F₁, h₁, subset_rfl, h⟩
      · exact ⟨F₂, h₂, h, subset_rfl⟩
    exact ⟨⋂₀ c, ⟨isClosed_sInter fun F hF => (hc hF).1,
      isBoundarySet_sInter_of_directed hne hdir (fun F hF => (hc hF).1)
        (fun F hF => (hc hF).2)⟩, fun F hF => Set.sInter_subset_of_mem hF⟩

/-! ## The Shilov boundary -/

/-- The intersection of every closed boundary. -/
def shilovBoundary (S : Submodule ℂ C(X, ℂ)) : Set X :=
  ⋂₀ {F : Set X | IsClosed F ∧ IsBoundarySet S F}

omit [T2Space X] in
theorem isClosed_shilovBoundary (S : Submodule ℂ C(X, ℂ)) : IsClosed (shilovBoundary S) :=
  isClosed_sInter fun _ hF => hF.1

omit [T2Space X] in
theorem shilovBoundary_subset {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (hb : IsBoundarySet S F) : shilovBoundary S ⊆ F :=
  Set.sInter_subset_of_mem ⟨hF, hb⟩

omit [T2Space X] in
/-- The peak points are forced into the Shilov boundary. -/
theorem closure_setOf_isPeakPoint_subset_shilovBoundary (S : Submodule ℂ C(X, ℂ)) :
    closure {x : X | IsPeakPoint S x} ⊆ shilovBoundary S := by
  refine Set.subset_sInter fun F hF => ?_
  exact closure_setOf_isPeakPoint_subset hF.1 hF.2

omit [T2Space X] in
/-- **The Shilov boundary is least once closed boundaries intersect.**  Binary intersection-closure
makes the family of closed boundaries downward directed, and directed intersections of closed
boundaries are boundaries, so the intersection of all of them is itself a boundary. -/
theorem isLeast_shilovBoundary (S : Submodule ℂ C(X, ℂ))
    (hinter : ∀ F G : Set X, IsClosed F → IsBoundarySet S F → IsClosed G → IsBoundarySet S G →
      IsBoundarySet S (F ∩ G)) :
    IsLeast {F : Set X | IsClosed F ∧ IsBoundarySet S F} (shilovBoundary S) := by
  have hne : {F : Set X | IsClosed F ∧ IsBoundarySet S F}.Nonempty :=
    ⟨Set.univ, isClosed_univ, isBoundarySet_univ S⟩
  have hdir : DirectedOn (· ⊇ ·) {F : Set X | IsClosed F ∧ IsBoundarySet S F} := by
    rintro F ⟨hFc, hFb⟩ G ⟨hGc, hGb⟩
    exact ⟨F ∩ G, ⟨hFc.inter hGc, hinter F G hFc hFb hGc hGb⟩,
      Set.inter_subset_left, Set.inter_subset_right⟩
  refine ⟨⟨isClosed_shilovBoundary S, ?_⟩, fun F hF => shilovBoundary_subset hF.1 hF.2⟩
  exact isBoundarySet_sInter_of_directed hne hdir (fun _ hF => hF.1) (fun _ hF => hF.2)

omit [CompactSpace X] [T2Space X] in
/-- Vanishing ideals are antitone in the set. -/
theorem vanishingIdeal_mono {F G : Set X} (h : F ⊆ G) : vanishingIdeal G ≤ vanishingIdeal F :=
  fun _ hf x hx => hf x (h hx)

omit [T2Space X] in
/-- **The greatest vanishing-type boundary ideal.**  Under binary intersection-closure the
vanishing ideal of the Shilov boundary is a boundary ideal containing every other vanishing-type
one, so it is the Shilov ideal within that family. -/
theorem isGreatest_vanishingIdeal_shilovBoundary (S : Submodule ℂ C(X, ℂ))
    (hinter : ∀ F G : Set X, IsClosed F → IsBoundarySet S F → IsClosed G → IsBoundarySet S G →
      IsBoundarySet S (F ∩ G)) :
    IsBoundaryIdeal S (vanishingIdeal (shilovBoundary S)) ∧
      ∀ F : Set X, IsClosed F → IsBoundarySet S F →
        vanishingIdeal F ≤ vanishingIdeal (shilovBoundary S) := by
  refine ⟨isBoundaryIdeal_of_isBoundarySet (isLeast_shilovBoundary S hinter).1.2,
    fun F hFc hFb => vanishingIdeal_mono (shilovBoundary_subset hFc hFb)⟩

omit [T2Space X] in
/-- **Peak points suffice.**  If the closure of the peak points is itself a boundary, then closed
boundaries are automatically closed under intersection: every one of them contains that closure. -/
theorem isBoundarySet_inter_of_isBoundarySet_closure_peakPoints {S : Submodule ℂ C(X, ℂ)}
    (hb : IsBoundarySet S (closure {x : X | IsPeakPoint S x}))
    {F G : Set X} (hF : IsClosed F) (hbF : IsBoundarySet S F) (hG : IsClosed G)
    (hbG : IsBoundarySet S G) : IsBoundarySet S (F ∩ G) :=
  hb.mono (Set.subset_inter (closure_setOf_isPeakPoint_subset hF hbF)
    (closure_setOf_isPeakPoint_subset hG hbG))

omit [T2Space X] in
/-- **Identification of the Shilov boundary.**  When the closure of the peak points is a boundary
it is exactly the Shilov boundary, since it is contained in every closed boundary. -/
theorem shilovBoundary_eq_closure_peakPoints {S : Submodule ℂ C(X, ℂ)}
    (hb : IsBoundarySet S (closure {x : X | IsPeakPoint S x})) :
    shilovBoundary S = closure {x : X | IsPeakPoint S x} :=
  le_antisymm (shilovBoundary_subset isClosed_closure hb)
    (closure_setOf_isPeakPoint_subset_shilovBoundary S)

/-! ## The classical description -/

omit [T2Space X] in
/-- A closed boundary attains the norm of every element of `S`. -/
theorem IsBoundarySet.exists_norm_eq {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (hne : F.Nonempty) (hb : IsBoundarySet S F) {s : C(X, ℂ)} (hs : s ∈ S) :
    ∃ x ∈ F, ‖s x‖ = ‖s‖ := by
  obtain ⟨x, hxF, hxmax⟩ := hF.isCompact.exists_isMaxOn hne s.continuous.norm.continuousOn
  refine ⟨x, hxF, le_antisymm (ContinuousMap.norm_coe_le_norm s x) ?_⟩
  exact hb s hs ‖s x‖ (norm_nonneg _) fun y hy => hxmax hy

omit [T2Space X] in
/-- Norm attainment on `F` is the classical definition of a boundary, and it agrees with the
bound-transfer definition used here. -/
theorem isBoundarySet_iff_exists_norm_eq {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hF : IsClosed F)
    (hne : F.Nonempty) :
    IsBoundarySet S F ↔ ∀ s ∈ S, ∃ x ∈ F, ‖s x‖ = ‖s‖ := by
  refine ⟨fun hb s hs => hb.exists_norm_eq hF hne hs, fun h s hs r _ hr => ?_⟩
  obtain ⟨x, hxF, hxeq⟩ := h s hs
  rw [← hxeq]
  exact hr x hxF

omit [T2Space X] in
/-- Boundaries pass to closures. -/
theorem IsBoundarySet.closure {S : Submodule ℂ C(X, ℂ)} {F : Set X} (hb : IsBoundarySet S F) :
    IsBoundarySet S (_root_.closure F) :=
  hb.mono subset_closure

end Commutative

end ShilovLocal

end GaloisForLFunctions.HTGeometry
