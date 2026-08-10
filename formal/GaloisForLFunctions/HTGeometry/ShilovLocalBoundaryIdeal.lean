import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Order.Zorn

/-!
# Local boundary ideals of a coordinate tower

The algebraic core of Shilov boundary migration is the quotient calculus of
`ShilovBoundaryMigrationDefect.lean`.  This module supplies the metric layer that identifies which
submodule the calculus should be applied to: the *boundary ideal* condition.

A submodule `J` of a normed space `A` is a boundary ideal for a distinguished subspace `S` when
quotienting by `J` shortens no element of `S`,

```text
∀ s ∈ S, ∀ j ∈ J,  ‖s‖ ≤ ‖s - j‖,
```

equivalently `‖s‖ ≤ infDist s J`, equivalently the quotient map `A → A/J` is isometric on `S`.
Boundary ideals are downward closed, stable under closure and under directed unions, so maximal
ones exist; the greatest one, when it exists, is the Shilov ideal, and it is automatically closed.

The main theorem is the representation-free identification of the *local* Shilov ideal of a
coordinate tower: if every stage ideal `J i` is the greatest boundary ideal of its stage system
`S i`, then

```text
J_loc = {a | ∀ i, p i a ∈ J i}
```

is the greatest local boundary ideal, where a submodule is called a local boundary ideal when each
of its closed coordinate images is a stage boundary ideal.  Both halves are elementary: `J_loc`
maps into each `J i`, and boundary-ness is downward closed, so `J_loc` qualifies; conversely each
coordinate image of a local boundary ideal is a stage boundary ideal, hence sits inside `J i` by
maximality.

The index type is arbitrary, so taking it to be a product of a tower index and a matrix size gives
the completely isometric statement with no extra work.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ## Boundary ideals at one stage -/

section Stage

variable {A : Type*} [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]

/-- `J` is a boundary ideal for the subspace `S` when subtracting an element of `J` never shortens
an element of `S`; equivalently the quotient map is isometric on `S`. -/
def IsBoundaryIdeal (S J : Submodule 𝕜 A) : Prop :=
  ∀ s ∈ S, ∀ j ∈ J, ‖s‖ ≤ ‖s - j‖

/-- The boundary condition in quotient-norm form. -/
theorem isBoundaryIdeal_iff_le_infDist (S J : Submodule 𝕜 A) :
    IsBoundaryIdeal S J ↔ ∀ s ∈ S, ‖s‖ ≤ Metric.infDist s (J : Set A) := by
  constructor
  · intro h s hs
    rw [Metric.le_infDist ⟨0, J.zero_mem⟩]
    intro y hy
    rw [dist_eq_norm]
    exact h s hs y hy
  · intro h s hs j hj
    have h1 := h s hs
    have h2 : Metric.infDist s (J : Set A) ≤ dist s j := Metric.infDist_le_dist_of_mem hj
    rw [dist_eq_norm] at h2
    linarith

theorem IsBoundaryIdeal.mono {S J J' : Submodule 𝕜 A} (h : IsBoundaryIdeal S J) (hJ : J' ≤ J) :
    IsBoundaryIdeal S J' := fun s hs j hj => h s hs j (hJ hj)

theorem isBoundaryIdeal_bot (S : Submodule 𝕜 A) : IsBoundaryIdeal S ⊥ := by
  intro s _ j hj
  rw [Submodule.mem_bot] at hj
  rw [hj, sub_zero]

/-- Boundary ideals are stable under closure. -/
theorem IsBoundaryIdeal.topologicalClosure {S J : Submodule 𝕜 A} (h : IsBoundaryIdeal S J) :
    IsBoundaryIdeal S J.topologicalClosure := by
  intro s hs j hj
  have hclosed : IsClosed {x : A | ‖s‖ ≤ ‖s - x‖} :=
    isClosed_le continuous_const ((continuous_const.sub continuous_id).norm)
  have hsub : (J : Set A) ⊆ {x : A | ‖s‖ ≤ ‖s - x‖} := fun x hx => h s hs x hx
  have hcl : (J.topologicalClosure : Set A) ⊆ {x : A | ‖s‖ ≤ ‖s - x‖} := by
    rw [Submodule.topologicalClosure_coe]
    exact hclosed.closure_subset_iff.mpr hsub
  exact hcl hj

/-- A directed union of boundary ideals is a boundary ideal. -/
theorem isBoundaryIdeal_sSup {S : Submodule 𝕜 A} {C : Set (Submodule 𝕜 A)}
    (hne : C.Nonempty) (hC : DirectedOn (· ≤ ·) C) (h : ∀ J ∈ C, IsBoundaryIdeal S J) :
    IsBoundaryIdeal S (sSup C) := by
  intro s hs j hj
  rw [Submodule.mem_sSup_of_directed hne hC] at hj
  obtain ⟨J, hJC, hjJ⟩ := hj
  exact h J hJC s hs j hjJ

/-- **Maximal boundary ideals exist.**  Zorn's lemma applies because boundary ideals are closed
under directed unions and contain the zero ideal. -/
theorem exists_maximal_isBoundaryIdeal (S : Submodule 𝕜 A) :
    ∃ J : Submodule 𝕜 A, Maximal (fun K => IsBoundaryIdeal S K) J := by
  refine zorn_le₀ {K : Submodule 𝕜 A | IsBoundaryIdeal S K} fun C hC hchain => ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊥, isBoundaryIdeal_bot S, fun z hz => absurd hz (Set.notMem_empty z)⟩
  · exact ⟨sSup C, isBoundaryIdeal_sSup hne hchain.directedOn fun J hJ => hC hJ,
      fun z hz => le_sSup hz⟩

/-- The greatest boundary ideal — the Shilov ideal — is automatically closed. -/
theorem isClosed_of_isGreatest_isBoundaryIdeal {S J : Submodule 𝕜 A}
    (hJ : IsGreatest {K : Submodule 𝕜 A | IsBoundaryIdeal S K} J) : IsClosed (J : Set A) := by
  have h1 : J.topologicalClosure ≤ J := hJ.2 hJ.1.topologicalClosure
  have h2 : J.topologicalClosure = J := le_antisymm h1 (Submodule.le_topologicalClosure J)
  have h3 := Submodule.isClosed_topologicalClosure J
  rwa [h2] at h3

end Stage

/-! ## The local boundary ideal of a coordinate tower -/

section Tower

variable {ι : Type*} {A : ι → Type*} [∀ i, SeminormedAddCommGroup (A i)]
  [∀ i, NormedSpace 𝕜 (A i)]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The local ideal cut out by a family of stage ideals along the coordinate maps. -/
def localIdeal (p : ∀ i, E →ₗ[𝕜] A i) (J : ∀ i, Submodule 𝕜 (A i)) : Submodule 𝕜 E :=
  ⨅ i, (J i).comap (p i)

theorem mem_localIdeal {p : ∀ i, E →ₗ[𝕜] A i} {J : ∀ i, Submodule 𝕜 (A i)} {a : E} :
    a ∈ localIdeal p J ↔ ∀ i, p i a ∈ J i := by
  simp [localIdeal, Submodule.mem_iInf, Submodule.mem_comap]

/-- The local ideal is exactly the kernel of the comparison map into the stage quotients. -/
theorem mem_localIdeal_iff_mkQ_eq_zero {p : ∀ i, E →ₗ[𝕜] A i} {J : ∀ i, Submodule 𝕜 (A i)}
    {a : E} : a ∈ localIdeal p J ↔ ∀ i, (J i).mkQ (p i a) = 0 := by
  rw [mem_localIdeal]
  refine forall_congr' fun i => ?_
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- A submodule is a local boundary ideal when each of its closed coordinate images is a stage
boundary ideal. -/
def IsLocalBoundaryIdeal (p : ∀ i, E →ₗ[𝕜] A i) (S : ∀ i, Submodule 𝕜 (A i))
    (H : Submodule 𝕜 E) : Prop :=
  ∀ i, IsBoundaryIdeal (S i) ((H.map (p i)).topologicalClosure)

/-- The local ideal cut out by closed stage boundary ideals is a local boundary ideal. -/
theorem isLocalBoundaryIdeal_localIdeal {p : ∀ i, E →ₗ[𝕜] A i} {S J : ∀ i, Submodule 𝕜 (A i)}
    (hclosed : ∀ i, IsClosed ((J i : Set (A i)))) (hJ : ∀ i, IsBoundaryIdeal (S i) (J i)) :
    IsLocalBoundaryIdeal p S (localIdeal p J) := by
  intro i
  refine (hJ i).mono (Submodule.topologicalClosure_minimal _ ?_ (hclosed i))
  rintro x hx
  rw [Submodule.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact (mem_localIdeal.mp ha) i

/-- Every local boundary ideal sits inside the local ideal cut out by the stage Shilov ideals. -/
theorem le_localIdeal_of_isLocalBoundaryIdeal {p : ∀ i, E →ₗ[𝕜] A i}
    {S J : ∀ i, Submodule 𝕜 (A i)}
    (hmax : ∀ i, ∀ K : Submodule 𝕜 (A i), IsBoundaryIdeal (S i) K → K ≤ J i)
    {H : Submodule 𝕜 E} (hH : IsLocalBoundaryIdeal p S H) :
    H ≤ localIdeal p J := by
  intro a ha
  rw [mem_localIdeal]
  intro i
  have hsub : (H.map (p i)).topologicalClosure ≤ J i := hmax i _ (hH i)
  exact hsub (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ha))

/-- **Representation-free identification of the local Shilov ideal.**  If every stage ideal is the
greatest boundary ideal of its stage system, then the ideal it cuts out along the coordinate maps
is the greatest local boundary ideal. -/
theorem localIdeal_isGreatest {p : ∀ i, E →ₗ[𝕜] A i} {S J : ∀ i, Submodule 𝕜 (A i)}
    (hJ : ∀ i, IsGreatest {K : Submodule 𝕜 (A i) | IsBoundaryIdeal (S i) K} (J i)) :
    IsGreatest {H : Submodule 𝕜 E | IsLocalBoundaryIdeal p S H} (localIdeal p J) := by
  refine ⟨isLocalBoundaryIdeal_localIdeal
    (fun i => isClosed_of_isGreatest_isBoundaryIdeal (hJ i)) (fun i => (hJ i).1),
    fun H hH => le_localIdeal_of_isLocalBoundaryIdeal (fun i K hK => (hJ i).2 hK) hH⟩

end Tower

/-! ## Boundary migration along a link -/

section Link

variable {A B : Type*} [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]

/-- **Escape freedom is exactly envelope descent.**  A link descends to the boundary quotients
precisely when it carries the source boundary ideal into the target one. -/
theorem escapeFree_iff_exists_descent (α : A →ₗ[𝕜] B) (JA : Submodule 𝕜 A)
    (JB : Submodule 𝕜 B) :
    JA.map α ≤ JB ↔ ∃ θ : (A ⧸ JA) →ₗ[𝕜] (B ⧸ JB), ∀ a, θ (JA.mkQ a) = JB.mkQ (α a) := by
  constructor
  · intro h
    have hle : JA ≤ JB.comap α := fun x hx => h (Submodule.mem_map_of_mem hx)
    refine ⟨JA.mapQ JB α hle, fun a => ?_⟩
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
  · rintro ⟨θ, hθ⟩ y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h0 : JA.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero JA).mpr hx
    have := hθ x
    rw [h0, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero JB).mp this.symm

/-- A boundary ideal pulls back along a contraction that is isometric on the source system. -/
theorem isBoundaryIdeal_comap (α : A →ₗ[𝕜] B) {SA : Submodule 𝕜 A} {SB JB : Submodule 𝕜 B}
    (hcontr : ∀ x : A, ‖α x‖ ≤ ‖x‖) (hiso : ∀ s ∈ SA, ‖α s‖ = ‖s‖)
    (hmap : SA.map α ≤ SB) (hJB : IsBoundaryIdeal SB JB) :
    IsBoundaryIdeal SA (JB.comap α) := by
  intro s hs j hj
  rw [Submodule.mem_comap] at hj
  have h1 : ‖α s‖ ≤ ‖α s - α j‖ := hJB (α s) (hmap (Submodule.mem_map_of_mem hs)) (α j) hj
  have h2 : ‖α s - α j‖ = ‖α (s - j)‖ := by rw [map_sub]
  have h3 : ‖α (s - j)‖ ≤ ‖s - j‖ := hcontr _
  rw [hiso s hs] at h1
  linarith [h1, h2.le, h2.ge, h3]

/-- **Boundary-ideal pushforward along a complete quotient link.**  If the link realises its
target as a metric quotient, is isometric on the source system, and its kernel already lies inside
the source boundary ideal, then the image of that ideal is a target boundary ideal. -/
theorem isBoundaryIdeal_map_of_quotient (α : A →ₗ[𝕜] B) {SA JA : Submodule 𝕜 A}
    {SB : Submodule 𝕜 B}
    (hquot : ∀ x : A, ‖α x‖ = Metric.infDist x ((LinearMap.ker α : Submodule 𝕜 A) : Set A))
    (hker : LinearMap.ker α ≤ JA) (hSB : SB ≤ SA.map α) (hiso : ∀ s ∈ SA, ‖α s‖ = ‖s‖)
    (hJA : IsBoundaryIdeal SA JA) :
    IsBoundaryIdeal SB (JA.map α) := by
  intro t ht j' hj'
  rw [Submodule.mem_map] at hj'
  obtain ⟨j, hj, rfl⟩ := hj'
  obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp (hSB ht)
  have hne : ((LinearMap.ker α : Submodule 𝕜 A) : Set A).Nonempty :=
    ⟨0, (LinearMap.ker α).zero_mem⟩
  have hlow : ‖s‖ ≤ Metric.infDist (s - j) ((LinearMap.ker α : Submodule 𝕜 A) : Set A) := by
    rw [Metric.le_infDist hne]
    intro k hk
    rw [dist_eq_norm]
    have hmem : j + k ∈ JA := JA.add_mem hj (hker hk)
    have := hJA s hs (j + k) hmem
    rw [sub_add_eq_sub_sub] at this
    exact this
  have hval : ‖α s - α j‖ = Metric.infDist (s - j)
      ((LinearMap.ker α : Submodule 𝕜 A) : Set A) := by
    rw [← map_sub, hquot]
  rw [hiso s hs, hval]
  exact hlow

/-- If the target boundary ideal is greatest, a complete quotient link is automatically escape
free. -/
theorem map_le_of_isGreatest (α : A →ₗ[𝕜] B) {SA JA : Submodule 𝕜 A} {SB JB : Submodule 𝕜 B}
    (hquot : ∀ x : A, ‖α x‖ = Metric.infDist x ((LinearMap.ker α : Submodule 𝕜 A) : Set A))
    (hker : LinearMap.ker α ≤ JA) (hSB : SB ≤ SA.map α) (hiso : ∀ s ∈ SA, ‖α s‖ = ‖s‖)
    (hJA : IsBoundaryIdeal SA JA)
    (hJB : IsGreatest {K : Submodule 𝕜 B | IsBoundaryIdeal SB K} JB) :
    JA.map α ≤ JB :=
  hJB.2 (isBoundaryIdeal_map_of_quotient α hquot hker hSB hiso hJA)

end Link

/-! ## Recursive lifting along a deficit-free tower -/

section Lifting

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]
variable {α : ∀ n, A (n + 1) →ₗ[𝕜] A n} {J : ∀ n, Submodule 𝕜 (A n)}

/-- The chosen upward tower of ideal lifts over a bottom element. -/
noncomputable def upLift (hdef : ∀ n, ∀ x ∈ J n, ∃ y ∈ J (n + 1), α n y = x)
    {j : A 0} (hj : j ∈ J 0) : ∀ n, {x : A n // x ∈ J n}
  | 0 => ⟨j, hj⟩
  | (n + 1) =>
    ⟨(hdef n (upLift hdef hj n).1 (upLift hdef hj n).2).choose,
     (hdef n (upLift hdef hj n).1 (upLift hdef hj n).2).choose_spec.1⟩

theorem upLift_zero (hdef : ∀ n, ∀ x ∈ J n, ∃ y ∈ J (n + 1), α n y = x) {j : A 0}
    (hj : j ∈ J 0) : (upLift hdef hj 0).1 = j := rfl

theorem alpha_upLift_succ (hdef : ∀ n, ∀ x ∈ J n, ∃ y ∈ J (n + 1), α n y = x) {j : A 0}
    (hj : j ∈ J 0) (n : ℕ) : α n (upLift hdef hj (n + 1)).1 = (upLift hdef hj n).1 :=
  (hdef n (upLift hdef hj n).1 (upLift hdef hj n).2).choose_spec.2

/-- **Recursive lifting.**  In a tower whose restricted ideal maps are surjective, every bottom
ideal element is the bottom coordinate of a coherent sequence lying in every stage ideal.  The
same recursion at a shifted starting stage gives the statement at any stage. -/
theorem exists_coherent_lift (hdef : ∀ n, ∀ x ∈ J n, ∃ y ∈ J (n + 1), α n y = x) {j : A 0}
    (hj : j ∈ J 0) :
    ∃ a : ∀ m, A m, (∀ n, α n (a (n + 1)) = a n) ∧ (∀ n, a n ∈ J n) ∧ a 0 = j :=
  ⟨fun m => (upLift hdef hj m).1, alpha_upLift_succ hdef hj,
    fun n => (upLift hdef hj n).2, upLift_zero hdef hj⟩

end Lifting

end ShilovLocal

end GaloisForLFunctions.HTGeometry
