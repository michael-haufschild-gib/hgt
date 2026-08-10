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

/-- The quotient norm of a class is the distance to the submodule. -/
theorem norm_mkQ_eq_infDist (J : Submodule 𝕜 A) (x : A) :
    ‖J.mkQ x‖ = Metric.infDist x (J : Set A) :=
  QuotientAddGroup.norm_mk x

/-- **The boundary condition is isometry of the quotient map on `S`.**  This is the definition the
`C^*`-theoretic notion of a boundary ideal specialises to. -/
theorem isBoundaryIdeal_iff_norm_mkQ (S J : Submodule 𝕜 A) :
    IsBoundaryIdeal S J ↔ ∀ s ∈ S, ‖J.mkQ s‖ = ‖s‖ := by
  rw [isBoundaryIdeal_iff_le_infDist]
  refine forall_congr' fun s => forall_congr' fun _ => ?_
  rw [norm_mkQ_eq_infDist]
  constructor
  · intro h
    refine le_antisymm ?_ h
    have hz := Metric.infDist_le_dist_of_mem (x := s) J.zero_mem
    rwa [dist_zero_right] at hz
  · intro h
    exact h.ge

/-- The relative boundary condition is the boundary condition in the quotient. -/
theorem infDist_le_infDist_sub_iff (S J₁ J₂ : Submodule 𝕜 A) :
    (∀ s ∈ S, ∀ j ∈ J₂,
        Metric.infDist s (J₁ : Set A) ≤ Metric.infDist (s - j) (J₁ : Set A))
      ↔ IsBoundaryIdeal (S.map J₁.mkQ) (J₂.map J₁.mkQ) := by
  constructor
  · rintro h s' hs' j' hj'
    obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hs'
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.mp hj'
    rw [← map_sub, norm_mkQ_eq_infDist, norm_mkQ_eq_infDist]
    exact h s hs j hj
  · intro h s hs j hj
    have := h (J₁.mkQ s) (Submodule.mem_map_of_mem hs) (J₁.mkQ j) (Submodule.mem_map_of_mem hj)
    rwa [← map_sub, norm_mkQ_eq_infDist, norm_mkQ_eq_infDist] at this

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

/-- A boundary ideal meets the system only in null vectors: the quotient map is injective on `S`
up to the seminorm. -/
theorem norm_eq_zero_of_mem_inf {S J : Submodule 𝕜 A} (h : IsBoundaryIdeal S J)
    {x : A} (hxJ : x ∈ J) (hxS : x ∈ S) : ‖x‖ = 0 := by
  have hle := h x hxS x hxJ
  rw [sub_self, norm_zero] at hle
  exact le_antisymm hle (norm_nonneg x)

/-- **Boundary ideals compose.**  If `J₁` is a boundary ideal for `S` and `J₂` shortens no element
of `S` measured modulo `J₁`, then the join `J₁ ⊔ J₂` is again a boundary ideal.  This is the metric
form of the statement that a boundary ideal of the quotient by a boundary ideal is a boundary
ideal. -/
theorem isBoundaryIdeal_sup {S J₁ J₂ : Submodule 𝕜 A} (h₁ : IsBoundaryIdeal S J₁)
    (h₂ : ∀ s ∈ S, ∀ j ∈ J₂,
      Metric.infDist s (J₁ : Set A) ≤ Metric.infDist (s - j) (J₁ : Set A)) :
    IsBoundaryIdeal S (J₁ ⊔ J₂) := by
  intro s hs j hj
  obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := Submodule.mem_sup.mp hj
  have hbase : ‖s‖ ≤ Metric.infDist s (J₁ : Set A) :=
    (isBoundaryIdeal_iff_le_infDist S J₁).mp h₁ s hs
  have hstep : Metric.infDist (s - j₂) (J₁ : Set A) ≤ dist (s - j₂) j₁ :=
    Metric.infDist_le_dist_of_mem hj₁
  rw [dist_eq_norm] at hstep
  have hrw : s - j₂ - j₁ = s - (j₁ + j₂) := by abel
  rw [hrw] at hstep
  have := h₂ s hs j₂ hj₂
  linarith

/-- **Transitivity of the boundary condition.**  A boundary ideal of the quotient by a boundary
ideal joins with it to a boundary ideal. -/
theorem IsBoundaryIdeal.sup_of_quotient {S J₁ J₂ : Submodule 𝕜 A} (h₁ : IsBoundaryIdeal S J₁)
    (h₂ : IsBoundaryIdeal (S.map J₁.mkQ) (J₂.map J₁.mkQ)) : IsBoundaryIdeal S (J₁ ⊔ J₂) :=
  isBoundaryIdeal_sup h₁ ((infDist_le_infDist_sub_iff S J₁ J₂).mpr h₂)

/-- **Transitivity is an equivalence, not a reduction.**  Given a boundary ideal `J₁`, the join
`J₁ ⊔ J₂` is a boundary ideal precisely when the image of `J₂` is one in the quotient.  So the join
problem cannot be bootstrapped by iterating quotients: passing to `A/J₁` restates it rather than
weakening it. -/
theorem isBoundaryIdeal_sup_iff {S J₁ J₂ : Submodule 𝕜 A} (h₁ : IsBoundaryIdeal S J₁) :
    IsBoundaryIdeal S (J₁ ⊔ J₂) ↔ IsBoundaryIdeal (S.map J₁.mkQ) (J₂.map J₁.mkQ) := by
  refine ⟨fun h => (infDist_le_infDist_sub_iff S J₁ J₂).mp ?_, h₁.sup_of_quotient⟩
  intro s hs j hj
  have hle : Metric.infDist s (J₁ : Set A) ≤ ‖s‖ := by
    have hz := Metric.infDist_le_dist_of_mem (x := s) J₁.zero_mem
    rwa [dist_zero_right] at hz
  have hge : ‖s‖ ≤ Metric.infDist s (J₁ : Set A) :=
    (isBoundaryIdeal_iff_le_infDist S J₁).mp h₁ s hs
  have hEq : Metric.infDist s (J₁ : Set A) = ‖s‖ := le_antisymm hle hge
  rw [hEq, Metric.le_infDist ⟨0, J₁.zero_mem⟩]
  intro y hy
  rw [dist_eq_norm, show s - j - y = s - (y + j) by abel]
  exact h s hs (y + j) (Submodule.mem_sup.mpr ⟨y, hy, j, hj, rfl⟩)

/-- If boundary ideals are closed under joins, a maximal one is greatest. -/
theorem isGreatest_of_maximal_of_sup_closed {S : Submodule 𝕜 A}
    (hsup : ∀ J₁ J₂ : Submodule 𝕜 A, IsBoundaryIdeal S J₁ → IsBoundaryIdeal S J₂ →
      IsBoundaryIdeal S (J₁ ⊔ J₂))
    {J : Submodule 𝕜 A} (hJ : Maximal (fun K => IsBoundaryIdeal S K) J) :
    IsGreatest {K : Submodule 𝕜 A | IsBoundaryIdeal S K} J := by
  refine ⟨hJ.1, fun K hK => ?_⟩
  exact le_trans le_sup_right (hJ.2 (hsup J K hJ.1 hK) le_sup_left)

/-- **Maximal boundary ideals exist.**  Zorn's lemma applies because boundary ideals are closed
under directed unions and contain the zero ideal. -/
theorem exists_maximal_isBoundaryIdeal (S : Submodule 𝕜 A) :
    ∃ J : Submodule 𝕜 A, Maximal (fun K => IsBoundaryIdeal S K) J := by
  refine zorn_le₀ {K : Submodule 𝕜 A | IsBoundaryIdeal S K} fun C hC hchain => ?_
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⊥, isBoundaryIdeal_bot S, fun z hz => absurd hz (Set.notMem_empty z)⟩
  · exact ⟨sSup C, isBoundaryIdeal_sSup hne hchain.directedOn fun J hJ => hC hJ,
      fun z hz => le_sSup hz⟩

/-- **Existence of the Shilov ideal, reduced to join-closure.**  Whenever the boundary ideals of
`S` are closed under joins, a greatest one exists.  `isBoundaryIdeal_sup` gives a metric sufficient
condition for that closure, so this isolates exactly what the `C^*`-theoretic construction has to
supply. -/
theorem exists_isGreatest_isBoundaryIdeal {S : Submodule 𝕜 A}
    (hsup : ∀ J₁ J₂ : Submodule 𝕜 A, IsBoundaryIdeal S J₁ → IsBoundaryIdeal S J₂ →
      IsBoundaryIdeal S (J₁ ⊔ J₂)) :
    ∃ J : Submodule 𝕜 A, IsGreatest {K : Submodule 𝕜 A | IsBoundaryIdeal S K} J := by
  obtain ⟨J, hJ⟩ := exists_maximal_isBoundaryIdeal S
  exact ⟨J, isGreatest_of_maximal_of_sup_closed hsup hJ⟩

/-- **The Shilov quotient has trivial Shilov ideal.**  Quotienting by the greatest boundary ideal
leaves a cover in which no nonzero boundary ideal survives, so the construction is idempotent and
the resulting cover is minimal.  The proof is transitivity: a boundary ideal upstairs of the
quotient pulls back to one joined with `J`, which greatestness collapses. -/
theorem isBoundaryIdeal_quotient_eq_bot {S J : Submodule 𝕜 A}
    (hJ : IsGreatest {K : Submodule 𝕜 A | IsBoundaryIdeal S K} J)
    {K : Submodule 𝕜 (A ⧸ J)} (hK : IsBoundaryIdeal (S.map J.mkQ) K) : K = ⊥ := by
  have hsurj : Function.Surjective (J.mkQ) := Submodule.mkQ_surjective J
  have hmap : (K.comap J.mkQ).map J.mkQ = K := Submodule.map_comap_eq_of_surjective hsurj K
  have hsup : IsBoundaryIdeal S (J ⊔ K.comap J.mkQ) :=
    hJ.1.sup_of_quotient (by rw [hmap]; exact hK)
  have hle : K.comap J.mkQ ≤ J := le_trans le_sup_right (hJ.2 hsup)
  rw [← hmap]
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  exact (Submodule.mem_bot 𝕜).mpr ((Submodule.Quotient.mk_eq_zero J).mpr (hle ha))

/-- The greatest boundary ideal — the Shilov ideal — is automatically closed. -/
theorem isClosed_of_isGreatest_isBoundaryIdeal {S J : Submodule 𝕜 A}
    (hJ : IsGreatest {K : Submodule 𝕜 A | IsBoundaryIdeal S K} J) : IsClosed (J : Set A) := by
  have h1 : J.topologicalClosure ≤ J := hJ.2 hJ.1.topologicalClosure
  have h2 : J.topologicalClosure = J := le_antisymm h1 (Submodule.le_topologicalClosure J)
  have h3 := Submodule.isClosed_topologicalClosure J
  rwa [h2] at h3

end Stage

/-! ## The local boundary ideal of a coordinate tower -/

section TowerAlgebraic

variable {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module 𝕜 (A i)]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Module 𝕜 (B i)]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

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

/-- The diagonal representation assembled from stage representations along the coordinates. -/
def diagonalRep (p : ∀ i, E →ₗ[𝕜] A i) (ρ : ∀ i, A i →ₗ[𝕜] B i) : E →ₗ[𝕜] ∀ i, B i where
  toFun a := fun i => ρ i (p i a)
  map_add' a b := by
    funext i
    simp
  map_smul' c a := by
    funext i
    simp

@[simp]
theorem diagonalRep_apply (p : ∀ i, E →ₗ[𝕜] A i) (ρ : ∀ i, A i →ₗ[𝕜] B i) (a : E) (i : ι) :
    diagonalRep p ρ a i = ρ i (p i a) := rfl

/-- **The kernel of the diagonal stage representation is the local ideal.**  This is the card's
`ker ρ = ⋂ pₙ⁻¹(Jₙ) = J_loc`, given that each stage representation has kernel its stage ideal. -/
theorem ker_diagonalRep {p : ∀ i, E →ₗ[𝕜] A i} {ρ : ∀ i, A i →ₗ[𝕜] B i}
    {J : ∀ i, Submodule 𝕜 (A i)} (hker : ∀ i, LinearMap.ker (ρ i) = J i) :
    LinearMap.ker (diagonalRep p ρ) = localIdeal p J := by
  ext a
  rw [LinearMap.mem_ker, mem_localIdeal, funext_iff]
  refine forall_congr' fun i => ?_
  rw [diagonalRep_apply, Pi.zero_apply, ← LinearMap.mem_ker, hker i]

/-- **Faithfulness of the local representation.**  The diagonal stage representation descends to an
injective map on the local envelope. -/
theorem injective_liftQ_diagonalRep {p : ∀ i, E →ₗ[𝕜] A i} {ρ : ∀ i, A i →ₗ[𝕜] B i}
    {J : ∀ i, Submodule 𝕜 (A i)} (hker : ∀ i, LinearMap.ker (ρ i) = J i) :
    Function.Injective ((localIdeal p J).liftQ (diagonalRep p ρ)
      (le_of_eq (ker_diagonalRep hker).symm)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot]
  exact le_of_eq (ker_diagonalRep hker)

end TowerAlgebraic

/-! ## Local boundary ideals -/

section TowerMetric

variable {ι : Type*} {A : ι → Type*} [∀ i, SeminormedAddCommGroup (A i)]
  [∀ i, NormedSpace 𝕜 (A i)]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

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

/-- Coordinate inclusion already forces containment in the local ideal.  This is the step that
upgrades the classical coordinate inclusion `closure(pₙ(H)) ⊆ Jₙ` to a statement about `H`. -/
theorem le_localIdeal_of_closure_le {p : ∀ i, E →ₗ[𝕜] A i} {J : ∀ i, Submodule 𝕜 (A i)}
    {H : Submodule 𝕜 E} (h : ∀ i, (H.map (p i)).topologicalClosure ≤ J i) :
    H ≤ localIdeal p J := by
  intro a ha
  rw [mem_localIdeal]
  intro i
  exact h i (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ha))

/-- The local ideal of closed stage ideals is closed, so the local envelope is separated. -/
theorem isClosed_localIdeal {p : ∀ i, E →ₗ[𝕜] A i} {J : ∀ i, Submodule 𝕜 (A i)}
    (hp : ∀ i, Continuous (p i)) (hJ : ∀ i, IsClosed ((J i : Set (A i)))) :
    IsClosed ((localIdeal p J : Set E)) := by
  have hset : (localIdeal p J : Set E) = ⋂ i, (p i) ⁻¹' (J i : Set (A i)) := by
    ext a
    simp [mem_localIdeal, Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun i => (hJ i).preimage (hp i)

/-- **Representation-free identification of the local Shilov ideal.**  If every stage ideal is the
greatest boundary ideal of its stage system, then the ideal it cuts out along the coordinate maps
is the greatest local boundary ideal. -/
theorem localIdeal_isGreatest {p : ∀ i, E →ₗ[𝕜] A i} {S J : ∀ i, Submodule 𝕜 (A i)}
    (hJ : ∀ i, IsGreatest {K : Submodule 𝕜 (A i) | IsBoundaryIdeal (S i) K} (J i)) :
    IsGreatest {H : Submodule 𝕜 E | IsLocalBoundaryIdeal p S H} (localIdeal p J) := by
  refine ⟨isLocalBoundaryIdeal_localIdeal
    (fun i => isClosed_of_isGreatest_isBoundaryIdeal (hJ i)) (fun i => (hJ i).1),
    fun H hH => le_localIdeal_of_isLocalBoundaryIdeal (fun i K hK => (hJ i).2 hK) hH⟩

/-- **Triviality of the local Shilov ideal over a tower of envelopes.**  If no stage system has a
nonzero boundary ideal in its stage cover, and the coordinates are jointly injective, then the only
local boundary ideal is zero.  This is the step by which the inverse limit of the stage envelopes
is itself a cover with trivial local Shilov ideal. -/
theorem eq_bot_of_isLocalBoundaryIdeal {p : ∀ i, E →ₗ[𝕜] A i} {S : ∀ i, Submodule 𝕜 (A i)}
    (hstage : ∀ i, ∀ K : Submodule 𝕜 (A i), IsBoundaryIdeal (S i) K → K = ⊥)
    (hinj : ∀ a : E, (∀ i, p i a = 0) → a = 0)
    {H : Submodule 𝕜 E} (hH : IsLocalBoundaryIdeal p S H) : H = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  refine (Submodule.mem_bot 𝕜).mpr (hinj a fun i => ?_)
  have hbot : (H.map (p i)).topologicalClosure = ⊥ := hstage i _ (hH i)
  have hmem : p i a ∈ (H.map (p i)).topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ha)
  rw [hbot] at hmem
  exact (Submodule.mem_bot 𝕜).mp hmem

/-- The local Shilov ideal of a tower of Shilov stages is closed. -/
theorem isClosed_localIdeal_of_isGreatest {p : ∀ i, E →ₗ[𝕜] A i} {S J : ∀ i, Submodule 𝕜 (A i)}
    (hp : ∀ i, Continuous (p i))
    (hJ : ∀ i, IsGreatest {K : Submodule 𝕜 (A i) | IsBoundaryIdeal (S i) K} (J i)) :
    IsClosed ((localIdeal p J : Set E)) :=
  isClosed_localIdeal hp fun i => isClosed_of_isGreatest_isBoundaryIdeal (hJ i)

end TowerMetric

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

/-! ## Joins genuinely fail without extra structure -/

section NoGo

/-- The diagonal of the sup-normed plane. -/
noncomputable def diagLine : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((1 : ℝ), (1 : ℝ))}

/-- The first coordinate axis. -/
noncomputable def firstAxis : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((1 : ℝ), (0 : ℝ))}

/-- The second coordinate axis. -/
noncomputable def secondAxis : Submodule ℝ (ℝ × ℝ) := Submodule.span ℝ {((0 : ℝ), (1 : ℝ))}

theorem isBoundaryIdeal_firstAxis : IsBoundaryIdeal diagLine firstAxis := by
  intro s hs j hj
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hj
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_sub_mk, sub_zero,
    Prod.norm_def, Real.norm_eq_abs, sup_le_iff, le_sup_iff]
  exact Or.inr ⟨le_rfl, le_rfl⟩

theorem isBoundaryIdeal_secondAxis : IsBoundaryIdeal diagLine secondAxis := by
  intro s hs j hj
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hj
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_sub_mk, sub_zero,
    Prod.norm_def, Real.norm_eq_abs, sup_le_iff, le_sup_iff]
  exact Or.inl ⟨le_rfl, le_rfl⟩

/-- **Boundary ideals are not closed under joins.**  In the sup-normed plane both coordinate axes
are boundary ideals for the diagonal, but their join is everything, which shortens the diagonal to
zero.  Hence no purely metric axiom produces a greatest boundary ideal: the hypothesis of
`exists_isGreatest_isBoundaryIdeal` cannot be removed, and the `C^*`-theoretic input is necessary
rather than merely convenient. -/
theorem not_isBoundaryIdeal_sup_axes :
    ¬ IsBoundaryIdeal diagLine (firstAxis ⊔ secondAxis) := by
  intro h
  have hs : ((1 : ℝ), (1 : ℝ)) ∈ diagLine := Submodule.mem_span_singleton_self _
  have hj : ((1 : ℝ), (1 : ℝ)) ∈ firstAxis ⊔ secondAxis :=
    Submodule.mem_sup.mpr ⟨((1 : ℝ), (0 : ℝ)), Submodule.mem_span_singleton_self _,
      ((0 : ℝ), (1 : ℝ)), Submodule.mem_span_singleton_self _, by norm_num⟩
  have hcon := h _ hs _ hj
  simp only [sub_self, norm_zero, Prod.norm_def, Real.norm_eq_abs, abs_one, sup_le_iff] at hcon
  linarith [hcon.1]

/-- The metric family of boundary ideals therefore need not be a principal order ideal. -/
theorem not_exists_isGreatest_isBoundaryIdeal_diagLine :
    ¬ ∃ J : Submodule ℝ (ℝ × ℝ), IsGreatest {K | IsBoundaryIdeal diagLine K} J := by
  rintro ⟨J, hJmem, hJmax⟩
  exact not_isBoundaryIdeal_sup_axes
    (hJmem.mono (sup_le (hJmax isBoundaryIdeal_firstAxis) (hJmax isBoundaryIdeal_secondAxis)))

end NoGo

/-! ## Triviality of the Shilov ideal does not pin down the cover -/

section Generation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A]

/-- A boundary ideal meets the system trivially. -/
theorem inf_eq_bot_of_isBoundaryIdeal {S J : Submodule 𝕜 A} (h : IsBoundaryIdeal S J) :
    J ⊓ S = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hzero : ‖x‖ = 0 := norm_eq_zero_of_mem_inf h hx.1 hx.2
  exact (Submodule.mem_bot 𝕜).mpr (norm_eq_zero.mp hzero)

/-- **The system is always its own cover with trivial Shilov ideal.**  So triviality of the Shilov
ideal alone cannot characterise the envelope: without a hypothesis that the ambient space is
generated by the system, a cover with no nonzero boundary ideal need not be the envelope.  This
locates exactly what the `C^*`-theoretic uniqueness statement adds — generation, not merely
minimality. -/
theorem eq_bot_of_isBoundaryIdeal_top {J : Submodule 𝕜 A} (h : IsBoundaryIdeal ⊤ J) : J = ⊥ := by
  have := inf_eq_bot_of_isBoundaryIdeal h
  rwa [inf_top_eq] at this

end Generation

/-! ## Generation makes the envelope comparison unique -/

section Uniqueness

variable {B : Type*} [Ring B]

/-- The ambient algebra is generated by the system. -/
def Generates {A : Type*} [Ring A] [Algebra 𝕜 A] (S : Submodule 𝕜 A) : Prop :=
  Algebra.adjoin 𝕜 (S : Set A) = ⊤

/-- **Generation makes an envelope comparison unique.**  Two algebra maps agreeing on a generating
system coincide, so the content of a comparison theorem such as the card's `Θ` is existence of the
map, never its uniqueness. -/
theorem eq_of_eqOn_generates {A : Type*} [Ring A] [Algebra 𝕜 A] [Algebra 𝕜 B]
    {S : Submodule 𝕜 A} (hgen : Generates S) {φ ψ : A →ₐ[𝕜] B}
    (h : ∀ s ∈ S, φ s = ψ s) : φ = ψ :=
  AlgHom.ext_of_adjoin_eq_top hgen fun x hx => h x hx

end Uniqueness

section Existence

variable {A B : Type*} [Ring A] [Algebra 𝕜 A] [Ring B] [Algebra 𝕜 B] [TopologicalSpace B]
  [IsTopologicalRing B]

/-- **Existence from a closed range.**  A homomorphism whose range is closed and contains a
topologically generating set is onto.

This is where an envelope comparison map becomes surjective.  In the `C^*` setting the range of a
`*`-homomorphism is automatically closed, so the analytic content of an envelope theorem is
closedness of the range together with generation — not the algebraic comparison itself. -/
theorem surjective_of_isClosed_range_of_generates (φ : A →ₐ[𝕜] B) {T : Set B}
    (hT : T ⊆ Set.range φ) (hclosed : IsClosed (Set.range φ))
    (hgen : (Algebra.adjoin 𝕜 T).topologicalClosure = ⊤) :
    Function.Surjective φ := by
  have hle : Algebra.adjoin 𝕜 T ≤ φ.range := Algebra.adjoin_le hT
  have hclosed' : IsClosed ((φ.range : Subalgebra 𝕜 B) : Set B) := hclosed
  have h2 : (Algebra.adjoin 𝕜 T).topologicalClosure ≤ φ.range :=
    Subalgebra.topologicalClosure_minimal hle hclosed'
  rw [hgen] at h2
  intro y
  exact h2 (Algebra.mem_top)

end Existence

section Comparison

variable {A B : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [NormedRing B] [NormedAlgebra 𝕜 B]

/-- **The envelope comparison is onto once it is isometric.**  An isometric homomorphism from a
complete algebra has closed range, so if its range contains a topologically generating set it is
surjective, hence bijective.

For the card's `Θ` this closes the chain: injectivity is `mem_localIdeal_iff_mkQ_eq_zero`, and an
injective `*`-homomorphism of `C^*`-algebras is isometric, so the only remaining input is
generation. -/
theorem surjective_of_isometry_of_generates (φ : A →ₐ[𝕜] B) (hiso : Isometry φ) {T : Set B}
    (hT : T ⊆ Set.range φ) (hgen : (Algebra.adjoin 𝕜 T).topologicalClosure = ⊤) :
    Function.Surjective φ :=
  surjective_of_isClosed_range_of_generates φ hT hiso.isClosedEmbedding.isClosed_range hgen

/-- The comparison is then bijective. -/
theorem bijective_of_isometry_of_generates (φ : A →ₐ[𝕜] B) (hiso : Isometry φ) {T : Set B}
    (hT : T ⊆ Set.range φ) (hgen : (Algebra.adjoin 𝕜 T).topologicalClosure = ⊤) :
    Function.Bijective φ :=
  ⟨hiso.injective, surjective_of_isometry_of_generates φ hiso hT hgen⟩

end Comparison

/-! ## Coordinatewise approximation in a coordinate tower -/

section Approximation

variable {A : ℕ → Type*} [∀ n, SeminormedAddCommGroup (A n)]

/-- **Coordinatewise approximation reaches a closed set.**  If every finite set of coordinates of
`a` can be approximated simultaneously from a closed set, then `a` belongs to it.

This is the topological core of a generation hypothesis for a coordinate tower: generating means
approximating in finitely many stage seminorms at once, and the projective topology then delivers
the limit.  Note the algebraic analogue is false — coordinatewise surjectivity alone does not force
equality — so the closure really is doing work. -/
theorem mem_of_coordinatewise_approx {C : Set (∀ n, A n)} (hC : IsClosed C) {a : ∀ n, A n}
    (h : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ c ∈ C, ∀ k ≤ n, ‖c k - a k‖ < ε) : a ∈ C := by
  choose c hcC hcapp using fun m : ℕ => h m (1 / (m + 1)) (by positivity)
  have htend : Filter.Tendsto c Filter.atTop (nhds a) := by
    rw [tendsto_pi_nhds]
    intro k
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨max k N, fun m hm => ?_⟩
    have hmk : k ≤ m := le_trans (le_max_left _ _) hm
    have hmN : N ≤ m := le_trans (le_max_right _ _) hm
    have happ := hcapp m k hmk
    have hlt : (1 : ℝ) / (m + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      have hNm : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hmN
      have hinv : 1 / ε < (m : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hε] at hinv
      linarith
    rw [dist_eq_norm]
    linarith
  exact hC.mem_of_tendsto htend (Filter.Eventually.of_forall hcC)

end Approximation

end ShilovLocal

end GaloisForLFunctions.HTGeometry
