import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Real.Basic

/-!
# Endogenous viability and observer exchange

Closed decreasing source horizons commute with observation across compact fibres.  If finite
observed survival has no global source witness, every compact part of the fibre eventually
disappears and every compact-sublevel source cost diverges.  Compact legal-control spaces also
make the endogenous viability predecessor commute with a decreasing closed horizon, producing the
greatest viable fixed point and permanent finite plateaux.

No project postulate, computation tactic, or unproved premise is used.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

section ObserverExchange

variable {X Y : Type*} [TopologicalSpace X]

/-- A compact source fibre turns compatible finite observed survival into one global source
witness. -/
theorem observer_iInter_mem_of_compact_fiber
    (q : X → Y) (W : ℕ → Set X) (y : Y)
    (hclosed : ∀ n, IsClosed (W n))
    (hmono : ∀ n, W (n + 1) ⊆ W n)
    (hy : y ∈ ⋂ n, q '' W n)
    (hfiber : IsCompact (q ⁻¹' {y})) :
    y ∈ q '' (⋂ n, W n) := by
  let F : Set X := q ⁻¹' {y}
  have hF : IsCompact F := hfiber
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF
  let C : ℕ → Set F := fun n => Subtype.val ⁻¹' W n
  have hCn : ∀ n, (C n).Nonempty := by
    intro n
    rcases (Set.mem_iInter.mp hy n) with ⟨x, hxW, hxq⟩
    refine ⟨⟨x, ?_⟩, hxW⟩
    simp [F, hxq]
  have hCc : ∀ n, IsClosed (C n) := by
    intro n
    exact (hclosed n).preimage continuous_subtype_val
  have hCd : ∀ n, C (n + 1) ⊆ C n := by
    intro n x hx
    exact hmono n hx
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hCd hCn (hCc 0).isCompact hCc
  refine ⟨x, ?_, ?_⟩
  · exact Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx n
  · exact x.property

/-- Observation commutes with every closed decreasing cofinal horizon when all observer fibres are
compact. -/
theorem observerImage_iInter_eq_iInter_image_of_compact_fiber
    (q : X → Y) (W : ℕ → Set X)
    (hclosed : ∀ n, IsClosed (W n))
    (hmono : ∀ n, W (n + 1) ⊆ W n)
    (hfiber : ∀ y, IsCompact (q ⁻¹' {y})) :
    q '' (⋂ n, W n) = ⋂ n, q '' W n := by
  apply Set.Subset.antisymm
  · exact Set.image_iInter_subset W q
  · intro y hy
    exact observer_iInter_mem_of_compact_fiber q W y hclosed hmono hy (hfiber y)

/-- If an observed value has no global source witness, every compact part of its source fibre is
disjoint from all sufficiently late horizons. -/
theorem noGlobalObserverLaw_eventually_disjoint_compact
    (q : X → Y) (W : ℕ → Set X) (y : Y)
    (hclosed : ∀ n, IsClosed (W n))
    (hmono : ∀ n, W (n + 1) ⊆ W n)
    (hglobal : y ∉ q '' (⋂ n, W n))
    {K : Set X} (hK : IsCompact K) (hKfiber : K ⊆ q ⁻¹' {y}) :
    ∃ N, ∀ n, N ≤ n → K ∩ W n = ∅ := by
  by_contra h
  push Not at h
  have hWantitone : Antitone W := antitone_nat_of_succ_le hmono
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : ℕ → Set K := fun n => Subtype.val ⁻¹' W n
  have hnon : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨m, hnm, hm⟩ := h n
    obtain ⟨x, hxK, hxW⟩ := hm
    exact ⟨⟨x, hxK⟩, hWantitone hnm hxW⟩
  have hcl : ∀ n, IsClosed (C n) := by
    intro n
    exact (hclosed n).preimage continuous_subtype_val
  have hdec : ∀ n, C (n + 1) ⊆ C n := by
    intro n x hx
    exact hmono n hx
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    C hdec hnon (hcl 0).isCompact hcl
  apply hglobal
  refine ⟨x, ?_, ?_⟩
  · exact Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx n
  · exact hKfiber x.property

/-- A source cost with compact fibrewise sublevels eventually exceeds every finite threshold when
the observed value has no global source witness. -/
theorem noGlobalObserverLaw_properCost_escape
    (q : X → Y) (W : ℕ → Set X) (y : Y) (P : X → ℝ)
    (hclosed : ∀ n, IsClosed (W n))
    (hmono : ∀ n, W (n + 1) ⊆ W n)
    (hglobal : y ∉ q '' (⋂ n, W n))
    (hproper : ∀ R, IsCompact {x | q x = y ∧ P x ≤ R}) :
    ∀ R, ∃ N, ∀ n, N ≤ n → ∀ x, q x = y → x ∈ W n → R < P x := by
  intro R
  let K : Set X := {x | q x = y ∧ P x ≤ R}
  obtain ⟨N, hN⟩ := noGlobalObserverLaw_eventually_disjoint_compact
    q W y hclosed hmono hglobal (hproper R) (K := K) (by
      intro x hx
      simpa [K] using hx.1)
  refine ⟨N, fun n hn x hxq hxW => ?_⟩
  by_contra hle
  have hxK : x ∈ K := ⟨hxq, le_of_not_gt hle⟩
  have hx : x ∈ K ∩ W n := ⟨hxK, hxW⟩
  rw [hN n hn] at hx
  exact hx

/-- Finite observed survival without global survival forces failure of closed admission, compact
source fibre, or coherent decreasing horizons. -/
theorem finiteHorizon_promotion_trilemma
    (q : X → Y) (W : ℕ → Set X) (y : Y)
    (hfinite : y ∈ ⋂ n, q '' W n)
    (hglobal : y ∉ q '' (⋂ n, W n)) :
    (¬ ∀ n, IsClosed (W n)) ∨
      ¬ IsCompact (q ⁻¹' {y}) ∨
      ¬ ∀ n, W (n + 1) ⊆ W n := by
  by_contra h
  push Not at h
  exact hglobal (observer_iInter_mem_of_compact_fiber q W y h.1 h.2.2 hfinite h.2.1)

end ObserverExchange

section EndogenousPredecessor

variable {X U C : Type*}

/-- Controls that are legal now and keep every generated challenge inside a candidate future set. -/
def endogenousControlSet (legal : X → U → Prop) (challenge : X → U → Set C)
    (next : X → U → C → X) (A : Set X) (x : X) : Set U :=
  {u | legal x u ∧ ∀ c ∈ challenge x u, next x u c ∈ A}

/-- One endogenous viability predecessor step. -/
def endogenousPredecessor (S : Set X) (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    (A : Set X) : Set X :=
  {x | x ∈ S ∧ (endogenousControlSet legal challenge next A x).Nonempty}

theorem endogenousControlSet_mono (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    {A B : Set X} (hAB : A ⊆ B) (x : X) :
    endogenousControlSet legal challenge next A x ⊆
      endogenousControlSet legal challenge next B x := by
  intro u hu
  exact ⟨hu.1, fun c hc => hAB (hu.2 c hc)⟩

theorem endogenousPredecessor_mono (S : Set X) (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    {A B : Set X} (hAB : A ⊆ B) :
    endogenousPredecessor S legal challenge next A ⊆
      endogenousPredecessor S legal challenge next B := by
  intro x hx
  exact ⟨hx.1, hx.2.mono (endogenousControlSet_mono legal challenge next hAB x)⟩

theorem endogenousControlSet_iInter (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    (A : ℕ → Set X) (x : X) :
    endogenousControlSet legal challenge next (⋂ n, A n) x =
      ⋂ n, endogenousControlSet legal challenge next (A n) x := by
  ext u
  simp only [endogenousControlSet, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · rintro ⟨hlegal, hnext⟩ n
    exact ⟨hlegal, fun c hc => hnext c hc n⟩
  · intro h
    exact ⟨(h 0).1, fun c hc n => (h n).2 c hc⟩

end EndogenousPredecessor

section PredecessorExchange

variable {X U C : Type*} [TopologicalSpace X] [TopologicalSpace U]

/-- Compact legal-control fibres make endogenous predecessor formation commute with a decreasing
closed cofinal horizon. -/
theorem endogenousPredecessor_iInter [CompactSpace U]
    (S : Set X) (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    (A : ℕ → Set X) (hAclosed : ∀ n, IsClosed (A n))
    (hAmono : ∀ n, A (n + 1) ⊆ A n)
    (hGclosed : ∀ (B : Set X), IsClosed B → ∀ x,
      IsClosed (endogenousControlSet legal challenge next B x)) :
    endogenousPredecessor S legal challenge next (⋂ n, A n) =
      ⋂ n, endogenousPredecessor S legal challenge next (A n) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iInter.mpr fun n => endogenousPredecessor_mono S legal challenge next
      (Set.iInter_subset A n) hx
  · intro x hx
    have hxall := Set.mem_iInter.mp hx
    have hnon : ∀ n, (endogenousControlSet legal challenge next (A n) x).Nonempty :=
      fun n => (hxall n).2
    have hcl : ∀ n, IsClosed (endogenousControlSet legal challenge next (A n) x) :=
      fun n => hGclosed (A n) (hAclosed n) x
    have hdec : ∀ n,
        endogenousControlSet legal challenge next (A (n + 1)) x ⊆
          endogenousControlSet legal challenge next (A n) x :=
      fun n => endogenousControlSet_mono legal challenge next (hAmono n) x
    obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => endogenousControlSet legal challenge next (A n) x)
      hdec hnon (hcl 0).isCompact hcl
    refine ⟨(hxall 0).1, u, ?_⟩
    rw [endogenousControlSet_iInter]
    exact hu

end PredecessorExchange

section ViabilityFixedPoint

variable {Z : Type*}

/-- Finite-horizon viability approximants of a predecessor. -/
def viabilityHorizon (Φ : Set Z → Set Z) (S : Set Z) : ℕ → Set Z
  | 0 => S
  | n + 1 => Φ (viabilityHorizon Φ S n)

@[simp] theorem viabilityHorizon_zero (Φ : Set Z → Set Z) (S : Set Z) :
    viabilityHorizon Φ S 0 = S := rfl

@[simp] theorem viabilityHorizon_succ (Φ : Set Z → Set Z) (S : Set Z) (n : ℕ) :
    viabilityHorizon Φ S (n + 1) = Φ (viabilityHorizon Φ S n) := rfl

theorem viabilityHorizon_antitone (Φ : Set Z → Set Z) (S : Set Z)
    (hΦmono : Monotone Φ) (hΦS : Φ S ⊆ S) : Antitone (viabilityHorizon Φ S) := by
  apply antitone_nat_of_succ_le
  intro n
  induction n with
  | zero => exact hΦS
  | succ n ih => exact hΦmono ih

/-- Once a fixed predecessor iteration reaches a plateau, every later horizon is the same. -/
theorem viabilityHorizon_plateau (Φ : Set Z → Set Z) (S : Set Z) (n : ℕ)
    (hplateau : viabilityHorizon Φ S (n + 1) = viabilityHorizon Φ S n) :
    ∀ k, viabilityHorizon Φ S (n + k) = viabilityHorizon Φ S n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, viabilityHorizon_succ, ih]
      exact hplateau

/-- Cofinal predecessor exchange makes the infinite horizon the greatest post-fixed law. -/
theorem viabilityHorizon_greatest_fixedPoint (Φ : Set Z → Set Z) (S : Set Z)
    (hΦmono : Monotone Φ) (hΦS : Φ S ⊆ S)
    (hexchange : Φ (⋂ n, viabilityHorizon Φ S n) =
      ⋂ n, Φ (viabilityHorizon Φ S n)) :
    Φ (⋂ n, viabilityHorizon Φ S n) = ⋂ n, viabilityHorizon Φ S n ∧
      ∀ A : Set Z, A ⊆ S → A ⊆ Φ A → A ⊆ ⋂ n, viabilityHorizon Φ S n := by
  have hanti := viabilityHorizon_antitone Φ S hΦmono hΦS
  have hshift : (⋂ n, Φ (viabilityHorizon Φ S n)) =
      ⋂ n, viabilityHorizon Φ S n := by
    apply Set.Subset.antisymm
    · intro x hx
      apply Set.mem_iInter.mpr
      intro n
      cases n with
      | zero => exact hanti (Nat.zero_le 1) (Set.mem_iInter.mp hx 0)
      | succ n => exact Set.mem_iInter.mp hx n
    · intro x hx
      exact Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx (n + 1)
  constructor
  · exact hexchange.trans hshift
  · intro A hAS hpost
    have hAn : ∀ n, A ⊆ viabilityHorizon Φ S n := by
      intro n
      induction n with
      | zero => exact hAS
      | succ n ih => exact fun x hx => hΦmono ih (hpost hx)
    exact fun x hx => Set.mem_iInter.mpr fun n => hAn n hx

end ViabilityFixedPoint

section EndogenousFixedPoint

variable {X U C : Type*} [TopologicalSpace X] [TopologicalSpace U] [CompactSpace U]

/-- Closed admission and compact legal-control fibres make the cofinal endogenous horizon the
greatest viable law. -/
theorem endogenousViability_greatest_fixedPoint
    (S : Set X) (legal : X → U → Prop)
    (challenge : X → U → Set C) (next : X → U → C → X)
    (hSclosed : IsClosed S)
    (hGclosed : ∀ (B : Set X), IsClosed B → ∀ x,
      IsClosed (endogenousControlSet legal challenge next B x))
    (hΦclosed : ∀ (B : Set X), IsClosed B →
      IsClosed (endogenousPredecessor S legal challenge next B)) :
    let Φ := endogenousPredecessor S legal challenge next
    let W := viabilityHorizon Φ S
    Φ (⋂ n, W n) = ⋂ n, W n ∧
      ∀ A : Set X, A ⊆ S → A ⊆ Φ A → A ⊆ ⋂ n, W n := by
  dsimp only
  let Φ : Set X → Set X := endogenousPredecessor S legal challenge next
  let W : ℕ → Set X := viabilityHorizon Φ S
  have hΦmono : Monotone Φ := by
    intro A B hAB
    exact endogenousPredecessor_mono S legal challenge next hAB
  have hΦS : Φ S ⊆ S := fun _ hx => hx.1
  have hWanti : Antitone W := viabilityHorizon_antitone Φ S hΦmono hΦS
  have hWclosed : ∀ n, IsClosed (W n) := by
    intro n
    induction n with
    | zero => exact hSclosed
    | succ n ih => exact hΦclosed (W n) ih
  have hexchange : Φ (⋂ n, W n) = ⋂ n, Φ (W n) := by
    exact endogenousPredecessor_iInter S legal challenge next W hWclosed
      (fun n => hWanti (Nat.le_succ n)) hGclosed
  exact viabilityHorizon_greatest_fixedPoint Φ S hΦmono hΦS hexchange

end EndogenousFixedPoint

end GaloisForLFunctions.HTGeometry
