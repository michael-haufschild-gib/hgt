import GaloisForLFunctions.RHTower.DeningerRootDisjointFactors

/-!
# A stage carrying a family of elements

For a free group of rank at least two the tower adjoins roots to many elements in turn, so a stage
carries a family and the step roots one member of it, replacing that member by the root and the
others by their images.  The invariant is the one the inheritance theorems preserve.

* `DeningerFamilyStage`, `DeningerFamilyGood`, `deningerFamilyStep` : the tower data.
* `deningerFamilyStep_uniqueRoots`, `deningerFamilyStep_torsionFree` : the two global properties of
  the step.
* `deningerFamilyStep_order` : every member of the new family has infinite order.
* `deningerFamilyStep_central` : every member of the new family is its own centralizer.
* `deningerFamilyStep_isolated` : every member of the new family generates an isolated subgroup.
* `deningerFamilyStep_disjoint` : different members of the new family stay disjoint.
* `deningerFamilyStep_good` : the step preserves the invariant.
-/

namespace RHTower

open Monoid Monoid.PushoutI

universe u

namespace RootAdjunction

/-- A stage of a tower which roots a family of elements. -/
structure DeningerFamilyStage : Type (u + 1) where
  /-- The underlying group of the stage. -/
  carrier : Type u
  /-- Its group structure. -/
  [group : Group carrier]
  /-- The family of elements still waiting for their roots. -/
  fam : ℕ → carrier

attribute [instance] DeningerFamilyStage.group

/-- The invariant carried along the tower. -/
structure DeningerFamilyGood (S : DeningerFamilyStage.{u}) : Prop where
  /-- The stage has unique roots. -/
  uniqueRoots : ∀ (x y : S.carrier) (n : ℕ), 0 < n → x ^ n = y ^ n → x = y
  /-- The stage is torsion free. -/
  torsionFree : ∀ (x : S.carrier) (n : ℕ), 0 < n → x ^ n = 1 → x = 1
  /-- Every member of the family has infinite order. -/
  order : ∀ q : ℕ, ∀ n : ℤ, (S.fam q) ^ n = 1 → n = 0
  /-- Every member is its own centralizer. -/
  central : ∀ q : ℕ, ∀ x : S.carrier, x * S.fam q * x⁻¹ = S.fam q →
    x ∈ Subgroup.zpowers (S.fam q)
  /-- Every member generates an isolated subgroup. -/
  isolated : ∀ q : ℕ, ∀ (y : S.carrier) (n : ℕ), 0 < n →
    y ^ n ∈ Subgroup.zpowers (S.fam q) → y ∈ Subgroup.zpowers (S.fam q)
  /-- Different members stay disjoint under conjugation. -/
  disjoint : ∀ q r : ℕ, q ≠ r → ∀ (x : S.carrier) (c : ℤ), c ≠ 0 → ∀ k : ℤ,
    x⁻¹ * (S.fam q) ^ c * x ≠ (S.fam r) ^ k

/-- **The step of the tower**: adjoin an `m`-th root to the `p`-th member of the family, and replace
that member by the root and the others by their images. -/
noncomputable def deningerFamilyStep (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ) :
    DeningerFamilyStage.{u} :=
  ⟨PushoutI (deningerRootMap S.carrier (S.fam p) m),
    fun q => if q = p then deningerRootElt S.carrier (S.fam p) m
      else PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q)⟩

/-- **The step has unique roots.** -/
theorem deningerFamilyStep_uniqueRoots (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hS : DeningerFamilyGood S)
    (x y : (deningerFamilyStep S p m).carrier) (n : ℕ) (hn : 0 < n) (h : x ^ n = y ^ n) :
    x = y := by
  refine deningerRootAdjunction_uniqueRoots S.carrier (S.fam p) m hm (hS.order p)
    hS.uniqueRoots (hS.isolated p)
    (deningerCentralizer_zpow_subset hS.uniqueRoots (S.fam p) (hS.central p))
    hS.torsionFree x y (n - 1) ?_
  rw [show n - 1 + 1 = n by omega]
  exact h

/-- **The step is torsion free.** -/
theorem deningerFamilyStep_torsionFree (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hS : DeningerFamilyGood S)
    (x : (deningerFamilyStep S p m).carrier) (n : ℕ) (hn : 0 < n) (h : x ^ n = 1) : x = 1 :=
  deningerRootAdjunction_torsionFree S.carrier (S.fam p) m hm (hS.order p) hS.torsionFree x n hn h

/-- **Every member of the new family has infinite order.** -/
theorem deningerFamilyStep_order (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hS : DeningerFamilyGood S) (q : ℕ) (n : ℤ)
    (h : ((deningerFamilyStep S p m).fam q) ^ n = 1) : n = 0 := by
  have hφ := deningerRootMap_injective S.carrier (S.fam p) m hm (hS.order p)
  by_cases hq : q = p
  · subst hq
    have hfam : (deningerFamilyStep S q m).fam q = deningerRootElt S.carrier (S.fam q) m := by
      show (if q = q then _ else _) = _
      rw [if_pos rfl]
    rw [hfam] at h
    refine deningerInfiniteOrder (deningerRootElt S.carrier (S.fam q) m) ?_
      (deningerFamilyStep_torsionFree S q m hm hS) n h
    intro hc1
    have h1 : PushoutI.of (φ := deningerRootMap S.carrier (S.fam q) m) (ULift.up false)
        deningerRootGen.{u} =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam q) m) (ULift.up false) 1 := by
      rw [map_one]
      exact hc1
    exact deningerRootGen_ne_one (PushoutI.of_injective hφ _ h1)
  · have hfam : (deningerFamilyStep S p m).fam q =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q) := by
      show (if q = p then _ else _) = _
      rw [if_neg hq]
    rw [hfam] at h
    refine hS.order q n (PushoutI.of_injective hφ (ULift.up true) ?_)
    calc PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q ^ n)
        = (PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true)
            (S.fam q)) ^ n :=
          map_zpow (PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true))
            (S.fam q) n
      _ = 1 := h
      _ = PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) 1 :=
          (map_one _).symm

/-- The disjointness of a waiting member from the subgroup being rooted, in the form the
inheritance theorems consume. -/
theorem deningerFamilyStep_disjBase (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hS : DeningerFamilyGood S) (q : ℕ) (hq : q ≠ p) :
    ∀ (x : S.carrier) (c : ℤ), c ≠ 0 → ∀ k : ULift.{u} (Multiplicative ℤ),
      x⁻¹ * (S.fam q) ^ c * x ≠
        deningerRootMap S.carrier (S.fam p) m (ULift.up true) k := by
  intro x c hc k
  rw [deningerRootMap_true_apply]
  exact hS.disjoint q p hq x c hc (Multiplicative.toAdd (MulEquiv.ulift k))

/-- **Every member of the new family is its own centralizer.** -/
theorem deningerFamilyStep_central (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hm2 : 2 ≤ m.natAbs) (hS : DeningerFamilyGood S) (q : ℕ)
    (x : (deningerFamilyStep S p m).carrier)
    (h : x * (deningerFamilyStep S p m).fam q * x⁻¹ = (deningerFamilyStep S p m).fam q) :
    x ∈ Subgroup.zpowers ((deningerFamilyStep S p m).fam q) := by
  by_cases hq : q = p
  · subst hq
    have hfam : (deningerFamilyStep S q m).fam q = deningerRootElt S.carrier (S.fam q) m := by
      show (if q = q then _ else _) = _
      rw [if_pos rfl]
    rw [hfam] at h ⊢
    exact deningerRootElt_centralizer S.carrier (S.fam q) m hm hm2 (hS.order q) x
      (mul_inv_eq_iff_eq_mul.mp h)
  · have hfam : (deningerFamilyStep S p m).fam q =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q) := by
      show (if q = p then _ else _) = _
      rw [if_neg hq]
    rw [hfam] at h ⊢
    exact (deningerRootAdjunction_inherit S.carrier (S.fam p) m hm (hS.order p) hS.torsionFree
      (S.fam q) (deningerFamilyStep_disjBase S p m hS q hq) (hS.central q)
      (hS.isolated q)).1 x (mul_inv_eq_iff_eq_mul.mp h)

/-- **Every member of the new family generates an isolated subgroup.** -/
theorem deningerFamilyStep_isolated (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hS : DeningerFamilyGood S) (q : ℕ)
    (y : (deningerFamilyStep S p m).carrier) (n : ℕ) (hn : 0 < n)
    (hy : y ^ n ∈ Subgroup.zpowers ((deningerFamilyStep S p m).fam q)) :
    y ∈ Subgroup.zpowers ((deningerFamilyStep S p m).fam q) := by
  by_cases hq : q = p
  · subst hq
    have hfam : (deningerFamilyStep S q m).fam q = deningerRootElt S.carrier (S.fam q) m := by
      show (if q = q then _ else _) = _
      rw [if_pos rfl]
    rw [hfam] at hy ⊢
    exact deningerRootElt_isolated S.carrier (S.fam q) m hm (hS.order q)
      (deningerCentralizer_zpow_subset hS.uniqueRoots (S.fam q) (hS.central q))
      hS.uniqueRoots (hS.isolated q) hS.torsionFree y n hn hy
  · have hfam : (deningerFamilyStep S p m).fam q =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q) := by
      show (if q = p then _ else _) = _
      rw [if_neg hq]
    rw [hfam] at hy ⊢
    exact (deningerRootAdjunction_inherit S.carrier (S.fam p) m hm (hS.order p) hS.torsionFree
      (S.fam q) (deningerFamilyStep_disjBase S p m hS q hq) (hS.central q)
      (hS.isolated q)).2.1 y n hn hy

/-- **Different members of the new family stay disjoint under conjugation.** -/
theorem deningerFamilyStep_disjoint (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm : m ≠ 0) (hS : DeningerFamilyGood S) (q r : ℕ) (hqr : q ≠ r)
    (x : (deningerFamilyStep S p m).carrier) (c : ℤ) (hc : c ≠ 0) (k : ℤ) :
    x⁻¹ * ((deningerFamilyStep S p m).fam q) ^ c * x ≠
      ((deningerFamilyStep S p m).fam r) ^ k := by
  by_cases hqp : q = p
  · subst hqp
    have hr : r ≠ q := fun h => hqr h.symm
    have hfamq : (deningerFamilyStep S q m).fam q = deningerRootElt S.carrier (S.fam q) m := by
      show (if q = q then _ else _) = _
      rw [if_pos rfl]
    have hfamr : (deningerFamilyStep S q m).fam r =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam q) m) (ULift.up true) (S.fam r) := by
      show (if r = q then _ else _) = _
      rw [if_neg hr]
    rw [hfamq, hfamr]
    exact deningerRootAdjunction_disjoint_symm S.carrier (S.fam q) m hm (hS.order q)
      hS.torsionFree (S.fam r) (deningerFamilyStep_disjBase S q m hS r hr) x c hc k
  · have hfamq : (deningerFamilyStep S p m).fam q =
        PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam q) := by
      show (if q = p then _ else _) = _
      rw [if_neg hqp]
    by_cases hrp : r = p
    · subst hrp
      have hfamr : (deningerFamilyStep S r m).fam r = deningerRootElt S.carrier (S.fam r) m := by
        show (if r = r then _ else _) = _
        rw [if_pos rfl]
      rw [hfamq, hfamr]
      intro hcon
      refine (deningerRootAdjunction_inherit S.carrier (S.fam r) m hm (hS.order r) hS.torsionFree
        (S.fam q) (deningerFamilyStep_disjBase S r m hS q hqp) (hS.central q)
        (hS.isolated q)).2.2 x c hc (deningerRootGen.{u} ^ k) ?_
      exact hcon.trans (map_zpow (PushoutI.of (φ := deningerRootMap S.carrier (S.fam r) m)
        (ULift.up false)) deningerRootGen.{u} k).symm
    · have hfamr : (deningerFamilyStep S p m).fam r =
          PushoutI.of (φ := deningerRootMap S.carrier (S.fam p) m) (ULift.up true) (S.fam r) := by
        show (if r = p then _ else _) = _
        rw [if_neg hrp]
      rw [hfamq, hfamr]
      exact deningerRootAdjunction_disjoint_factors S.carrier (S.fam p) m hm (hS.order p)
        (S.fam q) (S.fam r) (deningerFamilyStep_disjBase S p m hS q hqp)
        (hS.disjoint q r hqr) x c hc k

/-- **The step preserves the invariant.** -/
theorem deningerFamilyStep_good (S : DeningerFamilyStage.{u}) (p : ℕ) (m : ℤ)
    (hm2 : 2 ≤ m.natAbs) (hS : DeningerFamilyGood S) :
    DeningerFamilyGood (deningerFamilyStep S p m) := by
  have hm : m ≠ 0 := by omega
  exact ⟨deningerFamilyStep_uniqueRoots S p m hm hS, deningerFamilyStep_torsionFree S p m hm hS,
    deningerFamilyStep_order S p m hm hS, deningerFamilyStep_central S p m hm hm2 hS,
    deningerFamilyStep_isolated S p m hm hS, deningerFamilyStep_disjoint S p m hm hS⟩

end RootAdjunction

end RHTower
