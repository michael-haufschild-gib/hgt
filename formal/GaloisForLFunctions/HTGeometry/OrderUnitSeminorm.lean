import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The order-unit seminorm

An operator system is a matrix-ordered `*`-vector space with an Archimedean matrix order unit, and
its norm is built level by level from the order-unit seminorm.  Mathlib has no order-unit theory at
all, so this module supplies the scalar level: for an ordered module over `ℝ` with an order unit
`e`, the quantity

```text
‖v‖_e = inf {t > 0 : -(t • e) ≤ v ≤ t • e}
```

is well defined, nonnegative, vanishes at zero, is symmetric, and is subadditive — that is, it is a
seminorm.  This is the scalar layer beneath a matrix-ordered structure, and it is the norm the
boundary-ideal condition of `ShilovLocalBoundaryIdeal.lean` refers to in the operator-system case.
-/

namespace GaloisForLFunctions.HTGeometry

namespace OrderUnit

variable {V : Type*} [AddCommGroup V] [PartialOrder V] [IsOrderedAddMonoid V] [Module ℝ V]
  [PosSMulMono ℝ V] [SMulPosMono ℝ V]

/-- `e` is an order unit: it is positive and absorbs every element after scaling. -/
structure IsOrderUnit (e : V) : Prop where
  nonneg : 0 ≤ e
  absorbing : ∀ v : V, ∃ t : ℝ, 0 < t ∧ v ≤ t • e

/-- The positive scalars bounding `v` symmetrically by `e`. -/
def unitBounds (e v : V) : Set ℝ := {t : ℝ | 0 < t ∧ -(t • e) ≤ v ∧ v ≤ t • e}

/-- The order-unit seminorm. -/
noncomputable def orderUnitNorm (e v : V) : ℝ := sInf (unitBounds e v)

omit [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V] in
theorem mem_unitBounds {e v : V} {t : ℝ} :
    t ∈ unitBounds e v ↔ 0 < t ∧ -(t • e) ≤ v ∧ v ≤ t • e := Iff.rfl

omit [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V] in
theorem bddBelow_unitBounds (e v : V) : BddBelow (unitBounds e v) :=
  ⟨0, fun _ ht => le_of_lt ht.1⟩

omit [PosSMulMono ℝ V] in
/-- Enlarging a bound keeps it a bound. -/
theorem unitBounds_mono {e v : V} (he : IsOrderUnit e) {t s : ℝ} (ht : t ∈ unitBounds e v)
    (hts : t ≤ s) : s ∈ unitBounds e v := by
  obtain ⟨htpos, hlow, hhigh⟩ := ht
  have hscale : t • e ≤ s • e := smul_le_smul_of_nonneg_right hts he.nonneg
  refine ⟨lt_of_lt_of_le htpos hts, ?_, le_trans hhigh hscale⟩
  exact le_trans (neg_le_neg hscale) hlow

omit [PosSMulMono ℝ V] in
theorem unitBounds_nonempty {e : V} (he : IsOrderUnit e) (v : V) :
    (unitBounds e v).Nonempty := by
  obtain ⟨t₁, ht₁, hv₁⟩ := he.absorbing v
  obtain ⟨t₂, ht₂, hv₂⟩ := he.absorbing (-v)
  refine ⟨max t₁ t₂, lt_of_lt_of_le ht₁ (le_max_left _ _), ?_, ?_⟩
  · have hscale : t₂ • e ≤ max t₁ t₂ • e :=
      smul_le_smul_of_nonneg_right (le_max_right _ _) he.nonneg
    have : -(max t₁ t₂ • e) ≤ -(t₂ • e) := neg_le_neg hscale
    exact le_trans this (neg_le_of_neg_le hv₂)
  · have hscale : t₁ • e ≤ max t₁ t₂ • e :=
      smul_le_smul_of_nonneg_right (le_max_left _ _) he.nonneg
    exact le_trans hv₁ hscale

omit [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V] in
theorem orderUnitNorm_nonneg (e v : V) : 0 ≤ orderUnitNorm e v :=
  Real.sInf_nonneg fun _ ht => le_of_lt ht.1

omit [IsOrderedAddMonoid V] [PosSMulMono ℝ V] [SMulPosMono ℝ V] in
theorem orderUnitNorm_le {e v : V} {t : ℝ} (ht : t ∈ unitBounds e v) :
    orderUnitNorm e v ≤ t :=
  csInf_le (bddBelow_unitBounds e v) ht

omit [PosSMulMono ℝ V] in
theorem le_orderUnitNorm {e v : V} (he : IsOrderUnit e) {r : ℝ}
    (h : ∀ t ∈ unitBounds e v, r ≤ t) : r ≤ orderUnitNorm e v :=
  le_csInf (unitBounds_nonempty he v) h

omit [SMulPosMono ℝ V] in
@[simp]
theorem orderUnitNorm_zero {e : V} (he : IsOrderUnit e) : orderUnitNorm e (0 : V) = 0 := by
  refine le_antisymm ?_ (orderUnitNorm_nonneg e 0)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hmem : ε ∈ unitBounds e (0 : V) := by
    refine ⟨hε, ?_, ?_⟩
    · have : (0 : V) ≤ ε • e := smul_nonneg hε.le he.nonneg
      simpa using neg_nonpos_of_nonneg this
    · exact smul_nonneg hε.le he.nonneg
  simpa using orderUnitNorm_le hmem

omit [PosSMulMono ℝ V] [SMulPosMono ℝ V] in
theorem orderUnitNorm_neg (e v : V) : orderUnitNorm e (-v) = orderUnitNorm e v := by
  have hset : unitBounds e (-v) = unitBounds e v := by
    ext t
    constructor
    · rintro ⟨ht, hlow, hhigh⟩
      exact ⟨ht, neg_le_of_neg_le hhigh, neg_le_neg_iff.mp hlow⟩
    · rintro ⟨ht, hlow, hhigh⟩
      exact ⟨ht, neg_le_neg hhigh, neg_le_of_neg_le hlow⟩
  rw [orderUnitNorm, orderUnitNorm, hset]

omit [PosSMulMono ℝ V] in
theorem orderUnitNorm_add_le {e : V} (he : IsOrderUnit e) (v w : V) :
    orderUnitNorm e (v + w) ≤ orderUnitNorm e v + orderUnitNorm e w := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨t, htmem, htlt⟩ := exists_lt_of_csInf_lt (unitBounds_nonempty he v)
    (show orderUnitNorm e v < orderUnitNorm e v + ε / 2 by linarith)
  obtain ⟨s, hsmem, hslt⟩ := exists_lt_of_csInf_lt (unitBounds_nonempty he w)
    (show orderUnitNorm e w < orderUnitNorm e w + ε / 2 by linarith)
  have hsum : t + s ∈ unitBounds e (v + w) := by
    obtain ⟨htp, htl, hth⟩ := htmem
    obtain ⟨hsp, hsl, hsh⟩ := hsmem
    refine ⟨by linarith, ?_, ?_⟩
    · rw [add_smul, neg_add]
      exact add_le_add htl hsl
    · rw [add_smul]
      exact add_le_add hth hsh
  have := orderUnitNorm_le hsum
  linarith

/-! ## Positive homogeneity -/

omit [IsOrderedAddMonoid V] [SMulPosMono ℝ V] in
theorem smul_mem_unitBounds {e v : V} {c t : ℝ} (hc : 0 < c) (ht : t ∈ unitBounds e v) :
    c * t ∈ unitBounds e (c • v) := by
  obtain ⟨htp, htl, hth⟩ := ht
  refine ⟨mul_pos hc htp, ?_, ?_⟩
  · have hstep : c • (-(t • e)) ≤ c • v := smul_le_smul_of_nonneg_left htl hc.le
    rwa [smul_neg, smul_smul] at hstep
  · have hstep : c • v ≤ c • (t • e) := smul_le_smul_of_nonneg_left hth hc.le
    rwa [smul_smul] at hstep

theorem orderUnitNorm_smul_le {e : V} (he : IsOrderUnit e) {c : ℝ} (hc : 0 < c) (v : V) :
    orderUnitNorm e (c • v) ≤ c * orderUnitNorm e v := by
  have hdiv : orderUnitNorm e (c • v) / c ≤ orderUnitNorm e v := by
    refine le_orderUnitNorm he fun t ht => ?_
    have hbound := orderUnitNorm_le (smul_mem_unitBounds hc ht)
    rw [div_le_iff₀ hc]
    linarith
  rw [div_le_iff₀ hc] at hdiv
  linarith

/-- **The order-unit seminorm is positively homogeneous.** -/
theorem orderUnitNorm_smul {e : V} (he : IsOrderUnit e) {c : ℝ} (hc : 0 < c) (v : V) :
    orderUnitNorm e (c • v) = c * orderUnitNorm e v := by
  refine le_antisymm (orderUnitNorm_smul_le he hc v) ?_
  have hinv := orderUnitNorm_smul_le he (inv_pos.mpr hc) (c • v)
  rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] at hinv
  have hmul := mul_le_mul_of_nonneg_left hinv hc.le
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul] at hmul

/-! ## Definiteness from the Archimedean property -/

/-- The Archimedean property of an order unit: only the nonpositive elements are dominated by
every positive multiple of `e`. -/
def IsArchimedean (e : V) : Prop := ∀ v : V, (∀ ε : ℝ, 0 < ε → v ≤ ε • e) → v ≤ 0

omit [PosSMulMono ℝ V] in
theorem le_smul_of_orderUnitNorm_eq_zero {e : V} (he : IsOrderUnit e) {v : V}
    (hv : orderUnitNorm e v = 0) {ε : ℝ} (hε : 0 < ε) : v ≤ ε • e := by
  obtain ⟨t, htmem, htlt⟩ := exists_lt_of_csInf_lt (unitBounds_nonempty he v)
    (show orderUnitNorm e v < ε by rw [hv]; exact hε)
  exact le_trans htmem.2.2 (smul_le_smul_of_nonneg_right htlt.le he.nonneg)

omit [PosSMulMono ℝ V] in
/-- **Definiteness.**  With an Archimedean order unit the order-unit seminorm is a norm. -/
theorem eq_zero_of_orderUnitNorm_eq_zero {e : V} (he : IsOrderUnit e) (harch : IsArchimedean e)
    {v : V} (hv : orderUnitNorm e v = 0) : v = 0 := by
  have hup : v ≤ 0 := harch v fun ε hε => le_smul_of_orderUnitNorm_eq_zero he hv hε
  have hvneg : orderUnitNorm e (-v) = 0 := by rw [orderUnitNorm_neg, hv]
  have hdown : -v ≤ 0 := harch (-v) fun ε hε => le_smul_of_orderUnitNorm_eq_zero he hvneg hε
  exact le_antisymm hup (by simpa using neg_nonpos.mp hdown)

end OrderUnit

end GaloisForLFunctions.HTGeometry
