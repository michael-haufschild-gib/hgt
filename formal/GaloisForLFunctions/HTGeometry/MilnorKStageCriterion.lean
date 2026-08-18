import GaloisForLFunctions.HTGeometry.MilnorKUnitRankOne
import GaloisForLFunctions.HTGeometry.DivisibilityFirewall

/-!
# The stage-by-stage criterion for torsion of `K₂^M`

`K₂^M(F)` is the directed union of the symbol subgroups of the finitely generated subgroups of
`Fˣ`, and each of those stages is a **finitely generated** abelian group.  The divisibility firewall
says that no mod-`m` statement about `K₂^M(F)` itself can decide whether it is torsion — a directed
union of infinite cyclic groups can be `ℚ`.  But the firewall is broken one stage at a time: a
finitely generated abelian group is torsion exactly when it has no `ℤ`-quotient, and that *is*
visible modulo every `m`.

Putting the two together turns "the tame kernel of a number field is torsion" — an analytic theorem
of Borel and Garland — into a statement about a directed system of finitely generated abelian
groups, each of which is decided by its `ℤ`-quotients.

* `symbolStage` : the stage attached to a finite set of units.
* `symbolStage_addGroup_fg` : **every stage is finitely generated.**
* `symbolStage_le_torsion_iff_no_int_quotient` : **a stage is torsion iff it has no `ℤ`-quotient.**
* `milnorKDegTwo_le_torsion_iff_stages` : `K₂^M(F)` is torsion iff every stage is.
* `milnorKDegTwo_le_torsion_iff_no_stage_int_quotient` : **the two combined.**
-/

namespace GaloisForLFunctions.HTGeometry

variable (F : Type*) [Field F]

/-- The stage of the symbol filtration attached to a finite set of units. -/
def symbolStage (G : Finset Fˣ) : AddSubgroup (MilnorKDeg F 2) :=
  symbolSubgroup F (Subgroup.closure (G : Set Fˣ))

theorem symbolStage_fg (G : Finset Fˣ) : (symbolStage F G).FG :=
  symbolSubgroup_fg_of_fg F ⟨G, rfl⟩

instance symbolStage_addGroup_fg (G : Finset Fˣ) : AddGroup.FG (symbolStage F G) :=
  (AddGroup.fg_iff_addSubgroup_fg _).2 (symbolStage_fg F G)

/-- **`K₂^M(F)` is torsion exactly when every stage is.** -/
theorem milnorKDegTwo_le_torsion_iff_stages :
    (∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
      ↔ ∀ G : Finset Fˣ, symbolStage F G ≤ torsionAddSubgroup (MilnorKDeg F 2) := by
  constructor
  · intro h G x _
    exact h x
  · intro h x
    obtain ⟨G, hG⟩ := exists_finset_mem_symbolSubgroup F x
    exact h G hG

/-- **A stage is torsion exactly when it has no `ℤ`-quotient.**  The forward direction is that a
torsion group has no `ℤ`-quotient; the converse is the firewall-breaking lemma, available because
the stage is finitely generated. -/
theorem symbolStage_le_torsion_iff_no_int_quotient (G : Finset Fˣ) :
    symbolStage F G ≤ torsionAddSubgroup (MilnorKDeg F 2)
      ↔ ∀ φ : (symbolStage F G) →+ ℤ, ¬ Function.Surjective φ := by
  constructor
  · intro h φ hφ
    obtain ⟨y, hy⟩ := hφ 1
    obtain ⟨n, hn, hnx⟩ := h y.2
    have hz : (n : ℤ) • φ y = 0 := by
      rw [← map_zsmul]
      have : (n : ℤ) • y = 0 := Subtype.ext hnx
      rw [this, map_zero]
    rw [hy, smul_eq_mul, mul_one] at hz
    exact hn hz
  · intro h y hy
    have htor : AddMonoid.IsTorsion (symbolStage F G) :=
      isTorsion_of_fg_of_no_int_quotient h
    obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).1 (htor ⟨y, hy⟩)
    refine ⟨(n : ℤ), by exact_mod_cast hn.ne', ?_⟩
    have : ((n : ℤ)) • (⟨y, hy⟩ : symbolStage F G) = 0 := by
      rw [natCast_zsmul]
      exact hnx
    exact congrArg Subtype.val this

/-- **The stage-by-stage criterion.**  `K₂^M(F)` is torsion if and only if no stage of the symbol
filtration admits a surjection onto `ℤ`.  Each stage is a finitely generated abelian group, so the
right-hand condition is a statement that finite-coefficient information decides — which is exactly
what the divisibility firewall shows is impossible for `K₂^M(F)` as a whole. -/
theorem milnorKDegTwo_le_torsion_iff_no_stage_int_quotient :
    (∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
      ↔ ∀ G : Finset Fˣ, ∀ φ : (symbolStage F G) →+ ℤ, ¬ Function.Surjective φ := by
  rw [milnorKDegTwo_le_torsion_iff_stages]
  exact forall_congr' fun G => symbolStage_le_torsion_iff_no_int_quotient F G

theorem symbolStage_mono {G G' : Finset Fˣ} (h : G ⊆ G') :
    symbolStage F G ≤ symbolStage F G' :=
  symbolSubgroup_mono F (Subgroup.closure_mono (by exact_mod_cast h))

/-- **A cofinal family of stages suffices.**  Because the stages are monotone, killing the rank of
a cofinal family of them kills it everywhere.  This is the freedom that the exceptional-unit
formulation uses: to control `{a, b}` one is allowed to enlarge the set of units until enough
Steinberg relations `{g, 1 − g} = 0` become available. -/
theorem milnorKDegTwo_le_torsion_of_cofinal_stages
    (S : Set (Finset Fˣ)) (hcof : ∀ G : Finset Fˣ, ∃ G' ∈ S, G ⊆ G')
    (h : ∀ G' ∈ S, symbolStage F G' ≤ torsionAddSubgroup (MilnorKDeg F 2)) :
    ∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2) := by
  refine (milnorKDegTwo_le_torsion_iff_stages F).2 fun G => ?_
  obtain ⟨G', hG', hsub⟩ := hcof G
  exact le_trans (symbolStage_mono F hsub) (h G' hG')

/-! ## Multiplicatively dependent entries -/

/-- **A symbol with multiplicatively dependent entries is torsion.**  If `aᵐ bⁿ = 1` with `m ≠ 0`
then `m·{a,b} = {aᵐ, b} = {b⁻ⁿ, b} = −n·{b,b}`, and `{b,b} = {−1,b}` is killed by two, so
`2m·{a,b} = 0`.  No structure theory is used: this is the whole content of "rank at most one" for a
single symbol. -/
theorem milnorSym2_mem_torsion_of_dependent {a b : Fˣ} {m n : ℤ} (hm : m ≠ 0)
    (h : a ^ m * b ^ n = 1) :
    milnorSym2 F a b ∈ torsionAddSubgroup (MilnorKDeg F 2) := by
  have hab : a ^ m = b ^ (-n) := by
    rw [zpow_neg, eq_inv_iff_mul_eq_one]
    exact h
  have hstep : m • milnorSym2 F a b = (-n) • milnorSym2 F b b := by
    rw [← milnorSym2_zpow_left a b m, hab, milnorSym2_zpow_left]
  refine ⟨2 * m, mul_ne_zero two_ne_zero hm, ?_⟩
  have h2 : (2 * m) • milnorSym2 F a b = (2 : ℤ) • (m • milnorSym2 F a b) := by
    rw [smul_smul]
  rw [h2, hstep, smul_comm, milnorSym2_two_zsmul_self, smul_zero]

/-- **`K₂^M(F)` is torsion exactly when every single symbol is.** -/
theorem milnorKDegTwo_le_torsion_iff_symbols :
    (∀ x : MilnorKDeg F 2, x ∈ torsionAddSubgroup (MilnorKDeg F 2))
      ↔ ∀ a b : Fˣ, milnorSym2 F a b ∈ torsionAddSubgroup (MilnorKDeg F 2) := by
  constructor
  · intro h a b
    exact h _
  · intro h x
    have hle : AddSubgroup.closure (Set.range fun p : Fˣ × Fˣ => milnorSym2 F p.1 p.2)
        ≤ torsionAddSubgroup (MilnorKDeg F 2) := by
      refine AddSubgroup.closure_le _ |>.2 ?_
      rintro y ⟨p, rfl⟩
      exact h p.1 p.2
    rw [closure_range_milnorSym2] at hle
    exact hle (AddSubgroup.mem_top x)

/-! ## The subtraction identity -/

/-- The unit `b - a`, available whenever `a ≠ b`. -/
def subUnit {a b : Fˣ} (hab : (a : F) ≠ (b : F)) : Fˣ :=
  Units.mk0 ((b : F) - (a : F)) (sub_ne_zero.mpr (Ne.symm hab))

@[simp]
theorem subUnit_val {a b : Fˣ} (hab : (a : F) ≠ (b : F)) :
    ((subUnit F hab : Fˣ) : F) = (b : F) - (a : F) := rfl

/-- **The subtraction identity.**  For `a ≠ b`,

`{a, b} = {a/b, b − a} + {−1, b}`.

It is the Steinberg relation at `x = a/b`, whose complement is `1 − a/b = (b − a)/b`, expanded in
both slots.  Over `ℤ` this is exactly the move that drives Tate's Euclidean descent: it trades the
symbol `{a, b}` for one whose second entry is the *remainder* `b − a`.  Over a general number field
the identity still holds, but there is no size function that the exchange decreases — which is the
precise reason the descent does not generalize past one archimedean place. -/
theorem milnorSym2_sub_identity {a b : Fˣ} (hab : (a : F) ≠ (b : F)) :
    milnorSym2 F a b
      = milnorSym2 F (a * b⁻¹) (subUnit F hab) + milnorSym2 F (-1) b := by
  have hx : ((a * b⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    apply hab
    have hb : ((b : F)) ≠ 0 := b.ne_zero
    have hval : (a : F) * ((b : F))⁻¹ = 1 := by
      simpa [Units.val_mul, Units.val_inv_eq_inv_val] using h
    field_simp at hval
    exact hval
  have hsteinberg : milnorSym2 F (a * b⁻¹) (oneSubUnit hx) = 0 := milnorSym2_steinberg hx
  have hunit : oneSubUnit hx = subUnit F hab * b⁻¹ := by
    refine Units.ext ?_
    have hb : ((b : F)) ≠ 0 := b.ne_zero
    simp only [oneSubUnit_val, subUnit_val, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  rw [hunit, milnorSym2_mul_left, milnorSym2_mul_right, milnorSym2_mul_right,
    milnorSym2_inv_left, milnorSym2_inv_right, milnorSym2_inv_left,
    milnorSym2_inv_right] at hsteinberg
  have hbb : milnorSym2 F b b = milnorSym2 F (-1) b := milnorSym2_self b
  have hgoal : milnorSym2 F a b
      = milnorSym2 F a (subUnit F hab) - milnorSym2 F b (subUnit F hab)
        + milnorSym2 F b b := by
    rw [show (milnorSym2 F a (subUnit F hab) + -milnorSym2 F a b
        + (-milnorSym2 F b (subUnit F hab) + - -milnorSym2 F b b))
        = (milnorSym2 F a (subUnit F hab) - milnorSym2 F b (subUnit F hab)
            + milnorSym2 F b b) - milnorSym2 F a b from by abel] at hsteinberg
    exact (sub_eq_zero.mp hsteinberg).symm
  rw [hgoal, hbb, milnorSym2_mul_left, milnorSym2_inv_left]
  abel

end GaloisForLFunctions.HTGeometry
