import GaloisForLFunctions.RHTower.Deninger.DeningerSeminormQuotient

/-!
# The quotient seminorm

The infimum of a seminorm over the representatives of a class is again a seminorm on the quotient
module: the infimum is attained approximately, so subadditivity follows by choosing representatives
within `ε` of the infimum, and homogeneity follows because multiplication by a nonzero scalar is a
bijection of the representative sets.

A domination of seminorms passes to the quotients with the same constant, so a quotient of a
locally convex space carries the quotient family, and the comparison maps of the quotient family
are the ones induced by the comparison maps upstairs.

* `deningerQuotientSeminorm` : the quotient seminorm.
* `deningerQuotientSeminorm_mk_le` : it is at most the seminorm of any representative.
* `deningerQuotientSeminorm_exists_lt` : representatives attain it approximately.
* `deningerQuotientSeminorm_le_of_le` : dominations pass to the quotient.
-/

namespace RHTower

open Set

section QuotientSeminorm

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- The representatives of a class in a quotient module. -/
abbrev DeningerQuotientReps (N : Submodule 𝕜 E) (x : E ⧸ N) : Type _ :=
  {y : E // Submodule.Quotient.mk y = x}

instance deningerQuotientReps_nonempty (N : Submodule 𝕜 E) (x : E ⧸ N) :
    Nonempty (DeningerQuotientReps N x) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective N x
  exact ⟨⟨y, hy⟩⟩

theorem deningerQuotient_bddBelow (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E ⧸ N) :
    BddBelow (Set.range fun y : DeningerQuotientReps N x => p (y : E)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨y, rfl⟩
  exact apply_nonneg _ _

/-- The value of the quotient seminorm: the infimum over representatives. -/
noncomputable def deningerQuotientFun (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E ⧸ N) : ℝ :=
  ⨅ y : DeningerQuotientReps N x, p (y : E)

theorem deningerQuotientFun_nonneg (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E ⧸ N) :
    0 ≤ deningerQuotientFun N p x :=
  le_ciInf fun _ => apply_nonneg _ _

theorem deningerQuotientFun_mk_le (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (y : E) :
    deningerQuotientFun N p (Submodule.Quotient.mk y) ≤ p y :=
  ciInf_le (deningerQuotient_bddBelow N p _) (⟨y, rfl⟩ : DeningerQuotientReps N _)

theorem deningerQuotientFun_exists_lt (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E ⧸ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, Submodule.Quotient.mk y = x ∧ p y < deningerQuotientFun N p x + ε := by
  have hlt : deningerQuotientFun N p x < deningerQuotientFun N p x + ε := by linarith
  obtain ⟨y, hy⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨(y : E), y.2, hy⟩

theorem deningerQuotientFun_zero (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    deningerQuotientFun N p 0 = 0 := by
  refine le_antisymm ?_ (deningerQuotientFun_nonneg N p 0)
  have h := deningerQuotientFun_mk_le N p (0 : E)
  rw [map_zero] at h
  have hzero : (Submodule.Quotient.mk (0 : E) : E ⧸ N) = 0 := by
    rw [Submodule.Quotient.mk_zero]
  rwa [hzero] at h

theorem deningerQuotientFun_add_le (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x y : E ⧸ N) :
    deningerQuotientFun N p (x + y)
      ≤ deningerQuotientFun N p x + deningerQuotientFun N p y := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, halt⟩ := deningerQuotientFun_exists_lt N p x (half_pos hε)
  obtain ⟨b, hb, hblt⟩ := deningerQuotientFun_exists_lt N p y (half_pos hε)
  have hmk : (Submodule.Quotient.mk (a + b) : E ⧸ N) = x + y := by
    rw [Submodule.Quotient.mk_add, ha, hb]
  have hle := deningerQuotientFun_mk_le N p (a + b)
  rw [hmk] at hle
  have hadd : p (a + b) ≤ p a + p b := map_add_le_add p a b
  linarith

theorem deningerQuotientFun_smul (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (c : 𝕜) (x : E ⧸ N) :
    deningerQuotientFun N p (c • x) = ‖c‖ * deningerQuotientFun N p x := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, deningerQuotientFun_zero, norm_zero, zero_mul]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    obtain ⟨a, ha, hlt⟩ := deningerQuotientFun_exists_lt N p x (div_pos hε hcpos)
    have hmk : (Submodule.Quotient.mk (c • a) : E ⧸ N) = c • x := by
      rw [Submodule.Quotient.mk_smul, ha]
    have hle := deningerQuotientFun_mk_le N p (c • a)
    rw [hmk, map_smul_eq_mul] at hle
    have hstep : ‖c‖ * p a ≤ ‖c‖ * (deningerQuotientFun N p x + ε / ‖c‖) :=
      mul_le_mul_of_nonneg_left hlt.le hcpos.le
    have hval : ‖c‖ * (deningerQuotientFun N p x + ε / ‖c‖)
        = ‖c‖ * deningerQuotientFun N p x + ε := by
      field_simp
    linarith [hle, hstep, hval.le, hval.ge]
  · have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [← le_div_iff₀' hcpos]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcinv : 0 < ‖c‖ := hcpos
    obtain ⟨a, ha, hlt⟩ :=
      deningerQuotientFun_exists_lt N p (c • x) (mul_pos hε hcinv)
    have hmk : (Submodule.Quotient.mk (c⁻¹ • a) : E ⧸ N) = x := by
      rw [Submodule.Quotient.mk_smul, ha, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hle := deningerQuotientFun_mk_le N p (c⁻¹ • a)
    rw [hmk, map_smul_eq_mul, norm_inv] at hle
    have hstep : ‖c‖⁻¹ * p a < ‖c‖⁻¹ * (deningerQuotientFun N p (c • x) + ε * ‖c‖) :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    have hval : ‖c‖⁻¹ * (deningerQuotientFun N p (c • x) + ε * ‖c‖)
        = deningerQuotientFun N p (c • x) / ‖c‖ + ε := by
      field_simp
    linarith [hle, hstep, hval.le, hval.ge]

/-- **The quotient seminorm.** -/
noncomputable def deningerQuotientSeminorm (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) :
    Seminorm 𝕜 (E ⧸ N) where
  toFun := deningerQuotientFun N p
  map_zero' := deningerQuotientFun_zero N p
  add_le' := deningerQuotientFun_add_le N p
  neg' := by
    intro x
    have h := deningerQuotientFun_smul N p (-1 : 𝕜) x
    rw [neg_one_smul, norm_neg, norm_one, one_mul] at h
    exact h
  smul' := deningerQuotientFun_smul N p

@[simp] theorem deningerQuotientSeminorm_apply (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E)
    (x : E ⧸ N) : deningerQuotientSeminorm N p x = deningerQuotientFun N p x := rfl

theorem deningerQuotientSeminorm_mk_le (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (y : E) :
    deningerQuotientSeminorm N p (Submodule.Quotient.mk y) ≤ p y :=
  deningerQuotientFun_mk_le N p y

theorem deningerQuotientSeminorm_exists_lt (N : Submodule 𝕜 E) (p : Seminorm 𝕜 E) (x : E ⧸ N)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, Submodule.Quotient.mk y = x ∧ p y < deningerQuotientSeminorm N p x + ε :=
  deningerQuotientFun_exists_lt N p x hε

/-- **A domination of seminorms passes to the quotients**, with the same constant. -/
theorem deningerQuotientSeminorm_le_of_le (N : Submodule 𝕜 E) {p q : Seminorm 𝕜 E} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x, p x ≤ C * q x) (x : E ⧸ N) :
    deningerQuotientSeminorm N p x ≤ C * deningerQuotientSeminorm N q x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases eq_or_lt_of_le hC with rfl | hCpos
  · have hzero : ∀ y : E, p y ≤ 0 := by
      intro y
      have := h y
      linarith
    obtain ⟨y, hy, _⟩ := deningerQuotientSeminorm_exists_lt N p x hε
    have hle : deningerQuotientSeminorm N p x ≤ p y := by
      rw [← hy]
      exact deningerQuotientSeminorm_mk_le N p y
    have hpy : p y ≤ 0 := hzero y
    have hnn : 0 ≤ deningerQuotientSeminorm N q x := deningerQuotientFun_nonneg N q x
    linarith
  · obtain ⟨y, hy, hlt⟩ := deningerQuotientSeminorm_exists_lt N q x (div_pos hε hCpos)
    have hle : deningerQuotientSeminorm N p x ≤ p y := by
      rw [← hy]
      exact deningerQuotientSeminorm_mk_le N p y
    have hstep : p y ≤ C * q y := h y
    have hstep2 : C * q y ≤ C * (deningerQuotientSeminorm N q x + ε / C) :=
      mul_le_mul_of_nonneg_left hlt.le hC
    have hval : C * (deningerQuotientSeminorm N q x + ε / C)
        = C * deningerQuotientSeminorm N q x + ε := by
      field_simp
    linarith

end QuotientSeminorm

end RHTower
