/-
# Bondarenko--Heap Lemma 7: inverse-incidence arithmetic

Lemma 7 counts fibers of `r m⁻¹` modulo the conductor.  This module closes
the exact algebraic conversion of fiber equality to the cross-product
congruence used by the source additive-divisor argument.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterOrthogonality

noncomputable section

namespace RHTower

/-- The residue class used by the source Lemma-7 inverse-incidence fibers. -/
def unitInverseIncidenceClass (q : ℕ) [NeZero q]
    (r : ZMod q) (m : (ZMod q)ˣ) : ZMod q :=
  r * ((m⁻¹ : (ZMod q)ˣ) : ZMod q)

/-- For a fixed unit denominator, the inverse-incidence class is a permutation
of the residue ring. -/
def unitInverseIncidenceEquiv (q : ℕ) [NeZero q] (m : (ZMod q)ˣ) :
    ZMod q ≃ ZMod q where
  toFun r := unitInverseIncidenceClass q r m
  invFun x := x * (m : ZMod q)
  left_inv r := by
    unfold unitInverseIncidenceClass
    change (r * ((m⁻¹ : (ZMod q)ˣ) : ZMod q)) * (m : ZMod q) = r
    have hm : ((m⁻¹ : (ZMod q)ˣ) : ZMod q) * (m : ZMod q) = 1 := Units.inv_mul m
    rw [show r * ((m⁻¹ : (ZMod q)ˣ) : ZMod q) * (m : ZMod q) =
      r * (((m⁻¹ : (ZMod q)ˣ) : ZMod q) * (m : ZMod q)) by ring, hm]
    ring
  right_inv x := by
    unfold unitInverseIncidenceClass
    change (x * (m : ZMod q)) * ((m⁻¹ : (ZMod q)ˣ) : ZMod q) = x
    have hm : (m : ZMod q) * ((m⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv m
    rw [show x * (m : ZMod q) * ((m⁻¹ : (ZMod q)ˣ) : ZMod q) =
      x * ((m : ZMod q) * ((m⁻¹ : (ZMod q)ˣ) : ZMod q)) by ring, hm]
    ring

/-- Exact reindexing of a complete residue sum along a fixed inverse-incidence fiber map. -/
theorem sum_unitInverseIncidenceClass (q : ℕ) [NeZero q] (m : (ZMod q)ˣ)
    (f : ZMod q → ℂ) :
    ∑ r : ZMod q, f (unitInverseIncidenceClass q r m) = ∑ x : ZMod q, f x :=
  Equiv.sum_comp (unitInverseIncidenceEquiv q m) f

/-- Unit scaling sends a residue to zero exactly when that residue was zero. -/
theorem unitInverseIncidenceClass_eq_zero_iff (q : ℕ) [NeZero q]
    (r : ZMod q) (m : (ZMod q)ˣ) :
    unitInverseIncidenceClass q r m = 0 ↔ r = 0 := by
  constructor
  · intro h
    apply (unitInverseIncidenceEquiv q m).injective
    simpa [unitInverseIncidenceClass] using h
  · intro h
    subst r
    simp [unitInverseIncidenceClass]

/-- Sum of coefficients in one fiber of an arbitrary finite incidence map. -/
noncomputable def finiteFibreSum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (φ : A → B) (c : A → ℂ) (x : B) : ℂ := by
  classical
  exact ∑ a : A, if φ a = x then c a else 0

/-- Exact finite fiber-energy identity.  This is the algebraic expansion of
the source Lemma-7 second moment before its cross-product divisor count. -/
theorem finiteFibreSum_energy {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (φ : A → B) (c : A → ℂ) :
    ∑ x : B, finiteFibreSum φ c x * star (finiteFibreSum φ c x) =
      ∑ a : A, ∑ b : A, if φ a = φ b then c a * star (c b) else 0 := by
  have hinner (a b : A) :
      ∑ x : B, (if φ a = x then c a else 0) * star (if φ b = x then c b else 0) =
        if φ a = φ b then c a * star (c b) else 0 := by
    by_cases hab : φ a = φ b
    · rw [hab]
      rw [Finset.sum_eq_single (φ b)]
      · simp
      · intro x _ hx
        have hbx : ¬ φ b = x := fun hbx => hx hbx.symm
        simp [hbx]
      · simp
    · rw [if_neg hab]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hax : φ a = x
      · simp only [hax, if_pos]
        have hbx : ¬ φ b = x := by
          intro hbx
          apply hab
          rw [hax, hbx]
        simp [hbx]
      · simp [hax]
  unfold finiteFibreSum
  simp_rw [star_sum, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  simp_rw [hinner]

/-- Equality of two modular inverse-incidence fibers is exactly the source
cross-product congruence.  The unit denominators are data, so no coprimality
premise is exposed in the theorem statement. -/
theorem unitInverseIncidenceClass_eq_iff_crossMul
    (q : ℕ) [NeZero q] (r₁ r₂ : ZMod q) (m₁ m₂ : (ZMod q)ˣ) :
    unitInverseIncidenceClass q r₁ m₁ = unitInverseIncidenceClass q r₂ m₂ ↔
      r₁ * (m₂ : ZMod q) = r₂ * (m₁ : ZMod q) := by
  have hm₁left : ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) * (m₁ : ZMod q) = 1 := Units.inv_mul m₁
  have hm₁right : (m₁ : ZMod q) * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv m₁
  have hm₂left : ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) * (m₂ : ZMod q) = 1 := Units.inv_mul m₂
  have hm₂right : (m₂ : ZMod q) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv m₂
  unfold unitInverseIncidenceClass
  constructor
  · intro h
    calc
      r₁ * (m₂ : ZMod q) = r₁ *
          ((((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) * (m₁ : ZMod q)) * (m₂ : ZMod q)) := by
            rw [hm₁left]
            ring
      _ = (r₁ * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((m₁ : ZMod q) * (m₂ : ZMod q)) := by ring
      _ = (r₂ * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((m₁ : ZMod q) * (m₂ : ZMod q)) := by rw [h]
      _ = r₂ * ((((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) * (m₂ : ZMod q)) * (m₁ : ZMod q)) := by ring
      _ = r₂ * (m₁ : ZMod q) := by
            rw [hm₂left]
            ring
  · intro h
    have hmul := congrArg (fun z : ZMod q => z *
      ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q)) h
    calc
      r₁ * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) = r₁ *
          (((m₂ : ZMod q) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
            rw [hm₂right]
            ring
      _ = (r₁ * (m₂ : ZMod q)) * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) := by ring
      _ = (r₂ * (m₁ : ZMod q)) * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) := hmul
      _ = r₂ * (((m₁ : ZMod q) * ((m₁⁻¹ : (ZMod q)ˣ) : ZMod q)) * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q)) := by ring
      _ = r₂ * ((m₂⁻¹ : (ZMod q)ˣ) : ZMod q) := by
            rw [hm₁right]
            ring

/-- The finite Lemma-7 fiber sum for coefficients indexed by residues and unit denominators. -/
noncomputable def unitInverseIncidenceFibreSum (q : ℕ) [NeZero q]
    (c : ZMod q × (ZMod q)ˣ → ℂ) (x : ZMod q) : ℂ :=
  finiteFibreSum (fun rm : ZMod q × (ZMod q)ˣ =>
    unitInverseIncidenceClass q rm.1 rm.2) c x

/-- Exact source collision expansion for the finite `r m⁻¹` fibers. -/
theorem unitInverseIncidenceFibreSum_energy (q : ℕ) [NeZero q]
    (c : ZMod q × (ZMod q)ˣ → ℂ) :
    ∑ x : ZMod q,
      unitInverseIncidenceFibreSum q c x * star (unitInverseIncidenceFibreSum q c x) =
      ∑ a : ZMod q × (ZMod q)ˣ, ∑ b : ZMod q × (ZMod q)ˣ,
        if a.1 * (b.2 : ZMod q) = b.1 * (a.2 : ZMod q) then c a * star (c b) else 0 := by
  unfold unitInverseIncidenceFibreSum
  rw [finiteFibreSum_energy]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [unitInverseIncidenceClass_eq_iff_crossMul]

/-- The Bézout parameter direction used in the source: simultaneously shifting
`m₁` by `n r₁` and `m₂` by `n r₂` preserves the cross-product difference. -/
theorem crossMul_parametric_shift (r₁ r₂ m₁ m₂ n : ℤ) :
    r₁ * (m₂ + n * r₂) - r₂ * (m₁ + n * r₁) = r₁ * m₂ - r₂ * m₁ := by
  ring

end RHTower
