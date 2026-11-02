import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheJordanLimitCountsProjectiveSpace

/-!
# The count law over every finite ring

The first-order structure of the degeneration is the point count of projective space over the
residue rings `ℤ/m` (`TheJordanLimitCountsProjectiveSpace`). The count law is not a property of `ℤ`:
it holds over every finite commutative ring, in particular over the residue rings `𝔽_q[T]/(m)` of
the function field, where RH is a theorem.

* **Orbit law** (`natCard_unimodular_eq`): units act freely on unimodular vectors of `R^k`, so
  `#Unimod(R^k) = #ℙ^{k−1}(R) · #Rˣ` for every finite commutative ring `R`.
* **Local count** (`natCard_unimodular_local`): over a finite local ring with maximal ideal `𝔪` a
  vector is unimodular iff some entry is a unit, so `#Unimod(R^k) = |R|^k − |𝔪|^k`.
* **Hensel law** (`natCard_projSpace_local`): `#ℙ^{k−1}(R) (|R| − |𝔪|) = |R|^k − |𝔪|^k`; with
  `|R| = |𝔪| q`, `q = |R/𝔪|`, this is `#ℙ^{k−1}(R) = |𝔪|^{k−1} #ℙ^{k−1}(𝔽_q)`, the weight string
  of a prime power over its residue field, in every residue ring of every Dedekind domain.

The first-order count is the same over `ℤ` and over `𝔽_q[T]`: it carries no selection, and the
sign question lives in the second-order term on both sides.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

variable (R : Type*) [CommRing R] (k : ℕ)

/-- The unimodular vectors of `R^k`: entries generating the unit ideal. -/
abbrev Unimodular := {v : Fin k → R // IsPrimitiveVec v}

/-- Units act on unimodular vectors by scaling. -/
instance unimodularMulAction : MulAction Rˣ (Unimodular R k) where
  smul u v := ⟨fun i => (u : R) * v.1 i, by
    obtain ⟨l, hl⟩ := v.2
    refine ⟨fun i => (↑u⁻¹ : R) * l i, ?_⟩
    calc ∑ i, (↑u⁻¹ : R) * l i * ((u : R) * v.1 i) = ((↑u⁻¹ : R) * u) * ∑ i, l i * v.1 i := by
          rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
      _ = 1 := by rw [hl, Units.inv_mul, one_mul]⟩
  one_smul v := Subtype.ext (funext fun i => by
    change ((1 : Rˣ) : R) * v.1 i = v.1 i
    rw [Units.val_one, one_mul])
  mul_smul u w v := Subtype.ext (funext fun i => by
    change ((u * w : Rˣ) : R) * v.1 i = (u : R) * ((w : R) * v.1 i)
    rw [Units.val_mul, mul_assoc])

/-- The points of `ℙ^{k−1}(R)`: unimodular vectors modulo units. -/
abbrev ProjSpace := MulAction.orbitRel.Quotient Rˣ (Unimodular R k)

variable {R k}

/-- The action of the units is free. -/
theorem eq_one_of_smul_eq_unimodular {u : Rˣ} {v : Unimodular R k} (h : u • v = v) : u = 1 := by
  obtain ⟨l, hl⟩ := v.2
  have hv : ∀ i, (u : R) * v.1 i = v.1 i := fun i => congrFun (congrArg Subtype.val h) i
  apply Units.ext
  calc (u : R) = (u : R) * ∑ i, l i * v.1 i := by rw [hl, mul_one]
    _ = ∑ i, l i * ((u : R) * v.1 i) := by rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
    _ = 1 := by simp only [hv, hl]
    _ = ((1 : Rˣ) : R) := Units.val_one.symm

variable (R k)

/-- **Orbit law**: `#Unimod(R^k) = #ℙ^{k−1}(R) · #Rˣ`. -/
theorem natCard_unimodular_eq [Fintype R] [DecidableEq R] :
    Nat.card (Unimodular R k) = Nat.card (ProjSpace R k) * Nat.card Rˣ := by
  classical
  have horb : ∀ x : Unimodular R k, Nat.card (MulAction.orbit Rˣ x) = Nat.card Rˣ := fun x => by
    refine (Nat.card_congr (Equiv.ofBijective (fun g : Rˣ =>
      (⟨g • x, MulAction.mem_orbit x g⟩ : MulAction.orbit Rˣ x)) ⟨?_, ?_⟩)).symm
    · intro g h hgh
      have h1 : g • x = h • x := congrArg Subtype.val hgh
      have h2 : (h⁻¹ * g) • x = x := by rw [mul_smul, h1, ← mul_smul, inv_mul_cancel, one_smul]
      have := eq_one_of_smul_eq_unimodular h2
      rw [inv_mul_eq_one] at this
      exact this.symm
    · rintro ⟨y, g, rfl⟩
      exact ⟨g, rfl⟩
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits Rˣ (Unimodular R k)), Nat.card_sigma]
  simp only [horb, sum_const, card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card (α := ProjSpace R k)]

/-! ### Finite local rings -/

/-- Over a local ring a vector is unimodular iff some entry is a unit. -/
theorem isPrimitiveVec_iff_exists_isUnit_of_local [IsLocalRing R] (v : Fin k → R) :
    IsPrimitiveVec v ↔ ∃ i, IsUnit (v i) := by
  constructor
  · rintro ⟨l, hl⟩
    by_contra hall
    push Not at hall
    have hmem : ∑ i, l i * v i ∈ IsLocalRing.maximalIdeal R :=
      Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _
        ((IsLocalRing.mem_maximalIdeal _).mpr (hall i))
    rw [hl] at hmem
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
  · rintro ⟨i, hi⟩
    obtain ⟨u, hu⟩ := hi
    refine ⟨fun j => if j = i then (↑u⁻¹ : R) else 0, ?_⟩
    rw [sum_eq_single i (fun j _ hj => by simp only [if_neg hj, zero_mul])
      (fun h => absurd (mem_univ i) h)]
    simp only [← hu, if_true, Units.inv_mul]

/-- The non-unimodular vectors of a local ring are the vectors with entries in `𝔪`. -/
def notUnimodularEquiv [IsLocalRing R] :
    {v : Fin k → R // ¬IsPrimitiveVec v} ≃ (Fin k → IsLocalRing.maximalIdeal R) where
  toFun v i := ⟨v.1 i, by
    have := v.2
    rw [isPrimitiveVec_iff_exists_isUnit_of_local, not_exists] at this
    exact (IsLocalRing.mem_maximalIdeal _).mpr (this i)⟩
  invFun w := ⟨fun i => (w i : R), by
    rw [isPrimitiveVec_iff_exists_isUnit_of_local, not_exists]
    exact fun i => (IsLocalRing.mem_maximalIdeal _).mp (w i).2⟩
  left_inv v := rfl
  right_inv w := rfl

/-- **Local count**: `#Unimod(R^k) = |R|^k − |𝔪|^k`. -/
theorem natCard_unimodular_local [Fintype R] [DecidableEq R] [IsLocalRing R] :
    Nat.card (Unimodular R k) = Nat.card R ^ k - Nat.card (IsLocalRing.maximalIdeal R) ^ k := by
  classical
  have htot : Nat.card (Unimodular R k) + Nat.card {v : Fin k → R // ¬IsPrimitiveVec v} =
      Nat.card (Fin k → R) := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl fun v : Fin k → R => IsPrimitiveVec v)]
  rw [Nat.card_congr (notUnimodularEquiv R k), Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin k),
    Fintype.card_fin] at htot
  omega

/-- In a local ring the units are the complement of `𝔪`: `#Rˣ = |R| − |𝔪|`. -/
theorem natCard_units_local [Fintype R] [DecidableEq R] [IsLocalRing R] :
    Nat.card Rˣ = Nat.card R - Nat.card (IsLocalRing.maximalIdeal R) := by
  classical
  have h1 : Nat.card Rˣ = Nat.card {x : R // IsUnit x} :=
    Nat.card_congr (unitsEquivIsUnit R)
  have h2 : Nat.card {x : R // IsUnit x} + Nat.card {x : R // ¬IsUnit x} = Nat.card R := by
    rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl fun x : R => IsUnit x)]
  have h3 : Nat.card {x : R // ¬IsUnit x} = Nat.card (IsLocalRing.maximalIdeal R) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (IsLocalRing.mem_maximalIdeal x).symm)
  omega

/-- **Hensel law of the count**: over a finite local ring,
`#ℙ^{k−1}(R) (|R| − |𝔪|) = |R|^k − |𝔪|^k`. -/
theorem natCard_projSpace_local [Fintype R] [DecidableEq R] [IsLocalRing R] :
    Nat.card (ProjSpace R k) * (Nat.card R - Nat.card (IsLocalRing.maximalIdeal R)) =
      Nat.card R ^ k - Nat.card (IsLocalRing.maximalIdeal R) ^ k := by
  rw [← natCard_units_local, ← natCard_unimodular_eq, natCard_unimodular_local]

/-- Over the residue rings of `ℤ` the general count is the Jordan count:
`#ℙ^{k−1}(ℤ/m) = #ProjPoints k m`. -/
theorem natCard_projSpace_zmod (m : ℕ) :
    Nat.card (ProjSpace (ZMod m) k) = Nat.card (ProjPoints k m) := rfl

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
