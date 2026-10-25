import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteFunctions

/-!
# Integer positive-definite functions are sign characters of subgroups

On an additive commutative group `G` of any rank, the even positive-definite functions with integer
values and `φ(0) = 1` are exactly the sign characters of subgroups extended by zero:

`φ(u) = χ(u)` for `u ∈ H`, `φ(u) = 0` otherwise, with `H ≤ G` and `χ : H → {±1}` additive-to-
multiplicative (`intValued_posDef_iff_signCharacter`).

* Every sign character is positive definite (`signCharacter_isEvenPosDef`). Choose a representative
  `r(x)` of each coset of `H`; then `φ(x − y) = [r x = r y] χ(x − r x) χ(y − r y)`, and the Gram
  form is a sum over cosets of squares.
* The converse is the Gram quantization of `PositiveDefiniteFunctions`: the nonvanishing set is a
  subgroup and `φ` is multiplicative on it.
* **Pole isolation.** `φ ≤ 0` off the origin forces `φ = 1_{0}` on every such `φ` exactly when `G`
  has no `2`-torsion (`isolation_forces_dirac_iff`). An element `u ≠ 0` with `2u = 0` carries the
  isolated sign character `1, −1` on `{0, u}`.

So the boundary law of multiplicative positivity is rank-independent: on `ℤ^r`, on `S`-unit groups
`ℤ log p₁ + ⋯ + ℤ log p_r` and on `ℝ` the integer boundary configurations with a unit pole are sign
characters of subgroups, and isolation leaves only `1_{0}`.
-/

open Finset

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open MultiplicativePositivityGeometry

variable {G : Type*} [AddCommGroup G]

/-- A sign character of a subgroup: additive to multiplicative, with values `± 1`. -/
structure IsSignCharacter {H : AddSubgroup G} (χ : H → ℝ) : Prop where
  map_add : ∀ a b, χ (a + b) = χ a * χ b
  sq_eq_one : ∀ a, χ a ^ 2 = 1

/-- A function on a subgroup extended by zero. -/
def extendByZero (H : AddSubgroup G) (χ : H → ℝ) (u : G) : ℝ :=
  if h : u ∈ H then χ ⟨u, h⟩ else 0

namespace IsSignCharacter

variable {H : AddSubgroup G} {χ : H → ℝ}

theorem map_zero (hχ : IsSignCharacter χ) : χ 0 = 1 := by
  have h := hχ.map_add 0 0
  rw [add_zero] at h
  have h1 := hχ.sq_eq_one 0
  nlinarith

theorem map_neg (hχ : IsSignCharacter χ) (a : H) : χ (-a) = χ a := by
  have h := hχ.map_add a (-a)
  rw [add_neg_cancel, hχ.map_zero] at h
  have h1 := hχ.sq_eq_one a
  calc χ (-a) = χ (-a) * χ a ^ 2 := by rw [h1, mul_one]
    _ = χ a * (χ a * χ (-a)) := by ring
    _ = χ a := by rw [← h, mul_one]

theorem map_sub (hχ : IsSignCharacter χ) (a b : H) : χ (a - b) = χ a * χ b := by
  rw [sub_eq_add_neg, hχ.map_add, hχ.map_neg]

end IsSignCharacter

/-- The coset representative of `x`. -/
def cosetRep (H : AddSubgroup G) (x : G) : G := (QuotientAddGroup.mk x : G ⧸ H).out

theorem neg_cosetRep_add_mem (H : AddSubgroup G) (x : G) : -cosetRep H x + x ∈ H :=
  QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : G ⧸ H))

theorem cosetRep_eq_iff (H : AddSubgroup G) (x y : G) :
    cosetRep H x = cosetRep H y ↔ x - y ∈ H := by
  unfold cosetRep
  constructor
  · intro h
    have := congrArg (QuotientAddGroup.mk : G → G ⧸ H) h
    rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
    have h2 := QuotientAddGroup.eq.mp this.symm
    rw [show x - y = -y + x by abel]
    exact h2
  · intro h
    congr 1
    refine QuotientAddGroup.eq.mpr ?_
    rw [show -x + y = -(x - y) by abel]
    exact H.neg_mem h

/-- The sign of `x` relative to its coset representative. -/
def cosetSign (H : AddSubgroup G) (χ : H → ℝ) (x : G) : ℝ :=
  χ ⟨-cosetRep H x + x, neg_cosetRep_add_mem H x⟩

/-- **Coset factorization.** `φ(x − y) = [r x = r y] ε(x) ε(y)`. -/
theorem extendByZero_sub_eq {H : AddSubgroup G} {χ : H → ℝ} (hχ : IsSignCharacter χ) (x y : G) :
    extendByZero H χ (x - y) =
      if cosetRep H x = cosetRep H y then cosetSign H χ x * cosetSign H χ y else 0 := by
  unfold extendByZero
  by_cases hxy : x - y ∈ H
  · have hr := (cosetRep_eq_iff H x y).mpr hxy
    rw [dif_pos hxy, if_pos hr]
    unfold cosetSign
    rw [← hχ.map_sub]
    congr 1
    ext
    simp only [AddSubgroup.coe_sub, hr]
    abel
  · rw [dif_neg hxy, if_neg (fun h => hxy ((cosetRep_eq_iff H x y).mp h))]

/-- **Every sign character of a subgroup is positive definite.** -/
theorem signCharacter_isEvenPosDef {H : AddSubgroup G} {χ : H → ℝ} (hχ : IsSignCharacter χ) :
    IsEvenPosDef (extendByZero H χ) where
  even u := by
    unfold extendByZero
    by_cases hu : u ∈ H
    · rw [dif_pos (H.neg_mem hu), dif_pos hu]
      exact hχ.map_neg ⟨u, hu⟩
    · rw [dif_neg (fun h => hu (by simpa using H.neg_mem h)), dif_neg hu]
  posDef n x c := by
    set R := Finset.univ.image fun i => cosetRep H (x i)
    set f : G → Fin n → ℝ := fun ρ i => if cosetRep H (x i) = ρ then c i * cosetSign H χ (x i) else 0
    have hsplit : ∀ i j, c i * c j * extendByZero H χ (x i - x j) = ∑ ρ ∈ R, f ρ i * f ρ j := by
      intro i j
      rw [extendByZero_sub_eq hχ]
      have hi : cosetRep H (x i) ∈ R := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      by_cases hij : cosetRep H (x i) = cosetRep H (x j)
      · rw [if_pos hij, Finset.sum_eq_single_of_mem _ hi]
        · simp only [f, if_pos rfl, if_pos hij.symm]
          ring
        · intro ρ _ hρ
          simp only [f, if_neg (Ne.symm hρ), zero_mul]
      · rw [if_neg hij, mul_zero]
        refine (Finset.sum_eq_zero fun ρ _ => ?_).symm
        simp only [f]
        by_cases h1 : cosetRep H (x i) = ρ
        · have h2 : ¬ cosetRep H (x j) = ρ := fun h2 => hij (h1.trans h2.symm)
          simp only [if_neg h2, mul_zero]
        · simp only [if_neg h1, zero_mul]
    calc (0 : ℝ) ≤ ∑ ρ ∈ R, (∑ i, f ρ i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      _ = ∑ i, ∑ j, c i * c j * extendByZero H χ (x i - x j) := by
        simp only [hsplit, sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]

/-- **Classification.** An even positive-definite function with integer values and `φ(0) = 1` is
a sign character of a subgroup extended by zero, and conversely. -/
theorem intValued_posDef_iff_signCharacter (φ : G → ℝ) :
    (IsEvenPosDef φ ∧ φ 0 = 1 ∧ ∀ u, ∃ n : ℤ, φ u = n) ↔
      ∃ (H : AddSubgroup G) (χ : H → ℝ), IsSignCharacter χ ∧ φ = extendByZero H χ := by
  constructor
  · rintro ⟨hφ, h0, hint⟩
    refine ⟨nonvanishingSubgroup hφ h0 hint, fun a => φ a, ⟨fun a b => ?_, fun a => ?_⟩, ?_⟩
    · exact intValued_mul hφ h0 hint a.2 b
    · have ha : φ a ≠ 0 := a.2
      rcases intValued_values hφ h0 hint a with h | h | h
      · rw [h]; norm_num
      · exact absurd h ha
      · rw [h]; norm_num
    · funext u
      unfold extendByZero
      by_cases hu : φ u ≠ 0
      · rw [dif_pos (show u ∈ nonvanishingSubgroup hφ h0 hint from hu)]
      · push Not at hu
        rw [dif_neg (show u ∉ nonvanishingSubgroup hφ h0 hint from fun h => h hu), hu]
  · rintro ⟨H, χ, hχ, rfl⟩
    refine ⟨signCharacter_isEvenPosDef hχ, ?_, fun u => ?_⟩
    · unfold extendByZero
      rw [dif_pos H.zero_mem]
      exact hχ.map_zero
    · unfold extendByZero
      by_cases hu : u ∈ H
      · rw [dif_pos hu]
        have hsq : χ ⟨u, hu⟩ * χ ⟨u, hu⟩ = 1 := by rw [← sq]; exact hχ.sq_eq_one ⟨u, hu⟩
        rcases mul_self_eq_one_iff.mp hsq with h | h
        · exact ⟨1, by rw [h]; norm_num⟩
        · exact ⟨-1, by rw [h]; norm_num⟩
      · exact ⟨0, by rw [dif_neg hu]; norm_num⟩

/-! ### Pole isolation and `2`-torsion -/

/-- The subgroup `{0, u}` of an element of order two. -/
def orderTwoSubgroup {u : G} (hu : u + u = 0) : AddSubgroup G where
  carrier := {0, u}
  zero_mem' := Or.inl rfl
  add_mem' {a b} ha hb := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add _)
    · exact Or.inr (add_zero _)
    · exact Or.inl hu
  neg_mem' {a} ha := by
    rcases ha with rfl | rfl
    · exact Or.inl neg_zero
    · exact Or.inr (neg_eq_of_add_eq_zero_right hu)

/-- The sign character `0 ↦ 1`, `u ↦ −1` on `{0, u}`. -/
theorem isSignCharacter_orderTwo {u : G} (hu : u + u = 0) (hu0 : u ≠ 0) :
    IsSignCharacter (fun a : orderTwoSubgroup hu => if (a : G) = 0 then (1 : ℝ) else -1) where
  map_add a b := by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp [hu, hu0]
  sq_eq_one a := by split_ifs <;> norm_num

/-- **Isolation forces the Dirac function iff there is no `2`-torsion.** -/
theorem isolation_forces_dirac_iff :
    (∀ φ : G → ℝ, IsEvenPosDef φ → φ 0 = 1 → (∀ u, ∃ n : ℤ, φ u = n) →
        (∀ u, u ≠ 0 → φ u ≤ 0) → ∀ u, u ≠ 0 → φ u = 0) ↔
      ∀ u : G, u + u = 0 → u = 0 := by
  constructor
  · intro h u hu
    by_contra hu0
    set χ := fun a : orderTwoSubgroup hu => if (a : G) = 0 then (1 : ℝ) else -1
    have hχ := isSignCharacter_orderTwo hu hu0
    have hmem : u ∈ orderTwoSubgroup hu := Or.inr rfl
    have hval : extendByZero (orderTwoSubgroup hu) χ u = -1 := by
      unfold extendByZero
      rw [dif_pos hmem]
      simp [χ, hu0]
    obtain ⟨hpd, h0, hint⟩ :=
      (intValued_posDef_iff_signCharacter (extendByZero (orderTwoSubgroup hu) χ)).mpr
        ⟨_, χ, hχ, rfl⟩
    have hnp : ∀ v, v ≠ 0 → extendByZero (orderTwoSubgroup hu) χ v ≤ 0 := by
      intro v hv
      unfold extendByZero
      split_ifs with hm
      · simp [χ, hv]
      · exact le_rfl
    have := h _ hpd h0 hint hnp u hu0
    rw [hval] at this
    norm_num at this
  · intro htor φ hφ h0 hint hnp u hu
    exact intValued_eq_zero_of_nonpos hφ h0 hint hnp htor hu

/-- On a torsion-free group (`ℤ^r`, `ℝ`, `S`-unit groups) isolation leaves only `1_{0}`. -/
theorem isolation_forces_dirac [NoZeroSMulDivisors ℕ G] {φ : G → ℝ} (hφ : IsEvenPosDef φ)
    (h0 : φ 0 = 1) (hint : ∀ u, ∃ n : ℤ, φ u = n) (hnp : ∀ u, u ≠ 0 → φ u ≤ 0) {u : G}
    (hu : u ≠ 0) : φ u = 0 :=
  isolation_forces_dirac_iff.mpr (fun v hv => by
    have : (2 : ℕ) • v = 0 := by rw [two_nsmul]; exact hv
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)) φ hφ h0 hint hnp u hu

end GaloisForLFunctions.ArithmeticPositiveDuality
