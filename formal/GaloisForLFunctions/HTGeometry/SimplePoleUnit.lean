import GaloisForLFunctions.HTGeometry.QResidueStabilizer

/-!
# The normalized simple-pole unit `x/(x − α)`

This is the building block of the realization theorem: it vanishes at the origin, is regular
everywhere except at `α`, and has principal part exactly `α/(x − α)`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- The normalized simple-pole unit `x/(x − α)`. -/
def simplePoleUnit (α : K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) Polynomial.X
    / algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)

theorem simplePoleUnit_mul (α : K) :
    simplePoleUnit α * ((RatFunc.X : RatFunc K) - algebraMap K (RatFunc K) α)
      = algebraMap (Polynomial K) (RatFunc K) Polynomial.X
        / algebraMap (Polynomial K) (RatFunc K) 1 := by
  have hne : algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero α)
  rw [simplePoleUnit, ratFuncX_sub_algebraMap, map_one, div_one, div_mul_cancel₀ _ hne]

theorem polePart_simplePoleUnit_self (α : K) :
    polePart (simplePoleUnit α) α 1 = α := by
  have h := polePart_top_of_repr (g := simplePoleUnit α) (c := α) (m := 1)
    (P := Polynomial.X) (Q := 1) (by simp) (by simpa using simplePoleUnit_mul α)
  simpa using h

theorem polePart_simplePoleUnit_self_of_lt (α : K) {d : ℕ} (hd : 1 < d) :
    polePart (simplePoleUnit α) α d = 0 := by
  refine polePart_eq_zero_of_regularAt_mul_pow (m := 1) ?_ hd
  rw [pow_one]
  exact regularAt_of_repr (P := Polynomial.X) (Q := 1) (by simp)
    (by simpa using simplePoleUnit_mul α)

theorem regularAt_simplePoleUnit {α β : K} (h : β ≠ α) : RegularAt (simplePoleUnit α) β := by
  refine regularAt_of_repr (P := Polynomial.X) (Q := Polynomial.X - Polynomial.C α) ?_ rfl
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.2 h

theorem polePart_simplePoleUnit_of_ne {α β : K} (h : β ≠ α) {d : ℕ} (hd : 0 < d) :
    polePart (simplePoleUnit α) β d = 0 :=
  polePart_eq_zero_of_poleOrder_zero hd
    ((regularAt_iff_poleOrder_eq_zero _ _).1 (regularAt_simplePoleUnit h))

theorem polePart_simplePoleUnit_zero_zero {α : K} (hα : α ≠ 0) :
    polePart (simplePoleUnit α) 0 0 = 0 := by
  rw [polePart, ratFuncShift_zero, simplePoleUnit, Nat.cast_zero, neg_zero,
    coeff_zero_algebraMap_div Polynomial.X (Polynomial.X - Polynomial.C α)
      (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
          exact neg_ne_zero.2 hα)]
  simp


/-- The realization increment attached to a finite set of poles. -/
def simplePoleSum (S : Finset K) : RatFunc K := ∑ α ∈ S, simplePoleUnit α

theorem polePart_simplePoleSum_mem {S : Finset K} {β : K} (hβ : β ∈ S) :
    polePart (simplePoleSum S) β 1 = β := by
  classical
  rw [simplePoleSum, polePart_sum, Finset.sum_eq_single β]
  · exact polePart_simplePoleUnit_self β
  · intro b _ hb
    exact polePart_simplePoleUnit_of_ne (fun h => hb h.symm) one_pos
  · intro h
    exact absurd hβ h

theorem polePart_simplePoleSum_not_mem {S : Finset K} {β : K} (hβ : β ∉ S) {d : ℕ} (hd : 0 < d) :
    polePart (simplePoleSum S) β d = 0 := by
  classical
  rw [simplePoleSum, polePart_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  exact polePart_simplePoleUnit_of_ne (fun h => hβ (by rw [h]; exact hb)) hd

theorem polePart_simplePoleSum_of_lt {S : Finset K} (β : K) {d : ℕ} (hd : 1 < d) :
    polePart (simplePoleSum S) β d = 0 := by
  classical
  rw [simplePoleSum, polePart_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  by_cases h : β = b
  · subst h
    exact polePart_simplePoleUnit_self_of_lt β hd
  · exact polePart_simplePoleUnit_of_ne h (by omega)

theorem polePart_simplePoleSum_zero_zero {S : Finset K} (hS0 : ∀ α ∈ S, α ≠ 0) :
    polePart (simplePoleSum S) 0 0 = 0 := by
  classical
  rw [simplePoleSum, polePart_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  exact polePart_simplePoleUnit_zero_zero (hS0 b hb)

theorem polePart_simplePoleSum_zero {S : Finset K} (hS0 : ∀ α ∈ S, α ≠ 0) {d : ℕ} (hd : 0 < d) :
    polePart (simplePoleSum S) 0 d = 0 := by
  classical
  refine polePart_simplePoleSum_not_mem (fun h => ?_) hd
  exact hS0 0 h rfl


/-- The union of the `q`-orbits of a finite set of points. -/
def orbitUnion (q : K) (S : Finset K) : Set K := {γ : K | γ ≠ 0 ∧ ∃ n : ℤ, γ * q ^ n ∈ S}

theorem qOrbitResidue_simplePoleSum_one_of_mem {q : K} (hq : q ≠ 0) {S : Finset K}
    (hSorb : ∀ α ∈ S, ∀ β ∈ S, ∀ n : ℤ, α = β * q ^ n → n = 0)
    {γ : K} {n₀ : ℤ} (hn₀ : γ * q ^ n₀ ∈ S) :
    qOrbitResidue q γ 1 (simplePoleSum S) = γ := by
  classical
  have hmem : ∀ n : ℤ, polePart (simplePoleSum S) (multOrbit q γ n) 1 ≠ 0 →
      n ∈ ({n₀} : Finset ℤ) := by
    intro n hn
    by_cases h : γ * q ^ n ∈ S
    · have hrel : γ * q ^ n = (γ * q ^ n₀) * q ^ (n - n₀) := by
        rw [mul_assoc, ← zpow_add₀ hq]
        congr 2
        ring
      have := hSorb _ h _ hn₀ (n - n₀) hrel
      simp only [Finset.mem_singleton]
      omega
    · exact absurd (polePart_simplePoleSum_not_mem (by simpa [multOrbit] using h) one_pos) hn
  rw [qOrbitResidue_eq_sum _ _ hmem, Finset.sum_singleton]
  rw [show multOrbit q γ n₀ = γ * q ^ n₀ from rfl, polePart_simplePoleSum_mem hn₀]
  rw [Nat.cast_one, ← zpow_mul]
  rw [show q ^ (-(1 : ℤ) * n₀) * (γ * q ^ n₀) = γ * (q ^ (-(1 : ℤ) * n₀) * q ^ n₀) from by ring,
    ← zpow_add₀ hq, show -(1 : ℤ) * n₀ + n₀ = 0 from by ring, zpow_zero, mul_one]

theorem qOrbitResidue_simplePoleSum_one_of_not_mem {q : K} {S : Finset K} {γ : K}
    (h : ∀ n : ℤ, γ * q ^ n ∉ S) :
    qOrbitResidue q γ 1 (simplePoleSum S) = 0 := by
  classical
  rw [qOrbitResidue_eq_sum _ (∅ : Finset ℤ) ?_, Finset.sum_empty]
  intro n hn
  exact absurd (polePart_simplePoleSum_not_mem (by simpa [multOrbit] using h n) one_pos) hn

theorem qOrbitResidue_simplePoleSum_of_lt {q : K} {S : Finset K} (γ : K) {d : ℕ} (hd : 1 < d) :
    qOrbitResidue q γ d (simplePoleSum S) = 0 := by
  classical
  rw [qOrbitResidue_eq_sum _ (∅ : Finset ℤ) ?_, Finset.sum_empty]
  intro n hn
  exact absurd (polePart_simplePoleSum_of_lt _ hd) hn

/-- **The residue support of the realization increment is the orbit union.** -/
theorem residueSupport_simplePoleSum {q : K} (hq : q ≠ 0) {S : Finset K}
    (hSorb : ∀ α ∈ S, ∀ β ∈ S, ∀ n : ℤ, α = β * q ^ n → n = 0) :
    residueSupport q (simplePoleSum S) = orbitUnion q S := by
  ext γ
  constructor
  · rintro ⟨hγ0, d, hd, hres⟩
    refine ⟨hγ0, ?_⟩
    by_contra hcon
    push Not at hcon
    rcases Nat.lt_or_ge 1 d with h | h
    · exact hres (qOrbitResidue_simplePoleSum_of_lt γ h)
    · have hd1 : d = 1 := by omega
      subst hd1
      exact hres (qOrbitResidue_simplePoleSum_one_of_not_mem hcon)
  · rintro ⟨hγ0, n₀, hn₀⟩
    refine ⟨hγ0, 1, one_pos, ?_⟩
    rw [qOrbitResidue_simplePoleSum_one_of_mem hq hSorb hn₀]
    exact hγ0


theorem mem_orbitUnion_of_mem (q : K) {S : Finset K} (hS0 : ∀ α ∈ S, α ≠ 0) {α : K}
    (hα : α ∈ S) : α ∈ orbitUnion q S :=
  ⟨hS0 α hα, 0, by simpa using hα⟩

theorem one_mem_orbitUnion {q : K} {S : Finset K} (hS0 : ∀ α ∈ S, α ≠ 0) (hne : S.Nonempty)
    (hdiv : ∀ x ∈ orbitUnion q S, ∀ y ∈ orbitUnion q S, x / y ∈ orbitUnion q S) :
    (1 : K) ∈ orbitUnion q S := by
  obtain ⟨α₀, hα₀⟩ := hne
  have hmem := mem_orbitUnion_of_mem q hS0 hα₀
  have := hdiv α₀ hmem α₀ hmem
  rwa [div_self (hS0 α₀ hα₀)] at this

theorem mul_mem_orbitUnion {q : K} {S : Finset K} (hS0 : ∀ α ∈ S, α ≠ 0) (hne : S.Nonempty)
    (hdiv : ∀ x ∈ orbitUnion q S, ∀ y ∈ orbitUnion q S, x / y ∈ orbitUnion q S)
    {x y : K} (hx : x ∈ orbitUnion q S) (hy : y ∈ orbitUnion q S) :
    x * y ∈ orbitUnion q S := by
  have hone := one_mem_orbitUnion hS0 hne hdiv
  have hinv : (1 : K) / y ∈ orbitUnion q S := hdiv 1 hone y hy
  have := hdiv x hx (1 / y) hinv
  rwa [div_div_eq_mul_div, div_one] at this

/-- **Realization.**  The summability stabilizer of the realization increment is exactly the given
orbit union. -/
theorem qSummable_ratFuncScale_simplePoleSum_sub_iff [CharZero K] [IsAlgClosed K] {q : K}
    (hq : q ≠ 0) (hqtor : ∀ n : ℤ, n ≠ 0 → q ^ n ≠ 1) {S : Finset K}
    (hS0 : ∀ α ∈ S, α ≠ 0)
    (hSorb : ∀ α ∈ S, ∀ β ∈ S, ∀ n : ℤ, α = β * q ^ n → n = 0)
    (hne : S.Nonempty)
    (hdiv : ∀ x ∈ orbitUnion q S, ∀ y ∈ orbitUnion q S, x / y ∈ orbitUnion q S)
    {a : K} (ha : a ≠ 0) :
    QSummable q hq (ratFuncScale a ha (simplePoleSum S) - simplePoleSum S)
      ↔ a ∈ orbitUnion q S := by
  obtain ⟨α₀, hα₀S⟩ := hne
  have hα₀ : α₀ ∈ orbitUnion q S := mem_orbitUnion_of_mem q hS0 hα₀S
  have hsupp := residueSupport_simplePoleSum hq hSorb (S := S)
  constructor
  · intro hsum
    have hmul : a * α₀ ∈ orbitUnion q S := by
      rw [← hsupp]
      exact mul_mem_residueSupport hq hqtor ha _ hsum (by rw [hsupp]; exact hα₀)
    have := hdiv (a * α₀) hmul α₀ hα₀
    rwa [mul_div_assoc, div_self (hS0 α₀ hα₀S), mul_one] at this
  · intro hamem
    have hstab : ∀ γ : K, γ ≠ 0 → (a * γ ∈ orbitUnion q S ↔ γ ∈ orbitUnion q S) := by
      intro γ hγ
      constructor
      · intro h
        have := hdiv (a * γ) h a hamem
        rwa [mul_comm, mul_div_assoc, div_self ha, mul_one] at this
      · intro h
        exact mul_mem_orbitUnion hS0 ⟨α₀, hα₀S⟩ hdiv hamem h
    refine exists_dilationTelescoper_of_qOrbitResidue_vanish hq hqtor _
      (polePart_ratFuncScale_sub_zero ha _ 0 (polePart_simplePoleSum_zero_zero hS0))
      (fun d hd => polePart_ratFuncScale_sub_zero ha _ d (polePart_simplePoleSum_zero hS0 hd))
      fun γ hγ d hd => ?_
    rw [qOrbitResidue_sub hq hqtor hγ hd, qOrbitResidue_ratFuncScale ha γ d]
    rcases Nat.lt_or_ge 1 d with hd2 | hd1
    · rw [qOrbitResidue_simplePoleSum_of_lt _ hd2, qOrbitResidue_simplePoleSum_of_lt _ hd2]
      ring
    · have hd1' : d = 1 := by omega
      subst hd1'
      by_cases hγmem : γ ∈ orbitUnion q S
      · obtain ⟨-, n₀, hn₀⟩ := hγmem
        obtain ⟨-, m₀, hm₀⟩ := (hstab γ hγ).2 ⟨hγ, n₀, hn₀⟩
        rw [qOrbitResidue_simplePoleSum_one_of_mem hq hSorb hm₀,
          qOrbitResidue_simplePoleSum_one_of_mem hq hSorb hn₀, Nat.cast_one, zpow_neg, zpow_one]
        field_simp
        ring
      · have hnot : ∀ n : ℤ, γ * q ^ n ∉ S := by
          intro n hn
          exact hγmem ⟨hγ, n, hn⟩
        have hnot' : ∀ n : ℤ, a * γ * q ^ n ∉ S := by
          intro n hn
          exact hγmem ((hstab γ hγ).1 ⟨mul_ne_zero ha hγ, n, hn⟩)
        rw [qOrbitResidue_simplePoleSum_one_of_not_mem hnot,
          qOrbitResidue_simplePoleSum_one_of_not_mem hnot']
        ring

end

end GaloisForLFunctions.HTGeometry
