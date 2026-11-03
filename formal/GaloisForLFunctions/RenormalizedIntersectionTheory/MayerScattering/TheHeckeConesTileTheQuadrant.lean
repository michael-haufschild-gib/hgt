import Mathlib

/-!
# The Hecke cones tile the quadrant

The **Hecke bases** of determinant `n` are the integer matrices with rows `u₁ = (a, b)`, `u₂ = (c, d)`,
`0 ≤ c < a`, `0 ≤ b < d`, `ad − bc = n` (`IsHeckeBasis`); for `n = 2` they are the four Barnes cones of
the source operator `T₂`, for `n = 3` its seven cones. The **cone** of a basis is
`{m u₁ + k u₂ : m ≥ 1, k ≥ 0}` (`InHeckeCone`).

* **Uniqueness** (`heckeBasis_eq_of_inCone`): two Hecke bases of the same lattice whose cones share a
  vector coincide. The argument is integral: writing the second basis in the first,
  `u₁' = αu₁ + βu₂`, `u₂' = γu₁ + δu₂`, the Hecke inequalities force `α − γ ≥ 1`, `β − δ ≤ −1`
  (`hecke_shift_bounds`), the inverse change of basis forces `γ + δ ≥ 1`, `α + β ≥ 1`, and the
  unimodularity `αδ − βγ = 1` with the cone coefficients leaves only the identity.
* **The chain** (`exists_inCone_of_sameLattice`): from a Hecke basis whose second coefficient of a
  vector `v` (with `x ≥ 1`) is nonnegative, the successor `(u₂, t u₂ − u₁)`, `t = ⌈a/c⌉`, is again a
  Hecke basis of the same lattice; walking the chain reaches a basis whose cone contains `v`.
-/

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- A **Hecke basis** of determinant `n`: rows `(a, b)`, `(c, d)` with `0 ≤ c < a`, `0 ≤ b < d`,
`ad − bc = n`. -/
structure IsHeckeBasis (n a b c d : ℤ) : Prop where
  c_nonneg : 0 ≤ c
  c_lt : c < a
  b_nonneg : 0 ≤ b
  b_lt : b < d
  det : a * d - b * c = n

/-- `v = (x, y)` lies in the **cone** of the basis: `v = m(a, b) + k(c, d)`, `m ≥ 1`, `k ≥ 0`. -/
def InHeckeCone (a b c d x y : ℤ) : Prop :=
  ∃ m k : ℤ, 1 ≤ m ∧ 0 ≤ k ∧ x = m * a + k * c ∧ y = m * b + k * d

/-- Two bases span the **same lattice**: the second is a unimodular combination of the first. -/
def SameLattice (a b c d a' b' c' d' : ℤ) : Prop :=
  ∃ α β γ δ : ℤ, α * δ - β * γ = 1 ∧ a' = α * a + β * c ∧ b' = α * b + β * d ∧
    c' = γ * a + δ * c ∧ d' = γ * b + δ * d

theorem sameLattice_refl (a b c d : ℤ) : SameLattice a b c d a b c d :=
  ⟨1, 0, 0, 1, by ring, by ring, by ring, by ring, by ring⟩

theorem SameLattice.trans {a b c d a' b' c' d' a'' b'' c'' d'' : ℤ}
    (h₁ : SameLattice a b c d a' b' c' d') (h₂ : SameLattice a' b' c' d' a'' b'' c'' d'') :
    SameLattice a b c d a'' b'' c'' d'' := by
  obtain ⟨α, β, γ, δ, hd, h1, h2, h3, h4⟩ := h₁
  obtain ⟨α', β', γ', δ', hd', h1', h2', h3', h4'⟩ := h₂
  refine ⟨α' * α + β' * γ, α' * β + β' * δ, γ' * α + δ' * γ, γ' * β + δ' * δ, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (α' * δ' - β' * γ') * hd + hd'
  · rw [h1', h1, h3]; ring
  · rw [h2', h2, h4]; ring
  · rw [h3', h1, h3]; ring
  · rw [h4', h2, h4]; ring

theorem SameLattice.symm {a b c d a' b' c' d' : ℤ} (h : SameLattice a b c d a' b' c' d') :
    SameLattice a' b' c' d' a b c d := by
  obtain ⟨α, β, γ, δ, hd, h1, h2, h3, h4⟩ := h
  refine ⟨δ, -β, -γ, α, by linear_combination hd, ?_, ?_, ?_, ?_⟩
  · rw [h1, h3]; linear_combination (-a) * hd
  · rw [h2, h4]; linear_combination (-b) * hd
  · rw [h1, h3]; linear_combination (-c) * hd
  · rw [h2, h4]; linear_combination (-d) * hd

/-! ### Uniqueness -/

/-- **The Hecke inequalities pin the change of basis**: if `(a', b') = α(a,b) + β(c,d)` and
`(c', d') = γ(a,b) + δ(c,d)` with `c' < a'`, `b' < d'`, then `α − γ ≥ 1` and `β − δ ≤ −1`. -/
theorem hecke_shift_bounds {n a b c d α β γ δ : ℤ} (h : IsHeckeBasis n a b c d) (hn : 0 < n)
    (hca : γ * a + δ * c < α * a + β * c) (hbd : α * b + β * d < γ * b + δ * d) :
    1 ≤ α - γ ∧ β - δ ≤ -1 := by
  have hd0 : 0 < d := lt_of_le_of_lt h.b_nonneg h.b_lt
  have ha0 : 0 < a := lt_of_le_of_lt h.c_nonneg h.c_lt
  have e1 : 0 < (α - γ) * a + (β - δ) * c := by linarith
  have e2 : (α - γ) * b + (β - δ) * d < 0 := by linarith
  have hP : 0 < (α - γ) * n := by
    rw [← h.det]
    nlinarith [mul_pos e1 hd0, mul_nonpos_iff.mpr (Or.inl ⟨h.c_nonneg, e2.le⟩)]
  have hR : (β - δ) * n < 0 := by
    rw [← h.det]
    nlinarith [mul_neg_of_pos_of_neg ha0 e2, mul_nonneg h.b_nonneg e1.le]
  constructor
  · by_contra hc
    push_neg at hc
    nlinarith
  · by_contra hc
    push_neg at hc
    nlinarith

/-- **Uniqueness of the Hecke cone through a vector**: two Hecke bases of the same lattice whose
cones contain the same vector are equal. -/
theorem heckeBasis_eq_of_inCone {n a b c d a' b' c' d' x y : ℤ} (hn : 0 < n)
    (h : IsHeckeBasis n a b c d) (h' : IsHeckeBasis n a' b' c' d')
    (hs : SameLattice a b c d a' b' c' d') (hv : InHeckeCone a b c d x y)
    (hv' : InHeckeCone a' b' c' d' x y) : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  obtain ⟨α, β, γ, δ, hdet, h1, h2, h3, h4⟩ := hs
  obtain ⟨m, k, hm, hk, hx, hy⟩ := hv
  obtain ⟨m', k', hm', hk', hx', hy'⟩ := hv'
  -- coefficients of `v` in the first basis
  have hcx : (m - (m' * α + k' * γ)) * a + (k - (m' * β + k' * δ)) * c = 0 := by
    rw [h1, h3] at hx'; linear_combination hx - hx'
  have hcy : (m - (m' * α + k' * γ)) * b + (k - (m' * β + k' * δ)) * d = 0 := by
    rw [h2, h4] at hy'; linear_combination hy - hy'
  have hnz : (a * d - b * c) ≠ 0 := by rw [h.det]; exact hn.ne'
  have hmeq : m = m' * α + k' * γ := by
    have : (m - (m' * α + k' * γ)) * (a * d - b * c) = 0 := by
      linear_combination d * hcx - c * hcy
    have := (mul_eq_zero.mp this).resolve_right hnz
    linarith
  have hkeq : k = m' * β + k' * δ := by
    have : (k - (m' * β + k' * δ)) * (a * d - b * c) = 0 := by
      linear_combination a * hcy - b * hcx
    have := (mul_eq_zero.mp this).resolve_right hnz
    linarith
  -- the Hecke inequalities of both bases
  obtain ⟨hP, hR⟩ := hecke_shift_bounds h hn (by rw [← h1, ← h3]; exact h'.c_lt)
    (by rw [← h2, ← h4]; exact h'.b_lt)
  have hs' : SameLattice a' b' c' d' a b c d := (⟨α, β, γ, δ, hdet, h1, h2, h3, h4⟩ :
    SameLattice a b c d a' b' c' d').symm
  obtain ⟨hP', hR'⟩ := hecke_shift_bounds (α := δ) (β := -β) (γ := -γ) (δ := α) h' hn
    (by
      have e3 : a = δ * a' + -β * c' := by rw [h1, h3]; linear_combination (-a) * hdet
      have e4 : c = -γ * a' + α * c' := by rw [h1, h3]; linear_combination (-c) * hdet
      rw [← e3, ← e4]; exact h.c_lt)
    (by
      have e5 : b = δ * b' + -β * d' := by rw [h2, h4]; linear_combination (-b) * hdet
      have e6 : d = -γ * b' + α * d' := by rw [h2, h4]; linear_combination (-d) * hdet
      rw [← e5, ← e6]; exact h.b_lt)
  -- the change of basis is the identity
  have hid : α = 1 ∧ β = 0 ∧ γ = 0 ∧ δ = 1 := by
    have hk'eq : k' = α * k - β * m := by
      rw [hmeq, hkeq]; linear_combination (-k') * hdet
    rcases le_or_gt β 0 with hβ | hβ <;> rcases le_or_gt γ 0 with hγ | hγ
    · -- `β ≤ 0`, `γ ≤ 0`
      rcases lt_or_eq_of_le hβ with hβ' | hβ'
      · exfalso
        rcases lt_or_eq_of_le hγ with hγ' | hγ'
        · nlinarith
        · subst hγ'
          nlinarith
      · subst hβ'
        have hα : 1 ≤ α := by linarith
        have hδ1 : α * δ = 1 := by linarith
        have hδ : δ = 1 := by
          rcases (Int.eq_one_or_neg_one_of_mul_eq_one' hδ1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact h2
          · linarith
        have hα1 : α = 1 := by rw [hδ, mul_one] at hδ1; exact hδ1
        exact ⟨hα1, rfl, by linarith, hδ⟩
    · -- `β ≤ 0`, `γ ≥ 1`
      exfalso
      rcases le_or_gt δ 0 with hδ | hδ
      · nlinarith
      · nlinarith
    · -- `β ≥ 1`, `γ ≤ 0`
      exfalso
      nlinarith
    · -- `β ≥ 1`, `γ ≥ 1`
      exfalso
      nlinarith
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hid
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
