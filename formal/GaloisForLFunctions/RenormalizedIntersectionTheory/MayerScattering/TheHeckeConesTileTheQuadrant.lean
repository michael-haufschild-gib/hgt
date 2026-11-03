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
* **The chain** (`exists_inCone_of_basis`): from a Hecke basis whose second coefficient of a
  vector `v` (with `x ≥ 1`) is nonnegative, the successor `(u₂, t u₂ − u₁)`, `t = ⌈a/c⌉`, is again a
  Hecke basis of the same lattice; walking the chain reaches a basis whose cone contains `v`.
* **Prime count** (`heckeConeCount_eq`): for a prime `p` the index-`p` lattices are the `p + 1` lines of
  `𝔽_p²`; each line through `v` carries exactly one cone through `v`, so `v = (x, y)`, `x ≥ 1`, `y ≥ 0`,
  lies in `1` cone, or in `p + 1` cones when `p ∣ x` and `p ∣ y`.
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
    push Not at hc
    nlinarith
  · by_contra hc
    push Not at hc
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
    rw [h1, h3] at hx'; linear_combination hx' - hx
  have hcy : (m - (m' * α + k' * γ)) * b + (k - (m' * β + k' * δ)) * d = 0 := by
    rw [h2, h4] at hy'; linear_combination hy' - hy
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
  obtain ⟨hP, hR⟩ := hecke_shift_bounds (α := α) (β := β) (γ := γ) (δ := δ) h hn
    (by have := h'.c_lt; rw [h1, h3] at this; exact this)
    (by have := h'.b_lt; rw [h2, h4] at this; exact this)
  obtain ⟨hP', hR'⟩ := hecke_shift_bounds (α := δ) (β := -β) (γ := -γ) (δ := α) h' hn
    (by
      have e3 : a = δ * a' + -β * c' := by rw [h1, h3]; linear_combination (-a) * hdet
      have e4 : c = -γ * a' + α * c' := by rw [h1, h3]; linear_combination (-c) * hdet
      have := h.c_lt; rw [e3, e4] at this; exact this)
    (by
      have e5 : b = δ * b' + -β * d' := by rw [h2, h4]; linear_combination (-b) * hdet
      have e6 : d = -γ * b' + α * d' := by rw [h2, h4]; linear_combination (-d) * hdet
      have := h.b_lt; rw [e5, e6] at this; exact this)
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

/-! ### The chain -/

/-- The successor basis `(u₂, t u₂ − u₁)`, `t = ⌈a/c⌉`, of a Hecke basis with `c ≥ 1`. -/
theorem heckeBasis_successor {n a b c d : ℤ} (h : IsHeckeBasis n a b c d) (hc : 1 ≤ c) :
    ∃ t : ℤ, IsHeckeBasis n c d (t * c - a) (t * d - b) ∧ t * c - a < c ∧
      SameLattice a b c d c d (t * c - a) (t * d - b) := by
  have hc0 : 0 < c := by omega
  set q := (-a) / c with hq
  have h1 : q * c ≤ -a := by
    have := Int.ediv_mul_le (-a) hc0.ne'
    linarith
  have h2 : -a < (q + 1) * c := by
    have := Int.lt_ediv_add_one_mul_self (-a) hc0
    linarith
  refine ⟨-q, ⟨by nlinarith, by nlinarith, by linarith [h.b_nonneg, h.b_lt], ?_, ?_⟩, by nlinarith,
    ⟨0, 1, -1, -q, by ring, by ring, by ring, by ring, by ring⟩⟩
  · -- `d < t d − b` since `t ≥ 2`
    have ht : 2 ≤ -q := by
      by_contra hn
      push Not at hn
      have : -q ≤ 1 := by omega
      nlinarith [h.c_lt]
    nlinarith [h.b_lt, h.b_nonneg]
  · linear_combination h.det

/-- **Walking the chain**: if `v = m u₁ + k u₂` with `k ≥ 0` and `x ≥ 1`, some Hecke basis of the same
lattice has `v` in its cone. -/
theorem exists_inCone_of_basis {n : ℤ} (N : ℕ) :
    ∀ {a b c d x y m k : ℤ}, IsHeckeBasis n a b c d → c ≤ (N : ℤ) → 1 ≤ x →
      x = m * a + k * c → y = m * b + k * d → 0 ≤ k →
        ∃ a' b' c' d' : ℤ, IsHeckeBasis n a' b' c' d' ∧ SameLattice a b c d a' b' c' d' ∧
          InHeckeCone a' b' c' d' x y := by
  induction N with
  | zero =>
    intro a b c d x y m k h hcN hx hxe hye hk
    have hc : c = 0 := by have := h.c_nonneg; push_cast at hcN; omega
    have ha := lt_of_le_of_lt h.c_nonneg h.c_lt
    have hm : 1 ≤ m := by
      by_contra hm
      push Not at hm
      rw [hc] at hxe
      nlinarith
    exact ⟨a, b, c, d, h, sameLattice_refl a b c d, m, k, hm, hk, hxe, hye⟩
  | succ N ih =>
    intro a b c d x y m k h hcN hx hxe hye hk
    by_cases hm : 1 ≤ m
    · exact ⟨a, b, c, d, h, sameLattice_refl a b c d, m, k, hm, hk, hxe, hye⟩
    push Not at hm
    have ha := lt_of_le_of_lt h.c_nonneg h.c_lt
    have hc : 1 ≤ c := by
      by_contra hc
      push Not at hc
      have : c = 0 := by have := h.c_nonneg; omega
      rw [this] at hxe
      nlinarith
    obtain ⟨t, ht, htc, hs⟩ := heckeBasis_successor h hc
    have hlt : t * c - a ≤ (N : ℤ) := by
      have h1 : t * c - a + 1 ≤ c := Int.add_one_le_iff.mpr htc
      push_cast at hcN
      linarith
    obtain ⟨a', b', c', d', h', hs', hv⟩ := ih (y := y) ht hlt hx (m := m * t + k) (k := -m)
      (by rw [hxe]; ring) (by rw [hye]; ring) (by omega)
    exact ⟨a', b', c', d', h', hs.trans hs', hv⟩

/-! ### Lattices of index a prime -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- The index-`p` lattices: `L_∞ = {x ≡ 0}` and `L_k = {y ≡ kx}` (mod `p`). -/
def InLine (ℓ : Option (ZMod p)) (x y : ℤ) : Prop :=
  match ℓ with
  | none => (x : ZMod p) = 0
  | some k => (y : ZMod p) = k * x

instance (ℓ : Option (ZMod p)) (x y : ℤ) : Decidable (InLine ℓ x y) := by
  cases ℓ <;> (unfold InLine; infer_instance)

/-- The mod-`p` line of a Hecke basis of determinant `p`. -/
def heckeLabel (a b c d : ℤ) : Option (ZMod p) :=
  if (a : ZMod p) = 0 ∧ (c : ZMod p) = 0 then none
  else if (a : ZMod p) ≠ 0 then some ((b : ZMod p) / a) else some ((d : ZMod p) / c)

theorem det_zmod {a b c d : ℤ} (h : IsHeckeBasis p a b c d) :
    (a : ZMod p) * d = (b : ZMod p) * c := by
  have := congrArg (fun z : ℤ => (z : ZMod p)) h.det
  push_cast at this
  rw [ZMod.natCast_self] at this
  linear_combination this

/-- Both rows of a Hecke basis lie on its line. -/
theorem inLine_heckeLabel {a b c d : ℤ} (h : IsHeckeBasis p a b c d) :
    InLine (heckeLabel (p := p) a b c d) a b ∧ InLine (heckeLabel (p := p) a b c d) c d := by
  have hdet := det_zmod h
  unfold heckeLabel
  by_cases h0 : (a : ZMod p) = 0 ∧ (c : ZMod p) = 0
  · rw [if_pos h0]; exact ⟨h0.1, h0.2⟩
  · rw [if_neg h0]
    by_cases ha : (a : ZMod p) ≠ 0
    · rw [if_pos ha]
      refine ⟨by simp only [InLine]; field_simp, ?_⟩
      simp only [InLine]
      field_simp
      linear_combination hdet
    · rw [if_neg ha]
      push Not at ha
      have hc : (c : ZMod p) ≠ 0 := fun hc => h0 ⟨ha, hc⟩
      have hb : (b : ZMod p) = 0 := by
        rw [ha, zero_mul] at hdet
        exact (mul_eq_zero.mp hdet.symm).resolve_right hc
      refine ⟨?_, ?_⟩
      · simp only [InLine, ha, hb, mul_zero]
      · simp only [InLine]; field_simp

/-- Change of basis is unimodular when both bases have determinant `p`. -/
theorem sameLattice_of_coords {h₁ h₂ h₃ h₄ a b c d α β γ δ : ℤ} (hH : h₁ * h₄ - h₂ * h₃ = p)
    (hU : a * d - b * c = p) (e1 : a = α * h₁ + β * h₃) (e2 : b = α * h₂ + β * h₄)
    (e3 : c = γ * h₁ + δ * h₃) (e4 : d = γ * h₂ + δ * h₄) : SameLattice h₁ h₂ h₃ h₄ a b c d := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1 : (α * δ - β * γ - 1) * p = 0 := by
    rw [e1, e2, e3, e4] at hU; linear_combination hU - (α * δ - β * γ) * hH
  have : α * δ - β * γ - 1 = 0 := (mul_eq_zero.mp h1).resolve_right hp0
  exact ⟨α, β, γ, δ, by linarith, e1, e2, e3, e4⟩

theorem inLine_comb {ℓ : Option (ZMod p)} {a b c d : ℤ} (h1 : InLine ℓ a b) (h2 : InLine ℓ c d)
    (α β : ℤ) : InLine ℓ (α * a + β * c) (α * b + β * d) := by
  cases ℓ with
  | none => simp only [InLine] at *; push_cast; rw [h1, h2]; ring
  | some k => simp only [InLine] at *; push_cast; rw [h1, h2]; ring

theorem dvd_of_zmod {z : ℤ} (h : (z : ZMod p) = 0) : (p : ℤ) ∣ z :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h

/-- Coordinates in the start basis `((p,0),(0,1))` of the line `x ≡ 0`. -/
theorem coords_none {x y : ℤ} (h : InLine (none : Option (ZMod p)) x y) :
    x = x / p * p + y * 0 ∧ y = x / p * 0 + y * 1 := by
  have hd := dvd_of_zmod h
  exact ⟨by rw [Int.ediv_mul_cancel hd]; ring, by ring⟩

/-- Coordinates in the start basis `((1,0),(0,p))` of the line `y ≡ 0`. -/
theorem coords_zero {x y : ℤ} (h : InLine (some (0 : ZMod p)) x y) :
    x = x * 1 + y / p * 0 ∧ y = x * 0 + y / p * p := by
  have hd : (p : ℤ) ∣ y := dvd_of_zmod (by simpa [InLine] using h)
  exact ⟨by ring, by rw [Int.ediv_mul_cancel hd]; ring⟩

/-- The representative `j ∈ [0, p)` of `k⁻¹`. -/
def invRep (k : ZMod p) : ℤ := ((k⁻¹ : ZMod p).val : ℤ)

theorem invRep_cast (k : ZMod p) : ((invRep k : ℤ) : ZMod p) = k⁻¹ := by
  simp [invRep]

omit hp in
theorem invRep_nonneg (k : ZMod p) : 0 ≤ invRep k := Int.natCast_nonneg _

theorem invRep_lt (k : ZMod p) : invRep k < p := by
  unfold invRep; exact_mod_cast ZMod.val_lt _

/-- Coordinates in the start basis `((p,0),(j,1))`, `j ≡ k⁻¹`, of the line `y ≡ kx`, `k ≠ 0`. -/
theorem coords_some {k : ZMod p} (hk : k ≠ 0) {x y : ℤ} (h : InLine (some k) x y) :
    x = (x - y * invRep k) / p * p + y * invRep k ∧
      y = (x - y * invRep k) / p * 0 + y * 1 := by
  have hd : (p : ℤ) ∣ x - y * invRep k := by
    apply dvd_of_zmod
    simp only [InLine] at h
    push_cast
    rw [invRep_cast, h]
    field_simp
    ring
  exact ⟨by rw [Int.ediv_mul_cancel hd]; ring, by ring⟩

/-- A Hecke basis with both rows on the line `ℓ` spans the lattice of the start basis of `ℓ`. -/
theorem sameLattice_start_none {a b c d : ℤ} (h : IsHeckeBasis p a b c d)
    (h1 : InLine (none : Option (ZMod p)) a b) (h2 : InLine (none : Option (ZMod p)) c d) :
    SameLattice p 0 0 1 a b c d :=
  sameLattice_of_coords (by ring) h.det (coords_none h1).1 (coords_none h1).2
    (coords_none h2).1 (coords_none h2).2

theorem sameLattice_start_zero {a b c d : ℤ} (h : IsHeckeBasis p a b c d)
    (h1 : InLine (some (0 : ZMod p)) a b) (h2 : InLine (some (0 : ZMod p)) c d) :
    SameLattice 1 0 0 p a b c d :=
  sameLattice_of_coords (by ring) h.det (coords_zero h1).1 (coords_zero h1).2
    (coords_zero h2).1 (coords_zero h2).2

theorem sameLattice_start_some {k : ZMod p} (hk : k ≠ 0) {a b c d : ℤ}
    (h : IsHeckeBasis p a b c d) (h1 : InLine (some k) a b) (h2 : InLine (some k) c d) :
    SameLattice p 0 (invRep k) 1 a b c d :=
  sameLattice_of_coords (by ring) h.det (coords_some hk h1).1 (coords_some hk h1).2
    (coords_some hk h2).1 (coords_some hk h2).2

/-- **Every vector of a line lies in the cone of a Hecke basis on that line.** -/
theorem exists_heckeCone_of_inLine (ℓ : Option (ZMod p)) {x y : ℤ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hv : InLine ℓ x y) : ∃ a b c d : ℤ, IsHeckeBasis p a b c d ∧ InLine ℓ a b ∧ InLine ℓ c d ∧
      InHeckeCone a b c d x y := by
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
  -- run the chain from a start basis `(h₁, h₂, h₃, h₄)` whose rows lie on `ℓ`
  have run : ∀ {h₁ h₂ h₃ h₄ m k : ℤ}, IsHeckeBasis p h₁ h₂ h₃ h₄ → InLine ℓ h₁ h₂ →
      InLine ℓ h₃ h₄ → x = m * h₁ + k * h₃ → y = m * h₂ + k * h₄ → 0 ≤ k →
      ∃ a b c d : ℤ, IsHeckeBasis p a b c d ∧ InLine ℓ a b ∧ InLine ℓ c d ∧
        InHeckeCone a b c d x y := by
    intro h₁ h₂ h₃ h₄ m k hH r1 r2 hxe hye hk
    obtain ⟨a, b, c, d, hM, hs, hcone⟩ := exists_inCone_of_basis h₃.toNat hH
      (Int.self_le_toNat h₃) hx hxe hye hk
    obtain ⟨α, β, γ, δ, -, e1, e2, e3, e4⟩ := hs
    refine ⟨a, b, c, d, hM, ?_, ?_, hcone⟩
    · rw [e1, e2]; exact inLine_comb r1 r2 α β
    · rw [e3, e4]; exact inLine_comb r1 r2 γ δ
  cases ℓ with
  | none =>
    exact run (h₁ := p) (h₂ := 0) (h₃ := 0) (h₄ := 1) ⟨le_rfl, by omega, le_rfl, by norm_num, by ring⟩
      (by simp [InLine]) (by simp [InLine]) (coords_none hv).1 (coords_none hv).2 hy
  | some k =>
    by_cases hk : k = 0
    · subst hk
      exact run (h₁ := 1) (h₂ := 0) (h₃ := 0) (h₄ := p)
        ⟨le_rfl, by norm_num, le_rfl, by omega, by ring⟩ (by simp [InLine]) (by simp [InLine])
        (coords_zero hv).1 (coords_zero hv).2
        (Int.ediv_nonneg hy (by omega))
    · refine run (h₁ := p) (h₂ := 0) (h₃ := invRep k) (h₄ := 1)
        ⟨invRep_nonneg k, invRep_lt k, le_rfl, by norm_num, by ring⟩ (by simp [InLine])
        (by simp only [InLine]; push_cast; rw [invRep_cast]; field_simp)
        (coords_some hk hv).1 (coords_some hk hv).2 ?_
      simpa using hy

/-- **Uniqueness on a line**: two Hecke bases on the same line whose cones share a vector are equal. -/
theorem heckeBasis_eq_of_inLine {ℓ : Option (ZMod p)} {a b c d a' b' c' d' x y : ℤ}
    (h : IsHeckeBasis p a b c d) (h' : IsHeckeBasis p a' b' c' d')
    (r1 : InLine ℓ a b) (r2 : InLine ℓ c d) (r1' : InLine ℓ a' b') (r2' : InLine ℓ c' d')
    (hv : InHeckeCone a b c d x y) (hv' : InHeckeCone a' b' c' d' x y) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  refine heckeBasis_eq_of_inCone hp0 h h' ?_ hv hv'
  cases ℓ with
  | none =>
    exact (sameLattice_start_none h r1 r2).symm.trans (sameLattice_start_none h' r1' r2')
  | some k =>
    by_cases hk : k = 0
    · subst hk
      exact (sameLattice_start_zero h r1 r2).symm.trans (sameLattice_start_zero h' r1' r2')
    · exact (sameLattice_start_some hk h r1 r2).symm.trans (sameLattice_start_some hk h' r1' r2')

/-- The rows of a Hecke basis of determinant `p` are not both divisible by `p`. -/
theorem not_all_zmod_zero {a b c d : ℤ} (h : IsHeckeBasis p a b c d) :
    ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
  rintro ⟨ha, hb, hc, hd⟩
  obtain ⟨a', rfl⟩ := dvd_of_zmod ha
  obtain ⟨b', rfl⟩ := dvd_of_zmod hb
  obtain ⟨c', rfl⟩ := dvd_of_zmod hc
  obtain ⟨d', rfl⟩ := dvd_of_zmod hd
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.out.one_lt
  have hdet := h.det
  have : (p : ℤ) * (p * (a' * d' - b' * c')) = p * 1 := by linear_combination hdet
  have h1 : (p : ℤ) * (a' * d' - b' * c') = 1 := mul_left_cancel₀ (by omega) this
  have := Int.eq_one_of_mul_eq_one_right (by omega) h1
  omega

/-- **The line of a Hecke basis is determined by its rows.** -/
theorem heckeLabel_eq_of_inLine {ℓ : Option (ZMod p)} {a b c d : ℤ} (h : IsHeckeBasis p a b c d)
    (r1 : InLine ℓ a b) (r2 : InLine ℓ c d) : heckeLabel (p := p) a b c d = ℓ := by
  have hz := not_all_zmod_zero h
  unfold heckeLabel
  cases ℓ with
  | none =>
    simp only [InLine] at r1 r2
    rw [if_pos ⟨r1, r2⟩]
  | some k =>
    simp only [InLine] at r1 r2
    by_cases h0 : (a : ZMod p) = 0 ∧ (c : ZMod p) = 0
    · exfalso
      rw [h0.1, mul_zero] at r1
      rw [h0.2, mul_zero] at r2
      exact hz ⟨h0.1, r1, h0.2, r2⟩
    rw [if_neg h0]
    by_cases ha : (a : ZMod p) ≠ 0
    · rw [if_pos ha, r1]; field_simp
    · rw [if_neg ha]
      push Not at ha
      have hc : (c : ZMod p) ≠ 0 := fun hc => h0 ⟨ha, hc⟩
      rw [r2]; field_simp

omit hp in
/-- Entries of a Hecke basis of determinant `p` lie in `[0, p]`. -/
theorem heckeBasis_bounds {a b c d : ℤ} (h : IsHeckeBasis p a b c d) :
    0 ≤ a ∧ a ≤ p ∧ 0 ≤ b ∧ b ≤ p ∧ 0 ≤ c ∧ c ≤ p ∧ 0 ≤ d ∧ d ≤ p := by
  have hb := h.b_nonneg
  have hc := h.c_nonneg
  have hbd := h.b_lt
  have hca := h.c_lt
  have hdet := h.det
  have h1 : b ≤ d - 1 := by omega
  have h2 : c ≤ a - 1 := by omega
  have h3 := mul_le_mul h1 h2 hc (by omega)
  have key : a + d - 1 ≤ p := by nlinarith
  omega

open Classical in
/-- The Hecke bases of determinant `p`, a finite set. -/
noncomputable def heckeSet (p : ℕ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ((Finset.Icc 0 (p : ℤ)) ×ˢ (Finset.Icc 0 (p : ℤ)) ×ˢ (Finset.Icc 0 (p : ℤ)) ×ˢ
    (Finset.Icc 0 (p : ℤ))).filter fun M => IsHeckeBasis p M.1 M.2.1 M.2.2.1 M.2.2.2

open Classical in
/-- The number of Hecke cones of determinant `p` containing `(x, y)`. -/
noncomputable def heckeConeCount (p : ℕ) (x y : ℤ) : ℕ :=
  ((heckeSet p).filter fun M => InHeckeCone M.1 M.2.1 M.2.2.1 M.2.2.2 x y).card

theorem inLine_of_inCone {ℓ : Option (ZMod p)} {a b c d x y : ℤ} (r1 : InLine ℓ a b)
    (r2 : InLine ℓ c d) (hv : InHeckeCone a b c d x y) : InLine ℓ x y := by
  obtain ⟨m, k, -, -, rfl, rfl⟩ := hv
  exact inLine_comb r1 r2 m k

open Classical in
/-- **The cone count is the number of lines through the vector.** -/
theorem heckeConeCount_eq_card_lines {x y : ℤ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    heckeConeCount p x y = ((Finset.univ : Finset (Option (ZMod p))).filter
      fun ℓ => InLine ℓ x y).card := by
  unfold heckeConeCount
  refine Finset.card_bij (fun M _ => heckeLabel (p := p) M.1 M.2.1 M.2.2.1 M.2.2.2) ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_filter, heckeSet] at hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨r1, r2⟩ := inLine_heckeLabel hM.1.2
    exact inLine_of_inCone r1 r2 hM.2
  · intro M hM M' hM' hl
    simp only [Finset.mem_filter, heckeSet] at hM hM'
    obtain ⟨r1, r2⟩ := inLine_heckeLabel hM.1.2
    obtain ⟨r1', r2'⟩ := inLine_heckeLabel hM'.1.2
    rw [hl] at r1 r2
    obtain ⟨e1, e2, e3, e4⟩ := heckeBasis_eq_of_inLine hM.1.2 hM'.1.2 r1 r2 r1' r2' hM.2 hM'.2
    obtain ⟨a, b, c, d⟩ := M
    obtain ⟨a', b', c', d'⟩ := M'
    simp only at e1 e2 e3 e4
    rw [e1, e2, e3, e4]
  · intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    obtain ⟨a, b, c, d, hM, r1, r2, hv⟩ := exists_heckeCone_of_inLine ℓ hx hy hℓ
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := heckeBasis_bounds hM
    refine ⟨(a, b, c, d), ?_, heckeLabel_eq_of_inLine hM r1 r2⟩
    simp only [Finset.mem_filter, heckeSet, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨⟨b0, b1⟩, ⟨b2, b3⟩, ⟨b4, b5⟩, ⟨b6, b7⟩⟩, hM⟩, hv⟩

/-- The lines of `𝔽_p²` through a vector: one, or all `p + 1` through `0`. -/
theorem card_lines (x y : ℤ) :
    ((Finset.univ : Finset (Option (ZMod p))).filter fun ℓ => InLine ℓ x y).card =
      if (x : ZMod p) = 0 ∧ (y : ZMod p) = 0 then p + 1 else 1 := by
  by_cases hx0 : (x : ZMod p) = 0
  · by_cases hy0 : (y : ZMod p) = 0
    · rw [if_pos ⟨hx0, hy0⟩]
      have : ((Finset.univ : Finset (Option (ZMod p))).filter fun ℓ => InLine ℓ x y) =
          Finset.univ := by
        ext ℓ; cases ℓ <;> simp [InLine, hx0, hy0]
      rw [this, Finset.card_univ, Fintype.card_option, ZMod.card]
    · rw [if_neg (fun h => hy0 h.2)]
      have : ((Finset.univ : Finset (Option (ZMod p))).filter fun ℓ => InLine ℓ x y) = {none} := by
        ext ℓ; cases ℓ <;> simp [InLine, hx0, hy0]
      rw [this, Finset.card_singleton]
  · rw [if_neg (fun h => hx0 h.1)]
    have : ((Finset.univ : Finset (Option (ZMod p))).filter fun ℓ => InLine ℓ x y) =
        {some ((y : ZMod p) / x)} := by
      ext ℓ
      cases ℓ with
      | none => simp [InLine, hx0]
      | some k =>
        simp only [InLine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Option.some.injEq]
        constructor
        · intro h; rw [eq_div_iff hx0, h]
        · intro h; rw [h, div_mul_cancel₀ _ hx0]
    rw [this, Finset.card_singleton]

/-- **The Hecke cones of a prime determinant tile the quadrant**: a vector `(x, y)`, `x ≥ 1`,
`y ≥ 0`, lies in exactly one cone, or in `p + 1` cones when `p ∣ x` and `p ∣ y`. -/
theorem heckeConeCount_eq {x y : ℤ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    heckeConeCount p x y = if (p : ℤ) ∣ x ∧ (p : ℤ) ∣ y then p + 1 else 1 := by
  rw [heckeConeCount_eq_card_lines hx hy, card_lines]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]

omit hp in
/-- No cone reaches the line `x ≤ 0`: the first row has `a ≥ 1`. -/
theorem heckeConeCount_eq_zero {x y : ℤ} (hx : x < 1) : heckeConeCount p x y = 0 := by
  classical
  unfold heckeConeCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b, c, d⟩ hM ⟨m, k, hm, hk, hxe, -⟩
  simp only [heckeSet, Finset.mem_filter] at hM
  have hc := hM.2.c_nonneg
  have ha := hM.2.c_lt
  nlinarith

end Prime

/-- Transposing the quadrant and reversing the basis preserves Hecke bases. -/
theorem IsHeckeBasis.swap {n a b c d : ℤ} (h : IsHeckeBasis n a b c d) :
    IsHeckeBasis n d c b a :=
  ⟨h.b_nonneg, h.b_lt, h.c_nonneg, h.c_lt, by linarith [h.det]⟩


end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
