import GaloisForLFunctions.HTGeometry.ModularCellPointPair
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# Hyperbolic lattice points of `SL(2,ℤ)`

For `γ = (a b; c d) ∈ SL(2,ℤ)`, `4u(i, γi) + 2 = a² + b² + c² + d²`
(`four_mul_pairU_I_smul_I_add_two`), where `u` is the point-pair invariant, so
`1 + 2u(i,γi) = cosh d(i,γi)` is half the squared Frobenius norm.

**Linear count** (`ncard_pairU_I_smul_I_le`): `#{γ : u(i,γi) ≤ R} ≤ 320 (R + 1)` for `R ≥ 0`.
Write `u = (a,b)` and `v = (c,d)` for the rows.  For a fixed top row the bottom rows with
`det(u,v) = 1` form the line `v₀ + ℤu` (`eq_add_mul_of_det_eq_one`), and at most five of its points
satisfy `|v| ≤ |u|`, since two such points differ by `ku` with `k²|u|² ≤ 4|u|²`.  Multiplying by
`S` exchanges the two rows up to sign, so the case `|u| < |v|` costs no more.  Both rows lie in the
box `[-M, M]²` with `M² ≤ 4R + 2`, which gives `10 (2M + 1)²`.

**Summability** (`summable_one_add_two_mul_pairU_I_rpow`): `Σ_γ (1 + 2u(i,γi))^{-σ} < ∞` for
`σ > 1`.  With `t = ac + bd` and `m = a² + b²`, Lagrange's identity `t² + 1 = m(c² + d²)` holds, and
`γ ↦ (u, ⌊t/m⌋)` is injective because `t` runs through one residue class modulo `m`.  The bound
`3m(a² + b² + c² + d²) ≥ m²(1 + ⌊t/m⌋²)` dominates the series by
`6^σ ‖u‖^{-2σ} (q^{-2} + 1_{q=0})`, which is summable over `ℤ² × ℤ`.

**Other centres and subgroups** (`ncard_pairU_smul_le`, `summable_one_add_two_mul_pairU_rpow`,
`ncard_subgroup_pairU_smul_le`, `summable_subgroup_one_add_two_mul_pairU_rpow`): from
`d(i,γi) ≤ 2d(i,z) + d(z,γz)` and `cosh(x + y) ≤ 2 cosh x cosh y`,
`1 + 2u(i,γi) ≤ 2 cosh(2d(i,z)) (1 + 2u(z,γz))`.  So both statements hold at every centre,
uniformly for `d(i,z) ≤ D`, and for every subgroup of `SL(2,ℤ)`.
-/

open UpperHalfPlane GaloisForLFunctions.HTGeometry
open scoped MatrixGroups

namespace RHTower

noncomputable section

/-- The squared Frobenius norm `a² + b² + c² + d²` of `γ ∈ SL(2,ℤ)`. -/
def latticeNormSq (γ : SL(2, ℤ)) : ℤ := γ 0 0 ^ 2 + γ 0 1 ^ 2 + γ 1 0 ^ 2 + γ 1 1 ^ 2

theorem latticeDet (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

/-- **The norm formula.**  `4u(i,γi) + 2 = a² + b² + c² + d²`. -/
theorem four_mul_pairU_I_smul_I_add_two (γ : SL(2, ℤ)) :
    4 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) + 2 = (latticeNormSq γ : ℝ) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (γ 0 0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (γ 0 1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (γ 1 0 : ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (γ 1 1 : ℝ) := ⟨_, rfl⟩
  have hdet : a * d - b * c = 1 := by
    subst ha hb hc hd; exact_mod_cast latticeDet γ
  have hN : (latticeNormSq γ : ℝ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    subst ha hb hc hd; push_cast [latticeNormSq]; ring
  set w : ℍ := γ • UpperHalfPlane.I with hw
  have hcd : (c : ℂ) * Complex.I + d ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    rw [h1, h2] at hdet
    simp at hdet
  have hwc : (w : ℂ) = ((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d) := by
    rw [hw, coe_specialLinearGroup_apply, UpperHalfPlane.coe_I]
    subst ha hb hc hd
    simp
  have hmul : (w : ℂ) * ((c : ℂ) * Complex.I + d) = (a : ℂ) * Complex.I + b := by
    rw [hwc, div_mul_cancel₀ _ hcd]
  have hre := congrArg Complex.re hmul
  have him := congrArg Complex.im hmul
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
    sub_self] at hre him
  have hS : 0 < c ^ 2 + d ^ 2 := by
    rcases eq_or_ne c 0 with h | h
    · rcases eq_or_ne d 0 with h' | h'
      · rw [h, h'] at hdet; simp at hdet
      · positivity
    · positivity
  have hyS : (w : ℂ).im * (c ^ 2 + d ^ 2) = 1 := by linear_combination d * him - c * hre + hdet
  have hxS : (w : ℂ).re * (c ^ 2 + d ^ 2) = a * c + b * d := by
    linear_combination d * hre + c * him
  have hy' : (w : ℂ).im = 1 / (c ^ 2 + d ^ 2) := by field_simp; linarith
  have hx' : (w : ℂ).re = (a * c + b * d) / (c ^ 2 + d ^ 2) := by field_simp; linarith
  have hwim : w.im = 1 / (c ^ 2 + d ^ 2) := by rw [← UpperHalfPlane.coe_im]; exact hy'
  rw [hN, pairU, Complex.dist_eq, UpperHalfPlane.I_im, UpperHalfPlane.coe_I, Complex.sq_norm,
    Complex.normSq_apply, hwim]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  have hL : (a * c + b * d) ^ 2 + 1 = (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) := by
    linear_combination (-(a * d - b * c) - 1) * hdet
  rw [hy', hx']
  field_simp
  linear_combination hL

theorem one_add_two_mul_pairU_I_smul_I (γ : SL(2, ℤ)) :
    1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) = (latticeNormSq γ : ℝ) / 2 := by
  rw [← four_mul_pairU_I_smul_I_add_two]; ring

/-! ## The line of bottom rows -/

/-- **The bottom rows with a fixed top row form a line.**  If `ad − bc = 1 = ad' − bc'`, then
`(c', d') = (c, d) + k(a, b)` with `k = dc' − cd'`. -/
theorem eq_add_mul_of_det_eq_one {a b c d c' d' : ℤ} (h : a * d - b * c = 1)
    (h' : a * d' - b * c' = 1) :
    c' = c + (d * c' - c * d') * a ∧ d' = d + (d * c' - c * d') * b :=
  ⟨by linear_combination (-c') * h + c * h', by linear_combination (-d') * h + d * h'⟩

theorem one_le_sq_add_sq_of_det_eq_one {a b c d : ℤ} (h : a * d - b * c = 1) :
    1 ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a 0 with ha | ha
  · rcases eq_or_ne b 0 with hb | hb
    · rw [ha, hb] at h; simp at h
    · have : 0 < b ^ 2 := by positivity
      nlinarith
  · have : 0 < a ^ 2 := by positivity
    nlinarith

/-- Two short bottom rows on the same line differ by at most twice the top row. -/
theorem abs_le_two_of_det_eq_one {a b c d c' d' : ℤ} (h : a * d - b * c = 1)
    (h' : a * d' - b * c' = 1) (hv : c ^ 2 + d ^ 2 ≤ a ^ 2 + b ^ 2)
    (hv' : c' ^ 2 + d' ^ 2 ≤ a ^ 2 + b ^ 2) :
    -2 ≤ d * c' - c * d' ∧ d * c' - c * d' ≤ 2 := by
  obtain ⟨e1, e2⟩ := eq_add_mul_of_det_eq_one h h'
  set k := d * c' - c * d'
  have hm := one_le_sq_add_sq_of_det_eq_one h
  have hk : k ^ 2 * (a ^ 2 + b ^ 2) ≤ 4 * (a ^ 2 + b ^ 2) := by
    have : k ^ 2 * (a ^ 2 + b ^ 2) = (c' - c) ^ 2 + (d' - d) ^ 2 := by
      rw [e1, e2]; ring
    rw [this]
    nlinarith [sq_nonneg (c' + c), sq_nonneg (d' + d)]
  have hk4 : k ^ 2 ≤ 4 := le_of_mul_le_mul_right hk (by linarith)
  constructor <;> nlinarith [sq_nonneg (k + 2), sq_nonneg (k - 2)]

/-! ## The linear count -/

/-- The two rows of `γ`. -/
def latticeRows (γ : SL(2, ℤ)) : (ℤ × ℤ) × (ℤ × ℤ) := ((γ 0 0, γ 0 1), (γ 1 0, γ 1 1))

theorem latticeRows_injective : Function.Injective latticeRows := by
  intro γ γ' h
  simp only [latticeRows, Prod.mk.injEq] at h
  obtain ⟨⟨h00, h01⟩, h10, h11⟩ := h
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- The pairs of rows with determinant one and squared norm at most `K`, inside the box
`[-M, M]⁴`. -/
def latticeRowBox (M : ℕ) (K : ℤ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  {p ∈ (Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M) ×ˢ
      (Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M) |
    p.1.1 * p.2.2 - p.1.2 * p.2.1 = 1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ K}

theorem card_latticeRowBox_le (M : ℕ) (K : ℤ) :
    (latticeRowBox M K).card ≤ 10 * (2 * M + 1) ^ 2 := by
  classical
  set B := Finset.Icc (-(M : ℤ)) M with hB
  set P := latticeRowBox M K with hP
  have hBc : (B ×ˢ B).card = (2 * M + 1) ^ 2 := by
    rw [Finset.card_product, hB, Int.card_Icc]
    have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [this]; ring
  set P₁ := {p ∈ P | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ p.1.1 ^ 2 + p.1.2 ^ 2} with hP₁
  set P₂ := {p ∈ P | ¬ (p.2.1 ^ 2 + p.2.2 ^ 2 ≤ p.1.1 ^ 2 + p.1.2 ^ 2)} with hP₂
  have hsplit : P.card = P₁.card + P₂.card := (Finset.card_filter_add_card_filter_not _).symm
  have hmemP : ∀ p, p ∈ P ↔ ((p.1.1 ∈ B ∧ p.1.2 ∈ B) ∧ (p.2.1 ∈ B ∧ p.2.2 ∈ B)) ∧
      p.1.1 * p.2.2 - p.1.2 * p.2.1 = 1 ∧ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ K := by
    intro p
    simp only [hP, latticeRowBox, Finset.mem_filter, Finset.mem_product, hB]
  have hnegB : ∀ x, x ∈ B → -x ∈ B := by
    intro x hx
    rw [hB, Finset.mem_Icc] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]
  -- the swap `(u, v) ↦ (-v, u)` sends `P₂` into `P₁`
  have h21 : P₂.card ≤ P₁.card := by
    refine Finset.card_le_card_of_injOn (fun p => ((-p.2.1, -p.2.2), (p.1.1, p.1.2))) ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hP₂] at hp
      obtain ⟨hp, hlt⟩ := hp
      rw [hmemP] at hp
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hdet, hK⟩ := hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hP₁]
      refine ⟨(hmemP _).2 ⟨⟨⟨hnegB _ h3, hnegB _ h4⟩, h1, h2⟩, ?_, ?_⟩, ?_⟩
      · linear_combination hdet
      · linear_combination hK
      · push Not at hlt; nlinarith
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq, neg_inj] at hpq
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hpq
      exact Prod.ext (Prod.ext h3 h4) (Prod.ext h1 h2)
  -- each top row carries at most five short bottom rows
  have h1 : P₁.card ≤ 5 * (B ×ˢ B).card := by
    have hmaps : Set.MapsTo Prod.fst (P₁ : Set ((ℤ × ℤ) × (ℤ × ℤ)))
        ((B ×ˢ B : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
      intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hP₁] at hp
      have := ((hmemP p).1 hp.1).1.1
      simpa [Finset.mem_product] using this
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine le_trans (Finset.sum_le_card_nsmul _ _ 5 fun u _ => ?_) (by rw [smul_eq_mul, mul_comm])
    by_cases hne : ({p ∈ P₁ | p.1 = u}).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hne
      have hsub : {p ∈ P₁ | p.1 = u} ⊆ (Finset.Icc (-2 : ℤ) 2).image
          (fun k => (u, (p₀.2.1 + k * u.1, p₀.2.2 + k * u.2))) := by
        intro p hp
        simp only [Finset.mem_filter, hP₁] at hp hp₀
        obtain ⟨⟨hpP, hpshort⟩, hpu⟩ := hp
        obtain ⟨⟨hp₀P, hp₀short⟩, hp₀u⟩ := hp₀
        obtain ⟨_, hdet, _⟩ := (hmemP p).1 hpP
        obtain ⟨_, hdet₀, _⟩ := (hmemP p₀).1 hp₀P
        rw [hpu] at hdet hpshort
        rw [hp₀u] at hdet₀ hp₀short
        obtain ⟨e1, e2⟩ := eq_add_mul_of_det_eq_one hdet₀ hdet
        obtain ⟨k1, k2⟩ := abs_le_two_of_det_eq_one hdet₀ hdet hp₀short hpshort
        refine Finset.mem_image.2 ⟨_, Finset.mem_Icc.2 ⟨k1, k2⟩, ?_⟩
        rw [← hpu]
        exact Prod.ext rfl (Prod.ext (by rw [hpu, ← e1]) (by rw [hpu, ← e2]))
      refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
      simp
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  rw [hsplit]
  calc P₁.card + P₂.card ≤ 2 * (5 * (B ×ˢ B).card) := by omega
    _ = 10 * (2 * M + 1) ^ 2 := by rw [hBc]; ring

theorem mem_Icc_sqrt_of_sq_le {e K : ℤ} (h : e ^ 2 ≤ K) :
    e ∈ Finset.Icc (-(Nat.sqrt K.toNat : ℤ)) (Nat.sqrt K.toNat) := by
  have h1 : e.natAbs ^ 2 ≤ K.toNat := by
    have : ((e.natAbs ^ 2 : ℕ) : ℤ) ≤ (K.toNat : ℤ) := by
      push_cast; rw [sq_abs, Int.toNat_eq_max]; exact le_trans h (le_max_left _ _)
    exact_mod_cast this
  have h2 : ((e.natAbs : ℕ) : ℤ) ≤ (Nat.sqrt K.toNat : ℕ) := by exact_mod_cast Nat.le_sqrt'.2 h1
  rw [Int.natCast_natAbs] at h2
  exact Finset.mem_Icc.2 (abs_le.1 h2)

/-- The rows of every `γ` with `u(i,γi) ≤ R` lie in the row box with `K = ⌊4R + 2⌋`. -/
theorem latticeRows_mem_rowBox {R : ℝ} {γ : SL(2, ℤ)}
    (hγ : pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R) :
    latticeRows γ ∈ latticeRowBox (Nat.sqrt (⌊4 * R + 2⌋).toNat) ⌊4 * R + 2⌋ := by
  have hN : latticeNormSq γ ≤ ⌊4 * R + 2⌋ := by
    rw [Int.le_floor, ← four_mul_pairU_I_smul_I_add_two]; linarith
  unfold latticeNormSq at hN
  have hdet := latticeDet γ
  simp only [latticeRowBox, latticeRows, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨⟨mem_Icc_sqrt_of_sq_le ?_, mem_Icc_sqrt_of_sq_le ?_⟩,
    mem_Icc_sqrt_of_sq_le ?_, mem_Icc_sqrt_of_sq_le ?_⟩, hdet, hN⟩ <;>
    nlinarith [sq_nonneg (γ 0 0), sq_nonneg (γ 0 1), sq_nonneg (γ 1 0), sq_nonneg (γ 1 1)]

theorem finite_pairU_I_smul_I_le (R : ℝ) :
    {γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R}.Finite := by
  refine ((latticeRowBox (Nat.sqrt (⌊4 * R + 2⌋).toNat) ⌊4 * R + 2⌋).finite_toSet.preimage
    latticeRows_injective.injOn).subset fun γ hγ => ?_
  exact latticeRows_mem_rowBox hγ

/-- **The linear lattice-point count.**  `#{γ ∈ SL(2,ℤ) : u(i,γi) ≤ R} ≤ 320 (R + 1)`. -/
theorem ncard_pairU_I_smul_I_le {R : ℝ} (hR : 0 ≤ R) :
    ({γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R}.ncard : ℝ) ≤
      320 * (R + 1) := by
  set K := ⌊4 * R + 2⌋ with hK
  set M := Nat.sqrt K.toNat with hM
  have hle : {γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R}.ncard ≤
      (latticeRowBox M K).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard_of_injOn latticeRows (fun γ hγ => latticeRows_mem_rowBox hγ)
      latticeRows_injective.injOn
  have hcard := card_latticeRowBox_le M K
  have hK0 : 0 ≤ K := by rw [hK, Int.le_floor]; push_cast; linarith
  have hM2 : ((M : ℝ)) ^ 2 ≤ 4 * R + 2 := by
    have h1 : M ^ 2 ≤ K.toNat := Nat.sqrt_le' _
    have h2 : ((K.toNat : ℤ) : ℝ) = (K : ℝ) := by rw [Int.toNat_of_nonneg hK0]
    have h3 : (K : ℝ) ≤ 4 * R + 2 := Int.floor_le _
    have h4 : ((M ^ 2 : ℕ) : ℝ) ≤ (K.toNat : ℝ) := by exact_mod_cast h1
    push_cast at h4 h2
    linarith
  have hc : ((latticeRowBox M K).card : ℝ) ≤ 10 * (2 * (M : ℝ) + 1) ^ 2 := by exact_mod_cast hcard
  have hle' : ({γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R}.ncard : ℝ) ≤
      ((latticeRowBox M K).card : ℝ) := by exact_mod_cast hle
  nlinarith [sq_nonneg (2 * (M : ℝ) - 1)]

/-! ## Summability for `σ > 1` -/

/-- The top row and the quotient `⌊(ac + bd)/(a² + b²)⌋`. -/
def latticeLineIndex (γ : SL(2, ℤ)) : (Fin 2 → ℤ) × ℤ :=
  (![γ 0 0, γ 0 1], (γ 0 0 * γ 1 0 + γ 0 1 * γ 1 1) / (γ 0 0 ^ 2 + γ 0 1 ^ 2))

theorem latticeLineIndex_injective : Function.Injective latticeLineIndex := by
  intro γ γ' h
  simp only [latticeLineIndex, Prod.mk.injEq] at h
  obtain ⟨hu, hq⟩ := h
  have ha : γ 0 0 = γ' 0 0 := congrFun hu 0
  have hb : γ 0 1 = γ' 0 1 := congrFun hu 1
  rw [← ha, ← hb] at hq
  have hdet := latticeDet γ
  have hdet' := latticeDet γ'
  rw [← ha, ← hb] at hdet'
  set a := γ 0 0; set b := γ 0 1
  obtain ⟨e1, e2⟩ := eq_add_mul_of_det_eq_one hdet hdet'
  set k := γ 1 1 * γ' 1 0 - γ 1 0 * γ' 1 1
  have hm := one_le_sq_add_sq_of_det_eq_one hdet
  set m := a ^ 2 + b ^ 2
  set t := a * γ 1 0 + b * γ 1 1
  set t' := a * γ' 1 0 + b * γ' 1 1
  have ht' : t' = t + k * m := by
    simp only [t', t, m]; rw [e1, e2]; ring
  have hdt := Int.mul_ediv_add_emod t m
  have hdt' := Int.mul_ediv_add_emod t' m
  have r0 := Int.emod_nonneg t (by omega : m ≠ 0)
  have r1 := Int.emod_lt_of_pos t (by omega : 0 < m)
  have r0' := Int.emod_nonneg t' (by omega : m ≠ 0)
  have r1' := Int.emod_lt_of_pos t' (by omega : 0 < m)
  rw [hq] at hdt
  have hk : k * m = t' % m - t % m := by linarith
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with hneg | hzero | hpos
    · have : k * m ≤ -m := by nlinarith
      omega
    · exact hzero
    · have : m ≤ k * m := by nlinarith
      omega
  rw [hk0, zero_mul, add_zero] at e1 e2
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact e1.symm
  · exact e2.symm

/-- The comparison `3m(a² + b² + c² + d²) ≥ m²(1 + q²)`, `q = ⌊t/m⌋`. -/
theorem latticeNormSq_lower (γ : SL(2, ℤ)) :
    ((γ 0 0 ^ 2 + γ 0 1 ^ 2 : ℤ) : ℝ) * (1 + ((latticeLineIndex γ).2 : ℝ) ^ 2) ≤
      3 * (latticeNormSq γ : ℝ) := by
  have hdet := latticeDet γ
  have hm := one_le_sq_add_sq_of_det_eq_one hdet
  set a := γ 0 0; set b := γ 0 1; set c := γ 1 0; set d := γ 1 1
  set m := a ^ 2 + b ^ 2
  set t := a * c + b * d
  set q := t / m
  have hq : (latticeLineIndex γ).2 = q := rfl
  rw [hq]
  have hdt := Int.mul_ediv_add_emod t m
  have r0 := Int.emod_nonneg t (by omega : m ≠ 0)
  have r1 := Int.emod_lt_of_pos t (by omega : 0 < m)
  set r := t % m
  -- Lagrange: `m (c² + d²) = t² + 1`
  have hlag : m * (c ^ 2 + d ^ 2) = t ^ 2 + 1 := by
    simp only [m, t]; linear_combination (a * d - b * c + 1) * hdet
  have hNm : m * latticeNormSq γ = m ^ 2 + t ^ 2 + 1 := by
    simp only [latticeNormSq]; linear_combination hlag
  have key : m ^ 2 * (1 + q ^ 2) ≤ 3 * (m ^ 2 + t ^ 2 + 1) := by
    rcases le_or_gt 0 q with hq0 | hq0
    · have h1 : m * q ≤ t := by linarith
      have h0 : 0 ≤ m * q := mul_nonneg (by omega) hq0
      have : (m * q) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith
    · have : t < m * (q + 1) := by linarith
      have : m * (q + 1) ≤ 0 := by nlinarith
      have : (m * (q + 1)) ^ 2 ≤ t ^ 2 := by
        nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : t - m * (q + 1) ≤ 0)
          (by linarith : t + m * (q + 1) ≤ 0)]
      nlinarith [sq_nonneg (2 * q + 3)]
  have key' : m * (1 + q ^ 2) ≤ 3 * latticeNormSq γ := by
    have h3 : m * (m * (1 + q ^ 2)) ≤ m * (3 * latticeNormSq γ) := by
      rw [show m * (3 * latticeNormSq γ) = 3 * (m * latticeNormSq γ) by ring, hNm]
      linarith
    exact le_of_mul_le_mul_left h3 (by omega)
  exact_mod_cast key'

/-- **Summability.**  `Σ_{γ ∈ SL(2,ℤ)} (1 + 2u(i,γi))^{-σ} < ∞` for `σ > 1`. -/
theorem summable_one_add_two_mul_pairU_I_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun γ : SL(2, ℤ) =>
      (1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I)) ^ (-σ) := by
  set h : ℤ → ℝ := fun q => 1 / (q : ℝ) ^ 2 + if q = 0 then 1 else 0 with hh
  have hhs : Summable h :=
    (Real.summable_one_div_int_pow.2 one_lt_two).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  have hh0 : 0 ≤ h := fun q => by simp only [hh]; split_ifs <;> positivity
  have hgs : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * σ)) :=
    EisensteinSeries.summable_one_div_norm_rpow (by linarith)
  have hprod := ((hgs.mul_of_nonneg hhs (fun x => by positivity) hh0).mul_left
    (6 ^ σ)).comp_injective latticeLineIndex_injective
  refine hprod.of_nonneg_of_le (fun γ => ?_) (fun γ => ?_)
  · have := pairU_nonneg UpperHalfPlane.I (γ • UpperHalfPlane.I)
    positivity
  · rw [one_add_two_mul_pairU_I_smul_I]
    simp only [Function.comp_apply]
    have hdet := latticeDet γ
    have hm := one_le_sq_add_sq_of_det_eq_one hdet
    set m : ℝ := ((γ 0 0 ^ 2 + γ 0 1 ^ 2 : ℤ) : ℝ) with hmdef
    have hm1 : 1 ≤ m := by rw [hmdef]; exact_mod_cast hm
    set q : ℝ := ((latticeLineIndex γ).2 : ℝ) with hqdef
    have hlow := latticeNormSq_lower γ
    rw [← hmdef, ← hqdef] at hlow
    set u := (latticeLineIndex γ).1 with hudef
    have hu : u = ![γ 0 0, γ 0 1] := rfl
    -- `‖u‖² ≤ m` for the sup norm
    have hnorm : ‖u‖ ≤ Real.sqrt m := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Int.norm_eq_abs]
      apply Real.abs_le_sqrt
      rw [hmdef, hu]
      fin_cases i <;> simp <;> nlinarith [sq_nonneg ((γ 0 0 : ℤ) : ℝ), sq_nonneg ((γ 0 1 : ℤ) : ℝ)]
    have hupos : 0 < ‖u‖ := by
      rw [norm_pos_iff]
      intro h0
      have h00 : γ 0 0 = 0 := by simpa [hu] using congrFun h0 0
      have h01 : γ 0 1 = 0 := by simpa [hu] using congrFun h0 1
      rw [h00, h01] at hdet; simp at hdet
    have hnorm2 : ‖u‖ ^ 2 ≤ m := by
      calc ‖u‖ ^ 2 ≤ Real.sqrt m ^ 2 := by gcongr
        _ = m := Real.sq_sqrt (by linarith)
    have hNpos : 0 < (latticeNormSq γ : ℝ) / 2 := by
      have : 0 < m * (1 + q ^ 2) := by positivity
      linarith
    -- the three comparisons
    have c1 : ((latticeNormSq γ : ℝ) / 2) ^ (-σ) ≤ (m * (1 + q ^ 2) / 6) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have c2 : (m * (1 + q ^ 2) / 6) ^ (-σ) = 6 ^ σ * (m ^ (-σ) * (1 + q ^ 2) ^ (-σ)) := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
      field_simp
    have c3 : m ^ (-σ) ≤ ‖u‖ ^ (-(2 * σ)) := by
      have : ‖u‖ ^ (-(2 * σ)) = (‖u‖ ^ 2) ^ (-σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; push_cast; ring_nf
      rw [this]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hnorm2 (by linarith)
    have c4 : (1 + q ^ 2) ^ (-σ) ≤ h (latticeLineIndex γ).2 := by
      have h1 : (1 + q ^ 2) ^ (-σ) ≤ (1 + q ^ 2) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg q]) (by linarith)
      refine le_trans h1 ?_
      rw [Real.rpow_neg_one, hh]
      simp only
      rw [← hqdef]
      split_ifs with hq0
      · have : q = 0 := by rw [hqdef, hq0]; simp
        rw [this]; norm_num
      · have hq0' : q ≠ 0 := by rw [hqdef]; exact_mod_cast hq0
        have : 0 < q ^ 2 := by positivity
        rw [add_zero, one_div]
        exact inv_anti₀ this (by linarith)
    calc ((latticeNormSq γ : ℝ) / 2) ^ (-σ) ≤ 6 ^ σ * (m ^ (-σ) * (1 + q ^ 2) ^ (-σ)) := c2 ▸ c1
      _ ≤ 6 ^ σ * (‖u‖ ^ (-(2 * σ)) * h (latticeLineIndex γ).2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul c3 c4 (by positivity) (by positivity))
          (by positivity)

/-! ## Arbitrary centres and subgroups -/

/-- **Moving the centre.**  `1 + 2u(i,γi) ≤ 2 cosh(2d(i,z)) (1 + 2u(z,γz))`. -/
theorem one_add_two_mul_pairU_I_le (z : ℍ) (γ : SL(2, ℤ)) :
    1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤
      2 * Real.cosh (2 * dist UpperHalfPlane.I z) * (1 + 2 * pairU z (γ • z)) := by
  have hiso : dist (γ • z) (γ • UpperHalfPlane.I) = dist z UpperHalfPlane.I :=
    dist_smul (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ) z UpperHalfPlane.I
  have htri : dist UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤
      2 * dist UpperHalfPlane.I z + dist z (γ • z) := by
    have h1 := dist_triangle UpperHalfPlane.I z (γ • UpperHalfPlane.I)
    have h2 := dist_triangle z (γ • z) (γ • UpperHalfPlane.I)
    rw [hiso, dist_comm z UpperHalfPlane.I] at h2
    linarith
  set δ := 2 * dist UpperHalfPlane.I z
  set D := dist z (γ • z)
  have hδ : 0 ≤ δ := by positivity
  have hD : 0 ≤ D := dist_nonneg
  rw [pairU_eq_cosh, pairU_eq_cosh]
  have hc : Real.cosh (dist UpperHalfPlane.I (γ • UpperHalfPlane.I)) ≤ Real.cosh (δ + D) :=
    Real.cosh_le_cosh.2 (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by linarith)]; exact htri)
  have hs : Real.sinh δ * Real.sinh D ≤ Real.cosh δ * Real.cosh D :=
    mul_le_mul (Real.sinh_lt_cosh δ).le (Real.sinh_lt_cosh D).le (Real.sinh_nonneg_iff.2 hD)
      (Real.cosh_pos δ).le
  rw [Real.cosh_add] at hc
  nlinarith

/-- Every `γ` with `u(z,γz) ≤ R` has `u(i,γi) ≤ (2 cosh(2d(i,z))(1 + 2R) − 1)/2`. -/
theorem subset_pairU_I_smul_I_le (z : ℍ) (R : ℝ) :
    {γ : SL(2, ℤ) | pairU z (γ • z) ≤ R} ⊆
      {γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤
        (2 * Real.cosh (2 * dist UpperHalfPlane.I z) * (1 + 2 * R) - 1) / 2} := by
  intro γ hγ
  simp only [Set.mem_setOf_eq] at hγ ⊢
  have := one_add_two_mul_pairU_I_le z γ
  have hc : 0 < Real.cosh (2 * dist UpperHalfPlane.I z) := Real.cosh_pos _
  nlinarith

theorem finite_pairU_smul_le (z : ℍ) (R : ℝ) :
    {γ : SL(2, ℤ) | pairU z (γ • z) ≤ R}.Finite :=
  (finite_pairU_I_smul_I_le _).subset (subset_pairU_I_smul_I_le z R)

/-- **The count at every centre**, uniformly for centres within distance `D` of `i`. -/
theorem ncard_pairU_smul_le (D : ℝ) :
    ∃ C : ℝ, ∀ z : ℍ, dist UpperHalfPlane.I z ≤ D → ∀ R : ℝ, 0 ≤ R →
      ({γ : SL(2, ℤ) | pairU z (γ • z) ≤ R}.ncard : ℝ) ≤ C * (R + 1) := by
  refine ⟨640 * Real.cosh (2 * D), fun z hz R hR => ?_⟩
  set c := Real.cosh (2 * dist UpperHalfPlane.I z) with hcdef
  have hc1 : 1 ≤ c := Real.one_le_cosh _
  have hd0 : 0 ≤ dist UpperHalfPlane.I z := dist_nonneg
  have hcD : c ≤ Real.cosh (2 * D) :=
    Real.cosh_le_cosh.2 (by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
      linarith)
  set R' := (2 * c * (1 + 2 * R) - 1) / 2 with hR'def
  have hR' : 0 ≤ R' := by
    have : 1 ≤ 2 * c * (1 + 2 * R) := by nlinarith
    rw [hR'def]; linarith
  have h1 : ({γ : SL(2, ℤ) | pairU z (γ • z) ≤ R}.ncard : ℝ) ≤
      ({γ : SL(2, ℤ) | pairU UpperHalfPlane.I (γ • UpperHalfPlane.I) ≤ R'}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard (subset_pairU_I_smul_I_le z R) (finite_pairU_I_smul_I_le R')
  have h2 := ncard_pairU_I_smul_I_le hR'
  have h3 : 320 * (R' + 1) ≤ 640 * c * (R + 1) := by rw [hR'def]; nlinarith
  have h4 : 640 * c * (R + 1) ≤ 640 * Real.cosh (2 * D) * (R + 1) := by
    have : 0 ≤ R + 1 := by linarith
    nlinarith
  linarith

/-- **Summability at every centre.** -/
theorem summable_one_add_two_mul_pairU_rpow (z : ℍ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun γ : SL(2, ℤ) => (1 + 2 * pairU z (γ • z)) ^ (-σ) := by
  set c := Real.cosh (2 * dist UpperHalfPlane.I z)
  have hc : 0 < c := Real.cosh_pos _
  refine ((summable_one_add_two_mul_pairU_I_rpow hσ).mul_left ((2 * c) ^ σ)).of_nonneg_of_le
    (fun γ => ?_) (fun γ => ?_)
  · have := pairU_nonneg z (γ • z); positivity
  · have h0 := pairU_nonneg z (γ • z)
    have h0' := pairU_nonneg UpperHalfPlane.I (γ • UpperHalfPlane.I)
    have hle := one_add_two_mul_pairU_I_le z γ
    have hle' : (1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I)) / (2 * c) ≤
        1 + 2 * pairU z (γ • z) := by
      rw [div_le_iff₀ (by positivity)]; linarith
    calc (1 + 2 * pairU z (γ • z)) ^ (-σ)
        ≤ ((1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I)) / (2 * c)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle' (by linarith)
      _ = (2 * c) ^ σ * (1 + 2 * pairU UpperHalfPlane.I (γ • UpperHalfPlane.I)) ^ (-σ) := by
          rw [Real.div_rpow (by positivity) (by positivity),
            Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * c) σ, div_inv_eq_mul]
          ring

/-- **Subgroups.**  The count for a subgroup `Γ ≤ SL(2,ℤ)` is bounded by the full count. -/
theorem ncard_subgroup_pairU_smul_le (Γ : Subgroup SL(2, ℤ)) (D : ℝ) :
    ∃ C : ℝ, ∀ z : ℍ, dist UpperHalfPlane.I z ≤ D → ∀ R : ℝ, 0 ≤ R →
      ({γ : Γ | pairU z ((γ : SL(2, ℤ)) • z) ≤ R}.ncard : ℝ) ≤ C * (R + 1) := by
  obtain ⟨C, hC⟩ := ncard_pairU_smul_le D
  refine ⟨C, fun z hz R hR => le_trans ?_ (hC z hz R hR)⟩
  have hfin := finite_pairU_smul_le z R
  exact_mod_cast Set.ncard_le_ncard_of_injOn Subtype.val (fun γ hγ => hγ)
    Subtype.val_injective.injOn hfin

/-- **Summability over a subgroup.** -/
theorem summable_subgroup_one_add_two_mul_pairU_rpow (Γ : Subgroup SL(2, ℤ)) (z : ℍ) {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun γ : Γ => (1 + 2 * pairU z ((γ : SL(2, ℤ)) • z)) ^ (-σ) :=
  (summable_one_add_two_mul_pairU_rpow z hσ).comp_injective Subtype.val_injective

end

end RHTower
