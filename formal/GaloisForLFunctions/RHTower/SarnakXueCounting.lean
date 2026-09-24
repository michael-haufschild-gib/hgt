import Mathlib

open Finset

/-!
# Counting principal congruence elements that move a point a bounded distance

For `z = x + iy`, `2 cosh d(z, γz)` equals the quadratic form `qform x y γ`, the squared Frobenius norm of
`g_z⁻¹ γ g_z` (`two_cosh_dist_eq_qform`). For `p` an odd prime, `|x| ≤ 1/2`, `y ≥ 1/2`, `X ≥ 1` and
`d(n) ≤ C n^ε`, at most
`(2y√X/p + 1) + (4√X/p + 1) + (4√X/p² + 1)(4√X/p + 1) · 2C(9X)^ε`
elements of `Γ(p)` satisfy `qform x y γ ≤ X` (`card_le`). Upper-triangular elements are counted by
`b ≡ 0 (p)`, lower-triangular ones by `c ≡ 0 (p)`; the rest are fixed by the trace `t ≡ 2 (p²)`, the corner
`a ≡ 1 (p)` and a signed divisor `c` of `a(t - a) - 1`.
-/

namespace GaloisForLFunctions.RHTower.SarnakXueCounting

/-- Integers in `[-L, L]` in one residue class modulo `m` number at most `2L/m + 1`. -/
theorem card_le_of_modEq {T : Finset ℤ} {m : ℤ} (hm : 0 < m) (r : ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ t ∈ T, |(t : ℝ)| ≤ L ∧ m ∣ t - r) :
    (T.card : ℝ) ≤ 2 * L / m + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set lo : ℤ := ⌈(-L - r) / m⌉
  set hi : ℤ := ⌊(L - r) / m⌋
  have hmaps : ∀ t ∈ T, (t - r) / m ∈ Icc lo hi := by
    intro t ht
    obtain ⟨hab, hdvd⟩ := hT t ht
    obtain ⟨k, hk⟩ := hdvd
    have hkq : (t - r) / m = k := by rw [hk]; exact Int.mul_ediv_cancel_left k hm.ne'
    rw [hkq, mem_Icc]
    have htk : (t : ℝ) = r + m * k := by
      have : (t : ℝ) - r = m * k := by exact_mod_cast hk
      linarith
    have h1 := abs_le.mp hab
    constructor
    · apply Int.ceil_le.mpr
      rw [div_le_iff₀ hmR]; nlinarith
    · apply Int.le_floor.mpr
      rw [le_div_iff₀ hmR]; nlinarith
  have hinj : Set.InjOn (fun t => (t - r) / m) T := by
    intro t ht u hu h
    obtain ⟨k, hk⟩ := (hT t ht).2
    obtain ⟨l, hl⟩ := (hT u hu).2
    simp only at h
    rw [hk, hl, Int.mul_ediv_cancel_left _ hm.ne', Int.mul_ediv_cancel_left _ hm.ne'] at h
    rw [h] at hk
    linarith
  have hcard : T.card ≤ (Icc lo hi).card := by
    rw [← card_image_of_injOn hinj]
    exact card_le_card (fun v hv => by
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hv
      exact hmaps t ht)
  rw [Int.card_Icc] at hcard
  have hlo : (-L - r) / m ≤ lo := Int.le_ceil _
  have hhi : (hi : ℝ) ≤ (L - r) / m := Int.floor_le _
  have hpos : (0 : ℝ) ≤ 2 * L / m + 1 := by positivity
  rcases le_or_gt 0 (hi + 1 - lo) with h | h
  · have : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
      rw [show ((hi + 1 - lo).toNat : ℝ) = (((hi + 1 - lo).toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg h]
      push_cast; ring
    calc (T.card : ℝ) ≤ ((hi + 1 - lo).toNat : ℝ) := by exact_mod_cast hcard
      _ = (hi : ℝ) + 1 - lo := this
      _ ≤ (L - r) / m + 1 - (-L - r) / m := by linarith
      _ = 2 * L / m + 1 := by field_simp; ring
  · have : (hi + 1 - lo).toNat = 0 := Int.toNat_of_nonpos h.le
    rw [this] at hcard
    have : T.card = 0 := by omega
    rw [this]; simpa using hpos

open CongruenceSubgroup
open scoped MatrixGroups

variable {p : ℕ} [hp : Fact p.Prime]

theorem gamma_dvd {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma p) :
    (p : ℤ) ∣ γ 0 0 - 1 ∧ (p : ℤ) ∣ γ 0 1 ∧ (p : ℤ) ∣ γ 1 0 ∧ (p : ℤ) ∣ γ 1 1 - 1 := by
  rw [Gamma_mem] at hγ
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1, sub_self]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h2
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h3
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h4, sub_self]

theorem det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2
  rw [Matrix.det_fin_two] at this
  exact this

/-- In `Γ(p)` the trace is `2` modulo `p²`. -/
theorem trace_modEq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma p) :
    (p : ℤ) ^ 2 ∣ (γ 0 0 + γ 1 1) - 2 := by
  obtain ⟨ha, hb, hc, hd⟩ := gamma_dvd hγ
  have hdet := det_eq γ
  have h : (γ 0 0 + γ 1 1) - 2 = γ 0 1 * γ 1 0 - (γ 0 0 - 1) * (γ 1 1 - 1) := by linarith
  rw [h, sq]
  exact dvd_sub (mul_dvd_mul hb hc) (mul_dvd_mul ha hd)

/-- A unit diagonal entry in `Γ(p)`, `p` odd: `a = ±1` and `a ≡ 1` force `a = 1`. -/
theorem eq_one_of_mul_eq_one (hp2 : p ≠ 2) {a d : ℤ} (had : a * d = 1) (ha : (p : ℤ) ∣ a - 1) :
    a = 1 := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one had with h | h
  · exact h
  · exfalso
    rw [h] at ha
    have h2 : (p : ℤ) ∣ 2 := by
      have : (-1 : ℤ) - 1 = -2 := by norm_num
      rw [this, dvd_neg] at ha; exact ha
    have := Int.le_of_dvd (by norm_num) h2
    have hp' := hp.out.two_le
    have : p = 2 := by
      have h' : (p : ℤ) ≤ 2 := this
      omega
    exact hp2 this

/-- `2 cosh d(z, γz)` in coordinates `z = x + iy`: the squared Frobenius norm of `g_z⁻¹ γ g_z`. -/
noncomputable def qform (x y : ℝ) (γ : SL(2, ℤ)) : ℝ :=
  ((γ 0 0 : ℝ) - γ 1 0 * x) ^ 2 + (((γ 0 1 : ℝ) + ((γ 0 0 : ℝ) - γ 1 1) * x - γ 1 0 * x ^ 2) / y) ^ 2 +
    ((γ 1 0 : ℝ) * y) ^ 2 + ((γ 1 0 : ℝ) * x + γ 1 1) ^ 2

section bounds
variable {x y X : ℝ} {γ : SL(2, ℤ)}

theorem qform_parts (x y : ℝ) (γ : SL(2, ℤ)) :
    0 ≤ ((γ 0 0 : ℝ) - γ 1 0 * x) ^ 2 ∧
    0 ≤ (((γ 0 1 : ℝ) + ((γ 0 0 : ℝ) - γ 1 1) * x - γ 1 0 * x ^ 2) / y) ^ 2 ∧
    0 ≤ ((γ 1 0 : ℝ) * y) ^ 2 ∧ 0 ≤ ((γ 1 0 : ℝ) * x + γ 1 1) ^ 2 :=
  ⟨sq_nonneg _, sq_nonneg _, sq_nonneg _, sq_nonneg _⟩

theorem abs_c_le (hy : 0 < y) (h : qform x y γ ≤ X) : |(γ 1 0 : ℝ)| ≤ Real.sqrt X / y := by
  rw [le_div_iff₀ hy]
  obtain ⟨h1, h2, h3, h4⟩ := qform_parts x y γ
  have hc : ((γ 1 0 : ℝ) * y) ^ 2 ≤ X := by
    unfold qform at h
    linarith
  have := Real.abs_le_sqrt hc
  rwa [abs_mul, abs_of_pos hy] at this

theorem abs_a_sub_le (h : qform x y γ ≤ X) : |(γ 0 0 : ℝ) - γ 1 0 * x| ≤ Real.sqrt X := by
  apply Real.abs_le_sqrt
  obtain ⟨h1, h2, h3, h4⟩ := qform_parts x y γ
  unfold qform at h
  linarith

theorem abs_d_add_le (h : qform x y γ ≤ X) : |(γ 1 0 : ℝ) * x + γ 1 1| ≤ Real.sqrt X := by
  apply Real.abs_le_sqrt
  obtain ⟨h1, h2, h3, h4⟩ := qform_parts x y γ
  unfold qform at h
  linarith

theorem abs_trace_le (h : qform x y γ ≤ X) : |(γ 0 0 : ℝ) + γ 1 1| ≤ 2 * Real.sqrt X := by
  have h1 := abs_a_sub_le h
  have h2 := abs_d_add_le h
  calc |(γ 0 0 : ℝ) + γ 1 1| = |((γ 0 0 : ℝ) - γ 1 0 * x) + ((γ 1 0 : ℝ) * x + γ 1 1)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

theorem abs_a_le (hx : |x| ≤ 1 / 2) (hy : 1 / 2 ≤ y) (h : qform x y γ ≤ X) :
    |(γ 0 0 : ℝ)| ≤ 2 * Real.sqrt X := by
  have hc := abs_c_le (by linarith) h
  have h1 := abs_a_sub_le h
  have hcx : |(γ 1 0 : ℝ) * x| ≤ Real.sqrt X := by
    rw [abs_mul]
    have hs := Real.sqrt_nonneg X
    have : Real.sqrt X / y ≤ 2 * Real.sqrt X := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith [abs_nonneg (γ 1 0 : ℝ), abs_nonneg x]
  calc |(γ 0 0 : ℝ)| = |((γ 0 0 : ℝ) - γ 1 0 * x) + (γ 1 0 : ℝ) * x| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end bounds

/-- Signed divisors of an integer (empty for `0`). -/
def sdiv (n : ℤ) : Finset ℤ :=
  (n.natAbs.divisors.image (fun k : ℕ => (k : ℤ))) ∪ (n.natAbs.divisors.image (fun k : ℕ => -(k : ℤ)))

theorem card_sdiv_le (n : ℤ) : (sdiv n).card ≤ 2 * n.natAbs.divisors.card := by
  unfold sdiv
  calc _ ≤ _ := card_union_le _ _
    _ ≤ n.natAbs.divisors.card + n.natAbs.divisors.card := add_le_add card_image_le card_image_le
    _ = _ := by ring

theorem mem_sdiv {n c : ℤ} (hn : n ≠ 0) (hc : c ∣ n) : c ∈ sdiv n := by
  unfold sdiv
  have hk : c.natAbs ∈ n.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hc, Int.natAbs_ne_zero.mpr hn⟩
  rcases Int.natAbs_eq c with h | h
  · exact mem_union_left _ (mem_image.mpr ⟨_, hk, h.symm⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨_, hk, h.symm⟩)

theorem sl_ext {γ γ' : SL(2, ℤ)} (h00 : γ 0 0 = γ' 0 0) (h01 : γ 0 1 = γ' 0 1)
    (h10 : γ 1 0 = γ' 1 0) (h11 : γ 1 1 = γ' 1 1) : γ = γ' := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

/-- **Counting in `Γ(p)`.** For `p` an odd prime, `z = x + iy` with `|x| ≤ 1/2`, `y ≥ 1/2`, and `X ≥ 1`,
every finite set of `γ ∈ Γ(p)` with `2 cosh d(z, γz) ≤ X` has at most
`(2y√X/p + 1) + (4√X/p + 1) + (4√X/p² + 1)(4√X/p + 1) · 2C(9X)^ε` elements, where `d(n) ≤ C n^ε`.
The trace is `2` modulo `p²`, the corner `a` is `1` modulo `p`, and `(b, c)` is a signed divisor pair of
`a(t - a) - 1`. -/
theorem card_le (hp2 : p ≠ 2) {x y X ε C : ℝ} (hx : |x| ≤ 1 / 2) (hy : 1 / 2 ≤ y) (hX : 1 ≤ X)
    (hε : 0 < ε) (hC0 : 0 ≤ C)
    (hC : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε)
    (S : Finset SL(2, ℤ)) (hS : ∀ γ ∈ S, γ ∈ Gamma p ∧ qform x y γ ≤ X) :
    (S.card : ℝ) ≤ (2 * y * Real.sqrt X / p + 1) + (4 * Real.sqrt X / p + 1) +
      (4 * Real.sqrt X / (p : ℝ) ^ 2 + 1) * (4 * Real.sqrt X / p + 1) * (2 * C * (9 * X) ^ ε) := by
  classical
  have hy0 : 0 < y := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
  have hsX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  set S₀ := S.filter (fun γ => γ 1 0 = 0)
  set S₁ := S.filter (fun γ => γ 1 0 ≠ 0 ∧ γ 0 1 = 0)
  set S₂ := S.filter (fun γ => γ 1 0 ≠ 0 ∧ γ 0 1 ≠ 0)
  have hsplit : S.card ≤ S₀.card + S₁.card + S₂.card := by
    have h1 : S.card = S₀.card + (S.filter (fun γ => ¬ γ 1 0 = 0)).card :=
      (card_filter_add_card_filter_not _).symm
    have h2 : (S.filter (fun γ => ¬ γ 1 0 = 0)).card ≤ S₁.card + S₂.card := by
      calc _ ≤ (S₁ ∪ S₂).card := card_le_card (fun γ hγ => by
            obtain ⟨hS, hc⟩ := mem_filter.mp hγ
            by_cases hb : γ 0 1 = 0
            · exact mem_union_left _ (mem_filter.mpr ⟨hS, hc, hb⟩)
            · exact mem_union_right _ (mem_filter.mpr ⟨hS, hc, hb⟩))
        _ ≤ _ := card_union_le _ _
    omega
  -- `c = 0`: γ is determined by `b`
  have h0 : (S₀.card : ℝ) ≤ 2 * y * Real.sqrt X / p + 1 := by
    have hinj : Set.InjOn (fun γ : SL(2, ℤ) => γ 0 1) S₀ := by
      intro γ hγ γ' hγ' h
      obtain ⟨hSγ, hc⟩ := mem_filter.mp hγ
      obtain ⟨hSγ', hc'⟩ := mem_filter.mp hγ'
      have hdet := det_eq γ; have hdet' := det_eq γ'
      rw [hc, mul_zero, sub_zero] at hdet; rw [hc', mul_zero, sub_zero] at hdet'
      have ha := eq_one_of_mul_eq_one hp2 hdet (gamma_dvd (hS γ hSγ).1).1
      have ha' := eq_one_of_mul_eq_one hp2 hdet' (gamma_dvd (hS γ' hSγ').1).1
      rw [ha, one_mul] at hdet; rw [ha', one_mul] at hdet'
      exact sl_ext (ha.trans ha'.symm) h (hc.trans hc'.symm) (hdet.trans hdet'.symm)
    rw [← card_image_of_injOn hinj]
    suffices hb : ((S₀.image (fun γ : SL(2, ℤ) => γ 0 1)).card : ℝ) ≤ 2 * (y * Real.sqrt X) / (p : ℤ) + 1 by
      push_cast at hb; linarith [show 2 * (y * Real.sqrt X) / (p : ℝ) = 2 * y * Real.sqrt X / p by ring]
    refine card_le_of_modEq hpZ 0 (L := y * Real.sqrt X) (by positivity) (fun b hb => ?_)
    obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hb
    obtain ⟨hS', hc⟩ := mem_filter.mp hγ
    obtain ⟨hΓ, hq⟩ := hS γ hS'
    refine ⟨?_, by simpa using (gamma_dvd hΓ).2.1⟩
    have hdet := det_eq γ
    rw [hc, mul_zero, sub_zero] at hdet
    have ha := eq_one_of_mul_eq_one hp2 hdet (gamma_dvd hΓ).1
    rw [ha, one_mul] at hdet
    have hb2 : ((γ 0 1 : ℝ) / y) ^ 2 ≤ X := by
      obtain ⟨h1, h2, h3, h4⟩ := qform_parts x y γ
      unfold qform at hq
      simp only [hc, ha, hdet, Int.cast_zero, Int.cast_one, sub_self, zero_mul, sub_zero,
        add_zero, zero_add] at hq h1 h2 h3 h4
      linarith
    have := Real.abs_le_sqrt hb2
    rw [abs_div, abs_of_pos hy0, div_le_iff₀ hy0] at this
    linarith
  -- `b = 0`, `c ≠ 0`: γ is determined by `c`
  have h1 : (S₁.card : ℝ) ≤ 4 * Real.sqrt X / p + 1 := by
    have hinj : Set.InjOn (fun γ : SL(2, ℤ) => γ 1 0) S₁ := by
      intro γ hγ γ' hγ' h
      obtain ⟨hSγ, _, hb⟩ := mem_filter.mp hγ
      obtain ⟨hSγ', _, hb'⟩ := mem_filter.mp hγ'
      have hdet := det_eq γ; have hdet' := det_eq γ'
      rw [hb, zero_mul, sub_zero] at hdet; rw [hb', zero_mul, sub_zero] at hdet'
      have ha := eq_one_of_mul_eq_one hp2 hdet (gamma_dvd (hS γ hSγ).1).1
      have ha' := eq_one_of_mul_eq_one hp2 hdet' (gamma_dvd (hS γ' hSγ').1).1
      rw [ha, one_mul] at hdet; rw [ha', one_mul] at hdet'
      exact sl_ext (ha.trans ha'.symm) (hb.trans hb'.symm) h (hdet.trans hdet'.symm)
    rw [← card_image_of_injOn hinj]
    have hb := card_le_of_modEq hpZ 0 (L := Real.sqrt X / y) (by positivity)
      (T := S₁.image (fun γ : SL(2, ℤ) => γ 1 0)) (fun c hc => by
        obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hc
        obtain ⟨hS', _, _⟩ := mem_filter.mp hγ
        obtain ⟨hΓ, hq⟩ := hS γ hS'
        exact ⟨abs_c_le hy0 hq, by simpa using (gamma_dvd hΓ).2.2.1⟩)
    have : 2 * (Real.sqrt X / y) / p ≤ 4 * Real.sqrt X / p := by
      apply div_le_div_of_nonneg_right _ hpR.le
      rw [mul_div_assoc', div_le_iff₀ hy0]; nlinarith
    push_cast at hb
    linarith
  -- `bc ≠ 0`: γ is determined by `(a + d, a, c)`
  have h2 : (S₂.card : ℝ) ≤
      (4 * Real.sqrt X / (p : ℝ) ^ 2 + 1) * (4 * Real.sqrt X / p + 1) * (2 * C * (9 * X) ^ ε) := by
    set f : SL(2, ℤ) → ℤ × ℤ × ℤ := fun γ => (γ 0 0 + γ 1 1, γ 0 0, γ 1 0)
    have hinj : Set.InjOn f S₂ := by
      intro γ hγ γ' hγ' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨ht, ha, hc⟩ := h
      obtain ⟨_, hc0, _⟩ := mem_filter.mp hγ
      have hd : γ 1 1 = γ' 1 1 := by linarith
      have hdet := det_eq γ; have hdet' := det_eq γ'
      have hb : γ 0 1 = γ' 0 1 := by
        have : γ 0 1 * γ 1 0 = γ' 0 1 * γ 1 0 := by rw [hc] at hdet ⊢; rw [ha, hd] at hdet; linarith
        exact mul_right_cancel₀ hc0 this
      exact sl_ext ha hb hc hd
    set Tset := S₂.image (fun γ : SL(2, ℤ) => γ 0 0 + γ 1 1)
    set Aset := S₂.image (fun γ : SL(2, ℤ) => γ 0 0)
    set U := (Tset ×ˢ Aset).biUnion
      (fun ta => (sdiv (ta.2 * (ta.1 - ta.2) - 1)).image (fun c => (ta.1, ta.2, c)))
    have hsub : S₂.image f ⊆ U := by
      intro v hv
      obtain ⟨γ, hγ, rfl⟩ := mem_image.mp hv
      obtain ⟨_, hc0, hb0⟩ := mem_filter.mp hγ
      refine mem_biUnion.mpr ⟨(γ 0 0 + γ 1 1, γ 0 0),
        mem_product.mpr ⟨mem_image_of_mem _ hγ, mem_image_of_mem _ hγ⟩, ?_⟩
      apply mem_image.mpr
      refine ⟨γ 1 0, ?_, rfl⟩
      have hdet := det_eq γ
      have hn : γ 0 0 * (γ 0 0 + γ 1 1 - γ 0 0) - 1 = γ 0 1 * γ 1 0 := by linarith
      rw [hn]
      exact mem_sdiv (mul_ne_zero hb0 hc0) (dvd_mul_left _ _)
    have hdiv : ∀ ta ∈ Tset ×ˢ Aset,
        ((sdiv (ta.2 * (ta.1 - ta.2) - 1)).card : ℝ) ≤ 2 * C * (9 * X) ^ ε := by
      intro ta hta
      obtain ⟨ht, ha⟩ := mem_product.mp hta
      obtain ⟨γ, hγ, hγt⟩ := mem_image.mp ht
      obtain ⟨γ', hγ', hγa⟩ := mem_image.mp ha
      have hqt := (hS γ (mem_filter.mp hγ).1).2
      have hqa := (hS γ' (mem_filter.mp hγ').1).2
      have htb : |(ta.1 : ℝ)| ≤ 2 * Real.sqrt X := by
        rw [← hγt]; push_cast; exact abs_trace_le hqt
      have hab : |(ta.2 : ℝ)| ≤ 2 * Real.sqrt X := by
        rw [← hγa]; exact abs_a_le hx hy hqa
      set n := ta.2 * (ta.1 - ta.2) - 1
      have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt (by linarith)
      have hnb : (n.natAbs : ℝ) ≤ 9 * X := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        push_cast [n]
        have h1 : |(ta.2 : ℝ) * ((ta.1 : ℝ) - ta.2) - 1| ≤ |(ta.2 : ℝ)| * (|(ta.1 : ℝ)| + |(ta.2 : ℝ)|) + 1 := by
          calc _ ≤ |(ta.2 : ℝ) * ((ta.1 : ℝ) - ta.2)| + |(1 : ℝ)| := abs_sub _ _
            _ ≤ _ := by
              rw [abs_mul, abs_one]
              gcongr
              exact abs_sub _ _
        have h2 : |(ta.2 : ℝ)| * (|(ta.1 : ℝ)| + |(ta.2 : ℝ)|) ≤ 2 * Real.sqrt X * (4 * Real.sqrt X) := by
          apply mul_le_mul hab (by linarith) (by positivity) (by positivity)
        nlinarith
      by_cases hn0 : n.natAbs = 0
      · have : sdiv n = ∅ := by simp [sdiv, hn0]
        rw [this, card_empty, Nat.cast_zero]
        positivity
      · calc ((sdiv n).card : ℝ) ≤ 2 * (n.natAbs.divisors.card : ℝ) := by exact_mod_cast card_sdiv_le n
          _ ≤ 2 * (C * (n.natAbs : ℝ) ^ ε) := by
              gcongr; exact hC _ (Nat.one_le_iff_ne_zero.mpr hn0)
          _ ≤ 2 * (C * (9 * X) ^ ε) := by
              gcongr
          _ = 2 * C * (9 * X) ^ ε := by ring
    have hT : (Tset.card : ℝ) ≤ 4 * Real.sqrt X / (p : ℝ) ^ 2 + 1 := by
      have := card_le_of_modEq (pow_pos hpZ 2) 2 (L := 2 * Real.sqrt X) (by positivity)
        (T := Tset) (fun t ht => by
          obtain ⟨γ, hγ, rfl⟩ := mem_image.mp ht
          obtain ⟨hΓ, hq⟩ := hS γ (mem_filter.mp hγ).1
          exact ⟨by push_cast; exact abs_trace_le hq, trace_modEq hΓ⟩)
      push_cast at this
      have e : 2 * (2 * Real.sqrt X) / (p : ℝ) ^ 2 = 4 * Real.sqrt X / (p : ℝ) ^ 2 := by ring
      linarith
    have hA : (Aset.card : ℝ) ≤ 4 * Real.sqrt X / p + 1 := by
      have := card_le_of_modEq hpZ 1 (L := 2 * Real.sqrt X) (by positivity)
        (T := Aset) (fun a ha => by
          obtain ⟨γ, hγ, rfl⟩ := mem_image.mp ha
          obtain ⟨hΓ, hq⟩ := hS γ (mem_filter.mp hγ).1
          exact ⟨abs_a_le hx hy hq, (gamma_dvd hΓ).1⟩)
      push_cast at this
      have e : 2 * (2 * Real.sqrt X) / (p : ℝ) = 4 * Real.sqrt X / (p : ℝ) := by ring
      linarith
    calc (S₂.card : ℝ) = ((S₂.image f).card : ℝ) := by rw [card_image_of_injOn hinj]
      _ ≤ (U.card : ℝ) := by exact_mod_cast card_le_card hsub
      _ ≤ ∑ ta ∈ Tset ×ˢ Aset, ((sdiv (ta.2 * (ta.1 - ta.2) - 1)).card : ℝ) := by
          have := card_biUnion_le (s := Tset ×ˢ Aset)
            (t := fun ta => (sdiv (ta.2 * (ta.1 - ta.2) - 1)).image (fun c => (ta.1, ta.2, c)))
          calc (U.card : ℝ) ≤ ∑ ta ∈ Tset ×ˢ Aset,
                (((sdiv (ta.2 * (ta.1 - ta.2) - 1)).image (fun c => (ta.1, ta.2, c))).card : ℝ) := by
                exact_mod_cast this
            _ ≤ _ := sum_le_sum (fun ta _ => by exact_mod_cast card_image_le)
      _ ≤ ∑ ta ∈ Tset ×ˢ Aset, 2 * C * (9 * X) ^ ε := sum_le_sum hdiv
      _ = (Tset.card : ℝ) * Aset.card * (2 * C * (9 * X) ^ ε) := by
          rw [sum_const, card_product, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := by
          have hK : 0 ≤ 2 * C * (9 * X) ^ ε := by positivity
          gcongr
  have := (Nat.cast_le (α := ℝ)).mpr hsplit
  push_cast at this
  linarith

theorem qform_identity {a b c d x y D : ℝ} (hdet : a * d - b * c = 1) (hy : 0 < y) (hD : 0 < D) :
    2 * (1 + (((c * (x ^ 2 - y ^ 2) + (d - a) * x - b) ^ 2 + (y * (2 * c * x + d - a)) ^ 2) / D) /
      (2 * y * (y / D))) =
    (a - c * x) ^ 2 + ((b + (a - d) * x - c * x ^ 2) / y) ^ 2 + (c * y) ^ 2 + (c * x + d) ^ 2 := by
  field_simp
  linear_combination (-2 * y ^ 2) * hdet

open UpperHalfPlane in
/-- `2 cosh d(z, γz) = qform(Re z, Im z, γ)`. -/
theorem two_cosh_dist_eq_qform (γ : SL(2, ℤ)) (z : ℍ) :
    2 * Real.cosh (dist z (γ • z)) = qform z.re z.im γ := by
  set a : ℝ := ((γ 0 0 : ℤ) : ℝ)
  set b : ℝ := ((γ 0 1 : ℤ) : ℝ)
  set c : ℝ := ((γ 1 0 : ℤ) : ℝ)
  set d : ℝ := ((γ 1 1 : ℤ) : ℝ)
  set x := z.re
  set y := z.im
  have hy : 0 < y := z.im_pos
  have hdet : a * d - b * c = 1 := by
    have := det_eq γ
    simp only [a, b, c, d]; exact_mod_cast this
  set den : ℂ := (c : ℂ) * z + d
  have hden : den ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) z
    simpa [den, UpperHalfPlane.denom, c, d, Complex.ofReal_intCast] using this
  have hw : ((γ • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / den := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [a, b, c, d, den]
  have him : (γ • z).im = y / Complex.normSq den := by
    rw [ModularGroup.im_smul_eq_div_normSq]
    simp [den, UpperHalfPlane.denom, c, d, y, Complex.ofReal_intCast]
  have hnd : 0 < Complex.normSq den := Complex.normSq_pos.mpr hden
  have hz : (z : ℂ) = x + y * Complex.I := by
    apply Complex.ext <;> simp [x, y]
  set P : ℂ := (c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b
  have hsub : (z : ℂ) - ((γ • z : ℍ) : ℂ) = P / den := by
    rw [hw]; field_simp; simp only [P, den]; ring
  have hdist : dist (z : ℂ) ((γ • z : ℍ) : ℂ) ^ 2 = Complex.normSq P / Complex.normSq den := by
    rw [Complex.dist_eq, hsub, Complex.sq_norm, Complex.normSq_div]
  have hP : Complex.normSq P =
      (c * (x ^ 2 - y ^ 2) + (d - a) * x - b) ^ 2 + (y * (2 * c * x + d - a)) ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [P, hz]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [cosh_dist, hdist, him, hP]
  exact qform_identity hdet hy hnd

end GaloisForLFunctions.RHTower.SarnakXueCounting
