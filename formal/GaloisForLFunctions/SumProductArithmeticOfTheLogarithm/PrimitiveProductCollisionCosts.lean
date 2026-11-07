import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.RectangularProductCollisions

/-!
# Primitive-step costs for product collisions

For fixed positive rows `m,n`, write `g = gcd(m,n)` and `d = n/g`.
Column pairs in `[1,Z]` with prescribed product difference have at most
`floor(Z/d)+1` quotient labels. Only differences divisible by `g` occur,
so the cumulative count through `H` is at most
`(floor(Z/d)+1) * floor(H/g)`.

In the positive product ordering the larger product is at most `n*Z`.
At logarithmic width `1/T`, this gives a height-scaled count at most
`Z*(Z+n/g)`. Both orientations therefore cost at most
`Z*(2*Z+m/g+n/g)`, with no dyadic restriction on the rows.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- The primitive column step gives a fibre bound without a row-scale restriction. -/
theorem rectangularProductCollisionFiber_le_primitive {m n : ℕ} (hn : 0 < n) (Z h : ℕ) :
    (rectangularProductCollisionFiber m n Z h).card ≤ Z / (n / Nat.gcd m n) + 1 := by
  let g := Nat.gcd n m
  let d := n / g
  let F : Finset (ℕ × ℕ) := rectangularProductCollisionFiber m n Z h
  let label : ↥F → Fin (Z / d + 1) := fun p => ⟨p.val.1 / d, by
    have hp := (mem_Icc.mp (mem_product.mp (mem_filter.mp p.property).1).1).2
    have hq : p.val.1 / d ≤ Z / d := Nat.div_le_div_right hp
    omega⟩
  have hinj : Function.Injective label := by
    intro p p' he
    have hp : m * p.val.1 + h = n * p.val.2 := (mem_filter.mp p.property).2
    have hp' : m * p'.val.1 + h = n * p'.val.2 := (mem_filter.mp p'.property).2
    have hsum : Nat.ModEq n (m * p.val.1 + h) (m * p'.val.1 + h) := by
      rw [hp, hp']
      simp only [Nat.ModEq, Nat.mul_mod_right]
    have hmod : Nat.ModEq d p.val.1 p'.val.1 :=
      Nat.ModEq.cancel_left_div_gcd hn (Nat.ModEq.add_right_cancel' h hsum)
    have hquot : p.val.1 / d = p'.val.1 / d := congrArg Fin.val he
    have hfirst : p.val.1 = p'.val.1 := by
      rw [← Nat.mod_add_div p.val.1 d, ← Nat.mod_add_div p'.val.1 d]
      rw [show p.val.1 % d = p'.val.1 % d from hmod, hquot]
    have hcols : n * p.val.2 = n * p'.val.2 := by rw [← hp, ← hp', hfirst]
    exact Subtype.ext (Prod.ext hfirst (mul_left_cancel₀ hn.ne' hcols))
  simpa only [F, Fintype.card_coe, Fintype.card_fin, d, g, Nat.gcd_comm] using
    Fintype.card_le_of_injective label hinj

/-- Primitive-step fibres retain exact gcd compatibility of the integer difference. -/
theorem rectangularProductCollisionFiber_le_primitive_gate {m n : ℕ} (hn : 0 < n) (Z h : ℕ) :
    (rectangularProductCollisionFiber m n Z h).card ≤
      if Nat.gcd m n ∣ h then Z / (n / Nat.gcd m n) + 1 else 0 := by
  split_ifs with hd
  · exact rectangularProductCollisionFiber_le_primitive hn Z h
  · have hempty : rectangularProductCollisionFiber m n Z h = ∅ := by
      ext p
      constructor
      · intro hp
        have he := (mem_filter.mp hp).2
        have hl := dvd_mul_of_dvd_left (Nat.gcd_dvd_left m n) p.1
        have hr := dvd_mul_of_dvd_left (Nat.gcd_dvd_right m n) p.2
        rw [← he] at hr
        exact False.elim (hd ((Nat.dvd_add_right hl).mp hr))
      · intro hp
        simp at hp
    rw [hempty, card_empty]

/-- Summed differences keep the primitive column mesh and exact quotient cutoff. -/
theorem cumulative_rectangular_collision_le_primitive {m n : ℕ} (hn : 0 < n) (Z H : ℕ) :
    (∑ h ∈ Icc 1 H, (rectangularProductCollisionFiber m n Z h).card) ≤
      (Z / (n / Nat.gcd m n) + 1) * (H / Nat.gcd m n) := by
  let g := Nat.gcd m n
  have hcard : ((Icc 1 H).filter fun h => g ∣ h).card = H / g := by
    have he : Icc 1 H = Ioc 0 H := by ext h; simp only [mem_Icc, mem_Ioc]; omega
    rw [he]
    exact Nat.Ioc_filter_dvd_card_eq_div H g
  calc
    _ ≤ ∑ h ∈ Icc 1 H, if g ∣ h then Z / (n / g) + 1 else 0 :=
      sum_le_sum fun h _ => rectangularProductCollisionFiber_le_primitive_gate hn Z h
    _ = _ := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, hcard, Nat.cast_id]
      ring

private theorem primitive_nat_gap_le {a b : ℕ} (ha : 0 < a) (hab : a < b)
    {δ : ℝ} (hlog : Real.log (b : ℝ) - Real.log (a : ℝ) ≤ δ) :
    ((b - a : ℕ) : ℝ) ≤ (b : ℝ) * δ := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast ha.trans hab
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hbR haR)
  rw [Real.log_div hbR.ne' haR.ne', inv_div] at hl
  have he : 1 - (a : ℝ) / b = ((b : ℝ) - a) / b := by field_simp
  rw [he] at hl
  have h := (div_le_iff₀ hbR).mp (hl.trans hlog)
  rw [Nat.cast_sub hab.le]
  simpa only [mul_comm] using h

/-- The larger ordered product gives the exact row-dependent logarithmic cutoff. -/
theorem rectangularUpperLogFiber_le_primitive {m n Z : ℕ} (hm : 0 < m) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (rectangularUpperLogFiber m n Z δ).card ≤
      (Z / (n / Nat.gcd m n) + 1) * (⌊(n : ℝ) * Z * δ⌋₊ / Nat.gcd m n) := by
  let H := ⌊(n : ℝ) * Z * δ⌋₊
  have hsub : rectangularUpperLogFiber m n Z δ ⊆
      (Icc 1 H).biUnion (fun h => rectangularProductCollisionFiber m n Z h) := by
    intro p hp
    obtain ⟨hcols, hlt, hlog⟩ := mem_filter.mp hp
    let a := m * p.1
    let b := n * p.2
    have ha : 0 < a := Nat.mul_pos hm (mem_Icc.mp (mem_product.mp hcols).1).1
    have hb : (b : ℝ) ≤ (n : ℝ) * Z := by
      exact_mod_cast Nat.mul_le_mul_left n (mem_Icc.mp (mem_product.mp hcols).2).2
    have hgap : ((b - a : ℕ) : ℝ) ≤ (n : ℝ) * Z * δ :=
      (primitive_nat_gap_le ha hlt hlog).trans (mul_le_mul_of_nonneg_right hb hδ)
    apply mem_biUnion.mpr
    refine ⟨b - a, mem_Icc.mpr ⟨by omega, Nat.le_floor hgap⟩, mem_filter.mpr ⟨hcols, ?_⟩⟩
    change a + (b - a) = b
    omega
  exact ((card_le_card hsub).trans card_biUnion_le).trans
    (cumulative_rectangular_collision_le_primitive hn Z H)

/-- Height-scaled positive collisions pay the primitive row quotient, not the full row. -/
theorem mul_card_rectangularUpperLogFiber_le_primitive {m n Z : ℕ}
    (hm : 0 < m) (hn : 0 < n) {T : ℝ} (hT : 0 < T) :
    T * ((rectangularUpperLogFiber m n Z (1 / T)).card : ℝ) ≤
      (Z : ℝ) * (Z + (n / Nat.gcd m n : ℕ)) := by
  let g := Nat.gcd m n
  let d := n / g
  let q := Z / d + 1
  let H := ⌊(n : ℝ) * Z * (1 / T)⌋₊
  have hg : 0 < g := by
    dsimp only [g]
    rw [Nat.gcd_comm]
    exact Nat.gcd_pos_of_pos_left m hn
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hfac : g * d = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have hfacR : (g : ℝ) * d = n := by exact_mod_cast hfac
  have hH : T * (H : ℝ) ≤ (n : ℝ) * Z := by
    calc
      _ ≤ T * ((n : ℝ) * Z * (1 / T)) :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) hT.le
      _ = _ := by field_simp
  have hdiv : ((g * (H / g) : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.mul_div_le H g
  have hG : (g : ℝ) * (T * (H / g : ℕ)) ≤ (g : ℝ) * ((d : ℝ) * Z) := by
    calc
      _ = T * ((g * (H / g) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ T * H := mul_le_mul_of_nonneg_left hdiv hT.le
      _ ≤ (n : ℝ) * Z := hH
      _ = _ := by rw [← hfacR]; ring
  have hF : T * (H / g : ℕ) ≤ (d : ℝ) * Z := by
    by_contra hnot
    have hp := mul_pos hgR (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith only [hG, hp]
  have hqd : (q : ℝ) * d ≤ (Z : ℝ) + d := by
    have h := Nat.div_mul_le_self Z d
    exact_mod_cast (show q * d ≤ Z + d by dsimp only [q]; nlinarith only [h])
  have hc : ((rectangularUpperLogFiber m n Z (1 / T)).card : ℝ) ≤
      (q : ℝ) * (H / g : ℕ) := by
    dsimp only [q, d, g, H]
    exact_mod_cast rectangularUpperLogFiber_le_primitive (Z := Z) hm hn (by positivity : 0 ≤ 1 / T)
  calc
    _ ≤ T * ((q : ℝ) * (H / g : ℕ)) := mul_le_mul_of_nonneg_left hc hT.le
    _ = (q : ℝ) * (T * (H / g : ℕ)) := by ring
    _ ≤ (q : ℝ) * ((d : ℝ) * Z) := mul_le_mul_of_nonneg_left hF (by positivity)
    _ = ((q : ℝ) * d) * Z := by ring
    _ ≤ ((Z : ℝ) + d) * Z := mul_le_mul_of_nonneg_right hqd (by positivity)
    _ = _ := by dsimp only [d, g]; ring

/-- Arithmetic cost of both orientations of a product collision. -/
def primitiveProductCost (m n Z : ℕ) : ℝ :=
  (Z : ℝ) * (2 * Z + (m / Nat.gcd m n : ℕ) + (n / Nat.gcd m n : ℕ))

/-- All positive row pairs admit the primitive-step off-diagonal cost. -/
theorem mul_card_rectangularOffDiagonalLogFiber_le_primitive {m n Z : ℕ}
    (hm : 0 < m) (hn : 0 < n) {T : ℝ} (hT : 0 < T) :
    T * ((rectangularOffDiagonalLogFiber m n Z (1 / T)).card : ℝ) ≤
      primitiveProductCost m n Z := by
  have hsub : rectangularOffDiagonalLogFiber m n Z (1 / T) ⊆
      rectangularUpperLogFiber m n Z (1 / T) ∪
        (rectangularUpperLogFiber n m Z (1 / T)).image Prod.swap := by
    intro p hp
    obtain ⟨hcols, hne, habs⟩ := mem_filter.mp hp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mem_union_left _ (mem_filter.mpr ⟨hcols, hlt, by linarith only [(abs_le.mp habs).1]⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨Prod.swap p, ?_, Prod.swap_swap p⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_product.mp hcols).2, (mem_product.mp hcols).1⟩,
        hgt, (abs_le.mp habs).2⟩
  have hc : ((rectangularOffDiagonalLogFiber m n Z (1 / T)).card : ℝ) ≤
      (rectangularUpperLogFiber m n Z (1 / T)).card +
        (rectangularUpperLogFiber n m Z (1 / T)).card := by
    exact_mod_cast ((card_le_card hsub).trans (card_union_le _ _)).trans
      (Nat.add_le_add le_rfl card_image_le)
  calc
    _ ≤ T * ((rectangularUpperLogFiber m n Z (1 / T)).card +
        (rectangularUpperLogFiber n m Z (1 / T)).card) := mul_le_mul_of_nonneg_left hc hT.le
    _ = T * ((rectangularUpperLogFiber m n Z (1 / T)).card : ℝ) +
        T * ((rectangularUpperLogFiber n m Z (1 / T)).card : ℝ) := by ring
    _ ≤ (Z : ℝ) * (Z + (n / Nat.gcd m n : ℕ)) +
        (Z : ℝ) * (Z + (m / Nat.gcd n m : ℕ)) :=
      add_le_add (mul_card_rectangularUpperLogFiber_le_primitive hm hn hT)
        (mul_card_rectangularUpperLogFiber_le_primitive hn hm hT)
    _ = _ := by rw [Nat.gcd_comm n m]; unfold primitiveProductCost; ring

/-- Dropping the gcd saving gives a first-moment envelope on arbitrary positive supports. -/
theorem primitiveProductCost_le (m n Z : ℕ) :
    primitiveProductCost m n Z ≤ 2 * (Z : ℝ) ^ 2 + (Z : ℝ) * (m + n) := by
  have hm : ((m / Nat.gcd m n : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m (Nat.gcd m n)
  have hn : ((n / Nat.gcd m n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.div_le_self n (Nat.gcd m n)
  calc
    _ ≤ (Z : ℝ) * (2 * Z + m + n) :=
      mul_le_mul_of_nonneg_left (by linarith only [hm, hn]) (by positivity)
    _ = _ := by ring


end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
