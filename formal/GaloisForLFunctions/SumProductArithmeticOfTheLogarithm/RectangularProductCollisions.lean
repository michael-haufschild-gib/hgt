import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.CumulativeSmoothPrimeEnergy

/-!
# Rectangular product collisions

For rows above `X > 0` and columns in `[1,Z]`, a fixed product-difference
fibre has at most `(Z/X+1) * gcd(m,n)` elements. Only differences divisible
by the row gcd occur. Summing differences to `H` therefore costs at most
`(Z/X+1) * H`. For rows at most `2X`, a logarithmic window of width `delta`
has integer cutoff `floor(2*X*Z*delta)`; both off-diagonal orientations obey
twice the corresponding cumulative bound. No smoothness or primality is
needed for this integer census.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-- Column pairs in `[1,Z]` at a prescribed integer product difference. -/
def rectangularProductCollisionFiber (m n Z h : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 Z ×ˢ Icc 1 Z).filter fun p => m * p.1 + h = n * p.2

/-- Quotient labels bound a rectangular fibre, retaining its row gcd. -/
theorem rectangularProductCollisionFiber_le_gcd {X m n : ℕ}
    (hX : 0 < X) (hn : X < n) (Z h : ℕ) :
    (rectangularProductCollisionFiber m n Z h).card ≤
      (Z / X + 1) * Nat.gcd m n := by
  let g := Nat.gcd n m
  let d := n / g
  let q := Z / X + 1
  let F := {p : ℕ × ℕ // p ∈ rectangularProductCollisionFiber m n Z h}
  have hn0 : 0 < n := hX.trans hn
  have hg : 0 < g := Nat.gcd_pos_of_pos_left m hn0
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left m hn0) hg
  have hfac : g * d = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)
  have hZ : Z < q * X := by
    have he := Nat.mod_add_div Z X
    have hr := Nat.mod_lt Z hX
    dsimp only [q]
    nlinarith only [he, hr]
  let label : F → Fin (q * g) := fun p => ⟨p.val.1 / d, by
    rw [Nat.div_lt_iff_lt_mul hd, mul_assoc, hfac]
    have hp := (mem_Icc.mp (mem_product.mp (mem_filter.mp p.property).1).1).2
    exact (hp.trans_lt hZ).trans_le (Nat.mul_le_mul_left q hn.le)⟩
  have hinj : Function.Injective label := by
    intro p p' he
    have hp : m * p.val.1 + h = n * p.val.2 := (mem_filter.mp p.property).2
    have hp' : m * p'.val.1 + h = n * p'.val.2 := (mem_filter.mp p'.property).2
    have hsum : Nat.ModEq n (m * p.val.1 + h) (m * p'.val.1 + h) := by
      rw [hp, hp']
      simp only [Nat.ModEq, Nat.mul_mod_right]
    have hmod : Nat.ModEq d p.val.1 p'.val.1 :=
      Nat.ModEq.cancel_left_div_gcd hn0 (Nat.ModEq.add_right_cancel' h hsum)
    have hquot : p.val.1 / d = p'.val.1 / d := congrArg Fin.val he
    have hfirst : p.val.1 = p'.val.1 := by
      rw [← Nat.mod_add_div p.val.1 d, ← Nat.mod_add_div p'.val.1 d]
      rw [show p.val.1 % d = p'.val.1 % d from hmod, hquot]
    have hcols : n * p.val.2 = n * p'.val.2 := by rw [← hp, ← hp', hfirst]
    exact Subtype.ext (Prod.ext hfirst (mul_left_cancel₀ hn0.ne' hcols))
  simpa only [F, Fintype.card_coe, Fintype.card_fin, q, g, Nat.gcd_comm] using
    Fintype.card_le_of_injective label hinj

/-- Incompatible differences have empty fibres. -/
theorem rectangularProductCollisionFiber_le_gcd_gate {X m n : ℕ}
    (hX : 0 < X) (hn : X < n) (Z h : ℕ) :
    (rectangularProductCollisionFiber m n Z h).card ≤
      if Nat.gcd m n ∣ h then (Z / X + 1) * Nat.gcd m n else 0 := by
  split_ifs with hd
  · exact rectangularProductCollisionFiber_le_gcd hX hn Z h
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

/-- Summing integer differences removes the gcd cost also for unequal row and column scales. -/
theorem cumulative_rectangular_collision_fiber_le {X m n : ℕ}
    (hX : 0 < X) (hn : X < n) (Z H : ℕ) :
    (∑ h ∈ Icc 1 H, (rectangularProductCollisionFiber m n Z h).card) ≤
      (Z / X + 1) * H := by
  let g := Nat.gcd m n
  have hcard : ((Icc 1 H).filter fun h => g ∣ h).card = H / g := by
    have he : Icc 1 H = Ioc 0 H := by ext h; simp only [mem_Icc, mem_Ioc]; omega
    rw [he]
    exact Nat.Ioc_filter_dvd_card_eq_div H g
  calc
    _ ≤ ∑ h ∈ Icc 1 H, if g ∣ h then (Z / X + 1) * g else 0 :=
      sum_le_sum fun h _ => rectangularProductCollisionFiber_le_gcd_gate hX hn Z h
    _ = (Z / X + 1) * (g * (H / g)) := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, hcard, Nat.cast_id]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_div_le H g)

/-- Positive product differences in a closed logarithmic window. -/
def rectangularUpperLogFiber (m n Z : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  (Icc 1 Z ×ˢ Icc 1 Z).filter fun p =>
    m * p.1 < n * p.2 ∧ Real.log (n * p.2 : ℕ) - Real.log (m * p.1 : ℕ) ≤ δ

private theorem rectangular_nat_gap_le {a b : ℕ} (ha : 0 < a) (hab : a < b)
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

/-- Rectangular logarithmic collisions cost the integer width times `Z/X+1`. -/
theorem rectangularUpperLogFiber_le_floor {X m n Z : ℕ}
    (hX : 0 < X) (hm : 0 < m) (hn : X < n) (hn' : n ≤ 2 * X)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (rectangularUpperLogFiber m n Z δ).card ≤
      (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ := by
  let H := ⌊2 * (X : ℝ) * Z * δ⌋₊
  have hsub : rectangularUpperLogFiber m n Z δ ⊆
      (Icc 1 H).biUnion (fun h => rectangularProductCollisionFiber m n Z h) := by
    intro p hp
    obtain ⟨hpCols, hlt, hlog⟩ := mem_filter.mp hp
    let a := m * p.1
    let b := n * p.2
    have ha : 0 < a := Nat.mul_pos hm (mem_Icc.mp (mem_product.mp hpCols).1).1
    have hb : (b : ℝ) ≤ 2 * (X : ℝ) * Z := by
      exact_mod_cast Nat.mul_le_mul hn' (mem_Icc.mp (mem_product.mp hpCols).2).2
    have hgap : ((b - a : ℕ) : ℝ) ≤ 2 * (X : ℝ) * Z * δ :=
      (rectangular_nat_gap_le ha hlt hlog).trans (mul_le_mul_of_nonneg_right hb hδ)
    apply mem_biUnion.mpr
    refine ⟨b - a, mem_Icc.mpr ⟨by omega, Nat.le_floor hgap⟩, mem_filter.mpr ⟨hpCols, ?_⟩⟩
    change a + (b - a) = b
    omega
  exact ((card_le_card hsub).trans card_biUnion_le).trans
    (cumulative_rectangular_collision_fiber_le hX hn Z H)

/-- Distinct products in a closed logarithmic window, with columns in `[1,Z]`. -/
def rectangularOffDiagonalLogFiber (m n Z : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  (Icc 1 Z ×ˢ Icc 1 Z).filter fun p => m * p.1 ≠ n * p.2 ∧
    |Real.log (m * p.1 : ℕ) - Real.log (n * p.2 : ℕ)| ≤ δ

/-- Both orientations of the rectangular off-diagonal window have an arithmetic bound. -/
theorem rectangularOffDiagonalLogFiber_le_floor {X m n Z : ℕ}
    (hX : 0 < X) (hm : X < m) (hm' : m ≤ 2 * X) (hn : X < n) (hn' : n ≤ 2 * X)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (rectangularOffDiagonalLogFiber m n Z δ).card ≤
      2 * (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ := by
  have hsub : rectangularOffDiagonalLogFiber m n Z δ ⊆
      rectangularUpperLogFiber m n Z δ ∪ (rectangularUpperLogFiber n m Z δ).image Prod.swap := by
    intro p hp
    obtain ⟨hcols, hne, habs⟩ := mem_filter.mp hp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mem_union_left _ (mem_filter.mpr ⟨hcols, hlt, by linarith only [(abs_le.mp habs).1]⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨Prod.swap p, ?_, Prod.swap_swap p⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_product.mp hcols).2, (mem_product.mp hcols).1⟩,
        hgt, (abs_le.mp habs).2⟩
  have h1 := rectangularUpperLogFiber_le_floor hX (hX.trans hm) hn hn' hδ (Z := Z)
  have h2 := rectangularUpperLogFiber_le_floor hX (hX.trans hn) hm hm' hδ (Z := Z)
  calc
    _ ≤ (rectangularUpperLogFiber m n Z δ).card +
        ((rectangularUpperLogFiber n m Z δ).image Prod.swap).card :=
      (card_le_card hsub).trans (card_union_le _ _)
    _ ≤ (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ +
        (Z / X + 1) * ⌊2 * (X : ℝ) * Z * δ⌋₊ :=
      Nat.add_le_add h1 (card_image_le.trans h2)
    _ = _ := by ring


end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
