import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic

/-!
# The concave Dwork weight

For a base `b ≥ 2`, the lower envelope `inf r : ℕ, r + x / b^r`
interpolates linear growth and a logarithmic cost. Its scale increment is
exactly `min ((b - 1) * x) 1`. Concavity makes this a subadditive valuation
weight, suitable for bounds on products and matrix entries.
-/

noncomputable section
open scoped NNReal BigOperators
namespace GaloisForLFunctions.HTGeometry

/-- Lower envelope of the affine costs at the successive scales of base `p + 2`. -/
def dworkWeight (p : ℕ) (x : ℝ) : ℝ :=
  ⨅ r : ℕ, (r : ℝ) + x / ((p : ℝ) + 2) ^ r

private theorem dworkWeight_cost_nonneg (p : ℕ) {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    0 ≤ (r : ℝ) + x / ((p : ℝ) + 2) ^ r := by positivity

private theorem dworkWeight_cost_bddBelow (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    BddBelow (Set.range (fun r : ℕ => (r : ℝ) + x / ((p : ℝ) + 2) ^ r)) :=
  ⟨0, by rintro y ⟨r, rfl⟩; exact dworkWeight_cost_nonneg p hx r⟩

private theorem dworkWeight_le_cost (p : ℕ) {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    dworkWeight p x ≤ (r : ℝ) + x / ((p : ℝ) + 2) ^ r :=
  ciInf_le (dworkWeight_cost_bddBelow p hx) r

private theorem dworkWeight_nonneg_aux (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ dworkWeight p x := le_ciInf (dworkWeight_cost_nonneg p hx)

private theorem dworkWeight_le_self_aux (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    dworkWeight p x ≤ x := by
  simpa only [Nat.cast_zero, pow_zero, div_one, zero_add] using dworkWeight_le_cost p hx 0

/-- The weight vanishes at the origin. -/
theorem dworkWeight_zero (p : ℕ) : dworkWeight p 0 = 0 :=
  le_antisymm (dworkWeight_le_self_aux p le_rfl) (dworkWeight_nonneg_aux p le_rfl)

/-- Nonnegative inputs have a weight between zero and their linear cost. -/
theorem dworkWeight_bounds (p : ℕ) (x : ℝ≥0) :
    0 ≤ dworkWeight p x ∧ dworkWeight p x ≤ x :=
  ⟨dworkWeight_nonneg_aux p x.property, dworkWeight_le_self_aux p x.property⟩

/-- The infimum is a minimum, attained at an index no larger than the input. -/
theorem dworkWeight_attained (p : ℕ) (x : ℝ≥0) :
    ∃ r : ℕ, dworkWeight p x = (r : ℝ) + x / ((p : ℝ) + 2) ^ r ∧
      (r : ℝ) ≤ x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (x : ℝ)
  obtain ⟨r, hr, hmin⟩ := (Finset.range (N + 1)).exists_min_image
    (fun r : ℕ => (r : ℝ) + x / ((p : ℝ) + 2) ^ r)
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  have hzero := hmin 0 (Finset.mem_range.mpr (Nat.succ_pos N))
  simp only [Nat.cast_zero, pow_zero, div_one, zero_add] at hzero
  refine ⟨r, le_antisymm (dworkWeight_le_cost p x.property r) ?_, ?_⟩
  · apply le_ciInf
    intro s
    by_cases hs : s < N + 1
    · exact hmin s (Finset.mem_range.mpr hs)
    · have hNs : N ≤ s := Nat.le_trans (Nat.le_succ N) (Nat.le_of_not_gt hs)
      have hxs : (x : ℝ) ≤ s := hN.le.trans (by exact_mod_cast hNs)
      exact hzero.trans (hxs.trans (le_add_of_nonneg_right (by positivity)))
  · exact (le_add_of_nonneg_right (by positivity)).trans hzero

private theorem dworkWeight_eq_self_of_le_one (p : ℕ) {x : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : dworkWeight p x = x := by
  apply le_antisymm (dworkWeight_le_self_aux p hx)
  apply le_ciInf
  intro r
  cases r with
  | zero => simp
  | succ r =>
    have hr : (1 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast Nat.succ_pos r
    exact hx1.trans (hr.trans (le_add_of_nonneg_right (by positivity)))

private theorem dworkWeight_cost_scale (p : ℕ) (x : ℝ) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) + (((p : ℝ) + 2) * x) / ((p : ℝ) + 2) ^ (r + 1) =
      1 + ((r : ℝ) + x / ((p : ℝ) + 2) ^ r) := by
  have hb : ((p : ℝ) + 2) ≠ 0 := ne_of_gt (by positivity)
  rw [pow_succ]
  push_cast
  field_simp
  ring

private theorem dworkWeight_scale_aux (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    dworkWeight p (((p : ℝ) + 2) * x) =
      min (((p : ℝ) + 2) * x) (1 + dworkWeight p x) := by
  have hpx : 0 ≤ ((p : ℝ) + 2) * x := by positivity
  apply le_antisymm
  · apply le_min (dworkWeight_le_self_aux p hpx)
    have h : dworkWeight p (((p : ℝ) + 2) * x) - 1 ≤ dworkWeight p x := by
      apply le_ciInf
      intro r
      have hr := dworkWeight_le_cost p hpx (r + 1)
      rw [dworkWeight_cost_scale] at hr
      linarith only [hr]
    linarith only [h]
  · apply le_ciInf
    intro r
    cases r with
    | zero => simp only [Nat.cast_zero, pow_zero, div_one, zero_add]; exact min_le_left _ _
    | succ r =>
      rw [dworkWeight_cost_scale]
      exact (min_le_right _ _).trans (add_le_add (le_refl 1) (dworkWeight_le_cost p hx r))

/-- Exact scale recurrence, with no truncation of the infinite envelope. -/
theorem dworkWeight_scale (p : ℕ) (x : ℝ≥0) :
    dworkWeight p (((p : ℝ) + 2) * x) =
      min (((p : ℝ) + 2) * x) (1 + dworkWeight p x) :=
  dworkWeight_scale_aux p x.property

/-- Each dilation pays its linear cost until the increment saturates at one. -/
theorem dworkWeight_scale_increment (p : ℕ) (x : ℝ≥0) :
    dworkWeight p (((p : ℝ) + 2) * x) - dworkWeight p x =
      min (((p : ℝ) + 1) * x) 1 := by
  by_cases hsmall : ((p : ℝ) + 1) * x ≤ 1
  · have hx1 : (x : ℝ) ≤ 1 := by
      nlinarith only [hsmall, mul_nonneg (Nat.cast_nonneg p) x.property]
    rw [dworkWeight_scale, dworkWeight_eq_self_of_le_one p (x := (x : ℝ)) x.property hx1,
      min_eq_left (by nlinarith only [hsmall]), min_eq_left hsmall]
    ring
  · have hlarge : 1 ≤ ((p : ℝ) + 1) * x := (lt_of_not_ge hsmall).le
    have hcost := dworkWeight_le_self_aux p (x := (x : ℝ)) x.property
    rw [dworkWeight_scale, min_eq_right (by linarith only [hlarge, hcost]),
      min_eq_right hlarge]
    ring

/-- The first breakpoint is exactly `b / (b - 1)` for base `b = p + 2`. -/
theorem dworkWeight_eq_self_iff (p : ℕ) (x : ℝ≥0) :
    dworkWeight p x = x ↔ ((p : ℝ) + 1) * x ≤ (p : ℝ) + 2 := by
  have hb : 0 < (p : ℝ) + 2 := by positivity
  constructor
  · intro h
    have hc := dworkWeight_le_cost p (x := (x : ℝ)) x.property 1
    rw [h, Nat.cast_one, pow_one] at hc
    have hd : (x : ℝ) - 1 ≤ x / ((p : ℝ) + 2) := by linarith only [hc]
    have hm := (le_div_iff₀ hb).mp hd
    nlinarith only [hm]
  · intro h
    have hx : (x : ℝ) ≤ (p : ℝ) + 2 := by
      nlinarith only [h, mul_nonneg (Nat.cast_nonneg p) x.property]
    have hy : 0 ≤ (x : ℝ) / ((p : ℝ) + 2) := div_nonneg x.property hb.le
    have hy1 : (x : ℝ) / ((p : ℝ) + 2) ≤ 1 := (div_le_one hb).mpr hx
    have hcancel : ((p : ℝ) + 2) * ((x : ℝ) / ((p : ℝ) + 2)) = x := by
      field_simp
    have hd : (x : ℝ) - 1 ≤ x / ((p : ℝ) + 2) :=
      (le_div_iff₀ hb).mpr (by nlinarith only [h])
    have hs := dworkWeight_scale_aux p hy
    rw [hcancel, dworkWeight_eq_self_of_le_one p hy hy1,
      min_eq_left (by linarith only [hd])] at hs
    exact hs

/-- Taking a lower envelope preserves concavity on the nonnegative half-line. -/
theorem concaveOn_dworkWeight (p : ℕ) :
    ConcaveOn ℝ (Set.Ici 0) (dworkWeight p) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change a * dworkWeight p x + b * dworkWeight p y ≤ dworkWeight p (a * x + b * y)
  apply le_ciInf
  intro r
  calc
    _ ≤ a * ((r : ℝ) + x / ((p : ℝ) + 2) ^ r) +
        b * ((r : ℝ) + y / ((p : ℝ) + 2) ^ r) :=
      add_le_add (mul_le_mul_of_nonneg_left (dworkWeight_le_cost p hx r) ha)
        (mul_le_mul_of_nonneg_left (dworkWeight_le_cost p hy r) hb)
    _ = (a + b) * (r : ℝ) + (a * x + b * y) / ((p : ℝ) + 2) ^ r := by ring
    _ = _ := by rw [hab, one_mul]

/-- The weight is monotone on its natural domain. -/
theorem monotoneOn_dworkWeight (p : ℕ) : MonotoneOn (dworkWeight p) (Set.Ici 0) := by
  intro x hx y _ hxy
  exact ciInf_mono (dworkWeight_cost_bddBelow p hx) fun r =>
    add_le_add (le_refl (r : ℝ))
      (div_le_div_of_nonneg_right hxy (pow_nonneg (by positivity) r))

/-- Equal distribution maximizes the total weight at fixed total size. -/
theorem sum_dworkWeight_le (p n : ℕ) (x : Fin (n + 1) → ℝ≥0) :
    ∑ i, dworkWeight p (x i) ≤
      (n + 1 : ℝ) * dworkWeight p ((∑ i, (x i : ℝ)) / (n + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h := (concaveOn_dworkWeight p).le_map_sum
    (t := Finset.univ) (w := fun _ : Fin (n + 1) => (1 : ℝ) / (n + 1))
    (p := fun i => (x i : ℝ)) (fun _ _ => by positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; field_simp)
    (fun i _ => (x i).property)
  simp only [smul_eq_mul, one_div, ← div_eq_inv_mul, ← Finset.sum_div] at h
  exact (div_le_iff₀ hn).mp h |>.trans_eq (mul_comm _ _)

/-- The concave envelope is subadditive, so products pay at most the sum of
the weights of their factors. -/
theorem dworkWeight_subadd (p : ℕ) (x y : ℝ≥0) :
    dworkWeight p ((x : ℝ) + y) ≤ dworkWeight p x + dworkWeight p y := by
  by_cases hs : (x : ℝ) + y = 0
  · have hx : (x : ℝ) = 0 := by linarith only [hs, x.property, y.property]
    have hy : (y : ℝ) = 0 := by linarith only [hs, x.property, y.property]
    rw [hs, hx, hy, dworkWeight_zero, add_zero]
  · have hspos : 0 < (x : ℝ) + y :=
      lt_of_le_of_ne (add_nonneg x.property y.property) (Ne.symm hs)
    have ha : 0 ≤ (x : ℝ) / (x + y) := div_nonneg x.property hspos.le
    have hb : 0 ≤ (y : ℝ) / (x + y) := div_nonneg y.property hspos.le
    have hab : (x : ℝ) / (x + y) + (y : ℝ) / (x + y) = 1 := by
      rw [← add_div, div_self hs]
    have hx := (concaveOn_dworkWeight p).2
      (show (x : ℝ) + y ∈ Set.Ici 0 from hspos.le)
      (show (0 : ℝ) ∈ Set.Ici 0 from by simp only [Set.mem_Ici, le_refl]) ha hb hab
    have hy := (concaveOn_dworkWeight p).2
      (show (x : ℝ) + y ∈ Set.Ici 0 from hspos.le)
      (show (0 : ℝ) ∈ Set.Ici 0 from by simp only [Set.mem_Ici, le_refl])
      hb ha (by rw [add_comm]; exact hab)
    simp only [smul_eq_mul, dworkWeight_zero, mul_zero, add_zero,
      div_mul_cancel₀ _ hs] at hx hy
    calc
      _ = ((x : ℝ) / (x + y) + (y : ℝ) / (x + y)) * dworkWeight p (x + y) := by
        rw [hab, one_mul]
      _ = (x : ℝ) / (x + y) * dworkWeight p (x + y) +
          (y : ℝ) / (x + y) * dworkWeight p (x + y) := by ring
      _ ≤ _ := add_le_add hx hy

#print axioms dworkWeight_scale_increment
#print axioms dworkWeight_attained
#print axioms dworkWeight_eq_self_iff
#print axioms concaveOn_dworkWeight
#print axioms monotoneOn_dworkWeight
#print axioms sum_dworkWeight_le
#print axioms dworkWeight_subadd

end GaloisForLFunctions.HTGeometry
