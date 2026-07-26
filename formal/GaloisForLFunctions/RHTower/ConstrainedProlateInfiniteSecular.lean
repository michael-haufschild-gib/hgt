import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import GaloisForLFunctions.RHTower.TwoModeFuchsLimit

/-!
# The exact infinite-dimensional constrained secular root and its two-mode transfer

The constrained ground state of a diagonal leakage operator `B e_j = d_j e_j` restricted to the
hyperplane `⟨·, ℓ⟩ = 0` is governed by the secular function

```text
F(μ) = Σ_{j≥0} ℓ_j² / (d_j − μ),
```

over the *full* infinite index set.  On the first spectral gap `(d_0, d_1)` this module proves:
`F` is finite (the tail denominators are uniformly separated once `d_2 ≤ d_{j+2}`), continuous,
and strictly increasing; it has exactly one root `μ_0`, and that root lies below the two-mode
trial value `μ_2mode = (ℓ_0²d_1 + ℓ_1²d_0)/(ℓ_0² + ℓ_1²)`; below `d_0` the secular function is
positive, so every further root lies above `d_1`.

The quantitative heart is the tail-perturbation estimate

```text
0 ≤ μ_2mode − μ_0 ≤ T · d_1² / (ℓ_0² (d_2 − d_1)),      T = Σ_{j≥2} ℓ_j²,
```

obtained by comparing the two-mode part of `F` at the two roots: the two-mode part moves at speed
at least `ℓ_0²/d_1²` on `(d_0, d_1)`, while the whole tail contributes at most `T/(d_2 − d_1)`.

Feeding in an aperture family with the Bessel bound `Σ_j ℓ_j(λ)² ≤ 2λ`, coordinate limits
`ℓ_0 → a_0`, `ℓ_1 → a_1`, and the scale-separation rates `d_0/d_1 → 0` and
`λ·d_1/(d_2 − d_1) → 0`, the exact constrained ground root then obeys

```text
μ_0(λ)/d_1(λ) → a_0²/(a_0² + a_1²),
(d_1(λ) − μ_0(λ))/d_1(λ) → a_1²/(a_0² + a_1²),
```

and every competing secular root stays a definite multiple of `d_1` above `μ_0`.  With the
Connes–Consani–Moscovici seed values `a_0 = 2^{1/4}`, `a_1 = √3·2^{−5/4}` the two constants are
exactly `8/11` and `3/11`: the infinite prolate tail does not shift the two-mode limits.
-/

open Filter Set

namespace RHTower

/-- Division by a fixed positive constant is monotone. -/
theorem div_le_div_of_le_of_pos {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  rw [div_le_iff₀ hc, div_mul_cancel₀ _ hc.ne']
  exact h

noncomputable section

/-- The tail of the constrained secular function: all coordinates from index `2` on. -/
def infiniteSecularTail (d ℓ : ℕ → ℝ) (μ : ℝ) : ℝ :=
  ∑' j : ℕ, ℓ (j + 2) ^ 2 / (d (j + 2) - μ)

/-- The full constrained secular function `F(μ) = Σ_{j≥0} ℓ_j²/(d_j − μ)`, written as its two
head coordinates plus the tail. -/
def infiniteSecular (d ℓ : ℕ → ℝ) (μ : ℝ) : ℝ :=
  ℓ 0 ^ 2 / (d 0 - μ) + ℓ 1 ^ 2 / (d 1 - μ) + infiniteSecularTail d ℓ μ

variable {d ℓ : ℕ → ℝ}

/-- The head-plus-tail expression is the genuine full series. -/
theorem infiniteSecular_eq_tsum {μ : ℝ}
    (hall : Summable fun j : ℕ => ℓ j ^ 2 / (d j - μ)) :
    infiniteSecular d ℓ μ = ∑' j : ℕ, ℓ j ^ 2 / (d j - μ) := by
  have hsplit := hall.sum_add_tsum_nat_add 2
  rw [infiniteSecular, ← hsplit, Finset.sum_range_succ, Finset.sum_range_one]
  rfl

theorem infiniteSecularTail_term_nonneg (hd2 : ∀ j, d 2 ≤ d (j + 2)) {μ : ℝ}
    (hμ : μ < d 2) (j : ℕ) :
    0 ≤ ℓ (j + 2) ^ 2 / (d (j + 2) - μ) :=
  div_nonneg (sq_nonneg _) (by linarith [hd2 j])

theorem infiniteSecularTail_term_le (hd2 : ∀ j, d 2 ≤ d (j + 2)) {μ : ℝ}
    (hμ : μ < d 2) (j : ℕ) :
    ℓ (j + 2) ^ 2 / (d (j + 2) - μ) ≤ ℓ (j + 2) ^ 2 / (d 2 - μ) :=
  div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hd2 j])

theorem summable_infiniteSecularTail (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) {μ : ℝ} (hμ : μ < d 2) :
    Summable fun j : ℕ => ℓ (j + 2) ^ 2 / (d (j + 2) - μ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + 2) ^ 2 := (summable_nat_add_iff 2).mpr hsum
  exact Summable.of_nonneg_of_le (infiniteSecularTail_term_nonneg hd2 hμ)
    (infiniteSecularTail_term_le hd2 hμ) (hsum2.div_const _)

theorem infiniteSecularTail_nonneg (hd2 : ∀ j, d 2 ≤ d (j + 2)) {μ : ℝ} (hμ : μ < d 2) :
    0 ≤ infiniteSecularTail d ℓ μ :=
  tsum_nonneg (infiniteSecularTail_term_nonneg hd2 hμ)

/-- The whole tail is controlled by the total tail mass over the uniform denominator gap. -/
theorem infiniteSecularTail_le (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) {μ : ℝ} (hμ : μ < d 2) :
    infiniteSecularTail d ℓ μ ≤ (∑' j : ℕ, ℓ (j + 2) ^ 2) / (d 2 - μ) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + 2) ^ 2 := (summable_nat_add_iff 2).mpr hsum
  rw [← tsum_div_const]
  exact Summable.tsum_le_tsum (infiniteSecularTail_term_le hd2 hμ)
    (summable_infiniteSecularTail hd2 hsum hμ) (hsum2.div_const _)

theorem infiniteSecularTail_mono (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) {μ μ' : ℝ} (hle : μ ≤ μ') (hμ' : μ' < d 2) :
    infiniteSecularTail d ℓ μ ≤ infiniteSecularTail d ℓ μ' := by
  refine Summable.tsum_le_tsum (fun j => ?_)
    (summable_infiniteSecularTail hd2 hsum (lt_of_le_of_lt hle hμ'))
    (summable_infiniteSecularTail hd2 hsum hμ')
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hd2 j]) (by linarith)

/-- Uniform-bound continuity of the tail on every half-line strictly below `d 2`. -/
theorem infiniteSecularTail_continuousOn (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) {b : ℝ} (hb : b < d 2) :
    ContinuousOn (infiniteSecularTail d ℓ) (Set.Iic b) := by
  have hsum2 : Summable fun j : ℕ => ℓ (j + 2) ^ 2 := (summable_nat_add_iff 2).mpr hsum
  rw [continuousOn_iff_continuous_restrict]
  have hrestrict : (Set.Iic b).restrict (infiniteSecularTail d ℓ)
      = fun x : Set.Iic b => ∑' j : ℕ, ℓ (j + 2) ^ 2 / (d (j + 2) - (x : ℝ)) := rfl
  rw [hrestrict]
  refine continuous_tsum (fun j => ?_) (hsum2.div_const (d 2 - b)) (fun j x => ?_)
  · refine continuous_const.div (continuous_const.sub continuous_subtype_val) fun x => ?_
    have hx : (x : ℝ) ≤ b := x.2
    exact ne_of_gt (by linarith [hd2 j])
  · have hx : (x : ℝ) ≤ b := x.2
    have hpos : 0 < d (j + 2) - (x : ℝ) := by linarith [hd2 j]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hd2 j])

/-- The full secular function is continuous between its first two poles. -/
theorem infiniteSecular_continuousOn (h12 : d 1 < d 2) (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) {a b : ℝ} (ha : d 0 < a) (hb : b < d 1) :
    ContinuousOn (infiniteSecular d ℓ) (Set.Icc a b) := by
  have h0 : ContinuousOn (fun μ : ℝ => ℓ 0 ^ 2 / (d 0 - μ)) (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact ne_of_lt (by linarith [hx.1] : d 0 - x < 0)
  have h1 : ContinuousOn (fun μ : ℝ => ℓ 1 ^ 2 / (d 1 - μ)) (Set.Icc a b) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro x hx
    exact ne_of_gt (by linarith [hx.2] : 0 < d 1 - x)
  have ht : ContinuousOn (infiniteSecularTail d ℓ) (Set.Icc a b) :=
    (infiniteSecularTail_continuousOn hd2 hsum (lt_trans hb h12)).mono Set.Icc_subset_Iic_self
  exact (h0.add h1).add ht

/-- The full secular function is strictly increasing on the first spectral gap. -/
theorem infiniteSecular_strictMonoOn (h12 : d 1 < d 2) (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) (hℓ0 : ℓ 0 ≠ 0) :
    StrictMonoOn (infiniteSecular d ℓ) (Set.Ioo (d 0) (d 1)) := by
  intro μ hμ μ' hμ' hlt
  have hc : (0 : ℝ) < ℓ 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓ0))
  have h0 : ℓ 0 ^ 2 / (d 0 - μ) < ℓ 0 ^ 2 / (d 0 - μ') := by
    have hx : 0 < μ - d 0 := by linarith [hμ.1]
    have h := div_lt_div_of_pos_left hc hx (by linarith : μ - d 0 < μ' - d 0)
    have e1 : d 0 - μ = -(μ - d 0) := by ring
    have e2 : d 0 - μ' = -(μ' - d 0) := by ring
    rw [e1, e2, div_neg, div_neg]
    exact neg_lt_neg h
  have h1 : ℓ 1 ^ 2 / (d 1 - μ) ≤ ℓ 1 ^ 2 / (d 1 - μ') :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hμ'.2]) (by linarith)
  have ht : infiniteSecularTail d ℓ μ ≤ infiniteSecularTail d ℓ μ' :=
    infiniteSecularTail_mono hd2 hsum hlt.le (by linarith [hμ'.2])
  unfold infiniteSecular
  exact add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le h0 h1) ht

/-- Below the first pole all secular terms are nonnegative and the second is positive:
no constrained eigenvalue exists at or below `d 0`. -/
theorem infiniteSecular_pos_of_le (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hℓ1 : ℓ 1 ≠ 0) {μ : ℝ} (hμ : μ ≤ d 0) :
    0 < infiniteSecular d ℓ μ := by
  have hl1sq : (0 : ℝ) < ℓ 1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓ1))
  have h0 : 0 ≤ ℓ 0 ^ 2 / (d 0 - μ) := div_nonneg (sq_nonneg _) (by linarith)
  have h1 : 0 < ℓ 1 ^ 2 / (d 1 - μ) := div_pos hl1sq (by linarith)
  have ht : 0 ≤ infiniteSecularTail d ℓ μ := infiniteSecularTail_nonneg hd2 (by linarith)
  unfold infiniteSecular
  linarith

/-- At the two-mode trial value the head cancels exactly, leaving the (nonnegative) tail. -/
theorem infiniteSecular_apply_twoModeRoot (h01 : d 0 < d 1) (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    infiniteSecular d ℓ (GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1))
      = infiniteSecularTail d ℓ
          (GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1)) := by
  unfold infiniteSecular
  rw [GaloisForLFunctions.twoModeSecular_eq_zero h01 hℓ0 hℓ1, zero_add]

/-- **Existence of the exact constrained ground root.**  The full secular function vanishes
somewhere in `(d_0, d_1)`, at or below the two-mode trial value. -/
theorem infiniteSecular_exists_root (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    ∃ μ ∈ Set.Ioo (d 0) (d 1), infiniteSecular d ℓ μ = 0 ∧
      μ ≤ GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1) := by
  set μ2 := GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1) with hμ2def
  obtain ⟨hμ2l, hμ2r⟩ := GaloisForLFunctions.twoModeSecularRoot_mem_Ioo h01 hℓ0 hℓ1
  have hFμ2 : 0 ≤ infiniteSecular d ℓ μ2 := by
    rw [infiniteSecular_apply_twoModeRoot h01 hℓ0 hℓ1]
    exact infiniteSecularTail_nonneg hd2 (by linarith)
  have hl0sq : (0 : ℝ) < ℓ 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓ0))
  have hl1sq : (0 : ℝ) < ℓ 1 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓ1))
  set T := ∑' j : ℕ, ℓ (j + 2) ^ 2 with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg fun j => sq_nonneg _
  set Ch := ℓ 1 ^ 2 / (d 1 - μ2) with hChdef
  set Ct := T / (d 2 - μ2) with hCtdef
  have hCh : 0 < Ch := div_pos hl1sq (by linarith)
  have hCt : 0 ≤ Ct := div_nonneg hT0 (by linarith)
  have hChCt : 0 < Ch + Ct := add_pos_of_pos_of_nonneg hCh hCt
  set δ := min (ℓ 0 ^ 2 / (Ch + Ct)) (μ2 - d 0) with hδdef
  have hδ0 : 0 < δ := lt_min (div_pos hl0sq hChCt) (by linarith)
  set μlow := d 0 + δ / 2 with hμlowdef
  have hlow1 : d 0 < μlow := by rw [hμlowdef]; linarith
  have hlow2 : μlow < μ2 := by
    have hδle : δ ≤ μ2 - d 0 := min_le_right _ _
    rw [hμlowdef]; linarith
  have hFlow : infiniteSecular d ℓ μlow ≤ 0 := by
    have hden : d 0 - μlow = -(δ / 2) := by rw [hμlowdef]; ring
    have hhead0 : ℓ 0 ^ 2 / (d 0 - μlow) = -(ℓ 0 ^ 2 / (δ / 2)) := by rw [hden, div_neg]
    have hδle : δ ≤ ℓ 0 ^ 2 / (Ch + Ct) := min_le_left _ _
    have hstep : Ch + Ct ≤ ℓ 0 ^ 2 / δ := by
      rw [le_div_iff₀ hδ0]
      have h := (le_div_iff₀ hChCt).mp hδle
      linarith [mul_comm (Ch + Ct) δ, h]
    have hmono : ℓ 0 ^ 2 / δ ≤ ℓ 0 ^ 2 / (δ / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (half_pos hδ0) (by linarith)
    have hhead1 : ℓ 1 ^ 2 / (d 1 - μlow) ≤ Ch := by
      rw [hChdef]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
    have htail : infiniteSecularTail d ℓ μlow ≤ Ct := by
      have h1 := infiniteSecularTail_le hd2 hsum (μ := μlow) (by linarith)
      have h2 : T / (d 2 - μlow) ≤ T / (d 2 - μ2) :=
        div_le_div_of_nonneg_left hT0 (by linarith) (by linarith)
      rw [hCtdef]
      exact le_trans h1 h2
    unfold infiniteSecular
    rw [hhead0]
    linarith
  have hcont : ContinuousOn (infiniteSecular d ℓ) (Set.Icc μlow μ2) :=
    infiniteSecular_continuousOn h12 hd2 hsum hlow1 hμ2r
  have hivt := intermediate_value_Icc hlow2.le hcont
  have h0mem : (0 : ℝ) ∈ Set.Icc (infiniteSecular d ℓ μlow) (infiniteSecular d ℓ μ2) :=
    ⟨hFlow, hFμ2⟩
  obtain ⟨μ, hμmem, hμval⟩ := hivt h0mem
  exact ⟨μ, ⟨lt_of_lt_of_le hlow1 hμmem.1, lt_of_le_of_lt hμmem.2 hμ2r⟩, hμval, hμmem.2⟩

/-- **Uniqueness of the constrained ground root** in the first spectral gap. -/
theorem infiniteSecular_root_unique (h12 : d 1 < d 2) (hd2 : ∀ j, d 2 ≤ d (j + 2))
    (hsum : Summable fun j => ℓ j ^ 2) (hℓ0 : ℓ 0 ≠ 0)
    {μ μ' : ℝ} (hμ : μ ∈ Set.Ioo (d 0) (d 1)) (hμ' : μ' ∈ Set.Ioo (d 0) (d 1))
    (h : infiniteSecular d ℓ μ = 0) (h' : infiniteSecular d ℓ μ' = 0) : μ = μ' :=
  (infiniteSecular_strictMonoOn h12 hd2 hsum hℓ0).injOn hμ hμ' (h.trans h'.symm)

end

open Classical in
/-- The exact constrained ground root: the unique zero of the full secular function in the
first spectral gap (junk value `0` when no root exists). -/
noncomputable def infiniteSecularRoot (d ℓ : ℕ → ℝ) : ℝ :=
  if h : ∃ μ ∈ Set.Ioo (d 0) (d 1), infiniteSecular d ℓ μ = 0 then h.choose else 0

variable {d ℓ : ℕ → ℝ}

/-- The defining properties of the exact ground root: it lies in the gap, kills the secular
function, and sits at or below the two-mode trial value. -/
theorem infiniteSecularRoot_spec (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    infiniteSecularRoot d ℓ ∈ Set.Ioo (d 0) (d 1) ∧
      infiniteSecular d ℓ (infiniteSecularRoot d ℓ) = 0 ∧
      infiniteSecularRoot d ℓ ≤
        GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1) := by
  obtain ⟨μ, hμmem, hμ0, hμle⟩ := infiniteSecular_exists_root h01 h12 hd2 hsum hℓ0 hℓ1
  have hex : ∃ μ ∈ Set.Ioo (d 0) (d 1), infiniteSecular d ℓ μ = 0 := ⟨μ, hμmem, hμ0⟩
  rw [infiniteSecularRoot, dif_pos hex]
  obtain ⟨hcmem, hc0⟩ := hex.choose_spec
  have heq : hex.choose = μ :=
    infiniteSecular_root_unique h12 hd2 hsum hℓ0 hcmem hμmem hc0 hμ0
  refine ⟨hcmem, hc0, ?_⟩
  rw [heq]
  exact hμle

/-- **The uniform infinite-tail secular estimate.**  The exact ground root differs from the
two-mode trial value by at most the total tail mass times `d_1²/(ℓ_0²(d_2 − d_1))`: the tail
pushes the root down, and the two-mode secular part moves at speed at least `ℓ_0²/d_1²`. -/
theorem infiniteSecularRoot_twoMode_gap (hd0 : 0 ≤ d 0) (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1) - infiniteSecularRoot d ℓ
      ≤ (∑' j : ℕ, ℓ (j + 2) ^ 2) * d 1 ^ 2 / (ℓ 0 ^ 2 * (d 2 - d 1)) := by
  obtain ⟨hrmem, hr0, hrle⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  set r := infiniteSecularRoot d ℓ with hrdef
  set μ2 := GaloisForLFunctions.twoModeSecularRoot (d 0) (d 1) (ℓ 0) (ℓ 1) with hμ2def
  obtain ⟨hμ2l, hμ2r⟩ := GaloisForLFunctions.twoModeSecularRoot_mem_Ioo h01 hℓ0 hℓ1
  set T := ∑' j : ℕ, ℓ (j + 2) ^ 2 with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg fun j => sq_nonneg _
  have hl0sq : (0 : ℝ) < ℓ 0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hℓ0))
  have htail_le : infiniteSecularTail d ℓ r ≤ T / (d 2 - d 1) := by
    have h1 := infiniteSecularTail_le hd2 hsum (μ := r) (by linarith [hrmem.2])
    have h2 : T / (d 2 - r) ≤ T / (d 2 - d 1) :=
      div_le_div_of_nonneg_left hT0 (by linarith) (by linarith [hrmem.2])
    exact le_trans h1 h2
  have hhead_r : ℓ 0 ^ 2 / (d 0 - r) + ℓ 1 ^ 2 / (d 1 - r) = -infiniteSecularTail d ℓ r := by
    have h := hr0
    unfold infiniteSecular at h
    linarith
  have hhead_μ2 : ℓ 0 ^ 2 / (d 0 - μ2) + ℓ 1 ^ 2 / (d 1 - μ2) = 0 :=
    GaloisForLFunctions.twoModeSecular_eq_zero h01 hℓ0 hℓ1
  have hB1 : ℓ 1 ^ 2 / (d 1 - r) ≤ ℓ 1 ^ 2 / (d 1 - μ2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hrle])
  have hrpos : 0 < r - d 0 := by linarith [hrmem.1]
  have hμ2pos : 0 < μ2 - d 0 := by linarith
  have hne_r : d 0 - r ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith [hrmem.1]
  have hne_μ2 : d 0 - μ2 ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have hB0eq : ℓ 0 ^ 2 / (d 0 - μ2) - ℓ 0 ^ 2 / (d 0 - r)
      = ℓ 0 ^ 2 * (μ2 - r) / ((μ2 - d 0) * (r - d 0)) := by
    rw [div_sub_div _ _ hne_μ2 hne_r]
    rw [show (d 0 - μ2) * (d 0 - r) = (μ2 - d 0) * (r - d 0) by ring]
    congr 1
    ring
  have hprod_pos : 0 < (μ2 - d 0) * (r - d 0) := mul_pos hμ2pos hrpos
  have hprod_le : (μ2 - d 0) * (r - d 0) ≤ d 1 ^ 2 := by
    have h1 : μ2 - d 0 ≤ d 1 := by linarith
    have h2 : r - d 0 ≤ d 1 := by linarith [hrmem.2]
    have h := mul_le_mul h1 h2 hrpos.le (by linarith : (0 : ℝ) ≤ d 1)
    rw [pow_two]
    exact h
  have hB0ge : ℓ 0 ^ 2 * (μ2 - r) / d 1 ^ 2
      ≤ ℓ 0 ^ 2 * (μ2 - r) / ((μ2 - d 0) * (r - d 0)) :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (by linarith [hrle]))
      hprod_pos hprod_le
  have hkey : ℓ 0 ^ 2 * (μ2 - r) / d 1 ^ 2 ≤ T / (d 2 - d 1) := by
    have hsum_eq : (ℓ 0 ^ 2 / (d 0 - μ2) - ℓ 0 ^ 2 / (d 0 - r))
        + (ℓ 1 ^ 2 / (d 1 - μ2) - ℓ 1 ^ 2 / (d 1 - r)) = infiniteSecularTail d ℓ r := by
      linarith [hhead_r, hhead_μ2]
    have hB1' : 0 ≤ ℓ 1 ^ 2 / (d 1 - μ2) - ℓ 1 ^ 2 / (d 1 - r) := by linarith [hB1]
    calc ℓ 0 ^ 2 * (μ2 - r) / d 1 ^ 2
        ≤ ℓ 0 ^ 2 * (μ2 - r) / ((μ2 - d 0) * (r - d 0)) := hB0ge
      _ = ℓ 0 ^ 2 / (d 0 - μ2) - ℓ 0 ^ 2 / (d 0 - r) := hB0eq.symm
      _ ≤ infiniteSecularTail d ℓ r := by linarith [hsum_eq, hB1']
      _ ≤ T / (d 2 - d 1) := htail_le
  have hd1sq : (0 : ℝ) < d 1 ^ 2 := pow_pos (by linarith) 2
  have h1 : ℓ 0 ^ 2 * (μ2 - r) ≤ T / (d 2 - d 1) * d 1 ^ 2 := (div_le_iff₀ hd1sq).mp hkey
  rw [le_div_iff₀ (mul_pos hl0sq (by linarith : (0 : ℝ) < d 2 - d 1))]
  have h2 : T / (d 2 - d 1) * d 1 ^ 2 * (d 2 - d 1) = T * d 1 ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_div_cancel_right₀ _ (by linarith : (0 : ℝ) < d 2 - d 1).ne']
  have h3 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ d 2 - d 1)
  rw [h2] at h3
  have h4 : (μ2 - r) * (ℓ 0 ^ 2 * (d 2 - d 1)) = ℓ 0 ^ 2 * (μ2 - r) * (d 2 - d 1) := by ring
  rw [h4]
  exact h3

/-- Every secular zero other than the ground root lies at or above the second pole: the
constrained spectrum has nothing else in `(−∞, d_1)`. -/
theorem infiniteSecular_other_root_ge (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ 2)
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0)
    {μ' : ℝ} (h' : infiniteSecular d ℓ μ' = 0)
    (hne : μ' ≠ infiniteSecularRoot d ℓ) : d 1 ≤ μ' := by
  rcases lt_trichotomy μ' (d 1) with hlt | heq | hgt
  · exfalso
    rcases lt_trichotomy μ' (d 0) with hlt0 | heq0 | hgt0
    · exact absurd h'
        (ne_of_gt (infiniteSecular_pos_of_le h01 h12 hd2 hℓ1 hlt0.le))
    · exact absurd h'
        (ne_of_gt (infiniteSecular_pos_of_le h01 h12 hd2 hℓ1 heq0.le))
    · obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
      exact hne (infiniteSecular_root_unique h12 hd2 hsum hℓ0 ⟨hgt0, hlt⟩ hrmem h' hr0)
  · exact heq.ge
  · exact hgt.le

/-! ## The aperture-family limit -/

/-- Normalized two-mode limit for an arbitrary aperture family: when the leakage ratio
`d_0/d_1` collapses and the two constraint coordinates converge, the two-mode trial value
normalized by `d_1` converges to the limiting weight. -/
theorem twoModeSecularRoot_ratio_tendsto_general {α : Type*} {l : Filter α}
    {d0 d1 ℓ0 ℓ1 : α → ℝ} {a0 a1 : ℝ}
    (hd : Tendsto (fun x => d0 x / d1 x) l (nhds 0))
    (hd1 : ∀ᶠ x in l, d1 x ≠ 0)
    (hl0 : Tendsto ℓ0 l (nhds a0)) (hl1 : Tendsto ℓ1 l (nhds a1))
    (ha : a0 ^ 2 + a1 ^ 2 ≠ 0) :
    Tendsto (fun x => GaloisForLFunctions.twoModeSecularRoot (d0 x) (d1 x) (ℓ0 x) (ℓ1 x) / d1 x)
      l (nhds (a0 ^ 2 / (a0 ^ 2 + a1 ^ 2))) := by
  have h0sq : Tendsto (fun x => ℓ0 x ^ 2) l (nhds (a0 ^ 2)) := hl0.pow 2
  have h1sq : Tendsto (fun x => ℓ1 x ^ 2) l (nhds (a1 ^ 2)) := hl1.pow 2
  have hnum : Tendsto (fun x => ℓ0 x ^ 2 + ℓ1 x ^ 2 * (d0 x / d1 x)) l (nhds (a0 ^ 2)) := by
    have h := h0sq.add (h1sq.mul hd)
    simpa using h
  have hden : Tendsto (fun x => ℓ0 x ^ 2 + ℓ1 x ^ 2) l (nhds (a0 ^ 2 + a1 ^ 2)) :=
    h0sq.add h1sq
  have hlim := hnum.div hden ha
  have hne : ∀ᶠ x in l, ℓ0 x ^ 2 + ℓ1 x ^ 2 ≠ 0 := hden.eventually_ne ha
  refine hlim.congr' ?_
  filter_upwards [hd1, hne] with x hx1 hxne
  exact (twoModeSecularRoot_div _ _ _ _ hx1 hxne).symm

/-- **The exact constrained ground root keeps the two-mode limit.**  Under the Fuchs-type
scale separations `d_0/d_1 → 0` and `λ·d_1/(d_2 − d_1) → 0`, the Bessel bound
`Σ_j ℓ_j(λ)² ≤ 2λ`, and the coordinate limits `ℓ_0 → a_0 ≠ 0`, `ℓ_1 → a_1 ≠ 0`, the exact
infinite-dimensional constrained ground root satisfies
`μ_0(λ)/d_1(λ) → a_0²/(a_0² + a_1²)`: the infinite tail is invisible in the limit. -/
theorem infiniteSecularRoot_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ} {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => infiniteSecularRoot (d lam) (ℓ lam) / d lam 1) atTop
      (nhds (a0 ^ 2 / (a0 ^ 2 + a1 ^ 2))) := by
  have ha0sq : (0 : ℝ) < a0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha0))
  have haS : a0 ^ 2 + a1 ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ha0sq (sq_nonneg _))
  have hℓ0ne : ∀ᶠ lam in atTop, ℓ lam 0 ≠ 0 := hl0.eventually_ne ha0
  have hℓ1ne : ∀ᶠ lam in atTop, ℓ lam 1 ≠ 0 := hl1.eventually_ne ha1
  have hℓ0big : ∀ᶠ lam in atTop, a0 ^ 2 / 2 ≤ ℓ lam 0 ^ 2 :=
    ((hl0.pow 2).eventually (eventually_gt_nhds (by linarith))).mono fun x hx => hx.le
  have hd1ne : ∀ᶠ lam in atTop, d lam 1 ≠ 0 := by
    filter_upwards [hstruct] with lam hst
    obtain ⟨⟨hd0, h01, _⟩, _⟩ := hst
    exact (lt_of_le_of_lt hd0 h01).ne'
  have hgap : Tendsto (fun lam =>
      (GaloisForLFunctions.twoModeSecularRoot (d lam 0) (d lam 1) (ℓ lam 0) (ℓ lam 1)
        - infiniteSecularRoot (d lam) (ℓ lam)) / d lam 1) atTop (nhds 0) := by
    have hbound : Tendsto (fun lam =>
        4 / a0 ^ 2 * (lam * d lam 1 / (d lam 2 - d lam 1))) atTop (nhds 0) := by
      simpa using htail.const_mul (4 / a0 ^ 2)
    refine squeeze_zero' ?_ ?_ hbound
    · filter_upwards [hstruct, hsum, hℓ0ne, hℓ1ne] with lam hst hsm h0 h1
      obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
      obtain ⟨hrmem, hr0, hrle⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsm h0 h1
      exact div_nonneg (by linarith [hrle]) (by linarith)
    · filter_upwards [hstruct, hsum, hbessel, hℓ0ne, hℓ1ne, hℓ0big,
        eventually_ge_atTop (0 : ℝ)] with lam hst hsm hbes h0 h1 hbig hlam0
      obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
      have hquant := infiniteSecularRoot_twoMode_gap hd0 h01 h12 hd2 hsm h0 h1
      have hd1pos : 0 < d lam 1 := lt_of_le_of_lt hd0 h01
      have hd21 : 0 < d lam 2 - d lam 1 := by linarith
      have hl0sqpos : 0 < ℓ lam 0 ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
      have hT2 : (∑' j : ℕ, ℓ lam (j + 2) ^ 2) ≤ 2 * lam := by
        have hfull := hsm.sum_add_tsum_nat_add 2
        have hfin : 0 ≤ ∑ i ∈ Finset.range 2, ℓ lam i ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        linarith [hbes]
      have hnum_le : (∑' j : ℕ, ℓ lam (j + 2) ^ 2) * d lam 1 ^ 2
          ≤ 2 * lam * d lam 1 ^ 2 := mul_le_mul_of_nonneg_right hT2 (sq_nonneg _)
      have hstep1 : GaloisForLFunctions.twoModeSecularRoot (d lam 0) (d lam 1)
            (ℓ lam 0) (ℓ lam 1) - infiniteSecularRoot (d lam) (ℓ lam)
          ≤ 2 * lam * d lam 1 ^ 2 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1)) :=
        le_trans hquant (div_le_div_of_le_of_pos hnum_le (mul_pos hl0sqpos hd21))
      have heq2 : 2 * lam * d lam 1 ^ 2 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1)) / d lam 1
          = 2 * lam * d lam 1 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1)) := by
        field_simp
      have hstep2 : (GaloisForLFunctions.twoModeSecularRoot (d lam 0) (d lam 1)
            (ℓ lam 0) (ℓ lam 1) - infiniteSecularRoot (d lam) (ℓ lam)) / d lam 1
          ≤ 2 * lam * d lam 1 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1)) := by
        have h := div_le_div_of_le_of_pos hstep1 hd1pos
        rwa [heq2] at h
      have heq3 : 4 / a0 ^ 2 * (lam * d lam 1 / (d lam 2 - d lam 1))
          = 2 * lam * d lam 1 / (a0 ^ 2 / 2 * (d lam 2 - d lam 1)) := by
        field_simp
        ring
      have hnum0 : 0 ≤ 2 * lam * d lam 1 :=
        mul_nonneg (mul_nonneg (by norm_num) hlam0) hd1pos.le
      have hstep4 : 2 * lam * d lam 1 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1))
          ≤ 2 * lam * d lam 1 / (a0 ^ 2 / 2 * (d lam 2 - d lam 1)) :=
        div_le_div_of_nonneg_left hnum0 (mul_pos (half_pos ha0sq) hd21)
          (mul_le_mul_of_nonneg_right hbig hd21.le)
      calc (GaloisForLFunctions.twoModeSecularRoot (d lam 0) (d lam 1)
            (ℓ lam 0) (ℓ lam 1) - infiniteSecularRoot (d lam) (ℓ lam)) / d lam 1
          ≤ 2 * lam * d lam 1 / (ℓ lam 0 ^ 2 * (d lam 2 - d lam 1)) := hstep2
        _ ≤ 2 * lam * d lam 1 / (a0 ^ 2 / 2 * (d lam 2 - d lam 1)) := hstep4
        _ = 4 / a0 ^ 2 * (lam * d lam 1 / (d lam 2 - d lam 1)) := heq3.symm
  have h2mode := twoModeSecularRoot_ratio_tendsto_general hratio hd1ne hl0 hl1 haS
  have hfinal := h2mode.sub hgap
  rw [sub_zero] at hfinal
  exact hfinal.congr fun lam => by ring

/-- The complementary constrained gap ratio: `(d_1 − μ_0)/d_1 → a_1²/(a_0² + a_1²)`. -/
theorem infiniteSecularRoot_gap_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ} {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1)) :
    Tendsto (fun lam => (d lam 1 - infiniteSecularRoot (d lam) (ℓ lam)) / d lam 1) atTop
      (nhds (a1 ^ 2 / (a0 ^ 2 + a1 ^ 2))) := by
  have ha0sq : (0 : ℝ) < a0 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ha0))
  have haS : a0 ^ 2 + a1 ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg ha0sq (sq_nonneg _))
  have h := infiniteSecularRoot_ratio_tendsto ha0 ha1 hstruct hsum hbessel hratio htail hl0 hl1
  have h1 : Tendsto (fun lam => 1 - infiniteSecularRoot (d lam) (ℓ lam) / d lam 1) atTop
      (nhds (1 - a0 ^ 2 / (a0 ^ 2 + a1 ^ 2))) := tendsto_const_nhds.sub h
  have hval : 1 - a0 ^ 2 / (a0 ^ 2 + a1 ^ 2) = a1 ^ 2 / (a0 ^ 2 + a1 ^ 2) := by
    rw [eq_div_iff haS, sub_mul, one_mul, div_mul_cancel₀ _ haS]
    ring
  rw [hval] at h1
  refine h1.congr' ?_
  filter_upwards [hstruct] with lam hst
  obtain ⟨⟨hd0, h01, _⟩, _⟩ := hst
  have hd1 : d lam 1 ≠ 0 := (lt_of_le_of_lt hd0 h01).ne'
  field_simp

/-- **Constrained spectral-gap transfer.**  For every `c` below the limiting gap fraction
`a_1²/(a_0² + a_1²)`, eventually every competing secular zero sits at least `c·d_1` above the
exact ground root. -/
theorem infiniteSecularRoot_spectralGap_eventually
    {d ℓ : ℝ → ℕ → ℝ} {a0 a1 : ℝ} (ha0 : a0 ≠ 0) (ha1 : a1 ≠ 0)
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds a0))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop (nhds a1))
    {c : ℝ} (hc : c < a1 ^ 2 / (a0 ^ 2 + a1 ^ 2)) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ, infiniteSecular (d lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (d lam) (ℓ lam) →
      c * d lam 1 ≤ μ' - infiniteSecularRoot (d lam) (ℓ lam) := by
  have hgapr := infiniteSecularRoot_gap_ratio_tendsto ha0 ha1 hstruct hsum hbessel
    hratio htail hl0 hl1
  have hd1pos : ∀ᶠ lam in atTop, 0 < d lam 1 := by
    filter_upwards [hstruct] with lam hst
    obtain ⟨⟨hd0, h01, _⟩, _⟩ := hst
    exact lt_of_le_of_lt hd0 h01
  have hev := eventually_const_mul_le_of_tendsto_div_atTop hgapr hd1pos hc
  filter_upwards [hev, hstruct, hsum, hl0.eventually_ne ha0, hl1.eventually_ne ha1]
    with lam h1 hst hsm h0 h1'
  obtain ⟨⟨hd0, h01, h12⟩, hd2⟩ := hst
  intro μ' hroot' hne'
  have hge := infiniteSecular_other_root_ge h01 h12 hd2 hsm h0 h1' hroot' hne'
  linarith

/-! ## The Connes–Consani–Moscovici instance -/

/-- The complement of the CCM ground weight: `a_1²/(a_0² + a_1²) = 3/11` for the seed values
`a_0 = 2^{1/4}`, `a_1 = √3·2^{−5/4}`. -/
theorem ccm_groundState_weight_complement_eq :
    (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 /
      (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2)
      = 3 / 11 := by
  have hS : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 ≠ 0 := by
    positivity
  have h8 := GaloisForLFunctions.ccm_groundState_weight_eq
  have hsum1 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 /
        (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2)
      + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 /
        (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2) = 1 := by
    rw [← add_div]
    exact div_self hS
  linarith [h8, hsum1]

/-- **The exact CCM ground ratio `8/11`.**  For any aperture family with the CCM coordinate
limits, the Fuchs-type scale separations, and the Bessel bound, the exact
infinite-dimensional constrained ground root obeys `μ_0(λ)/d_1(λ) → 8/11`. -/
theorem ccm_infiniteSecularRoot_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ}
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => infiniteSecularRoot (d lam) (ℓ lam) / d lam 1) atTop
      (nhds (8 / 11)) := by
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have h := infiniteSecularRoot_ratio_tendsto ha0 ha1 hstruct hsum hbessel hratio htail hl0 hl1
  rwa [GaloisForLFunctions.ccm_groundState_weight_eq] at h

/-- **The exact CCM constrained gap `3/11`.**  Same hypotheses; the complementary gap ratio
of the exact ground root converges to `3/11`. -/
theorem ccm_infiniteSecularRoot_gap_ratio_tendsto
    {d ℓ : ℝ → ℕ → ℝ}
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam => (d lam 1 - infiniteSecularRoot (d lam) (ℓ lam)) / d lam 1) atTop
      (nhds (3 / 11)) := by
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have h := infiniteSecularRoot_gap_ratio_tendsto ha0 ha1 hstruct hsum hbessel
    hratio htail hl0 hl1
  rwa [ccm_groundState_weight_complement_eq] at h

/-- **The exact CCM constrained spectral gap, quantified.**  For every `c < 3/11`, eventually
every competing secular zero lies at least `c·d_1(λ)` above the exact ground root. -/
theorem ccm_infiniteSecularRoot_spectralGap_eventually
    {d ℓ : ℝ → ℕ → ℝ}
    (hstruct : ∀ᶠ lam in atTop,
      (0 ≤ d lam 0 ∧ d lam 0 < d lam 1 ∧ d lam 1 < d lam 2) ∧
        ∀ j, d lam 2 ≤ d lam (j + 2))
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hratio : Tendsto (fun lam => d lam 0 / d lam 1) atTop (nhds 0))
    (htail : Tendsto (fun lam => lam * d lam 1 / (d lam 2 - d lam 1)) atTop (nhds 0))
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    {c : ℝ} (hc : c < 3 / 11) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ, infiniteSecular (d lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (d lam) (ℓ lam) →
      c * d lam 1 ≤ μ' - infiniteSecularRoot (d lam) (ℓ lam) := by
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  refine infiniteSecularRoot_spectralGap_eventually ha0 ha1 hstruct hsum hbessel
    hratio htail hl0 hl1 ?_
  rwa [ccm_groundState_weight_complement_eq]

end RHTower
