import GaloisForLFunctions.RHTower.Sieve.FibreStartSeparation

/-!
# The centred maximal window

The `μ²` and `μ²·1_{p∤·}` inputs compare each fibre sum with `c` times the *real* fibre length
`h√x/a`, whereas a window sum over `[y, y+m]` carries `m+1` integers.  The two differ by at most one:

    ⌈x/a⌉ ≤ x/a + 1,   ⌊(x+h√x)/a⌋ > (x+h√x)/a − 1   ⟹   |(m+1) − h√x/a| ≤ 1,

so the centred deviation of a fibre differs from the centred deviation of the corresponding window
by at most `c`, and squaring costs only the additive `2c²` per element of the block.  Since the block
has `O(√x)` elements that contributes `O(√x) = o(h²√x)`.

Together with the four-fold multiplicity bound this puts the two density inputs in the same
literature form as the Möbius one: a maximal centred mean square over *all* starting points.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- The largest squared centred window deviation of length at most `H` starting at `y`. -/
noncomputable def maxWindowDevSq (f : ℕ → ℝ) (c : ℝ) (H y : ℕ) : ℝ :=
  (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one
    (fun m => ((∑ b ∈ Finset.Icc y (y + m), f b) - c * ((m : ℝ) + 1)) ^ 2)

theorem maxWindowDevSq_nonneg (f : ℕ → ℝ) (c : ℝ) (H y : ℕ) : 0 ≤ maxWindowDevSq f c H y := by
  refine le_trans (sq_nonneg ((∑ b ∈ Finset.Icc y (y + 0), f b) - c * ((0 : ℕ) + 1))) ?_
  exact Finset.le_sup'
    (fun m => ((∑ b ∈ Finset.Icc y (y + m), f b) - c * ((m : ℝ) + 1)) ^ 2)
    (Finset.mem_range.2 (by omega))

theorem sq_dev_le_maxWindowDevSq {f : ℕ → ℝ} {c : ℝ} {H y m : ℕ} (hm : m ≤ H) :
    ((∑ b ∈ Finset.Icc y (y + m), f b) - c * ((m : ℝ) + 1)) ^ 2 ≤ maxWindowDevSq f c H y :=
  Finset.le_sup'
    (fun m => ((∑ b ∈ Finset.Icc y (y + m), f b) - c * ((m : ℝ) + 1)) ^ 2)
    (Finset.mem_range.2 (by omega))

/-- **The fibre is a window whose integer length matches the real one to within one.** -/
theorem exists_fibre_window {x h : ℝ} (hx : 4 ≤ x) (hh : 4 ≤ h) {a : ℕ}
    (ha : a ∈ outerBlock x h) :
    ∃ m : ℕ, m ≤ ⌈h⌉₊
      ∧ innerFibre x h a = Finset.Icc ⌈x / (a : ℝ)⌉₊ (⌈x / (a : ℝ)⌉₊ + m)
      ∧ |((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ)| ≤ 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hmem := ha
  rw [mem_outerBlock] at hmem
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := hmem
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
  set y : ℕ := ⌈x / (a : ℝ)⌉₊ with hy
  set e : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with he
  have hy1 : x / (a : ℝ) ≤ (y : ℝ) := Nat.le_ceil _
  have hy2 : (y : ℝ) < x / (a : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have he1 : (e : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) := Nat.floor_le (by positivity)
  have he2 : (x + h * Real.sqrt x) / (a : ℝ) < (e : ℝ) + 1 := Nat.lt_floor_add_one _
  have hgap : (x + h * Real.sqrt x) / (a : ℝ) - x / (a : ℝ) = h * Real.sqrt x / (a : ℝ) := by
    field_simp
    ring
  have hmasslow : h / 2 ≤ h * Real.sqrt x / (a : ℝ) := by
    rw [le_div_iff₀ ha0]
    nlinarith
  have hmassup : h * Real.sqrt x / (a : ℝ) ≤ h := by
    rw [div_le_iff₀ ha0]
    nlinarith
  have hey : (y : ℝ) ≤ (e : ℝ) := by linarith
  have heyn : y ≤ e := by exact_mod_cast hey
  refine ⟨e - y, ?_, ?_, ?_⟩
  · have hcast : ((e - y : ℕ) : ℝ) = (e : ℝ) - (y : ℝ) := by
      push_cast [Nat.cast_sub heyn]
      ring
    have hceilh : h ≤ ((⌈h⌉₊ : ℕ) : ℝ) := Nat.le_ceil h
    have : ((e - y : ℕ) : ℝ) ≤ ((⌈h⌉₊ : ℕ) : ℝ) := by
      rw [hcast]
      linarith
    exact_mod_cast this
  · rw [innerFibre_eq hx (by linarith) ha, ← he, ← hy]
    congr 1
    omega
  · have hcast : ((e - y : ℕ) : ℝ) = (e : ℝ) - (y : ℝ) := by
      push_cast [Nat.cast_sub heyn]
      ring
    rw [hcast, abs_le]
    constructor <;> linarith

/-- **The centred fibre mean square is controlled by the centred maximal-window mean square.** -/
theorem sum_fibre_dev_sq_le_maximal {x h : ℝ} (hx : 4 ≤ x) (hh : 4 ≤ h) (f : ℕ → ℝ) {c : ℝ}
    (hc : 0 ≤ c) :
    ∑ a ∈ outerBlock x h,
        ((∑ b ∈ innerFibre x h a, f b) - c * (h * Real.sqrt x / (a : ℝ))) ^ 2
      ≤ 8 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊, maxWindowDevSq f c ⌈h⌉₊ y
        + 2 * c ^ 2 * (Real.sqrt x + 1) := by
  classical
  have hterm : ∀ a ∈ outerBlock x h,
      ((∑ b ∈ innerFibre x h a, f b) - c * (h * Real.sqrt x / (a : ℝ))) ^ 2
        ≤ 2 * maxWindowDevSq f c ⌈h⌉₊ ⌈x / (a : ℝ)⌉₊ + 2 * c ^ 2 := by
    intro a ha
    obtain ⟨m, hmH, hfib, hdiff⟩ := exists_fibre_window hx hh ha
    set y : ℕ := ⌈x / (a : ℝ)⌉₊ with hy
    set S : ℝ := ∑ b ∈ Finset.Icc y (y + m), f b with hS
    have hval : (∑ b ∈ innerFibre x h a, f b) - c * (h * Real.sqrt x / (a : ℝ))
        = (S - c * ((m : ℝ) + 1)) + c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ)) := by
      rw [hfib, ← hS]
      ring
    have hbound : |c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ))| ≤ c := by
      rw [abs_mul, abs_of_nonneg hc]
      calc c * |((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ)| ≤ c * 1 :=
            mul_le_mul_of_nonneg_left hdiff hc
        _ = c := by ring
    have hsq : ((S - c * ((m : ℝ) + 1)) + c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ))) ^ 2
        ≤ 2 * (S - c * ((m : ℝ) + 1)) ^ 2
          + 2 * (c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ))) ^ 2 := by
      nlinarith [sq_nonneg ((S - c * ((m : ℝ) + 1))
        - c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ)))]
    have hsq2 : (c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ))) ^ 2 ≤ c ^ 2 := by
      have habs := abs_nonneg (c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ)))
      nlinarith [sq_abs (c * (((m : ℝ) + 1) - h * Real.sqrt x / (a : ℝ))), hbound, hc]
    have hmax : (S - c * ((m : ℝ) + 1)) ^ 2 ≤ maxWindowDevSq f c ⌈h⌉₊ y := by
      rw [hS]
      exact sq_dev_le_maxWindowDevSq hmH
    rw [hval]
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  have htrans : ∑ a ∈ outerBlock x h, maxWindowDevSq f c ⌈h⌉₊ ⌈x / (a : ℝ)⌉₊
      ≤ 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊, maxWindowDevSq f c ⌈h⌉₊ y :=
    sum_block_comp_start_le hx (fun y => maxWindowDevSq_nonneg f c ⌈h⌉₊ y)
  have hcard : ((outerBlock x h).card : ℝ) ≤ Real.sqrt x + 1 :=
    card_outerBlock_le hx (by linarith)
  have hc2 : (0 : ℝ) ≤ 2 * c ^ 2 := by positivity
  nlinarith [htrans, hcard, hc2]

/-- **The centred maximal-window mean square at a moving pair of parameters.** -/
def MaximalWindowDevMeanSquareAt (f : ℕ → ℝ) (c : ℝ) (X hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x => (∑ y ∈ Finset.Icc ⌈Real.sqrt (X x) / 2⌉₊ ⌈Real.sqrt (X x)⌉₊,
      maxWindowDevSq f c ⌈hh x⌉₊ y) / (hh x ^ 2 * Real.sqrt (X x))) atTop (𝓝 0)

/-- **The centred fibre mean square follows from the centred maximal-window mean square.** -/
theorem averagedMeanSquareDensityAt_of_maximal {f : ℕ → ℝ} {c : ℝ} {X hh : ℝ → ℝ}
    (hc : 0 ≤ c) (hXtop : Tendsto X atTop atTop) (hgrow : Tendsto hh atTop atTop)
    (hmax : MaximalWindowDevMeanSquareAt f c X hh) :
    AveragedMeanSquareDensityAt f c X hh := by
  have hXsqrt : Tendsto (fun x => Real.sqrt (X x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hXtop
  have h8 : Tendsto (fun x => 8 * ((∑ y ∈ Finset.Icc ⌈Real.sqrt (X x) / 2⌉₊ ⌈Real.sqrt (X x)⌉₊,
      maxWindowDevSq f c ⌈hh x⌉₊ y) / (hh x ^ 2 * Real.sqrt (X x)))) atTop (𝓝 0) := by
    have := hmax.const_mul (8 : ℝ)
    rwa [mul_zero] at this
  have hrest : Tendsto (fun x => 2 * c ^ 2 * (Real.sqrt (X x) + 1)
      / (hh x ^ 2 * Real.sqrt (X x))) atTop (𝓝 0) := by
    have hnum : Tendsto (fun x : ℝ => 2 * c ^ 2 * (1 + 1 / Real.sqrt (X x)))
        atTop (𝓝 (2 * c ^ 2)) := by
      have hinv : Tendsto (fun x : ℝ => 1 / Real.sqrt (X x)) atTop (𝓝 0) :=
        tendsto_one_div_atTop.comp hXsqrt
      have hbase := tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℝ)) |>.add hinv
      rw [add_zero] at hbase
      have := hbase.const_mul (2 * c ^ 2)
      rwa [mul_one] at this
    have hden : Tendsto (fun x : ℝ => hh x ^ 2) atTop atTop := by
      have := hgrow.atTop_mul_atTop₀ hgrow
      refine this.congr fun x => ?_
      ring
    have := hnum.div_atTop hden
    refine this.congr' ?_
    filter_upwards [hXsqrt.eventually_gt_atTop 0, hgrow.eventually_gt_atTop 0] with x hs hhx
    field_simp
  have hsum := h8.add hrest
  rw [add_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hXtop.eventually_ge_atTop 4, hgrow.eventually_ge_atTop 4,
    hXsqrt.eventually_gt_atTop 0, hgrow.eventually_gt_atTop 0] with x hx hhx hs hhpos
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt (X x) := by positivity
  have hbridge := sum_fibre_dev_sq_le_maximal hx hhx f hc
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine le_trans (div_le_div_of_nonneg_right hbridge hden.le) (le_of_eq ?_)
  rw [add_div, mul_div_assoc]

end RHTower.Sieve
