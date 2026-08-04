import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare

/-!
# The fibre starting points are a bounded sample

The fibre above `a` starts at `⌈x/a⌉`.  As `a` runs over the block `(√x, 2√x]` the real numbers
`x/a` run over `[√x/2, √x)` with

    x/a − x/a'  =  x(a'−a)/(aa')  ≥  x/(4x)  =  1/4      (a < a' in the block),

so the starting points are `1/4`-separated: the map `a ↦ ⌈4x/a⌉` is *injective* on the block, and
since `⌈x/a⌉ = k` confines `⌈4x/a⌉` to the four values `4k−3, …, 4k`, at most four elements of the
block share a starting point.

Consequently any nonnegative quantity attached to the starting points can be summed over the block
at a cost of a factor `4`:

    ∑_{a ∈ block} G(⌈x/a⌉)  ≤  4 ∑_{⌈√x/2⌉ ≤ y ≤ ⌈√x⌉} G(y).

That is the transfer a short-interval estimate over *all* starting points needs in order to bound
the fibre family: the family is neither sparse nor clustered.
-/

namespace RHTower.Sieve

open Finset

/-- The quadrupled reciprocal is strictly monotone across the block. -/
theorem ceil_four_mul_lt {x h : ℝ} (hx : 4 ≤ x) {a a' : ℕ}
    (ha : a ∈ outerBlock x h) (ha' : a' ∈ outerBlock x h) (hlt : a < a') :
    ⌈4 * x / (a' : ℝ)⌉₊ < ⌈4 * x / (a : ℝ)⌉₊ := by
  rw [mem_outerBlock] at ha ha'
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  obtain ⟨⟨hone', -⟩, hlow', hhigh'⟩ := ha'
  have hx0 : (0 : ℝ) < x := by linarith
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
  have ha0' : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast hone'
  have hstep : (a : ℝ) + 1 ≤ (a' : ℝ) := by exact_mod_cast hlt
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hgap : 4 * x / (a' : ℝ) + 1 ≤ 4 * x / (a : ℝ) := by
    rw [div_add' _ _ _ (ne_of_gt ha0'), div_le_div_iff₀ ha0' ha0]
    nlinarith [hhigh, hhigh', hstep, hsq, Real.sqrt_nonneg x]
  have hupper : ((⌈4 * x / (a' : ℝ)⌉₊ : ℝ)) < 4 * x / (a' : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hlower : 4 * x / (a : ℝ) ≤ ((⌈4 * x / (a : ℝ)⌉₊ : ℝ)) := Nat.le_ceil _
  have : ((⌈4 * x / (a' : ℝ)⌉₊ : ℝ)) < ((⌈4 * x / (a : ℝ)⌉₊ : ℝ)) := by linarith
  exact_mod_cast this

/-- The quadrupled reciprocal is injective on the block. -/
theorem ceil_four_mul_injOn {x h : ℝ} (hx : 4 ≤ x) :
    Set.InjOn (fun a : ℕ => ⌈4 * x / (a : ℝ)⌉₊) (outerBlock x h) := by
  intro a ha a' ha' heq
  have ha0 : a ∈ outerBlock x h := Finset.mem_coe.1 ha
  have ha0' : a' ∈ outerBlock x h := Finset.mem_coe.1 ha'
  by_contra hne
  rcases Nat.lt_or_ge a a' with hlt | hge
  · exact absurd heq (ne_of_gt (ceil_four_mul_lt hx ha0 ha0' hlt))
  · have hlt' : a' < a := by omega
    exact absurd heq (ne_of_lt (ceil_four_mul_lt hx ha0' ha0 hlt'))

/-- The starting point is at least one. -/
theorem one_le_fibreStart {x h : ℝ} (hx : 4 ≤ x) {a : ℕ} (ha : a ∈ outerBlock x h) :
    1 ≤ ⌈x / (a : ℝ)⌉₊ := by
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, -, hhigh⟩ := ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
  have hx0 : (0 : ℝ) < x := by linarith
  refine Nat.one_le_ceil_iff.2 ?_
  positivity

/-- **At most four elements of the block share a starting point.** -/
theorem card_fibreStart_preimage_le {x h : ℝ} (hx : 4 ≤ x) (k : ℕ) :
    ((outerBlock x h).filter (fun a : ℕ => ⌈x / (a : ℝ)⌉₊ = k)).card ≤ 4 := by
  classical
  set A : Finset ℕ := (outerBlock x h).filter (fun a : ℕ => ⌈x / (a : ℝ)⌉₊ = k) with hA
  have hsub : A ⊆ outerBlock x h := Finset.filter_subset _ _
  have hinj : Set.InjOn (fun a : ℕ => ⌈4 * x / (a : ℝ)⌉₊) A := by
    intro a ha a' ha' heq
    exact ceil_four_mul_injOn hx (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 ha)))
      (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 ha'))) heq
  have himage : A.image (fun a : ℕ => ⌈4 * x / (a : ℝ)⌉₊) ⊆ Finset.Icc (4 * k - 3) (4 * k) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, haA, rfl⟩ := hy
    have haB : a ∈ outerBlock x h := hsub haA
    have hk : ⌈x / (a : ℝ)⌉₊ = k := by
      rw [hA, Finset.mem_filter] at haA
      exact haA.2
    have hk1 : 1 ≤ k := by
      rw [← hk]
      exact one_le_fibreStart hx haB
    rw [mem_outerBlock] at haB
    obtain ⟨⟨hone, -⟩, -, -⟩ := haB
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
    have hx0 : (0 : ℝ) < x := by linarith
    have hup : x / (a : ℝ) ≤ (k : ℝ) := by
      rw [← hk]
      exact Nat.le_ceil _
    have hdown : ((k - 1 : ℕ) : ℝ) < x / (a : ℝ) := by
      refine Nat.lt_ceil.1 ?_
      rw [hk]
      omega
    rw [Finset.mem_Icc]
    constructor
    · have hstep : ((4 * k - 4 : ℕ) : ℝ) < 4 * x / (a : ℝ) := by
        have hcast : ((4 * k - 4 : ℕ) : ℝ) = 4 * ((k - 1 : ℕ) : ℝ) := by
          have h1 : 1 ≤ k := hk1
          push_cast [Nat.cast_sub h1, Nat.cast_sub (by omega : 4 ≤ 4 * k)]
          ring
        rw [hcast]
        have : 4 * x / (a : ℝ) = 4 * (x / (a : ℝ)) := by ring
        rw [this]
        linarith
      have hnat : 4 * k - 4 < ⌈4 * x / (a : ℝ)⌉₊ := Nat.lt_ceil.2 hstep
      omega
    · refine Nat.ceil_le.2 ?_
      have : 4 * x / (a : ℝ) = 4 * (x / (a : ℝ)) := by ring
      rw [this]
      push_cast
      linarith
  have hcard : A.card = (A.image (fun a : ℕ => ⌈4 * x / (a : ℝ)⌉₊)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [hcard]
  refine le_trans (Finset.card_le_card himage) ?_
  rw [Nat.card_Icc]
  omega

/-- The starting points lie in a fixed range. -/
theorem fibreStart_mem_Icc {x h : ℝ} (hx : 4 ≤ x) {a : ℕ} (ha : a ∈ outerBlock x h) :
    ⌈x / (a : ℝ)⌉₊ ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
  rw [Finset.mem_Icc]
  constructor
  · refine Nat.ceil_le_ceil ?_
    rw [le_div_iff₀ ha0]
    nlinarith
  · refine Nat.ceil_le_ceil ?_
    rw [div_le_iff₀ ha0]
    nlinarith

/-- **The transfer.**  A nonnegative quantity attached to the starting points can be summed over the
block at the cost of a factor `4`. -/
theorem sum_block_comp_start_le {x h : ℝ} (hx : 4 ≤ x) {G : ℕ → ℝ} (hG : ∀ y, 0 ≤ G y) :
    ∑ a ∈ outerBlock x h, G ⌈x / (a : ℝ)⌉₊
      ≤ 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊, G y := by
  classical
  have hmaps : ∀ a ∈ outerBlock x h,
      ⌈x / (a : ℝ)⌉₊ ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊ :=
    fun a ha => fibreStart_mem_Icc hx ha
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun a => G ⌈x / (a : ℝ)⌉₊)
  rw [← hfib, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro y _
  have hval : ∑ a ∈ (outerBlock x h).filter (fun a : ℕ => ⌈x / (a : ℝ)⌉₊ = y),
      G ⌈x / (a : ℝ)⌉₊
      = (((outerBlock x h).filter (fun a : ℕ => ⌈x / (a : ℝ)⌉₊ = y)).card : ℝ) * G y := by
    rw [Finset.sum_congr rfl (fun a ha => by
      rw [(Finset.mem_filter.1 ha).2] : ∀ a ∈ (outerBlock x h).filter
        (fun a : ℕ => ⌈x / (a : ℝ)⌉₊ = y), G ⌈x / (a : ℝ)⌉₊ = G y),
      Finset.sum_const, nsmul_eq_mul]
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (hG y)
  have := card_fibreStart_preimage_le (x := x) (h := h) hx y
  exact_mod_cast this

/-- The largest squared window sum of length at most `H` starting at `y`. -/
noncomputable def maxWindowSq (f : ℕ → ℝ) (H y : ℕ) : ℝ :=
  (Finset.range (H + 1)).sup' Finset.nonempty_range_add_one
    (fun m => (∑ b ∈ Finset.Icc y (y + m), f b) ^ 2)

theorem maxWindowSq_nonneg (f : ℕ → ℝ) (H y : ℕ) : 0 ≤ maxWindowSq f H y := by
  refine le_trans (sq_nonneg (∑ b ∈ Finset.Icc y (y + 0), f b)) ?_
  exact Finset.le_sup' (fun m => (∑ b ∈ Finset.Icc y (y + m), f b) ^ 2)
    (Finset.mem_range.2 (by omega))

theorem sq_sum_le_maxWindowSq {f : ℕ → ℝ} {H y m : ℕ} (hm : m ≤ H) :
    (∑ b ∈ Finset.Icc y (y + m), f b) ^ 2 ≤ maxWindowSq f H y :=
  Finset.le_sup' (fun m => (∑ b ∈ Finset.Icc y (y + m), f b) ^ 2)
    (Finset.mem_range.2 (by omega))

/-- **The fibre mean square is controlled by the maximal-window mean square.**  Every fibre is a
window of length at most `⌈h⌉` starting at `⌈x/a⌉`, and at most four fibres share a start. -/
theorem sum_fibre_sq_le_maximal {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) (f : ℕ → ℝ) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ 4 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊, maxWindowSq f ⌈h⌉₊ y := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hterm : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, f b) ^ 2 ≤ maxWindowSq f ⌈h⌉₊ ⌈x / (a : ℝ)⌉₊ := by
    intro a ha
    have hmem := ha
    rw [mem_outerBlock] at hmem
    obtain ⟨⟨hone, -⟩, hlow, -⟩ := hmem
    have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hone
    rw [innerFibre_eq hx hh ha]
    set y : ℕ := ⌈x / (a : ℝ)⌉₊ with hy
    set e : ℕ := ⌊(x + h * Real.sqrt x) / (a : ℝ)⌋₊ with he
    rcases Nat.lt_or_ge e y with hlt | hge
    · have hempty : Finset.Icc y e = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty]
      simpa using maxWindowSq_nonneg f ⌈h⌉₊ y
    · have hlen : e - y ≤ ⌈h⌉₊ := by
        have hfl : ((e : ℕ) : ℝ) ≤ (x + h * Real.sqrt x) / (a : ℝ) :=
          Nat.floor_le (by positivity)
        have hce : x / (a : ℝ) ≤ ((y : ℕ) : ℝ) := Nat.le_ceil _
        have hgap : (x + h * Real.sqrt x) / (a : ℝ) - x / (a : ℝ) = h * Real.sqrt x / (a : ℝ) := by
          field_simp
          ring
        have hmass : h * Real.sqrt x / (a : ℝ) ≤ h := by
          rw [div_le_iff₀ ha0]
          nlinarith [Real.sqrt_nonneg x]
        have hceilh : h ≤ ((⌈h⌉₊ : ℕ) : ℝ) := Nat.le_ceil h
        have hreal : ((e : ℕ) : ℝ) ≤ ((y : ℕ) : ℝ) + ((⌈h⌉₊ : ℕ) : ℝ) := by linarith
        have hnat : e ≤ y + ⌈h⌉₊ := by exact_mod_cast hreal
        omega
      have hey : y + (e - y) = e := by omega
      rw [← hey]
      exact sq_sum_le_maxWindowSq hlen
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact sum_block_comp_start_le hx (fun y => maxWindowSq_nonneg f ⌈h⌉₊ y)

/-- **The maximal-window mean square over all starting points.**  This is the shape in which
short-interval estimates for a multiplicative function are proved. -/
def MaximalWindowMeanSquare (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Filter.Tendsto (fun x => (∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowSq f ⌈hh x⌉₊ y) / (hh x ^ 2 * Real.sqrt x)) Filter.atTop (nhds 0)

/-- **The fibre mean square follows from the maximal-window mean square.** -/
theorem averagedMeanSquare_of_maximal {f : ℕ → ℝ} {hh : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hmax : MaximalWindowMeanSquare f hh) : AveragedMeanSquare f hh := by
  have h4 : Filter.Tendsto (fun x => 4 * ((∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
      maxWindowSq f ⌈hh x⌉₊ y) / (hh x ^ 2 * Real.sqrt x))) Filter.atTop (nhds 0) := by
    have := hmax.const_mul (4 : ℝ)
    rwa [mul_zero] at this
  refine squeeze_zero_norm' ?_ h4
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_gt_atTop 0] with x hx hhx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt x := by positivity
  have hbridge := sum_fibre_sq_le_maximal hx hhx.le f
  have hQ0 : (0 : ℝ) ≤ ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2 := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [mul_div_assoc'] at *
  exact div_le_div_of_nonneg_right hbridge hden.le

end RHTower.Sieve
