import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupIsTransitiveOnTheZeros

/-!
# The number of a zero in the order of the real line is its strip at a real saddle

The zeros of `H_{1/8}` are real, simple and nonzero. Number them in the order of the real line:
`zeroIndex x` is the number of zeros in `(0, x)` for `x > 0`, and `-1 -` the number of zeros in
`(x, 0)` for `x < 0`. The numbering is injective and `zeroIndex (-x) = -1 - zeroIndex x`.

At a real saddle `σ` with the strip facts for a window (`StripWindow`), the transport along the
real times from `1/8` to `τ(σ)` carries the zero number `k` to the zero of the strip
`πk < Re(σz) < π(k + 1)`, for the strips of the window:

* `StripWindow.zeroIndex_eq_of_landsIn` — a zero that lands in the strip `k` has number `k`;
* `StripWindow.landsIn_zeroIndex` — a zero with a number of the window lands in its strip.

Proof. The transport keeps sign and order and is a bijection of the fibres; each strip of the
window holds one zero and every zero of the window lies in a strip. So the positive zeros below a
zero that lands in the strip `k` correspond to the strips `0, …, k - 1`.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

theorem eighth_re_pos : 0 < ((1 / 8 : ℝ) : ℂ).re := by
  rw [Complex.ofReal_re]
  norm_num

theorem eighth_not_mem_branchTimes : ((1 / 8 : ℝ) : ℂ) ∉ branchTimes :=
  ofReal_not_mem_branchTimes_of_eighth_le le_rfl

/-! ## The numbering -/

/-- The positive zeros of `H_{1/8}` below `x`. -/
def zerosBelow (x : ℂ) : Set ℂ :=
  {y | complexHeat ((1 / 8 : ℝ) : ℂ) y = 0 ∧ 0 < y.re ∧ y.re < x.re}

theorem finite_zerosBelow (x : ℂ) : (zerosBelow x).Finite := by
  refine (finite_zeros_closedBall ((1 / 8 : ℝ) : ℂ) |x.re|).subset fun y hy => ⟨?_, hy.1⟩
  rw [mem_closedBall_zero_iff, ← Complex.abs_re_eq_norm.mpr (im_eq_zero_of_zero le_rfl hy.1),
    abs_of_pos hy.2.1]
  exact hy.2.2.le.trans (le_abs_self _)

/-- The number of positive zeros of `H_{1/8}` below `x`. -/
def posIndex (x : ℂ) : ℕ := (zerosBelow x).ncard

/-- The number of a zero of `H_{1/8}` in the order of the real line: `0, 1, 2, …` for the positive
zeros and `-1, -2, …` for the negative zeros. -/
def zeroIndex (x : ℂ) : ℤ := if 0 < x.re then (posIndex x : ℤ) else -1 - posIndex (-x)

theorem zeroIndex_of_pos {x : ℂ} (h : 0 < x.re) : zeroIndex x = posIndex x := if_pos h

theorem zeroIndex_of_not_pos {x : ℂ} (h : ¬0 < x.re) : zeroIndex x = -1 - posIndex (-x) :=
  if_neg h

theorem re_ne_zero_of_zero_eighth {x : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0) :
    x.re ≠ 0 := fun h =>
  ne_zero_of_zero_ofReal hx (Complex.ext h (im_eq_zero_of_zero le_rfl hx))

/-- The partner `-x` has the number `-1 - k`. -/
theorem zeroIndex_neg {x : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0) :
    zeroIndex (-x) = -1 - zeroIndex x := by
  rcases lt_or_gt_of_ne (re_ne_zero_of_zero_eighth hx) with h | h
  · rw [zeroIndex_of_pos (by rw [Complex.neg_re]; linarith),
      zeroIndex_of_not_pos (not_lt.mpr h.le)]
    ring
  · rw [zeroIndex_of_not_pos (by rw [Complex.neg_re]; exact not_lt.mpr (by linarith)), neg_neg,
      zeroIndex_of_pos h]

theorem posIndex_lt_of_lt {x y : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (hpos : 0 < x.re) (hxy : x.re < y.re) : posIndex x < posIndex y := by
  refine Set.ncard_lt_ncard ⟨fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hxy⟩, fun hsub => ?_⟩
    (finite_zerosBelow y)
  exact lt_irrefl _ (hsub ⟨hx, hpos, hxy⟩).2.2

theorem eq_of_posIndex_eq {x y : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (hy : complexHeat ((1 / 8 : ℝ) : ℂ) y = 0) (hxp : 0 < x.re) (hyp : 0 < y.re)
    (h : posIndex x = posIndex y) : x = y := by
  have hre : x.re = y.re := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h' | h'
    · exact (posIndex_lt_of_lt hx hxp h').ne h
    · exact (posIndex_lt_of_lt hy hyp h').ne h.symm
  exact Complex.ext hre (by rw [im_eq_zero_of_zero le_rfl hx, im_eq_zero_of_zero le_rfl hy])

/-- **The numbering is injective.** -/
theorem eq_of_zeroIndex_eq {x y : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (hy : complexHeat ((1 / 8 : ℝ) : ℂ) y = 0) (h : zeroIndex x = zeroIndex y) : x = y := by
  have hneg : ∀ {z : ℂ}, complexHeat ((1 / 8 : ℝ) : ℂ) z = 0 → ¬0 < z.re → 0 < (-z).re :=
    fun {z} hz hn => by
      rw [Complex.neg_re]
      have := lt_of_le_of_ne (not_lt.mp hn) (re_ne_zero_of_zero_eighth hz)
      linarith
  by_cases hxp : 0 < x.re <;> by_cases hyp : 0 < y.re
  · rw [zeroIndex_of_pos hxp, zeroIndex_of_pos hyp] at h
    exact eq_of_posIndex_eq hx hy hxp hyp (by exact_mod_cast h)
  · rw [zeroIndex_of_pos hxp, zeroIndex_of_not_pos hyp] at h
    omega
  · rw [zeroIndex_of_not_pos hxp, zeroIndex_of_pos hyp] at h
    omega
  · rw [zeroIndex_of_not_pos hxp, zeroIndex_of_not_pos hyp] at h
    have h' : posIndex (-x) = posIndex (-y) := by omega
    exact neg_injective (eq_of_posIndex_eq (by rw [complexHeat_neg]; exact hx)
      (by rw [complexHeat_neg]; exact hy) (hneg hx hxp) (hneg hy hyp) h')

/-! ## The strips of a window at a real saddle -/

/-- The strips of the window `R` at the real saddle `σ`: the zeros of the window stay off the
lines between the strips, each strip holds at most one zero, and each strip holds a zero. -/
structure StripWindow (R σ : ℝ) : Prop where
  one_le : 1 ≤ σ
  facts : StripFacts R (σ : ℂ)
  exists_zero : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R →
    ∃ z : ℂ, complexHeat (saddleTime (σ : ℂ)) z = 0 ∧ (σ : ℂ) * z ∈ cosStrip θ

/-- Every real saddle far out has the strips of the window. -/
theorem exists_stripWindow (R : ℝ) : ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → StripWindow R σ := by
  obtain ⟨σ₁, h50, hdom⟩ := exists_real_dominance
  obtain ⟨σ₂, hfacts⟩ := exists_stripFacts R
  obtain ⟨σ₃, hzero⟩ := exists_zero_mem_cosStrip R
  refine ⟨max σ₁ (max σ₂ σ₃), fun σ hσ => ?_⟩
  have hσ₁ : σ₁ ≤ σ := (le_max_left _ _).trans hσ
  have hσ₂ : σ₂ ≤ σ := ((le_max_left _ _).trans (le_max_right _ _)).trans hσ
  have hσ₃ : σ₃ ≤ σ := ((le_max_right _ _).trans (le_max_right _ _)).trans hσ
  have hW := wideRegion_ofReal (h50.trans hσ₁)
  have hd := hdom σ hσ₁
  have hre : (σ : ℂ).re = σ := Complex.ofReal_re σ
  exact ⟨by linarith, hfacts _ hW (by rw [hre]; exact hσ₂) (cosineSide_of_dominance hd),
    fun θ hθ hθR => hzero _ hW (by rw [hre]; exact hσ₃) hd θ hθ hθR⟩

/-- The zero `x` of `H_{1/8}` goes, along the real times, to a zero of the strip `k` at the real
saddle `σ`. -/
def LandsIn (σ : ℝ) (x : ℂ) (k : ℤ) : Prop :=
  ∃ W : ℝ → ℂ, IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W ∧ W 0 = x ∧
    (σ : ℂ) * W 1 ∈ cosStrip (π * k)

section Lifts

variable {σ : ℝ} {W : ℝ → ℂ}

theorem IsZeroLift.zero_start (hW : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W) :
    complexHeat ((1 / 8 : ℝ) : ℂ) (W 0) = 0 := by
  have h := hW.zero 0 ⟨le_rfl, zero_le_one⟩
  rwa [timeSeg_zero] at h

theorem IsZeroLift.zero_end (hW : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W) :
    complexHeat (saddleTime (σ : ℂ)) (W 1) = 0 := by
  have h := hW.zero 1 ⟨zero_le_one, le_rfl⟩
  rwa [timeSeg_one, ← saddleTime_ofReal] at h

end Lifts

theorem LandsIn.zero {σ : ℝ} {x : ℂ} {k : ℤ} (h : LandsIn σ x k) :
    complexHeat ((1 / 8 : ℝ) : ℂ) x = 0 := by
  obtain ⟨W, hW, rfl, -⟩ := h
  exact hW.zero_start

/-- The partner `-x` lands in the strip `-1 - k`. -/
theorem LandsIn.neg {σ : ℝ} {x : ℂ} {k : ℤ} (h : LandsIn σ x k) : LandsIn σ (-x) (-1 - k) := by
  obtain ⟨W, hW, hW0, h1, h2, h3, h4⟩ := h
  have e : π * ((-1 - k : ℤ) : ℝ) = -(π * k) - π := by
    push_cast
    ring
  refine ⟨fun s => -W s, hW.neg, congrArg Neg.neg hW0, ?_⟩
  show (σ : ℂ) * -W 1 ∈ cosStrip (π * ((-1 - k : ℤ) : ℝ))
  rw [mul_neg, e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Complex.neg_re]
    linarith
  · rw [Complex.neg_re]
    linarith
  · rw [Complex.neg_im]
    linarith
  · rw [Complex.neg_im]
    linarith

section Window

variable {N : ℕ} {σ : ℝ} (hw : StripWindow (π * (N + 2) + 2) σ)
include hw

/-- Two zeros that land in one strip of the window are equal. -/
theorem StripWindow.eq_of_landsIn {x x' : ℂ} {k : ℤ} (hk1 : -(N : ℤ) - 1 ≤ k) (hk2 : k ≤ N)
    (h : LandsIn σ x k) (h' : LandsIn σ x' k) : x = x' := by
  obtain ⟨W, hW, hW0, hWk⟩ := h
  obtain ⟨W', hW', hW'0, hW'k⟩ := h'
  have hT := eighth_le_realSaddleTime hw.one_le
  have e := hw.facts.injOn (π * k) (sin_pi_mul_int k) (abs_pi_mul_int_add_le hk1 hk2) (W 1)
    (W' 1) hWk hW'k (by rw [hW.zero_end, hW'.zero_end])
  exact (isForwardPath_timeSeg le_rfl hT).transports_injective ⟨W, hW, hW0, rfl⟩
    ⟨W', hW', hW'0, e.symm⟩

/-- **At least as many zeros below as strips below.** If the end of a lift lies above the strips
`0, …, m - 1` of the window, the zeros of these strips come from `m` positive zeros below its
start. -/
theorem StripWindow.le_posIndex {W : ℝ → ℂ}
    (hW : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W) {m : ℕ} (hm : m ≤ N + 1)
    (hmW : π * m ≤ σ * (W 1).re) : m ≤ posIndex (W 0) := by
  have hT := eighth_le_realSaddleTime hw.one_le
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have hπ := Real.pi_pos
  -- the zeros of the strips `0, …, m - 1` and their lifts
  have hex : ∀ i ∈ Finset.range m, ∃ V : ℝ → ℂ,
      IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 V ∧
        (σ : ℂ) * V 1 ∈ cosStrip (π * ((i : ℤ) : ℝ)) := by
    intro i hi
    have hiN : i ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    obtain ⟨u, hu, huk⟩ := hw.exists_zero (π * ((i : ℤ) : ℝ)) (sin_pi_mul_int _)
      (abs_pi_mul_int_add_le (by omega) (by exact_mod_cast hiN))
    rw [saddleTime_ofReal] at hu
    obtain ⟨V, hV, hV1⟩ := exists_lift_ending_at h8 hT hu
    exact ⟨V, hV, by rw [hV1]; exact huk⟩
  choose! V hV hVk using hex
  have hstrip : ∀ i ∈ Finset.range m,
      π * i + 1 / 8 ≤ σ * (V i 1).re ∧ σ * (V i 1).re ≤ π * i + π - 1 / 8 := by
    intro i hi
    obtain ⟨h1, h2, -, -⟩ := hVk i hi
    rw [Complex.re_ofReal_mul] at h1 h2
    push_cast at h1 h2
    exact ⟨h1, h2⟩
  -- they are positive zeros below the start of the lift
  have hmem : ∀ i ∈ Finset.range m, V i 0 ∈ zerosBelow (W 0) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hstrip i hi
    have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hi
    have hpos1 : 0 < (V i 1).re := by
      have h3 : 0 < σ * (V i 1).re := by
        linarith [mul_nonneg hπ.le (Nat.cast_nonneg (α := ℝ) i)]
      exact pos_of_mul_pos_right h3 hσ0.le
    have hlt1 : (V i 1).re < (W 1).re := by
      have h3 : σ * (V i 1).re < σ * (W 1).re := by
        linarith [mul_le_mul_of_nonneg_left hi' hπ.le]
      exact lt_of_mul_lt_mul_left h3 hσ0.le
    exact ⟨(hV i hi).zero_start, (re_pos_iff_of_lift h8 hT (hV i hi)).mpr hpos1,
      (re_lt_iff_of_lifts h8 hT (hV i hi) hW).mpr hlt1⟩
  -- the lifts keep the order of the strips
  have hord : ∀ j ∈ Finset.range m, ∀ j' ∈ Finset.range m, j < j' →
      (V j 0).re < (V j' 0).re := by
    intro j hj j' hj' hjj
    obtain ⟨-, h2⟩ := hstrip j hj
    obtain ⟨h1', -⟩ := hstrip j' hj'
    have hjj' : (j : ℝ) + 1 ≤ j' := by exact_mod_cast Nat.succ_le_of_lt hjj
    have h3 : σ * (V j 1).re < σ * (V j' 1).re := by
      linarith [mul_le_mul_of_nonneg_left hjj' hπ.le]
    exact (re_lt_iff_of_lifts h8 hT (hV j hj) (hV j' hj')).mpr
      (lt_of_mul_lt_mul_left h3 hσ0.le)
  have hinj : Set.InjOn (fun i => V i 0) (Finset.range m : Set ℕ) := by
    intro i hi i' hi' heq
    have heq' : V i 0 = V i' 0 := heq
    rw [Finset.mem_coe] at hi hi'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := hord i hi i' hi' h
      rw [heq'] at h1
      exact lt_irrefl _ h1
    · have h1 := hord i' hi' i hi h
      rw [heq'] at h1
      exact lt_irrefl _ h1
  have hcard := Finset.card_le_card_of_injOn (s := Finset.range m)
    (t := (finite_zerosBelow (W 0)).toFinset) (fun i => V i 0) (fun i hi => by
    rw [Finset.mem_coe] at hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hmem i hi) hinj
  rw [Finset.card_range] at hcard
  rw [posIndex, Set.ncard_eq_toFinset_card _ (finite_zerosBelow (W 0))]
  exact hcard

/-- **At most as many zeros below as strips below.** A positive zero below the start of a lift
that ends in the strip `k` goes to one of the strips `0, …, k - 1`, and two of them go to
different strips. -/
theorem StripWindow.posIndex_le {W : ℝ → ℂ}
    (hW : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W) {k : ℕ} (hk : k ≤ N)
    (hWk : (σ : ℂ) * W 1 ∈ cosStrip (π * ((k : ℤ) : ℝ))) : posIndex (W 0) ≤ k := by
  have hT := eighth_le_realSaddleTime hw.one_le
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have hπ := Real.pi_pos
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hγ := isForwardPath_timeSeg h8 hT
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  have w2 := hWk.2.1
  rw [Complex.re_ofReal_mul] at w2
  push_cast at w2
  choose! V hV hV0 using fun (y : ℂ) (hy : complexHeat ((1 / 8 : ℝ) : ℂ) y = 0) =>
    exists_lift_starting_at (t₂ := realSaddleTime σ) h8 hT hy
  -- a positive zero below the start goes to a strip below `k`
  have key : ∀ y ∈ zerosBelow (W 0), 0 ≤ ⌊((σ : ℂ) * V y 1).re / π⌋ ∧
      ⌊((σ : ℂ) * V y 1).re / π⌋ < (k : ℤ) ∧
      (σ : ℂ) * V y 1 ∈ cosStrip (π * ((⌊((σ : ℂ) * V y 1).re / π⌋ : ℤ) : ℝ)) := by
    rintro y ⟨hy, hypos, hylt⟩
    have hpos : 0 < (V y 1).re :=
      (re_pos_iff_of_lift h8 hT (hV y hy)).mp (by rw [hV0 y hy]; exact hypos)
    have hlt : (V y 1).re < (W 1).re :=
      (re_lt_iff_of_lifts h8 hT (hV y hy) hW).mp (by rw [hV0 y hy]; exact hylt)
    have hu := (hV y hy).zero_end
    have him := (hV y hy).im_timeSeg h8 hT h11
    have hre : ((σ : ℂ) * V y 1).re = σ * (V y 1).re := Complex.re_ofReal_mul σ (V y 1)
    have h1 : 0 < σ * (V y 1).re := mul_pos hσ0 hpos
    have h2 : σ * (V y 1).re < σ * (W 1).re := mul_lt_mul_of_pos_left hlt hσ0
    have hnorm : ‖(σ : ℂ) * V y 1‖ ≤ π * (N + 2) + 2 := by
      have him' : ((σ : ℂ) * V y 1).im = 0 := by rw [Complex.im_ofReal_mul, him, mul_zero]
      rw [← Complex.abs_re_eq_norm.mpr him', hre, abs_of_pos h1]
      linarith [mul_le_mul_of_nonneg_left hkN hπ.le]
    have hmem := mem_openCosStrip_floor (hw.facts.collar (V y 1) hu hnorm)
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j = ⌊((σ : ℂ) * V y 1).re / π⌋ := ⟨_, rfl⟩
    rw [← hj] at hmem ⊢
    have hmem' := openCosStrip_subset _ hmem
    obtain ⟨m1, m2, -, -⟩ := hmem
    rw [hre] at m1 m2
    have hj0 : (-1 : ℝ) < j := by
      by_contra hcon
      push Not at hcon
      linarith [mul_le_mul_of_nonneg_left hcon hπ.le]
    have hjk : (j : ℝ) < k + 1 := by
      by_contra hcon
      push Not at hcon
      linarith [mul_le_mul_of_nonneg_left hcon hπ.le]
    have hj0' : (-1 : ℤ) < j := by exact_mod_cast hj0
    have hjk' : j < (k : ℤ) + 1 := by exact_mod_cast hjk
    refine ⟨by omega, ?_, hmem'⟩
    -- the strip `k` holds only the end of the lift
    rcases lt_or_eq_of_le (show j ≤ (k : ℤ) by omega) with h | h
    · exact h
    · exfalso
      rw [h] at hmem'
      have e := hw.facts.injOn (π * ((k : ℤ) : ℝ)) (sin_pi_mul_int _)
        (abs_pi_mul_int_add_le (by omega) (by exact_mod_cast hk)) (V y 1) (W 1) hmem' hWk
        (by rw [hu, hW.zero_end])
      rw [e] at hlt
      exact lt_irrefl _ hlt
  have hcard := Finset.card_le_card_of_injOn (s := (finite_zerosBelow (W 0)).toFinset)
    (t := Finset.range k) (fun y => ⌊((σ : ℂ) * V y 1).re / π⌋.toNat) (fun y hy => by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hy
    obtain ⟨h0, h1, -⟩ := key y hy
    have e0 := Int.toNat_of_nonneg h0
    rw [Finset.mem_coe, Finset.mem_range]
    show ⌊((σ : ℂ) * V y 1).re / π⌋.toNat < k
    omega) (fun y hy y' hy' heq => by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hy hy'
    obtain ⟨h0, h1, h2⟩ := key y hy
    obtain ⟨h0', h1', h2'⟩ := key y' hy'
    have e0 := Int.toNat_of_nonneg h0
    have e0' := Int.toNat_of_nonneg h0'
    have heq' : ⌊((σ : ℂ) * V y 1).re / π⌋.toNat = ⌊((σ : ℂ) * V y' 1).re / π⌋.toNat := heq
    have hfl : ⌊((σ : ℂ) * V y 1).re / π⌋ = ⌊((σ : ℂ) * V y' 1).re / π⌋ := by omega
    rw [hfl] at h2
    have e := hw.facts.injOn _ (sin_pi_mul_int _)
      (abs_pi_mul_int_add_le (by omega) (by omega)) (V y 1) (V y' 1) h2 h2'
      (by rw [(hV y hy.1).zero_end, (hV y' hy'.1).zero_end])
    exact hγ.transports_injective ⟨V y, hV y hy.1, hV0 y hy.1, rfl⟩
      ⟨V y', hV y' hy'.1, hV0 y' hy'.1, e.symm⟩)
  rw [Finset.card_range] at hcard
  rw [posIndex, Set.ncard_eq_toFinset_card _ (finite_zerosBelow (W 0))]
  exact hcard

/-- A lift that ends in the strip `k ≥ 0` of the window starts at the positive zero number `k`. -/
theorem StripWindow.posIndex_eq {W : ℝ → ℂ}
    (hW : IsZeroLift (timeSeg (1 / 8) (realSaddleTime σ)) 1 W) {k : ℕ} (hk : k ≤ N)
    (hWk : (σ : ℂ) * W 1 ∈ cosStrip (π * ((k : ℤ) : ℝ))) :
    0 < (W 0).re ∧ posIndex (W 0) = k := by
  have hT := eighth_le_realSaddleTime hw.one_le
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have h1 := hWk.1
  rw [Complex.re_ofReal_mul] at h1
  push_cast at h1
  have hk0 : 0 ≤ π * (k : ℝ) := mul_nonneg Real.pi_pos.le (Nat.cast_nonneg k)
  have hpos1 : 0 < (W 1).re := pos_of_mul_pos_right (by linarith : 0 < σ * (W 1).re) hσ0.le
  exact ⟨(re_pos_iff_of_lift le_rfl hT hW).mpr hpos1,
    le_antisymm (hw.posIndex_le hW hk hWk) (hw.le_posIndex hW (by omega) (by linarith))⟩

/-- The positive zero number `k` lands in the strip `k` of the window. -/
theorem StripWindow.landsIn_of_posIndex {x : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (hpos : 0 < x.re) (hN : posIndex x ≤ N) : LandsIn σ x (posIndex x) := by
  have hT := eighth_le_realSaddleTime hw.one_le
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hσ0 : 0 < σ := by linarith [hw.one_le]
  have hπ := Real.pi_pos
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨W, hW, hW0⟩ := exists_lift_starting_at (t₂ := realSaddleTime σ) h8 hT hx
  have hpos1 : 0 < (W 1).re := (re_pos_iff_of_lift h8 hT hW).mp (by rw [hW0]; exact hpos)
  have hre : ((σ : ℂ) * W 1).re = σ * (W 1).re := Complex.re_ofReal_mul σ (W 1)
  have him := hW.im_timeSeg h8 hT h11
  -- the end of the lift is below the strip `posIndex x + 1`
  have hlt : σ * (W 1).re < π * (posIndex x + 1) := by
    by_contra hcon
    push Not at hcon
    have := hw.le_posIndex hW (m := posIndex x + 1) (by omega) (by push_cast; exact hcon)
    rw [hW0] at this
    omega
  have h1 : 0 < σ * (W 1).re := mul_pos hσ0 hpos1
  have hnorm : ‖(σ : ℂ) * W 1‖ ≤ π * (N + 2) + 2 := by
    have him' : ((σ : ℂ) * W 1).im = 0 := by rw [Complex.im_ofReal_mul, him, mul_zero]
    have hN' : (posIndex x : ℝ) ≤ N := by exact_mod_cast hN
    rw [← Complex.abs_re_eq_norm.mpr him', hre, abs_of_pos h1]
    linarith [mul_le_mul_of_nonneg_left hN' hπ.le]
  have hmem := mem_openCosStrip_floor (hw.facts.collar (W 1) hW.zero_end hnorm)
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = ⌊((σ : ℂ) * W 1).re / π⌋ := ⟨_, rfl⟩
  rw [← hj] at hmem
  have hmem' := openCosStrip_subset _ hmem
  obtain ⟨m1, m2, -, -⟩ := hmem
  rw [hre] at m1 m2
  have hj0 : (-1 : ℝ) < j := by
    by_contra hcon
    push Not at hcon
    linarith [mul_le_mul_of_nonneg_left hcon hπ.le]
  have hjk : (j : ℝ) < posIndex x + 1 := by
    by_contra hcon
    push Not at hcon
    linarith [mul_le_mul_of_nonneg_left hcon hπ.le]
  have hj0' : (-1 : ℤ) < j := by exact_mod_cast hj0
  have hjk' : j < (posIndex x : ℤ) + 1 := by exact_mod_cast hjk
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by omega)
  rw [hn] at hmem'
  have hidx := (hw.posIndex_eq hW (k := n) (by omega) hmem').2
  rw [hW0] at hidx
  refine ⟨W, hW, hW0, ?_⟩
  rw [hidx]
  exact hmem'

/-- **A zero that lands in the strip `k` of the window has the number `k`.** -/
theorem StripWindow.zeroIndex_eq_of_landsIn {x : ℂ} {k : ℤ} (hk1 : -(N : ℤ) - 1 ≤ k)
    (hk2 : k ≤ N) (h : LandsIn σ x k) : zeroIndex x = k := by
  rcases le_or_gt 0 k with hk0 | hk0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hk0
    obtain ⟨W, hW, hW0, hWk⟩ := h
    rw [hn] at hWk
    obtain ⟨hpos, hidx⟩ := hw.posIndex_eq hW (k := n) (by omega) hWk
    rw [hW0] at hpos hidx
    rw [zeroIndex_of_pos hpos, hidx, hn]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -1 - k by omega)
    obtain ⟨W, hW, hW0, hWk⟩ := h.neg
    rw [hn] at hWk
    obtain ⟨hpos, hidx⟩ := hw.posIndex_eq hW (k := n) (by omega) hWk
    rw [hW0] at hpos hidx
    have hnp : ¬0 < x.re := by
      rw [Complex.neg_re] at hpos
      exact not_lt.mpr (by linarith)
    rw [zeroIndex_of_not_pos hnp, hidx]
    omega

/-- **A zero with a number of the window lands in the strip of its number.** -/
theorem StripWindow.landsIn_zeroIndex {x : ℂ} (hx : complexHeat ((1 / 8 : ℝ) : ℂ) x = 0)
    (h1 : -(N : ℤ) - 1 ≤ zeroIndex x) (h2 : zeroIndex x ≤ N) : LandsIn σ x (zeroIndex x) := by
  by_cases hpos : 0 < x.re
  · rw [zeroIndex_of_pos hpos] at h2 ⊢
    exact hw.landsIn_of_posIndex hx hpos (by exact_mod_cast h2)
  · have hneg : 0 < (-x).re := by
      rw [Complex.neg_re]
      have := lt_of_le_of_ne (not_lt.mp hpos) (re_ne_zero_of_zero_eighth hx)
      linarith
    have hx' : complexHeat ((1 / 8 : ℝ) : ℂ) (-x) = 0 := by
      rw [complexHeat_neg]
      exact hx
    rw [zeroIndex_of_not_pos hpos] at h1 ⊢
    have := (hw.landsIn_of_posIndex hx' hneg (by omega)).neg
    rwa [neg_neg] at this

end Window

end

end GaloisForLFunctions.GaloisTheoryOfZeros
