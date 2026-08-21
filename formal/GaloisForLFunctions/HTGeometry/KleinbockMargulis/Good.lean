import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `(C, α)`-good functions (Kleinbock–Margulis, §3)

Let `V ⊆ ℝ^d`.  For `C, α > 0` a function `f` on `V` is *`(C, α)`-good on `V`* if for every open
ball `B ⊆ V` and every `ε > 0`

`|{x ∈ B : |f x| < ε}| ≤ C · (ε / ‖f‖_B)^α · |B|`,

where `‖f‖_B = sup_{x ∈ B} |f x|` and one adopts the convention `1/0 = ∞`, so that the estimate
holds trivially when `f` vanishes identically on `B`.

Using the supremum norm directly would force a junk-value convention for unbounded `f`; instead we
quantify over the points of `B`, replacing `‖f‖_B` by `|f z|` for an arbitrary `z ∈ B`.  The two
formulations are equivalent — `IsGood.measure_mul_ofReal_rpow_le` recovers the supremum form from
any family of points realising the supremum in the limit — and the present one carries no side
conditions.

The ambient space is `Fin d → ℝ` with the supremum norm, so that metric balls are exactly open
cubes; this is the shape in which the estimates of §3 are proved and used.

## Main results

* `IsGood` — the definition, together with the real-valued reformulations `isGood_of_toReal`
  and `IsGood.toReal_le`.
* `isGood_abs_iff`, `IsGood.const_mul` — Lemma 3.1 (a), (b).
* `IsGood.mono_set`, `IsGood.mono_const` — monotonicity in `V` and in `C`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d : ℕ}

/-! ### Elementary facts about balls in `Fin d → ℝ` -/

theorem volume_ball_ne_top (x₀ : Fin d → ℝ) (r : ℝ) : volume (ball x₀ r) ≠ ∞ :=
  (measure_ball_lt_top).ne

theorem volume_ball_pos (x₀ : Fin d → ℝ) {r : ℝ} (hr : 0 < r) : 0 < volume (ball x₀ r) :=
  measure_ball_pos _ _ hr

/-! ### The definition -/

/-- **`(C, α)`-good functions.**  `f` is `(C, α)`-good on `V` when for every open ball `B ⊆ V`,
every `ε > 0` and every `z ∈ B` one has `|{x ∈ B : |f x| < ε}| · |f z|^α ≤ C ε^α |B|`.  Taking the
supremum over `z ∈ B` this is exactly `|{x ∈ B : |f x| < ε}| ≤ C (ε/‖f‖_B)^α |B|`. -/
def IsGood (C α : ℝ) (f : (Fin d → ℝ) → ℝ) (V : Set (Fin d → ℝ)) : Prop :=
  ∀ (x₀ : Fin d → ℝ) (r : ℝ), 0 < r → ball x₀ r ⊆ V → ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball x₀ r,
    volume {x ∈ ball x₀ r | |f x| < ε} * ENNReal.ofReal (|f z| ^ α)
      ≤ ENNReal.ofReal (C * ε ^ α) * volume (ball x₀ r)

variable {C C' α α' : ℝ} {f g : (Fin d → ℝ) → ℝ} {V W : Set (Fin d → ℝ)}

/-- The sublevel set of `f` inside a ball has finite measure. -/
theorem volume_sublevel_ne_top (f : (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ) (r ε : ℝ) :
    volume {x ∈ ball x₀ r | |f x| < ε} ≠ ∞ :=
  ne_top_of_le_ne_top (volume_ball_ne_top x₀ r) (measure_mono (fun _ hx => hx.1))

private theorem ofReal_measure_mul (f : (Fin d → ℝ) → ℝ) (x₀ : Fin d → ℝ) (r ε t : ℝ) :
    volume {x ∈ ball x₀ r | |f x| < ε} * ENNReal.ofReal t
      = ENNReal.ofReal ((volume {x ∈ ball x₀ r | |f x| < ε}).toReal * t) := by
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (volume_sublevel_ne_top f x₀ r ε)]

private theorem ofReal_mul_measure (x₀ : Fin d → ℝ) (r t : ℝ) :
    ENNReal.ofReal t * volume (ball x₀ r)
      = ENNReal.ofReal (t * (volume (ball x₀ r)).toReal) := by
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (volume_ball_ne_top x₀ r)]

/-- Real-valued reformulation: it suffices to check the estimate after `ENNReal.toReal`. -/
theorem isGood_of_toReal
    (h : ∀ (x₀ : Fin d → ℝ) (r : ℝ), 0 < r → ball x₀ r ⊆ V → ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball x₀ r,
      (volume {x ∈ ball x₀ r | |f x| < ε}).toReal * |f z| ^ α
        ≤ C * ε ^ α * (volume (ball x₀ r)).toReal) :
    IsGood C α f V := by
  intro x₀ r hr hball ε hε z hz
  rw [ofReal_measure_mul, ofReal_mul_measure]
  exact ENNReal.ofReal_le_ofReal (h x₀ r hr hball ε hε z hz)

/-- Real-valued form of the defining estimate. -/
theorem IsGood.toReal_le (hf : IsGood C α f V) (hC : 0 ≤ C) (x₀ : Fin d → ℝ) {r : ℝ} (hr : 0 < r)
    (hball : ball x₀ r ⊆ V) {ε : ℝ} (hε : 0 < ε) {z : Fin d → ℝ} (hz : z ∈ ball x₀ r) :
    (volume {x ∈ ball x₀ r | |f x| < ε}).toReal * |f z| ^ α
      ≤ C * ε ^ α * (volume (ball x₀ r)).toReal := by
  have h1 := hf x₀ r hr hball ε hε z hz
  rw [ofReal_measure_mul, ofReal_mul_measure] at h1
  have hpos : 0 ≤ C * ε ^ α * (volume (ball x₀ r)).toReal := by
    have : (0:ℝ) ≤ ε ^ α := Real.rpow_nonneg hε.le _
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff hpos).mp h1

/-! ### Monotonicity -/

/-- Restricting the domain preserves goodness. -/
theorem IsGood.mono_set (hf : IsGood C α f V) (hWV : W ⊆ V) : IsGood C α f W :=
  fun x₀ r hr hball ε hε z hz => hf x₀ r hr (hball.trans hWV) ε hε z hz

/-- Enlarging the constant preserves goodness. -/
theorem IsGood.mono_const (hf : IsGood C α f V) (_hα : 0 ≤ α) (hC : C ≤ C') :
    IsGood C' α f V := by
  intro x₀ r hr hball ε hε z hz
  refine (hf x₀ r hr hball ε hε z hz).trans (mul_le_mul_left ?_ _)
  refine ENNReal.ofReal_le_ofReal ?_
  have : (0:ℝ) ≤ ε ^ α := Real.rpow_nonneg hε.le _
  nlinarith

/-- Congruence in the function. -/
theorem IsGood.congr (hf : IsGood C α f V) (h : ∀ x, f x = g x) : IsGood C α g V := by
  have : f = g := funext h
  rwa [this] at hf

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1 (a).**  `f` is `(C, α)`-good on `V` if and only if `|f|` is. -/
theorem isGood_abs_iff : IsGood C α (fun x => |f x|) V ↔ IsGood C α f V := by
  simp only [IsGood, abs_abs]

alias ⟨IsGood.of_abs, IsGood.abs⟩ := isGood_abs_iff

/-- **Lemma 3.1 (b).**  Scalar multiples of `(C, α)`-good functions are `(C, α)`-good. -/
theorem IsGood.const_mul (hf : IsGood C α f V) (hα : 0 < α) (lam : ℝ) :
    IsGood C α (fun x => lam * f x) V := by
  intro x₀ r hr hball ε hε z hz
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp [Real.zero_rpow hα.ne']
  · have hlam' : 0 < |lam| := abs_pos.mpr hlam
    have hset : {x ∈ ball x₀ r | |lam * f x| < ε} = {x ∈ ball x₀ r | |f x| < ε / |lam|} := by
      ext x
      simp only [mem_setOf_eq, abs_mul, and_congr_right_iff]
      intro _
      rw [lt_div_iff₀ hlam', mul_comm |f x| |lam|]
    have hεdiv : 0 < ε / |lam| := div_pos hε hlam'
    have key := hf x₀ r hr hball (ε / |lam|) hεdiv z hz
    rw [← hset] at key
    have hmul := mul_le_mul_left key (ENNReal.ofReal (|lam| ^ α))
    calc volume {x ∈ ball x₀ r | |lam * f x| < ε} * ENNReal.ofReal (|lam * f z| ^ α)
        = volume {x ∈ ball x₀ r | |lam * f x| < ε} * ENNReal.ofReal (|f z| ^ α)
            * ENNReal.ofReal (|lam| ^ α) := by
          rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), abs_mul,
            Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm (|lam| ^ α)]
      _ ≤ ENNReal.ofReal (C * (ε / |lam|) ^ α) * volume (ball x₀ r)
            * ENNReal.ofReal (|lam| ^ α) := hmul
      _ = ENNReal.ofReal (C * ε ^ α) * volume (ball x₀ r) := by
          rw [mul_right_comm, ← ENNReal.ofReal_mul' (Real.rpow_nonneg (abs_nonneg lam) α)]
          congr 2
          rw [Real.div_rpow hε.le (abs_nonneg _)]
          field_simp

/-- A real-analysis helper: a bound `m t^α ≤ K` follows from the same bound for all smaller
positive values of `t`.  Used to pass from arbitrary points of a ball to the supremum norm. -/
theorem mul_rpow_le_of_forall_lt {m K t α : ℝ} (_hm : 0 ≤ m) (hK : 0 ≤ K) (hα : 0 < α)
    (ht : 0 ≤ t) (h : ∀ c, 0 < c → c < t → m * c ^ α ≤ K) : m * t ^ α ≤ K := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rwa [Real.zero_rpow hα.ne', mul_zero]
  · have hcont : Filter.Tendsto (fun c : ℝ => m * c ^ α) (𝓝[<] t) (𝓝 (m * t ^ α)) :=
      ((continuous_const.mul (Real.continuous_rpow_const hα.le)).tendsto t).mono_left
        nhdsWithin_le_nhds
    have hev : ∀ᶠ c in 𝓝[<] t, m * c ^ α ≤ K := by
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds htpos)] with c hc1 hc2
      exact h c hc2 hc1
    exact le_of_tendsto hcont hev

/-- A limiting form of the defining estimate: it is enough to know that arbitrarily large values
of `|f|` are attained on the ball.  This is the supremum form `‖f‖_B ≥ ρ ⟹ …` used throughout §4. -/
theorem IsGood.measure_mul_ofReal_rpow_le (hf : IsGood C α f V) (hC : 0 ≤ C) (hα : 0 < α)
    (x₀ : Fin d → ℝ) {r : ℝ} (hr : 0 < r) (hball : ball x₀ r ⊆ V) {ε : ℝ} (hε : 0 < ε)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hsup : ∀ c, c < ρ → ∃ z ∈ ball x₀ r, c < |f z|) :
    volume {x ∈ ball x₀ r | |f x| < ε} * ENNReal.ofReal (ρ ^ α)
      ≤ ENNReal.ofReal (C * ε ^ α) * volume (ball x₀ r) := by
  set m := (volume {x ∈ ball x₀ r | |f x| < ε}).toReal with hm
  set K := C * ε ^ α * (volume (ball x₀ r)).toReal with hK
  have hKnn : 0 ≤ K := by
    have : (0:ℝ) ≤ ε ^ α := Real.rpow_nonneg hε.le _
    rw [hK]; positivity
  have main : m * ρ ^ α ≤ K := by
    refine mul_rpow_le_of_forall_lt ENNReal.toReal_nonneg hKnn hα hρ ?_
    intro c hc hcρ
    obtain ⟨z, hz, hzc⟩ := hsup c hcρ
    have h2 := hf.toReal_le hC x₀ hr hball hε hz
    have hle : c ^ α ≤ |f z| ^ α := Real.rpow_le_rpow hc.le hzc.le hα.le
    nlinarith [ENNReal.toReal_nonneg (a := volume {x ∈ ball x₀ r | |f x| < ε})]
  rw [ofReal_measure_mul, ofReal_mul_measure, ← hm, ← hK]
  exact ENNReal.ofReal_le_ofReal main

/-- **Lemma 3.1 (c).**  A pointwise supremum of `(C, α)`-good functions is `(C, α)`-good.
The supremum is described by the two conditions `hle` (upper bound) and `hlt` (least upper
bound), so no boundedness or index-type hypothesis is needed. -/
theorem IsGood.sup {ι : Type*} {gi : ι → (Fin d → ℝ) → ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (hg : ∀ i, IsGood C α (gi i) V) (hle : ∀ i x, |gi i x| ≤ f x)
    (hlt : ∀ x c, c < f x → ∃ i, c < |gi i x|) :
    IsGood C α f V := by
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨i, hi⟩ := hlt x (f x - 1) (by linarith)
    exact absurd (hle i x) (by nlinarith [abs_nonneg (gi i x)])
  intro x₀ r hr hball ε hε z hz
  have hsub : ∀ i, {x ∈ ball x₀ r | |f x| < ε} ⊆ {x ∈ ball x₀ r | |gi i x| < ε} := by
    intro i x hx
    exact ⟨hx.1, lt_of_le_of_lt (hle i x) (by rw [← abs_of_nonneg (hfnn x)]; exact hx.2)⟩
  set m := (volume {x ∈ ball x₀ r | |f x| < ε}).toReal with hm
  set K := C * ε ^ α * (volume (ball x₀ r)).toReal with hK
  have hKnn : 0 ≤ K := by
    have : (0:ℝ) ≤ ε ^ α := Real.rpow_nonneg hε.le _
    rw [hK]; positivity
  have main : m * |f z| ^ α ≤ K := by
    rw [abs_of_nonneg (hfnn z)]
    refine mul_rpow_le_of_forall_lt ENNReal.toReal_nonneg hKnn hα (hfnn z) ?_
    intro c hc hcz
    obtain ⟨i, hi⟩ := hlt z c hcz
    have h2 := (hg i).toReal_le hC x₀ hr hball hε hz
    have hmono : m ≤ (volume {x ∈ ball x₀ r | |gi i x| < ε}).toReal :=
      ENNReal.toReal_mono (volume_sublevel_ne_top _ x₀ r ε) (measure_mono (hsub i))
    have hrle : c ^ α ≤ |gi i z| ^ α := Real.rpow_le_rpow hc.le hi.le hα.le
    have hcnn : (0:ℝ) ≤ c ^ α := Real.rpow_nonneg hc.le _
    nlinarith [ENNReal.toReal_nonneg (a := volume {x ∈ ball x₀ r | |f x| < ε})]
  rw [ofReal_measure_mul, ofReal_mul_measure, ← hm, ← hK]
  exact ENNReal.ofReal_le_ofReal main

/-- Decreasing the exponent preserves goodness, provided the constant is at least `1`. -/
theorem IsGood.mono_exponent (hf : IsGood C α f V) (hC : 1 ≤ C) (hα' : 0 < α') (hαα : α' ≤ α) :
    IsGood C α' f V := by
  have hα : 0 < α := lt_of_lt_of_le hα' hαα
  refine isGood_of_toReal ?_
  intro x₀ r hr hball ε hε z hz
  set m := (volume {x ∈ ball x₀ r | |f x| < ε}).toReal with hm
  set b := (volume (ball x₀ r)).toReal with hb
  have hmnn : 0 ≤ m := ENNReal.toReal_nonneg
  have hbnn : 0 ≤ b := ENNReal.toReal_nonneg
  have hmb : m ≤ b :=
    ENNReal.toReal_mono (volume_ball_ne_top x₀ r) (measure_mono (fun _ hx => hx.1))
  rcases le_or_gt (|f z|) ε with hcase | hcase
  · -- `|f z| ≤ ε`: the trivial bound `m ≤ b` suffices.
    have h1 : |f z| ^ α' ≤ ε ^ α' := Real.rpow_le_rpow (abs_nonneg _) hcase hα'.le
    have h2 : (0:ℝ) ≤ ε ^ α' := Real.rpow_nonneg hε.le _
    have h3 : (0:ℝ) ≤ |f z| ^ α' := Real.rpow_nonneg (abs_nonneg _) _
    calc m * |f z| ^ α' ≤ b * ε ^ α' := by
          exact mul_le_mul hmb h1 h3 hbnn
      _ ≤ C * ε ^ α' * b := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hbnn h2)]
  · -- `|f z| > ε`: interpolate using the sharper exponent `α`.
    have hfz : 0 < |f z| := lt_trans hε hcase
    have key := hf.toReal_le (le_trans zero_le_one hC) x₀ hr hball hε hz
    have hsplit : |f z| ^ α = |f z| ^ α' * |f z| ^ (α - α') := by
      rw [← Real.rpow_add hfz]; ring_nf
    have hsplit' : ε ^ α = ε ^ α' * ε ^ (α - α') := by
      rw [← Real.rpow_add hε]; ring_nf
    have hcmp : ε ^ (α - α') ≤ |f z| ^ (α - α') :=
      Real.rpow_le_rpow hε.le hcase.le (by linarith)
    have hpos : 0 < ε ^ (α - α') := Real.rpow_pos_of_pos hε _
    have hfnn' : (0:ℝ) ≤ |f z| ^ α' := Real.rpow_nonneg (abs_nonneg _) _
    have hεnn' : (0:ℝ) ≤ ε ^ α' := Real.rpow_nonneg hε.le _
    -- `m |f z|^α' ε^(α-α') ≤ m |f z|^α ≤ C ε^α b = C ε^α' b ε^(α-α')`
    have step : m * |f z| ^ α' * ε ^ (α - α') ≤ C * ε ^ α' * b * ε ^ (α - α') := by
      calc m * |f z| ^ α' * ε ^ (α - α') ≤ m * |f z| ^ α' * |f z| ^ (α - α') := by
            have : 0 ≤ m * |f z| ^ α' := by positivity
            nlinarith
        _ = m * |f z| ^ α := by rw [hsplit]; ring
        _ ≤ C * ε ^ α * b := key
        _ = C * ε ^ α' * b * ε ^ (α - α') := by rw [hsplit']; ring
    exact le_of_mul_le_mul_right step hpos

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
