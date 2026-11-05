import GaloisForLFunctions.SignedWindowCriticality.PerronSignLaw.TheEvenSectorIsMarkovUpToThePlasticThreshold

/-!
# Frustration cannot be switched away

On the half-window `[−c, 0]` the parity sectors of the window `[−c, c]` are nonlocal forms with the
absolutely continuous conductance kernels

* even: `k₊(u, v) = ω(|u − v|) + ω(−u − v) − 4cosh(u/2)cosh(v/2)` (Lévy jumps, trivial-zero
  reflections, minus the pole's positive square), plus the prime reflections, which are positive
  conductances on the anti-diagonals `u + v = −log n`;
* odd: `k₋(u, v) = ω(|u − v|) − ω(−u − v) + 4sinh(u/2)sinh(v/2)` (the light cone), plus the prime
  reflections, which are negative conductances `−w_n` on the anti-diagonals.

A **sign gauge** `σ : [−c, 0] → {±1}` switches a conductance `k(u, v)` to `σ(u)σ(v)k(u, v)` (and moves
mass to the potential); a form is **balanced** if some sign gauge makes every conductance nonnegative.
This module answers the switching half of review §2.7 Q2:

* **The logarithmic diagonal forbids nodes.** Both kernels are large and positive near the diagonal
  (`ω(t) ≥ e^{−1/2}/(2t)`), and a sign gauge that changes sign has sign changes at arbitrarily close
  pairs (`exists_close_pair_ne`). So every nonconstant sign gauge creates a negative switched
  conductance next to each of its nodes (`evenSectorKernel_pos_of_close`, `oddSectorKernel_pos`).
* **The even sector is balanced exactly up to `log ρ`** (`evenSectorKernel_nonneg_iff`), and past
  `log ρ` it is frustrated in every sign gauge (`even_frustrated_in_every_sign_gauge`): the pole
  frustrates the pair (edge, centre), whatever the prime weights.
* **The odd sector is frustrated in every sign gauge from the first prime on**
  (`odd_frustrated_in_every_sign_gauge`): near the centre `−½log 2` of the prime-two sliver the
  reflection pairs are close, so a sign gauge either keeps the prime conductance negative or
  changes sign across a short light-cone edge.

Hence past `log ρ` (even) and past `½log 2` (odd) no certificate can be Markov in any switched frame:
its gauge must be positive and its negative edges paid by the positive network (Kron domination), or
it must carry nodes, each of which costs a negative light-cone conductance.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower
open GaloisForLFunctions.RHTower (screwSignThreshold)

/-- The even-sector conductance kernel on the half-window (absolutely continuous part). -/
def evenSectorKernel (u v : ℝ) : ℝ :=
  archLevyDensity |u - v| + archLevyDensity (-u - v) - 4 * Real.cosh (u / 2) * Real.cosh (v / 2)

/-- The odd-sector conductance kernel on the half-window: the light cone. -/
def oddSectorKernel (u v : ℝ) : ℝ :=
  archLevyDensity |u - v| - archLevyDensity (-u - v) + 4 * Real.sinh (u / 2) * Real.sinh (v / 2)

/-- A sign gauge takes the values `±1`. -/
def IsSignGauge (σ : ℝ → ℝ) : Prop := ∀ x, σ x = 1 ∨ σ x = -1

theorem archLevyDensity_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ archLevyDensity x := by
  rcases hx.lt_or_eq with h | h
  · exact (archLevyDensity_pos h).le
  · subst h
    simp [archLevyDensity]

/-- `ω(t) ≥ e^{−1/2}/(2t)` on `(0, 1]`. -/
theorem archLevyDensity_ge_inv {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.exp (-(1 / 2)) / (2 * t) ≤ archLevyDensity t := by
  unfold archLevyDensity
  have h1 : 1 - Real.exp (-2 * t) ≤ 2 * t := by
    have := Real.add_one_le_exp (-2 * t)
    linarith
  have h2 : 0 < 1 - Real.exp (-2 * t) := by
    have : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h3 : Real.exp (-(1 / 2)) ≤ Real.exp (-t / 2) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp (-(1 / 2)) / (2 * t) ≤ Real.exp (-t / 2) / (2 * t) :=
        div_le_div_of_nonneg_right h3 (by linarith)
    _ ≤ Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le h2 h1

/-! ### Sign changes at close pairs -/

/-- **Bisection.** A sign gauge with different values at `a < b` has different values at two points
of `[a, b]` at distance `(b − a)/2ⁿ`, for every `n`. -/
theorem exists_pair_ne_dist {σ : ℝ → ℝ} (hσ : IsSignGauge σ) {a b : ℝ} (hab : a ≤ b)
    (hne : σ a ≠ σ b) (n : ℕ) :
    ∃ u v, a ≤ u ∧ v ≤ b ∧ v - u = (b - a) / 2 ^ n ∧ σ u ≠ σ v := by
  induction n with
  | zero => exact ⟨a, b, le_rfl, le_rfl, by simp, hne⟩
  | succ n ih =>
    obtain ⟨u, v, hu, hv, huv, hσuv⟩ := ih
    set m := (u + v) / 2
    have hlen : v - m = (b - a) / 2 ^ (n + 1) := by
      rw [show v - m = (v - u) / 2 by simp only [m]; ring, huv, pow_succ]
      ring
    have hlen' : m - u = (b - a) / 2 ^ (n + 1) := by
      rw [show m - u = (v - u) / 2 by simp only [m]; ring, huv, pow_succ]
      ring
    have hpos : 0 ≤ (b - a) / 2 ^ n := div_nonneg (by linarith) (by positivity)
    by_cases hm : σ u = σ m
    · refine ⟨m, v, ?_, hv, hlen, fun h => hσuv (hm.trans h)⟩
      simp only [m]; linarith
    · refine ⟨u, m, hu, ?_, hlen', hm⟩
      simp only [m]; linarith

/-- A sign gauge that differs at `a < b` differs at two distinct points of `[a, b]` closer than any
`δ > 0`. -/
theorem exists_close_pair_ne {σ : ℝ → ℝ} (hσ : IsSignGauge σ) {a b : ℝ} (hab : a < b)
    (hne : σ a ≠ σ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u v, a ≤ u ∧ u < v ∧ v ≤ b ∧ v - u < δ ∧ σ u ≠ σ v := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((b - a) / δ) (by norm_num : (1 : ℝ) < 2)
  obtain ⟨u, v, hu, hv, huv, hσ'⟩ := exists_pair_ne_dist hσ hab.le hne n
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hlt : (b - a) / 2 ^ n < δ := by
    rw [div_lt_iff₀ h2]
    rw [div_lt_iff₀ hδ] at hn
    linarith
  have hpos : 0 < (b - a) / 2 ^ n := div_pos (by linarith) h2
  exact ⟨u, v, hu, by linarith, hv, by linarith, hσ'⟩

theorem mul_eq_neg_one_of_ne {σ : ℝ → ℝ} (hσ : IsSignGauge σ) {u v : ℝ} (h : σ u ≠ σ v) :
    σ u * σ v = -1 := by
  rcases hσ u with hu | hu <;> rcases hσ v with hv | hv
  · exact absurd (hu.trans hv.symm) h
  · rw [hu, hv]; norm_num
  · rw [hu, hv]; norm_num
  · exact absurd (hu.trans hv.symm) h

theorem mul_eq_one_of_eq {σ : ℝ → ℝ} (hσ : IsSignGauge σ) {u v : ℝ} (h : σ u = σ v) :
    σ u * σ v = 1 := by
  rw [h]
  rcases hσ v with hv | hv <;> simp [hv]

/-! ### The kernels near the diagonal -/

theorem cosh_half_le {c u : ℝ} (hu : u ∈ Icc (-c) 0) : Real.cosh (u / 2) ≤ Real.cosh (c / 2) := by
  rw [Real.cosh_le_cosh]
  rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonneg (by linarith [hu.1, hu.2])]
  linarith [hu.1]

/-- **The even kernel is positive near the diagonal**: for `0 < |u − v| < e^{−1/2}/(8cosh²(c/2))`,
`k₊(u, v) > 0` on the half-window. -/
theorem evenSectorKernel_pos_of_close {c u v : ℝ} (hu : u ∈ Icc (-c) 0) (hv : v ∈ Icc (-c) 0)
    (huv : u ≠ v) (hclose : |u - v| < Real.exp (-(1 / 2)) / (8 * Real.cosh (c / 2) ^ 2)) :
    0 < evenSectorKernel u v := by
  have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have hch : 1 ≤ Real.cosh (c / 2) := Real.one_le_cosh _
  have hbound : Real.exp (-(1 / 2)) / (8 * Real.cosh (c / 2) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : Real.exp (-(1 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith
  have hω := archLevyDensity_ge_inv hd (by linarith)
  have hω2 := archLevyDensity_nonneg (show 0 ≤ -u - v by linarith [hu.2, hv.2])
  have hcu := cosh_half_le hu
  have hcv := cosh_half_le hv
  have hpos_u : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have hpos_v : 0 < Real.cosh (v / 2) := Real.cosh_pos _
  have hprod : 4 * Real.cosh (u / 2) * Real.cosh (v / 2) ≤ 4 * Real.cosh (c / 2) ^ 2 := by
    have := mul_le_mul hcu hcv hpos_v.le (by linarith)
    nlinarith
  have hbig : 4 * Real.cosh (c / 2) ^ 2 < Real.exp (-(1 / 2)) / (2 * |u - v|) := by
    rw [lt_div_iff₀ (by linarith)]
    rw [lt_div_iff₀ (by positivity)] at hclose
    nlinarith
  unfold evenSectorKernel
  linarith

/-- **The light cone is positive**: `k₋(u, v) > 0` for distinct `u, v < 0`. -/
theorem oddSectorKernel_pos {u v : ℝ} (hu : u < 0) (hv : v < 0) (huv : u ≠ v) :
    0 < oddSectorKernel u v := by
  have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have hlt : |u - v| < -u - v := by
    rw [abs_lt]
    constructor <;> linarith
  have hω : archLevyDensity (-u - v) < archLevyDensity |u - v| :=
    CHMDPolar.strictAntiOn_archLevyDensity_Ioi hd (by simp only [mem_Ioi]; linarith) hlt
  have hs : 0 < Real.sinh (u / 2) * Real.sinh (v / 2) :=
    mul_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr (by linarith)) (Real.sinh_neg_iff.mpr (by linarith))
  unfold oddSectorKernel
  nlinarith

/-! ### The even sector -/

/-- **The even kernel is nonnegative on the half-window exactly up to the plastic threshold.** -/
theorem evenSectorKernel_nonneg_iff {c : ℝ} (hc : 0 ≤ c) :
    (∀ u ∈ Icc (-c) 0, ∀ v ∈ Icc (-c) 0, u ≠ v → 0 ≤ evenSectorKernel u v) ↔
      c ≤ screwSignThreshold := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hc0 : 0 < c := lt_trans (lt_trans (by norm_num) WeilLevyCoshCrossover.screwSignThreshold_gt) hlt
    have hneg := SignedWindowCriticality.PerronSignLaw.evenKernel_neg_of_threshold_lt hlt
    have := h (-c) ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, le_rfl⟩ (by linarith)
    unfold evenSectorKernel at this
    rw [show -c - 0 = -c by ring, abs_neg, abs_of_pos hc0, show -(-c) - 0 = c by ring,
      show -c / 2 = -(c / 2) by ring, Real.cosh_neg, zero_div, Real.cosh_zero] at this
    rw [sub_zero, add_zero, abs_of_pos hc0, zero_div, Real.cosh_zero] at hneg
    linarith
  · intro hct u hu v hv huv
    have h := SignedWindowCriticality.PerronSignLaw.four_mul_cosh_mul_cosh_le (p := -u) (q := -v) (by linarith [hu.2])
      (by linarith [hv.2]) (by linarith [hu.1]) (by linarith [hv.1]) (by intro h; exact huv (by linarith))
    unfold evenSectorKernel
    rw [show -u - -v = -(u - v) by ring, abs_neg, show -u + -v = -u - v by ring,
      show -u / 2 = -(u / 2) by ring, show -v / 2 = -(v / 2) by ring, Real.cosh_neg,
      Real.cosh_neg] at h
    linarith

/-- **Past the plastic threshold the even sector is frustrated in every sign gauge**: for every sign
gauge `σ` there are distinct `u, v ∈ [−c, 0]` with `σ(u)σ(v)k₊(u, v) < 0`. -/
theorem even_frustrated_in_every_sign_gauge {c : ℝ} (hc : screwSignThreshold < c) {σ : ℝ → ℝ}
    (hσ : IsSignGauge σ) :
    ∃ u ∈ Icc (-c) 0, ∃ v ∈ Icc (-c) 0, u ≠ v ∧ σ u * σ v * evenSectorKernel u v < 0 := by
  have hc0 : 0 < c :=
    lt_trans (lt_trans (by norm_num) WeilLevyCoshCrossover.screwSignThreshold_gt) hc
  by_cases hend : σ (-c) = σ 0
  · refine ⟨-c, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith, ?_⟩
    rw [mul_eq_one_of_eq hσ hend, one_mul]
    have hneg := SignedWindowCriticality.PerronSignLaw.evenKernel_neg_of_threshold_lt hc
    rw [sub_zero, add_zero, abs_of_pos hc0, zero_div, Real.cosh_zero] at hneg
    unfold evenSectorKernel
    rw [show -c - 0 = -c by ring, abs_neg, abs_of_pos hc0, show -(-c) - 0 = c by ring,
      show -c / 2 = -(c / 2) by ring, Real.cosh_neg, zero_div, Real.cosh_zero]
    linarith
  · have hδ : 0 < Real.exp (-(1 / 2)) / (8 * Real.cosh (c / 2) ^ 2) := by positivity
    obtain ⟨u, v, hu, huv, hv, hclose, hne⟩ := exists_close_pair_ne hσ (by linarith) hend hδ
    have huI : u ∈ Icc (-c) 0 := ⟨hu, by linarith⟩
    have hvI : v ∈ Icc (-c) 0 := ⟨by linarith, hv⟩
    refine ⟨u, huI, v, hvI, huv.ne, ?_⟩
    rw [mul_eq_neg_one_of_ne hσ hne]
    have hk := evenSectorKernel_pos_of_close huI hvI huv.ne
      (by rw [abs_sub_comm, abs_of_pos (by linarith)]; exact hclose)
    linarith

/-! ### The odd sector -/

/-- **Every entry adds a frustrated anti-diagonal to the odd sector.** Let an acting prime power of
lag `ℓ` (`0 < ℓ < 2c`) carry the conductance `−w`, `w > 0`, on the anti-diagonal `u + v = −ℓ`. For
every sign gauge there are distinct `u, v ∈ (−c, 0)`, symmetric about the sliver centre `−ℓ/2`, on
which either the switched light cone or the switched prime conductance is negative. -/
theorem odd_frustrated_at_every_entry {c w ℓ : ℝ} (hℓ : 0 < ℓ) (hc : ℓ / 2 < c) (hw : 0 < w)
    {σ : ℝ → ℝ} (hσ : IsSignGauge σ) :
    ∃ u ∈ Ioo (-c) 0, ∃ v ∈ Ioo (-c) 0, u ≠ v ∧
      (σ u * σ v * oddSectorKernel u v < 0 ∨ (u + v = -ℓ ∧ σ u * σ v * (-w) < 0)) := by
  set η := min (c - ℓ / 2) (ℓ / 2) / 2 with hη
  have hmin : 0 < min (c - ℓ / 2) (ℓ / 2) := lt_min (by linarith) (by linarith)
  have hη0 : 0 < η := by linarith
  have hη1 : η < c - ℓ / 2 := by linarith [min_le_left (c - ℓ / 2) (ℓ / 2)]
  have hη2 : η < ℓ / 2 := by linarith [min_le_right (c - ℓ / 2) (ℓ / 2)]
  have huI : -(ℓ / 2) - η ∈ Ioo (-c) 0 := ⟨by linarith, by linarith⟩
  have hvI : -(ℓ / 2) + η ∈ Ioo (-c) 0 := ⟨by linarith, by linarith⟩
  have huv : -(ℓ / 2) - η ≠ -(ℓ / 2) + η := by intro h; linarith
  refine ⟨_, huI, _, hvI, huv, ?_⟩
  by_cases hs : σ (-(ℓ / 2) - η) = σ (-(ℓ / 2) + η)
  · right
    refine ⟨by ring, ?_⟩
    rw [mul_eq_one_of_eq hσ hs]
    linarith
  · left
    rw [mul_eq_neg_one_of_ne hσ hs]
    have := oddSectorKernel_pos huI.2 hvI.2 huv
    linarith

/-- **From the first prime on the odd sector is frustrated in every sign gauge** (the entry of `2`). -/
theorem odd_frustrated_in_every_sign_gauge {c w : ℝ} (hc : Real.log 2 / 2 < c) (hw : 0 < w)
    {σ : ℝ → ℝ} (hσ : IsSignGauge σ) :
    ∃ u ∈ Ioo (-c) 0, ∃ v ∈ Ioo (-c) 0, u ≠ v ∧
      (σ u * σ v * oddSectorKernel u v < 0 ∨ (u + v = -Real.log 2 ∧ σ u * σ v * (-w) < 0)) :=
  odd_frustrated_at_every_entry (Real.log_pos (by norm_num)) hc hw hσ

/-- **Below the first prime the odd sector is balanced**: its absolutely continuous kernel, the
light cone, is positive and no prime acts. -/
theorem oddSectorKernel_pos_on_halfWindow {c u v : ℝ} (hu : u ∈ Ioo (-c) 0) (hv : v ∈ Ioo (-c) 0)
    (huv : u ≠ v) : 0 < oddSectorKernel u v :=
  oddSectorKernel_pos hu.2 hv.2 huv

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
