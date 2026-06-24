/-
# Böttcher tower — concrete dynamics layer (objects for the q62 instantiation)

The verified skeleton (`Q62.lean`) is stated abstractly (`Disc : ℂ → Prop`, the
coordinates as field elements). To instantiate it onto Nguyen's actual setting we
need the genuine objects of quadratic dynamics, none of which are in Mathlib. This
file defines them and the predicate `Disconnected c` (`c ∉ M`) used as `Disc`.

  * `quadratic c`     — the map `z ↦ z² + c`
  * `filledJulia c`   — `K_c = { z : orbit of z is bounded }`
  * `mandelbrot`      — `M = { c : 0 ∈ K_c }` (orbit of the critical point bounded)
  * `Disconnected c`  — `c ∉ M`  (filled Julia set is a Cantor set)

Definitions + basic orbit lemmas; the analytic theory (Böttcher coordinate, Brolin
measure, full-shift coding) builds on these.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Bornology Metric

namespace Bottcher

/-- The quadratic map `f_c(z) = z² + c`. -/
noncomputable def quadratic (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

@[simp] theorem quadratic_apply (c z : ℂ) : quadratic c z = z ^ 2 + c := rfl

/-- The filled Julia set `K_c = { z : the forward orbit of z under `f_c` is bounded }`. -/
def filledJulia (c : ℂ) : Set ℂ :=
  {z | IsBounded (Set.range fun n : ℕ => (quadratic c)^[n] z)}

/-- The Mandelbrot set `M = { c : 0 ∈ K_c }`: the critical orbit is bounded. -/
def mandelbrot : Set ℂ := {c | (0 : ℂ) ∈ filledJulia c}

/-- `c` is a disconnected parameter when `c ∉ M`; then `K_c` is a Cantor set and `f_c`
on it is conjugate to the one-sided full two-shift. This is the `Disc` of `q62_independence`. -/
def Disconnected (c : ℂ) : Prop := c ∉ mandelbrot

/-- Membership in the filled Julia set is boundedness of the orbit. -/
theorem mem_filledJulia_iff (c z : ℂ) :
    z ∈ filledJulia c ↔ IsBounded (Set.range fun n : ℕ => (quadratic c)^[n] z) := Iff.rfl

/-- The critical orbit step: `f_c` applied to the orbit shifts the index. -/
theorem quadratic_iterate_succ (c z : ℂ) (n : ℕ) :
    (quadratic c)^[n + 1] z = (quadratic c)^[n] z ^ 2 + c := by
  rw [Function.iterate_succ', Function.comp_apply, quadratic_apply]

/-- **Escape estimate.** Beyond radius `2` (and `‖c‖ ≤ ‖z‖`), one quadratic step expands
the modulus: `‖f_c z‖ ≥ ‖z‖·(‖z‖-1)`. The geometric driver of escape to `∞`. -/
theorem quadratic_norm_ge {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖z‖ * (‖z‖ - 1) ≤ ‖quadratic c z‖ := by
  rw [quadratic_apply]
  have h1 : ‖z‖ ^ 2 - ‖c‖ ≤ ‖z ^ 2 + c‖ := by
    have h := norm_sub_norm_le (z ^ 2) (-c)
    rw [norm_neg, sub_neg_eq_add, norm_pow] at h
    exact h
  nlinarith [hc, h1]

/-- Strict expansion beyond radius `2`: `‖z‖ < ‖f_c z‖`. -/
theorem quadratic_norm_lt {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    ‖z‖ < ‖quadratic c z‖ := by
  have hge := quadratic_norm_ge hc hz
  nlinarith [hge, hz]

/-- **Geometric escape.** Beyond radius `2`, the orbit grows at least geometrically:
`‖z‖·(‖z‖-1)ⁿ ≤ ‖f_c^[n] z‖`. Since `‖z‖-1 > 1`, the orbit is unbounded — `z ∉ K_c`. -/
theorem quadratic_orbit_growth {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) (n : ℕ) :
    ‖z‖ * (‖z‖ - 1) ^ n ≤ ‖(quadratic c)^[n] z‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz1 : (1 : ℝ) ≤ ‖z‖ - 1 := by linarith
    have hge1 : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ hz1
    have hzpos : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    rw [Function.iterate_succ', Function.comp_apply]
    set w := (quadratic c)^[n] z with hw
    have hwz : ‖z‖ ≤ ‖w‖ := le_trans (by nlinarith [hge1, hzpos]) ih
    have hwc : ‖c‖ ≤ ‖w‖ := le_trans hc hwz
    have hw2 : 2 < ‖w‖ := lt_of_lt_of_le hz hwz
    have hstep : ‖w‖ * (‖w‖ - 1) ≤ ‖quadratic c w‖ := quadratic_norm_ge hwc hw2
    calc ‖z‖ * (‖z‖ - 1) ^ (n + 1)
        = (‖z‖ * (‖z‖ - 1) ^ n) * (‖z‖ - 1) := by ring
      _ ≤ ‖w‖ * (‖w‖ - 1) := by nlinarith [ih, hwz, hz1]
      _ ≤ ‖quadratic c w‖ := hstep

/-- Geometric escape ⟹ the point is not in the filled Julia set. -/
theorem not_mem_filledJulia {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    z ∉ filledJulia c := by
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
  push_neg
  intro C
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (show (1 : ℝ) < ‖z‖ - 1 by linarith)
  refine ⟨(quadratic c)^[n] z, ⟨n, rfl⟩, ?_⟩
  have hgrow := quadratic_orbit_growth hc hz n
  have hpow : (0 : ℝ) ≤ (‖z‖ - 1) ^ n := pow_nonneg (by linarith) n
  nlinarith [hn, hgrow, hpow, hz]

/-- **`K_c` is bounded**: the filled Julia set lies in the closed disk of radius
`max 2 ‖c‖`. (Connects the dynamics layer toward the Tier-2 capacity theory, where
`cap(K_c)=1` is needed.) -/
theorem filledJulia_subset_closedBall (c : ℂ) :
    filledJulia c ⊆ closedBall 0 (max 2 ‖c‖) := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  by_contra hlt
  push_neg at hlt
  have h2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hlt
  have hcc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hlt)
  exact not_mem_filledJulia hcc h2 hz

/-- The filled Julia set is bounded. -/
theorem isBounded_filledJulia (c : ℂ) : IsBounded (filledJulia c) :=
  (isBounded_closedBall).subset (filledJulia_subset_closedBall c)

/-- The quadratic map is continuous. -/
theorem continuous_quadratic (c : ℂ) : Continuous (quadratic c) := by
  unfold quadratic; fun_prop

/-- Forward invariance: a tail of a bounded orbit is bounded, so `f_c` maps `K_c` into itself. -/
theorem filledJulia_forward {c z : ℂ} (hz : z ∈ filledJulia c) (n : ℕ) :
    (quadratic c)^[n] z ∈ filledJulia c := by
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz ⊢
  obtain ⟨C, hC⟩ := hz
  refine ⟨C, ?_⟩
  rintro x ⟨k, rfl⟩
  dsimp only
  rw [← Function.iterate_add_apply]
  exact hC _ ⟨k + n, rfl⟩

/-- `K_c` as the points whose entire orbit stays in the escape disk. -/
theorem filledJulia_eq_iInter (c : ℂ) :
    filledJulia c = ⋂ n : ℕ, (fun z => (quadratic c)^[n] z) ⁻¹' closedBall 0 (max 2 ‖c‖) := by
  ext z
  simp only [Set.mem_iInter, Set.mem_preimage, mem_closedBall, dist_zero_right]
  constructor
  · intro hz n
    have hforward := filledJulia_forward hz n
    by_contra hgt
    push_neg at hgt
    have h2 : 2 < ‖(quadratic c)^[n] z‖ := lt_of_le_of_lt (le_max_left _ _) hgt
    have hcc : ‖c‖ ≤ ‖(quadratic c)^[n] z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hgt)
    exact not_mem_filledJulia hcc h2 hforward
  · intro hbound
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
    exact ⟨max 2 ‖c‖, by rintro x ⟨n, rfl⟩; exact hbound n⟩

/-- **`K_c` is closed.** -/
theorem isClosed_filledJulia (c : ℂ) : IsClosed (filledJulia c) := by
  rw [filledJulia_eq_iInter]
  exact isClosed_iInter fun n =>
    isClosed_closedBall.preimage ((continuous_quadratic c).iterate n)

/-- **`K_c` is compact** (closed + bounded in `ℂ`). The compactum on which the
equilibrium measure / capacity theory of Tier 2 will live. -/
theorem isCompact_filledJulia (c : ℂ) : IsCompact (filledJulia c) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_filledJulia c) (isBounded_filledJulia c)

/-- The basin of infinity `Ω_c = ℂ ∖ K_c`, the domain of the Böttcher coordinate. -/
def basinInfinity (c : ℂ) : Set ℂ := (filledJulia c)ᶜ

/-- `Ω_c` is open. -/
theorem isOpen_basinInfinity (c : ℂ) : IsOpen (basinInfinity c) :=
  (isClosed_filledJulia c).isOpen_compl

/-- Every point beyond radius `2` (with `‖c‖ ≤ ‖z‖`) lies in the basin of infinity. -/
theorem mem_basinInfinity_of_norm_gt {c z : ℂ} (hc : ‖c‖ ≤ ‖z‖) (hz : 2 < ‖z‖) :
    z ∈ basinInfinity c := not_mem_filledJulia hc hz

/-- `c` is disconnected iff the critical point `0` escapes (is not in `K_c`). -/
theorem disconnected_iff_zero_not_mem (c : ℂ) :
    Disconnected c ↔ (0 : ℂ) ∉ filledJulia c := Iff.rfl

/-- **Disconnected parameters exist** (and the disconnected case is non-vacuous):
every `c` with `‖c‖ > 2` is disconnected, since the critical orbit `0 ↦ c ↦ …` escapes. -/
theorem disconnected_of_norm_gt {c : ℂ} (hc : 2 < ‖c‖) : Disconnected c := by
  rw [disconnected_iff_zero_not_mem]
  intro h0
  have h1 : (quadratic c)^[1] 0 ∈ filledJulia c := filledJulia_forward h0 1
  rw [Function.iterate_one] at h1
  simp only [quadratic_apply] at h1
  rw [show (0 : ℂ) ^ 2 + c = c by ring] at h1
  exact not_mem_filledJulia (le_refl ‖c‖) hc h1

end Bottcher
