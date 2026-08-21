/-
# Busemann flows on NPC spaces

A *Busemann flow* on a metric space is the pair consisting of the gradient flow `Φ` of a
Busemann function `b` associated with a point at infinity, together with `b` itself.  On a
Hadamard manifold `Φ_t(x) = exp_x(-t grad b(x))` and `Φ_t(x)` is the unit-speed geodesic ray
from `x` asymptotic to the chosen point at infinity.  The four axioms below record exactly the
metric content of that situation:

* `flow_add`  — `Φ` is a semiflow;
* `dist_flow` — the flow lines are unit speed: `d(x, Φ_t x) = t`;
* `tendsto_fn` — the *defining* Busemann property: `d(Φ_H x, y) - H → b(y) - b(x)`.

Nothing about differentiability, curvature bounds or dimension is assumed.

The main result is `BusemannFlow.dist_flow_sq_le`, an exact quantitative first-variation
inequality
```
d(Φ_h x, y)^2 ≤ d(x,y)^2 - 2h (b(x) - b(y)) + h^2 ,
```
which on a Hilbert space with `b = ⟪u, ·⟫` and `Φ_h x = x - h u` is an identity.  It replaces
the Jacobi-field computation used in the literature, and is derived here from the NPC
inequality alone.  Everything else in this file — nonexpansiveness of `Φ_t`, the translation
law `b(Φ_t x) = b(x) - t`, and the two-point estimate `dist_flow_flow_sq_le` — is a consequence.
-/
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.NPCSpace
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace GaloisForLFunctions.HTGeometry.HadamardLipschitz

open Filter Topology

/-- A Busemann flow on a metric space: the (forward) gradient flow `flow` of a Busemann
function `fn`, presented purely metrically. -/
structure BusemannFlow (X : Type*) [MetricSpace X] where
  /-- The forward flow `Φ_t`. -/
  flow : ℝ → X → X
  /-- The Busemann function `b`. -/
  fn : X → ℝ
  /-- `Φ` is a semiflow on `[0, ∞)`. -/
  flow_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) : flow s (flow t x) = flow (s + t) x
  /-- Flow lines have unit speed. -/
  dist_flow (t : ℝ) (ht : 0 ≤ t) (x : X) : dist x (flow t x) = t
  /-- The defining property of the Busemann function attached to the flow. -/
  tendsto_fn (x y : X) :
    Tendsto (fun H : ℝ => dist (flow H x) y - H) atTop (𝓝 (fn y - fn x))

namespace BusemannFlow

variable {X : Type*} [MetricSpace X] (F : BusemannFlow X)

@[simp] theorem flow_zero (x : X) : F.flow 0 x = x :=
  (dist_eq_zero.mp (F.dist_flow 0 le_rfl x)).symm

/-- Distance along a single flow line. -/
theorem dist_flow_flow_line {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (x : X) :
    dist (F.flow t x) (F.flow s x) = s - t := by
  have h : F.flow s x = F.flow (s - t) (F.flow t x) := by
    rw [F.flow_add (s - t) t (by linarith) ht x]; ring_nf
  rw [h]
  exact F.dist_flow (s - t) (by linarith) (F.flow t x)

/-- Distance along a single flow line, without an ordering hypothesis. -/
theorem dist_flow_flow_abs {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : X) :
    dist (F.flow t x) (F.flow s x) = |s - t| := by
  rcases le_total t s with h | h
  · rw [F.dist_flow_flow_line ht h x, abs_of_nonneg (by linarith)]
  · rw [dist_comm, F.dist_flow_flow_line hs h x, abs_of_nonpos (by linarith)]; ring

/-- The Busemann function decreases at unit rate along the flow. -/
theorem fn_flow {t : ℝ} (ht : 0 ≤ t) (x : X) : F.fn (F.flow t x) = F.fn x - t := by
  have h := F.tendsto_fn x (F.flow t x)
  have heq : (fun H : ℝ => dist (F.flow H x) (F.flow t x) - H) =ᶠ[atTop] (fun _ => -t) := by
    filter_upwards [eventually_ge_atTop t] with H hH
    rw [dist_comm, F.dist_flow_flow_line ht hH x]; ring
  have h2 : Tendsto (fun H : ℝ => dist (F.flow H x) (F.flow t x) - H) atTop (𝓝 (-t)) :=
    Tendsto.congr' heq.symm tendsto_const_nhds
  have := tendsto_nhds_unique h h2
  linarith

/-- Analytic core of the key inequality: pass to the limit `H → ∞` in the NPC comparison. -/
private theorem npc_limit_helper (A c h P : ℝ) (E : ℝ → ℝ) (hE : Tendsto E atTop (𝓝 c))
    (hbound : ∀ᶠ H : ℝ in atTop,
      P ≤ A ^ 2 - h * A ^ 2 / H + h * E H * (E H / H + 2) + h ^ 2) :
    P ≤ A ^ 2 + 2 * h * c + h ^ 2 := by
  have h1 : Tendsto (fun H : ℝ => h * A ^ 2 / H) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have h2 : Tendsto (fun H : ℝ => E H / H) atTop (𝓝 0) := Tendsto.div_atTop hE tendsto_id
  have h3 : Tendsto (fun H : ℝ => A ^ 2 - h * A ^ 2 / H + h * E H * (E H / H + 2) + h ^ 2)
      atTop (𝓝 (A ^ 2 - 0 + h * c * (0 + 2) + h ^ 2)) :=
    ((tendsto_const_nhds.sub h1).add
      ((tendsto_const_nhds.mul hE).mul (h2.add tendsto_const_nhds))).add tendsto_const_nhds
  have h4 : A ^ 2 - 0 + h * c * (0 + 2) + h ^ 2 = A ^ 2 + 2 * h * c + h ^ 2 := by ring
  rw [h4] at h3
  exact ge_of_tendsto h3 hbound

variable [NPCSpace X]

/-- **Key first-variation inequality.**  Flowing `x` forward for time `h ≥ 0` changes the
squared distance to a fixed point `y` by at most `-2h(b(x) - b(y)) + h²`.

This is the metric replacement for the Jacobi-field estimate of the literature.  It is sharp:
in a Hilbert space with `b = ⟪u, ·⟫`, `‖u‖ = 1`, and `Φ_h x = x - h u`, it is an identity. -/
theorem dist_flow_sq_le (x y : X) {h : ℝ} (hh : 0 ≤ h) :
    dist (F.flow h x) y ^ 2 ≤ dist x y ^ 2 - 2 * h * (F.fn x - F.fn y) + h ^ 2 := by
  have hbound : ∀ᶠ H : ℝ in atTop,
      dist (F.flow h x) y ^ 2
        ≤ dist x y ^ 2 - h * dist x y ^ 2 / H
          + h * (dist (F.flow H x) y - H) * ((dist (F.flow H x) y - H) / H + 2) + h ^ 2 := by
    filter_upwards [eventually_gt_atTop (max h 1)] with H hH
    have hH0 : (0:ℝ) < H := lt_of_lt_of_le (by norm_num) (le_of_lt (lt_of_le_of_lt (le_max_right h 1) hH))
    have hHh : h < H := lt_of_le_of_lt (le_max_left h 1) hH
    have ht₀ : 0 ≤ h / H := div_nonneg hh hH0.le
    have ht₁ : h / H ≤ 1 := by rw [div_le_one hH0]; exact hHh.le
    have hxq : dist x (F.flow H x) = H := F.dist_flow H hH0.le x
    have h1 : dist x (F.flow h x) = (h / H) * dist x (F.flow H x) := by
      rw [F.dist_flow h hh x, hxq]; field_simp
    have h2 : dist (F.flow h x) (F.flow H x) = (1 - h / H) * dist x (F.flow H x) := by
      rw [F.dist_flow_flow_line hh hHh.le x, hxq]; field_simp
    have hnpc :=
      NPCSpace.dist_sq_le_of_between x (F.flow H x) (F.flow h x) y (h / H) ht₀ ht₁ h1 h2
    rw [hxq] at hnpc
    refine hnpc.trans (le_of_eq ?_)
    field_simp
    ring
  have := npc_limit_helper (dist x y) (F.fn y - F.fn x) h (dist (F.flow h x) y ^ 2)
    (fun H => dist (F.flow H x) y - H) (F.tendsto_fn x y) hbound
  linarith

/-- The Busemann flow is nonexpansive: a metric consequence of the key inequality. -/
theorem flow_nonexpansive {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    dist (F.flow t x) (F.flow t y) ≤ dist x y := by
  have h1 := F.dist_flow_sq_le x (F.flow t y) ht
  have h2 := F.dist_flow_sq_le y x ht
  rw [F.fn_flow ht y] at h1
  have h3 : dist x (F.flow t y) = dist (F.flow t y) x := dist_comm _ _
  have h4 : dist y x = dist x y := dist_comm _ _
  rw [h3] at h1
  rw [h4] at h2
  have hsq : dist (F.flow t x) (F.flow t y) ^ 2 ≤ dist x y ^ 2 := by nlinarith [h1, h2]
  nlinarith [hsq, dist_nonneg (x := F.flow t x) (y := F.flow t y), dist_nonneg (x := x) (y := y)]

/-- **Two-point estimate.**  Flowing `x` for time `s ≥ 0` and `y` for time `t ≥ 0`. -/
theorem dist_flow_flow_sq_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x y : X) :
    dist (F.flow s x) (F.flow t y) ^ 2
      ≤ dist x y ^ 2 - 2 * (s - t) * (F.fn x - F.fn y) + (s - t) ^ 2 := by
  rcases le_total t s with hle | hle
  · have hsplit : F.flow s x = F.flow t (F.flow (s - t) x) := by
      rw [F.flow_add t (s - t) ht (by linarith) x]; ring_nf
    have hne : dist (F.flow s x) (F.flow t y) ≤ dist (F.flow (s - t) x) y := by
      rw [hsplit]; exact F.flow_nonexpansive ht _ _
    have hkey := F.dist_flow_sq_le x y (h := s - t) (by linarith)
    have hnn : 0 ≤ dist (F.flow s x) (F.flow t y) := dist_nonneg
    nlinarith [hne, hkey, hnn, dist_nonneg (x := F.flow (s - t) x) (y := y)]
  · have hsplit : F.flow t y = F.flow s (F.flow (t - s) y) := by
      rw [F.flow_add s (t - s) hs (by linarith) y]; ring_nf
    have hne : dist (F.flow s x) (F.flow t y) ≤ dist x (F.flow (t - s) y) := by
      rw [hsplit, dist_comm, dist_comm x]
      exact F.flow_nonexpansive hs _ _
    have hkey := F.dist_flow_sq_le y x (h := t - s) (by linarith)
    have hnn : 0 ≤ dist (F.flow s x) (F.flow t y) := dist_nonneg
    have hd : dist x (F.flow (t - s) y) = dist (F.flow (t - s) y) x := dist_comm _ _
    have hd2 : dist y x = dist x y := dist_comm _ _
    rw [hd] at hne
    rw [hd2] at hkey
    nlinarith [hne, hkey, hnn, dist_nonneg (x := F.flow (t - s) y) (y := x)]

/-- The flow line through `x` is the geodesic realising `gd`. -/
theorem gd_flow {t : ℝ} (ht : 0 ≤ t) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (x : X) :
    NPCSpace.gd x (F.flow t x) α = F.flow (α * t) x := by
  refine (NPCSpace.eq_gd_of_dist x (F.flow t x) (F.flow (α * t) x) α hα₀ hα₁ ?_ ?_).symm
  · rw [F.dist_flow (α * t) (mul_nonneg hα₀ ht) x, F.dist_flow t ht x]
  · rw [F.dist_flow_flow_line (mul_nonneg hα₀ ht) (by nlinarith) x, F.dist_flow t ht x]; ring

end BusemannFlow

end GaloisForLFunctions.HTGeometry.HadamardLipschitz
