import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The endpoint revival lower bound for the centred discrepancy

A difference of two operators is bounded below in operator norm by any asymptotic image of a
sequence of unit vectors: if `B g_k` approaches a family of vectors of constant length `c` while
`A g_k` vanishes, then `‖B - A‖ ≥ c`.  This is the whole operator content of the revival argument —
the almost-periodic construction supplies the sequence, compactness supplies the vanishing, and no
property of either operator beyond boundedness is used.

The limiting window mass of the prime endpoint measure is an explicit exponential integral,
`∫_x^{x+L} e^{-u/2} du = 2(1 - e^{-L/2}) e^{-x/2}`, whose `L²(0,L)` norm divided by `√L` is the
constant `2(1 - e^{-L/2}) √((1 - e^{-L})/L)`.  It is positive for every positive window, so the
centred discrepancy cannot converge to zero in operator norm.
-/

open MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-! ## `(278)`: an asymptotic image bounds the operator norm below -/

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **An asymptotic image of unit vectors bounds the operator norm below.** -/
theorem le_opNorm_of_asymptotic_image {Z : E →L[𝕜] F} {g : ℕ → E} {v : ℕ → F} {c : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ 1) (hv : ∀ k, ‖v k‖ = c)
    (hconv : Filter.Tendsto (fun k => ‖Z (g k) - v k‖) Filter.atTop (nhds 0)) :
    c ≤ ‖Z‖ := by
  have hstep : ∀ k, c - ‖Z (g k) - v k‖ ≤ ‖Z‖ := by
    intro k
    have h1 : ‖v k‖ ≤ ‖Z (g k)‖ + ‖Z (g k) - v k‖ :=
      calc ‖v k‖ = ‖Z (g k) - (Z (g k) - v k)‖ := by congr 1; abel
        _ ≤ ‖Z (g k)‖ + ‖Z (g k) - v k‖ := norm_sub_le _ _
    have h2 : ‖Z (g k)‖ ≤ ‖Z‖ :=
      (Z.le_opNorm (g k)).trans (by
        have := Z.opNorm_nonneg
        nlinarith [hg k, norm_nonneg (g k)])
    rw [hv k] at h1
    linarith
  have hlim : Filter.Tendsto (fun k => c - ‖Z (g k) - v k‖) Filter.atTop (nhds (c - 0)) :=
    Filter.Tendsto.const_sub _ hconv
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hstep)

/-- **`(278)`: the centred difference has operator norm at least the revival amplitude.** -/
theorem le_opNorm_sub_of_split {B A : E →L[𝕜] F} {g : ℕ → E} {v : ℕ → F} {c : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ 1) (hv : ∀ k, ‖v k‖ = c)
    (hB : Filter.Tendsto (fun k => ‖B (g k) - v k‖) Filter.atTop (nhds 0))
    (hA : Filter.Tendsto (fun k => ‖A (g k)‖) Filter.atTop (nhds 0)) :
    c ≤ ‖B - A‖ := by
  refine le_opNorm_of_asymptotic_image hg hv ?_
  have hbound : ∀ k, ‖(B - A) (g k) - v k‖ ≤ ‖B (g k) - v k‖ + ‖A (g k)‖ := by
    intro k
    have hsplit : (B - A) (g k) - v k = (B (g k) - v k) - A (g k) := by
      have happ : (B - A) (g k) = B (g k) - A (g k) := rfl
      rw [happ]
      abel
    rw [hsplit]
    exact norm_sub_le _ _
  have hsum : Filter.Tendsto (fun k => ‖B (g k) - v k‖ + ‖A (g k)‖) Filter.atTop (nhds 0) := by
    simpa using hB.add hA
  refine squeeze_zero (fun k => norm_nonneg _) hbound hsum

/-! ## `(279)`: the limiting window mass and its norm -/

/-- The limiting window mass of the prime endpoint measure. -/
def windowMassLimit (L x : ℝ) : ℝ := 2 * (1 - Real.exp (-L / 2)) * Real.exp (-x / 2)

/-- The window integral of the limiting density is an explicit exponential. -/
theorem integral_windowDensity (L x : ℝ) :
    (∫ u in x..(x + L), Real.exp (-u / 2)) = windowMassLimit L x := by
  have hderiv : ∀ u ∈ Set.uIcc x (x + L),
      HasDerivAt (fun u : ℝ => -2 * Real.exp (-u / 2)) (Real.exp (-u / 2)) u := by
    intro u _
    have hinner : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2 : ℝ) u := by
      simpa using ((hasDerivAt_id u).neg).div_const 2
    have h : HasDerivAt (fun u : ℝ => Real.exp (-u / 2))
        (Real.exp (-u / 2) * (-1 / 2)) u := hinner.exp
    have h2 : HasDerivAt (fun u : ℝ => -2 * Real.exp (-u / 2))
        (-2 * (Real.exp (-u / 2) * (-1 / 2))) u := h.const_mul (-2 : ℝ)
    convert h2 using 1
    ring
  have hcont : IntervalIntegrable (fun u : ℝ => Real.exp (-u / 2)) volume x (x + L) :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont, windowMassLimit]
  have hexp : Real.exp (-(x + L) / 2) = Real.exp (-x / 2) * Real.exp (-L / 2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hexp]
  ring

/-- The squared `L²(0,L)` norm of the limiting window mass. -/
theorem integral_windowMassLimit_sq (L : ℝ) :
    (∫ x in (0 : ℝ)..L, windowMassLimit L x ^ (2 : ℕ))
      = 4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ) * (1 - Real.exp (-L)) := by
  have hsq : ∀ x : ℝ, windowMassLimit L x ^ (2 : ℕ)
      = (4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ)) * Real.exp (-x) := by
    intro x
    rw [windowMassLimit]
    have hx2 : Real.exp (-x / 2) ^ (2 : ℕ) = Real.exp (-x) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, mul_pow, hx2]
    ring
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) L,
      HasDerivAt (fun u : ℝ => -Real.exp (-u)) (Real.exp (-u)) u := by
    intro u _
    have hinner : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) u := hasDerivAt_neg u
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-u) * (-1)) u := hinner.exp
    have h2 : HasDerivAt (fun u : ℝ => -Real.exp (-u)) (-(Real.exp (-u) * (-1))) u := h1.neg
    convert h2 using 1
    ring
  have hcont : IntervalIntegrable (fun u : ℝ => Real.exp (-u)) volume 0 L :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [intervalIntegral.integral_congr (g := fun x => (4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ)) * Real.exp (-x))
      (fun x _ => hsq x), intervalIntegral.integral_const_mul,
    integral_eq_sub_of_hasDerivAt hderiv hcont]
  rw [neg_zero, Real.exp_zero]
  ring

/-- **`(279)`: the revival amplitude of the limiting window is strictly positive.** -/
theorem windowRevivalAmplitude_pos {L : ℝ} (hL : 0 < L) :
    0 < 2 * (1 - Real.exp (-L / 2)) * Real.sqrt ((1 - Real.exp (-L)) / L) := by
  have h1 : Real.exp (-L / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : Real.exp (-L) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h3 : 0 < (1 - Real.exp (-L)) / L := by
    apply div_pos (by linarith) hL
  have h4 : 0 < Real.sqrt ((1 - Real.exp (-L)) / L) := Real.sqrt_pos.mpr h3
  have h5 : 0 < 1 - Real.exp (-L / 2) := by linarith
  positivity

/-- The `L²(0,L)` norm of the limiting window mass, divided by `√L`, is the revival amplitude. -/
theorem sqrt_integral_windowMassLimit_sq_div (L : ℝ) (hL : 0 < L) :
    Real.sqrt (∫ x in (0 : ℝ)..L, windowMassLimit L x ^ (2 : ℕ)) / Real.sqrt L
      = 2 * (1 - Real.exp (-L / 2)) * Real.sqrt ((1 - Real.exp (-L)) / L) := by
  have h1 : Real.exp (-L / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h2 : Real.exp (-L) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  rw [integral_windowMassLimit_sq]
  have hfac : 4 * (1 - Real.exp (-L / 2)) ^ (2 : ℕ) * (1 - Real.exp (-L))
      = (2 * (1 - Real.exp (-L / 2))) ^ (2 : ℕ) * (1 - Real.exp (-L)) := by ring
  rw [hfac, Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]
  rw [mul_div_assoc, ← Real.sqrt_div (by linarith : (0:ℝ) ≤ 1 - Real.exp (-L)) L]

end RHTower
