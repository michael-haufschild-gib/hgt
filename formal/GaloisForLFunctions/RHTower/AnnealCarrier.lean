/-
Doc 22 §1 + doc 32 §§6–7 (task #143): the ANNEAL carrier layer — symmetrization
puts any approximant on the same FE×reality carrier as ξ, at zero analytic cost.

The ANNEAL reduction (doc 22) reads ζ-window parity off a finite truncation on
dominated windows. Its §1 claim — "the truncation lives on the same carrier-layer
as ξ; only the Euler depth differs" — and doc 32 §6's (SYM) brick — "the exact-FE
requirement of the finite side costs nothing" — are formalized here, generically:

* `symmetrize` / `symmetrize_one_sub` — Φ* := ½(Φ(s) + Φ(1−s)) satisfies the EXACT
  even functional equation; `symmetrize_xi` — ξ is a fixed point.
* `norm_sub_symmetrize_le` / `norm_sub_symmetrize_le_of_mem` — (SYM-err): on
  FE-closed sets, symmetrization preserves the approximation error (doc 32 §7's
  one-line proof, machine-checked) — exponential accuracy is free to keep.
* `symmetrize_differentiable`, `symmetrize_conj` — entirety and the Schwarz real
  structure are preserved.
* `symmetrize_orderAt_one_sub`, `symmetrize_orderAt_conj` — the FE and reality
  pairings of vanishing orders, the exact equivariance package that instantiates
  the window identity (ID) of `WindowRelation` on the finite carrier (the
  analogues of `xi_orderAt_one_sub`, `xi_orderAt_conj`).
* `chiSymmetrize` / `chiSymmetrize_one_sub` — doc 22 §1's multiplicative version:
  g := h + χ·h(1−·) satisfies the exact asymmetric FE g(1−s) = χ(1−s)·g(s)
  whenever χ(s)χ(1−s) = 1 (the Riemann–Siegel main sum g_N is the instance).
* `symmetrize_domination` — the (DOM) assembly of doc 32 §6: a sup-error bound ε
  on an FE-closed chart set plus the lower bound ε < ‖Φ*‖ yield the strict
  domination that `seam_transport` (doc 32 §1) consumes. The two analytic inputs
  — (AFE-exp) accuracy and the Cartan/(LOW-BC) lower bound — remain explicit
  hypotheses, per the missing-analytic-inputs discipline.

With `SeamTransport.seam_transport_ladder`, the chain is: (AFE-exp) + (LOW-BC)
⟹ `symmetrize_domination` ⟹ deck-class transport at every level 2^k — doc 22's
reduction with all wiring machine-checked and only the two instrument-grade
estimates left as hypotheses.
-/
import GaloisForLFunctions.RHTower.Reflection

namespace RHTower

open Complex

/-- FE symmetrization: `Φ*(s) = (Φ(s) + Φ(1−s))/2` (doc 32 §6, (SYM)). -/
noncomputable def symmetrize (Φ : ℂ → ℂ) : ℂ → ℂ := fun s => (Φ s + Φ (1 - s)) / 2

/-- (SYM-FE): the symmetrization satisfies the exact even functional equation. -/
theorem symmetrize_one_sub (Φ : ℂ → ℂ) (s : ℂ) :
    symmetrize Φ (1 - s) = symmetrize Φ s := by
  unfold symmetrize
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  ring

/-- FE-invariant functions are fixed points of symmetrization. -/
theorem symmetrize_eq_self {Φ : ℂ → ℂ} (h : ∀ s, Φ (1 - s) = Φ s) :
    symmetrize Φ = Φ := by
  funext s
  unfold symmetrize
  rw [h s]
  ring

/-- ξ is a fixed point of symmetrization. -/
theorem symmetrize_xi : symmetrize xi = xi :=
  symmetrize_eq_self xi_one_sub

/-- (SYM-err): symmetrizing costs at most the FE-orbit average of the error
(doc 32 §7, the one-line proof). -/
theorem norm_sub_symmetrize_le {f Φ : ℂ → ℂ} (hFE : ∀ s, f (1 - s) = f s) (s : ℂ) :
    ‖f s - symmetrize Φ s‖ ≤ (‖f s - Φ s‖ + ‖f (1 - s) - Φ (1 - s)‖) / 2 := by
  have key : f s - symmetrize Φ s
      = ((f s - Φ s) + (f (1 - s) - Φ (1 - s))) / 2 := by
    rw [hFE s]
    unfold symmetrize
    ring
  rw [key, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have := norm_add_le (f s - Φ s) (f (1 - s) - Φ (1 - s))
  linarith

/-- Symmetrization preserves entirety. -/
theorem symmetrize_differentiable {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) :
    Differentiable ℂ (symmetrize Φ) := by
  have h1 : Differentiable ℂ fun s : ℂ => Φ (1 - s) := by
    have h := hΦ.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
    simpa [Function.comp] using! h
  exact (hΦ.add h1).div_const 2

/-- FE pairing of orders for the symmetrized carrier: ord_{1−ρ} = ord_ρ — the
finite-side analogue of `xi_orderAt_one_sub`. -/
theorem symmetrize_orderAt_one_sub {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (z : ℂ) :
    analyticOrderAt (symmetrize Φ) (1 - z) = analyticOrderAt (symmetrize Φ) z := by
  have hfun : (fun w => symmetrize Φ (1 - w)) = symmetrize Φ := by
    funext w
    exact symmetrize_one_sub Φ w
  have h := analyticOrderAt_comp_one_sub (symmetrize_differentiable hΦ) z
  rwa [hfun] at h

/-- Symmetrization preserves the Schwarz real structure. -/
theorem symmetrize_conj {Φ : ℂ → ℂ}
    (hΦ : ∀ s, Φ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Φ s)) (s : ℂ) :
    symmetrize Φ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (symmetrize Φ s) := by
  unfold symmetrize
  have h1 : (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by
    rw [map_sub, map_one]
  rw [h1, hΦ, hΦ, map_div₀, map_add, map_ofNat]

/-- Reality pairing of orders for the symmetrized carrier: ord_{ρ̄} = ord_ρ — the
finite-side analogue of `xi_orderAt_conj`. -/
theorem symmetrize_orderAt_conj {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hconj : ∀ s, Φ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Φ s)) (z : ℂ) :
    analyticOrderAt (symmetrize Φ) ((starRingEnd ℂ) z)
      = analyticOrderAt (symmetrize Φ) z := by
  have hfun : (fun w => (starRingEnd ℂ) (symmetrize Φ ((starRingEnd ℂ) w)))
      = symmetrize Φ := by
    funext w
    rw [symmetrize_conj hconj, Complex.conj_conj]
  have h := analyticOrderAt_conj_conj (symmetrize_differentiable hΦ) z
  rwa [hfun] at h

/-- doc 22 §1: the χ-symmetrized truncation `g = h + χ·h(1−·)` (with
`h = Σ_{n≤N} n^{−s}` and χ the ζ-FE factor, this is the Riemann–Siegel main
sum `g_N`). -/
noncomputable def chiSymmetrize (χ h : ℂ → ℂ) : ℂ → ℂ := fun s => h s + χ s * h (1 - s)

/-- doc 22 §1's "one line": whenever `χ(s)·χ(1−s) = 1`, the χ-symmetrization
satisfies the EXACT asymmetric functional equation `g(1−s) = χ(1−s)·g(s)`. -/
theorem chiSymmetrize_one_sub {χ h : ℂ → ℂ} (hχ : ∀ s, χ s * χ (1 - s) = 1) (s : ℂ) :
    chiSymmetrize χ h (1 - s) = χ (1 - s) * chiSymmetrize χ h s := by
  unfold chiSymmetrize
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  linear_combination (-(h (1 - s))) * hχ s

/-- (SYM) on FE-closed sets: accuracy is preserved by symmetrization. -/
theorem norm_sub_symmetrize_le_of_mem {f Φ : ℂ → ℂ} (hFE : ∀ s, f (1 - s) = f s)
    {S : Set ℂ} (hS : ∀ z ∈ S, (1 : ℂ) - z ∈ S) {ε : ℝ}
    (hε : ∀ z ∈ S, ‖f z - Φ z‖ ≤ ε) {z : ℂ} (hz : z ∈ S) :
    ‖f z - symmetrize Φ z‖ ≤ ε := by
  have h := norm_sub_symmetrize_le (Φ := Φ) hFE z
  have h1 := hε z hz
  have h2 := hε (1 - z) (hS z hz)
  linarith

/-- (DOM) assembly (doc 32 §6): an approximation-error bound ε on an FE-closed
chart set plus the lower bound ε < ‖Φ*‖ yield the strict domination
`‖f − Φ*‖ < ‖Φ*‖` — exactly the `hdom` premise of `seam_transport` /
`seam_transport_ladder`. The two hypotheses are the reduction's remaining
instrument-grade analytic inputs: (AFE-exp) accuracy and the (LOW-BC)
Cartan lower bound. -/
theorem symmetrize_domination {f Φ : ℂ → ℂ} (hFE : ∀ s, f (1 - s) = f s)
    {S : Set ℂ} (hS : ∀ z ∈ S, (1 : ℂ) - z ∈ S) {ε : ℝ}
    (hε : ∀ z ∈ S, ‖f z - Φ z‖ ≤ ε)
    (hlow : ∀ z ∈ S, ε < ‖symmetrize Φ z‖) :
    ∀ z ∈ S, ‖f z - symmetrize Φ z‖ < ‖symmetrize Φ z‖ := fun z hz =>
  lt_of_le_of_lt (norm_sub_symmetrize_le_of_mem hFE hS hε hz) (hlow z hz)

end RHTower
