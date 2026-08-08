/-
# The entire regularized determinant of a Hilbert–Schmidt kernel

The corpus object `HilbertSchmidt.fredholmDet K z = exp(−∑_{n≥2} zⁿ/n·tr(Kⁿ))` is defined by a
series that converges only on the disc `|z|·‖K‖_HS < 1`, and it is nowhere zero there by
construction.  The Hilbert–Carleman determinant `det₂(1 − zK)` is its analytic continuation to the
whole plane; that continuation *does* vanish, exactly at the reciprocal eigenvalues.

This file makes the continuation a definite object.  An entire `D` **is a regularized determinant**
for `K` when it agrees with `fredholmDet K` on some disc around the origin on which the exponent
series converges.  Such a `D` is unique — that is the identity theorem — so the phrase "the
regularized determinant of `K`" is well posed, and any statement of the form
`det₂(1 − zK) = L(z)` for an entire `L` becomes the assertion `IsRegularizedDet K L`, whose whole
content is the disc-local identity.

Main results:
* `IsRegularizedDet` — the defining property.
* `IsRegularizedDet.unique` — at most one entire function has it.
* `IsRegularizedDet.eq_one_at_zero` — its value at the origin is `1`.
* `isRegularizedDet_of_logDeriv_eq` — the criterion actually used: an entire, disc-nonvanishing `L`
  with `L 0 = 1` and `logDeriv L = −resolventTrace K` on the disc is the regularized determinant.
-/
import GaloisForLFunctions.HTGeometry.FredholmDeterminant
import GaloisForLFunctions.HTGeometry.EntireIdentityTheorem

namespace GaloisForLFunctions.HTGeometry

open Metric HilbertSchmidt

variable {ι : Type*}

/-- `D` is **the regularized determinant** `det₂(1 − zK)` of the Hilbert–Schmidt kernel `K` when it
is entire and agrees with the disc-local exponential representative near the origin. -/
def IsRegularizedDet (K : ι × ι → ℂ) (D : ℂ → ℂ) : Prop :=
  Differentiable ℂ D ∧
    ∃ r : ℝ, 0 < r ∧ r * hsNorm K < 1 ∧ ∀ z ∈ ball (0 : ℂ) r, D z = fredholmDet K z

/-- **Uniqueness.**  Two entire functions agreeing with the local determinant near the origin agree
everywhere: their difference is entire and flat at the origin. -/
theorem IsRegularizedDet.unique {K : ι × ι → ℂ} {D₁ D₂ : ℂ → ℂ}
    (h₁ : IsRegularizedDet K D₁) (h₂ : IsRegularizedDet K D₂) : D₁ = D₂ := by
  obtain ⟨hd₁, r₁, hr₁, _, he₁⟩ := h₁
  obtain ⟨hd₂, r₂, hr₂, _, he₂⟩ := h₂
  set r := min r₁ r₂ with hrdef
  have hr : 0 < r := lt_min hr₁ hr₂
  have hev : (D₁ - D₂) =ᶠ[nhds (0 : ℂ)] 0 := by
    have hball : ball (0 : ℂ) r ∈ nhds (0 : ℂ) :=
      isOpen_ball.mem_nhds (by simpa using hr)
    filter_upwards [hball] with z hz
    have hz₁ : z ∈ ball (0 : ℂ) r₁ := ball_subset_ball (min_le_left _ _) hz
    have hz₂ : z ∈ ball (0 : ℂ) r₂ := ball_subset_ball (min_le_right _ _) hz
    simp [he₁ z hz₁, he₂ z hz₂]
  have hzero : ∀ k, iteratedDeriv k (D₁ - D₂) 0 = 0 := by
    intro k
    have := (GaloisForLFunctions.eventuallyEq_iteratedDeriv hev k).eq_of_nhds
    simpa using this
  have := GaloisForLFunctions.entire_eq_zero_of_forall_iteratedDeriv_zero (hd₁.sub hd₂) hzero
  have hfun : ∀ z, D₁ z - D₂ z = 0 := fun z => congrFun this z
  funext z
  linear_combination hfun z

/-- The regularized determinant takes the value `1` at the origin. -/
theorem IsRegularizedDet.eq_one_at_zero {K : ι × ι → ℂ} {D : ℂ → ℂ}
    (h : IsRegularizedDet K D) : D 0 = 1 := by
  obtain ⟨_, r, hr, _, he⟩ := h
  rw [he 0 (by simpa using hr), fredholmDet, fredholmExp]
  simp

/-- **The criterion.**  An entire `L` with `L 0 = 1`, nonvanishing on the disc, whose logarithmic
derivative there is the negative resolvent trace, *is* the regularized determinant of `K`.  This is
the corpus weld `fredholmDet_weld` with the constant pinned at the origin. -/
theorem isRegularizedDet_of_logDeriv_eq {K : ι × ι → ℂ} (hK : IsHS K) {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (hL0 : L 0 = 1) {r : ℝ} (hr : 0 < r) (hrK : r * hsNorm K < 1)
    (hLne : ∀ z ∈ ball (0 : ℂ) r, L z ≠ 0)
    (hmatch : ∀ z ∈ ball (0 : ℂ) r, logDeriv L z = - resolventTrace K z) :
    IsRegularizedDet K L := by
  obtain ⟨c, hc⟩ := fredholmDet_weld hK r hrK L hL.differentiableOn hLne hmatch
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := by simpa using hr
  have hc1 : c = 1 := by
    have := hc 0 h0
    rw [hL0, mul_one] at this
    rw [← this, fredholmDet, fredholmExp]
    simp
  refine ⟨hL, r, hr, hrK, fun z hz => ?_⟩
  rw [hc z hz, hc1, one_mul]

end GaloisForLFunctions.HTGeometry
