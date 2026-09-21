import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthAntiHermitianKernel

/-!
# FZZ-P ordered-source orientation law

At infinite depth the physical FZZ-P source is ordered.  Before taking that
limit, this leaf gives the exact finite law: orientation consists of two and
only two source terms—the anti-Hermitian depth current and the defect of
exchanging the ordered depth domain.  Thus order is a source datum, not an
analytic bookkeeping choice.

Proof-chain role:
`literal covariance + ordered source support -> anti-Hermitian/current-domain
decomposition -> source-fixed Ward orientation -> FZZ-P`.
-/

open Complex
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exchange of the two source coupling depths. -/
def fzzRadialCouplingDepthExchange (T : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) :=
  T.image (fun uv => (uv.2, uv.1))

/-- Finite ordered source accumulation of literal neutral cross-depth covariance. -/
def fzzRadialCouplingFiniteOrderedKernel
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ) : ℂ :=
  ∑ uv ∈ T, K uv.1 uv.2 *
    fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p

/-- Orientation created solely by failure of the depth domain to be exchange-stable. -/
def fzzRadialCouplingDepthOrderDefect
    (T : Finset (ℝ × ℝ)) (L : ℝ → ℝ → ℂ) : ℂ :=
  (∑ uv ∈ T, L uv.1 uv.2) -
    ∑ uv ∈ fzzRadialCouplingDepthExchange T, L uv.1 uv.2

private theorem depthExchange_injective :
    Set.InjOn (fun uv : ℝ × ℝ => (uv.2, uv.1)) Set.univ := by
  rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨h.2, h.1⟩

/-- Conjugating an ordered source transports it to the exchanged depth domain. -/
theorem star_fzzRadialCouplingFiniteOrderedKernel
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    star (fzzRadialCouplingFiniteOrderedKernel T K v p) =
      ∑ uv ∈ fzzRadialCouplingDepthExchange T,
        star (K uv.2 uv.1) *
          fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p := by
  classical
  unfold fzzRadialCouplingFiniteOrderedKernel fzzRadialCouplingDepthExchange
  change (starRingEnd ℂ) (∑ uv ∈ T, K uv.1 uv.2 *
    fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) = _
  simp only [map_sum, map_mul, starRingEnd_apply,
    star_fzzRadialCouplingCrossDepthCoherence]
  rw [Finset.sum_image]
  · intro a ha b hb hab
    exact depthExchange_injective (Set.mem_univ _) (Set.mem_univ _) hab

/-- Exact ordered-source decomposition.  Every finite FZZ-P orientation is
the sum of an anti-Hermitian source pairing and an exchange-order defect. -/
theorem fzzRadialCouplingFiniteOrderedKernel_sub_star
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    fzzRadialCouplingFiniteOrderedKernel T K v p -
        star (fzzRadialCouplingFiniteOrderedKernel T K v p) =
      (∑ uv ∈ T,
        fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
          fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) +
        fzzRadialCouplingDepthOrderDefect T (fun u₁ u₂ =>
          star (K u₂ u₁) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) := by
  classical
  rw [star_fzzRadialCouplingFiniteOrderedKernel]
  let P : ℂ := ∑ uv ∈ T, K uv.1 uv.2 *
    fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p
  let Q : ℂ := ∑ uv ∈ T, star (K uv.2 uv.1) *
    fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p
  let R : ℂ := ∑ uv ∈ fzzRadialCouplingDepthExchange T,
    star (K uv.2 uv.1) *
      fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p
  have hpair : P - Q = ∑ uv ∈ T,
      fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
        fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p := by
    dsimp only [P, Q]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro uv huv
    unfold fzzRadialCouplingDepthAntiHermitian
    ring
  change P - R = _
  rw [show P - R = (P - Q) + (Q - R) by ring, hpair]
  rfl

/-- The ordered Ward orientation is exactly the imaginary part of its two
source currents. -/
theorem fzzRadialCouplingFiniteOrderedKernel_twice_im
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    2 * (fzzRadialCouplingFiniteOrderedKernel T K v p).im =
      ((∑ uv ∈ T,
        fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
          fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) +
        fzzRadialCouplingDepthOrderDefect T (fun u₁ u₂ =>
          star (K u₂ u₁) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p)).im := by
  rw [← fzzRadialCouplingFiniteOrderedKernel_sub_star]
  change 2 * (fzzRadialCouplingFiniteOrderedKernel T K v p).im =
    (fzzRadialCouplingFiniteOrderedKernel T K v p).im -
      -(fzzRadialCouplingFiniteOrderedKernel T K v p).im
  ring

/-- Exchange-stable Hermitian finite sources are orientation-blind. -/
theorem fzzRadialCouplingFiniteOrderedKernel_im_eq_zero_of_exchangeHermitian
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ)
    (hT : fzzRadialCouplingDepthExchange T = T)
    (hK : ∀ u₁ u₂, K u₁ u₂ = star (K u₂ u₁)) :
    (fzzRadialCouplingFiniteOrderedKernel T K v p).im = 0 := by
  classical
  have hanti (uv : ℝ × ℝ) :
      fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
        fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p = 0 := by
    unfold fzzRadialCouplingDepthAntiHermitian
    rw [hK]
    ring
  have hsum : (∑ uv ∈ T,
      fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
        fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) = 0 := by
    apply Finset.sum_eq_zero
    intro uv huv
    exact hanti uv
  have horder : fzzRadialCouplingDepthOrderDefect T (fun u₁ u₂ =>
      star (K u₂ u₁) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p) = 0 := by
    unfold fzzRadialCouplingDepthOrderDefect
    rw [hT]
    ring
  have h := fzzRadialCouplingFiniteOrderedKernel_twice_im T K v p
  rw [hsum, horder] at h
  norm_num at h
  linarith

/-- Exact finite FZZ-P criterion: orientation survives precisely when the
combined anti-Hermitian and order currents have nonzero imaginary pairing. -/
theorem fzzRadialCouplingFiniteOrderedKernel_im_ne_zero_iff
    (T : Finset (ℝ × ℝ)) (K : ℝ → ℝ → ℂ) (v p : ℝ) :
    (fzzRadialCouplingFiniteOrderedKernel T K v p).im ≠ 0 ↔
      ((∑ uv ∈ T,
        fzzRadialCouplingDepthAntiHermitian K uv.1 uv.2 *
          fzzRadialCouplingCrossDepthCoherence uv.1 uv.2 v p) +
        fzzRadialCouplingDepthOrderDefect T (fun u₁ u₂ =>
          star (K u₂ u₁) * fzzRadialCouplingCrossDepthCoherence u₁ u₂ v p)).im ≠ 0 := by
  rw [← fzzRadialCouplingFiniteOrderedKernel_twice_im]
  constructor
  · intro h hzero
    apply h
    linarith
  · intro h hzero
    apply h
    rw [hzero]
    ring

end

end GaloisForLFunctions.RHTower
