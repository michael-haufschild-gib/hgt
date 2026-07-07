/-
The whole-loop closure: the band-edge pairing discharged by the winding integer, its parity the
enclosed order's — with the endpoint orientations removed entirely.

Two facts compose.  The incidence carrier's band-edge events on a lateral edge whose phase advances a
whole number of turns come in an even number and carry paired flux with no endpoint-orientation
hypothesis (`exists_incidence_edge_events_fluxPaired_of_wind`): the steerable endpoint datum is gone.
And that same winding integer has the parity of the enclosed order
(`arcWinding_parity_eq_enclosedOrder`): the deck class read as `(−1)^k` and as `deckRed 2 (Σ m)`
agree, so `k ≡ Σ m (mod 2)`.

The two windings are the one integer: the phase advance of the carrier `−Λ₂/Λ₁` across the edge and
the two-arc winding mismatch of a logarithm of the member differ only by the anchor's contribution,
which is monodromy-free.  Tying them by that identification, the paired-flux discharge is endpoint-free
and its parity is the enclosed order's — the whole-loop reading in place of the per-edge endpoint
signs the no-go steers.
-/
import GaloisForLFunctions.RHTower.WholeLoopParity
import GaloisForLFunctions.RHTower.WindingBoxCount

open Complex

namespace RHTower

/-- **The whole-loop closure.**  For an enclosed factorization `f = (∏_{i∈s}(·−ρ i)^{m i})·h` on a
ball around `a` with square roots `G₁ G₂` and logarithms `ℓ₁ ℓ₂` on the two annulus charts, and an
incidence carrier `Λ₁ Λ₂` presented in polar form on a lateral edge with strictly monotone continuous
phase, suppose the carrier's phase advance across the edge and the member's two-arc winding mismatch
are the common integer multiple `k·(2π)` of a turn (the identification made by the anchor being
monodromy-free).  Then the forced band-edge events come in an even number and carry paired flux with
no endpoint-orientation hypothesis, and the winding integer `k` has the parity of the enclosed total
order `Σ m`.  The paired-flux interface is discharged by the rigid winding integer, its parity pinned
to the enclosed zero count — the endpoint signs the no-go steers never enter. -/
theorem incidence_wholeLoop_closure {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f h G₁ G₂ ℓ₁ ℓ₂ Λ₁ Λ₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} {σ lo hi : ℝ} {Rmod θ : ℝ → ℝ} {U : Set ℂ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 = f z) (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 = f z)
    (hℓ₁ : AnalyticOnNhd ℂ ℓ₁ (chartRA a r₀ R)) (hℓ₂ : AnalyticOnNhd ℂ ℓ₂ (chartLA a r₀ R))
    (hexp₁ : ∀ z ∈ chartRA a r₀ R, Complex.exp (ℓ₁ z) = f z)
    (hexp₂ : ∀ z ∈ chartLA a r₀ R, Complex.exp (ℓ₂ z) = f z)
    (hab : lo < hi) (hmapU : ∀ τ ∈ Set.Icc lo hi, stripPt σ τ ∈ U)
    (hΛ1ne : ∀ z ∈ U, Λ₁ z ≠ 0)
    (hpolar : ∀ τ ∈ Set.Icc lo hi,
      incidence Λ₁ Λ₂ (stripPt σ τ) = (Rmod τ : ℂ) * Complex.exp ((θ τ : ℝ) * I))
    (hRmod : ∀ τ ∈ Set.Icc lo hi, 0 < Rmod τ)
    (hmono : StrictMonoOn θ (Set.Icc lo hi)) (hθc : ContinuousOn θ (Set.Icc lo hi))
    (hsin : Real.sin (θ lo) ≠ 0)
    {k : ℤ}
    (hwindEdge : θ hi - θ lo = (k : ℝ) * (2 * Real.pi))
    (hwindArc :
      ((ℓ₁ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im - (ℓ₁ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im)
          - ((ℓ₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im
              - (ℓ₂ (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im) = (k : ℝ) * (2 * Real.pi)) :
    (∃ (n : ℕ) (e : Fin n → ℝ), StrictMono e ∧
        (∀ i, e i ∈ Set.Icc lo hi ∧
          pencil Λ₁ Λ₂ ((incidence Λ₁ Λ₂ (stripPt σ (e i))).re : ℂ) 1 (stripPt σ (e i)) = 0) ∧
        Even n ∧ LedgerFluxPaired (List.replicate n 1))
      ∧ Even (k - ((∑ i ∈ s, m i : ℕ) : ℤ)) := by
  refine ⟨exists_incidence_edge_events_fluxPaired_of_wind hab hmapU hΛ1ne hpolar hRmod hmono hθc
      hsin hwindEdge, ?_⟩
  -- the arc winding integer of the member has the enclosed order's parity
  obtain ⟨kA, hwindA, _, hevenA⟩ := arcWinding_parity_eq_enclosedOrder s ρ m h0 hrR hρ hh hh0
    hfact hG₁ hG₂ hpG₁ hpG₂ hℓ₁ hℓ₂ hexp₁ hexp₂
  -- the two winding readings are the same integer
  have hkk : kA = k := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have := hwindA.symm.trans hwindArc
    exact_mod_cast (mul_right_cancel₀ (ne_of_gt h2π) this)
  rwa [hkk] at hevenA

end RHTower
