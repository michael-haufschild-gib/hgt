import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.Basic

/-!
# The boundary-layer coherence collapses to a normalized ground Fourier overlap

On a locked-floor boundary branch the three ingredients of the source coherence have exact
schedules in the layer parameter: the numerator is `δ⁻¹ c^k G (1 + o(1))`, the real-vector norm is
`δ⁻¹ H (1 + o(1))`, and the anchor norm is either `B/(ρ c²) (1 + o(1))` (odd-leading) or a finite
constant (even-leading).  Every power of `c` and every factor of the branch coefficient cancels in
the normalized quotient

`C = num² / (anc · vec)`,

leaving exactly `|G|²/(B H)` on the odd branch and `|G|²/(ρ A H)` on the even branch.  The
cancellation is an algebraic identity valid at each fixed layer parameter, so the limit needs no
uniformity beyond the three schedules themselves.

Consequently the boundary-layer obstruction is a near-zero problem for the single ground overlap
`G`: wherever `G` and the real-vector scale stay away from zero, the coherence has a positive floor.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The normalized source coherence built from a numerator and the two norms. -/
def coherenceQuotient (num anc vec : ℝ) : ℝ := num ^ (2 : ℕ) / (anc * vec)

/-! ## The exact cancellation -/

/-- The odd-leading cancellation identity: every power of the layer parameter and the branch
coefficient cancel out of the normalized quotient. -/
theorem coherenceQuotient_odd_factor {s : ℕ} {ρ c δ num anc vec : ℝ}
    (hρ : ρ ≠ 0) (hc : c ≠ 0) (hδ : δ ≠ 0) :
    coherenceQuotient num anc vec
      = (δ * num / c ^ s) ^ (2 : ℕ) * (ρ * c ^ (2 * s + 2) / δ)
          / ((ρ * c ^ (2 : ℕ) * anc) * (δ * vec)) := by
  rw [coherenceQuotient]
  rcases eq_or_ne anc 0 with h | h
  · simp [h]
  rcases eq_or_ne vec 0 with h' | h'
  · simp [h']
  field_simp
  ring

/-- The even-leading cancellation identity. -/
theorem coherenceQuotient_even_factor {r : ℕ} {c δ num anc vec : ℝ}
    (hc : c ≠ 0) (hδ : δ ≠ 0) :
    coherenceQuotient num anc vec
      = (δ * num / c ^ r) ^ (2 : ℕ) * (c ^ (2 * r) / δ) / (anc * (δ * vec)) := by
  rw [coherenceQuotient]
  rcases eq_or_ne anc 0 with h | h
  · simp [h]
  rcases eq_or_ne vec 0 with h' | h'
  · simp [h']
  field_simp
  ring

/-! ## The two boundary-layer limits -/

/-- **`(65)`: the odd-leading boundary layer has coherence limit `|G|²/(B H)`.** -/
theorem tendsto_coherenceQuotient_odd {s : ℕ} {ρ B G H : ℝ} (hB : 0 < B) (hH : 0 < H)
    {δ num anc vec : ℝ → ℝ} (hρ : ρ ≠ 0)
    (hδ : Tendsto (fun c => ρ * c ^ (2 * s + 2) / δ c) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hnum : Tendsto (fun c => δ c * num c / c ^ s) (𝓝[>] (0 : ℝ)) (𝓝 G))
    (hanc : Tendsto (fun c => ρ * c ^ (2 : ℕ) * anc c) (𝓝[>] (0 : ℝ)) (𝓝 B))
    (hvec : Tendsto (fun c => δ c * vec c) (𝓝[>] (0 : ℝ)) (𝓝 H))
    (hδ0 : ∀ᶠ c in 𝓝[>] (0 : ℝ), δ c ≠ 0) :
    Tendsto (fun c => coherenceQuotient (num c) (anc c) (vec c)) (𝓝[>] (0 : ℝ))
      (𝓝 (G ^ (2 : ℕ) / (B * H))) := by
  have hc0 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≠ 0 :=
    eventually_nhdsWithin_of_forall fun c hc => ne_of_gt hc
  have heq : (fun c => (δ c * num c / c ^ s) ^ (2 : ℕ) * (ρ * c ^ (2 * s + 2) / δ c)
      / ((ρ * c ^ (2 : ℕ) * anc c) * (δ c * vec c)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun c => coherenceQuotient (num c) (anc c) (vec c) := by
    filter_upwards [hc0, hδ0] with c hc hδc
    exact (coherenceQuotient_odd_factor (s := s) hρ hc hδc).symm
  refine Tendsto.congr' heq ?_
  have hlim : Tendsto (fun c => (δ c * num c / c ^ s) ^ (2 : ℕ) * (ρ * c ^ (2 * s + 2) / δ c)
      / ((ρ * c ^ (2 : ℕ) * anc c) * (δ c * vec c))) (𝓝[>] (0 : ℝ))
      (𝓝 (G ^ (2 : ℕ) * 1 / (B * H))) :=
    ((hnum.pow 2).mul hδ).div (hanc.mul hvec) (by positivity)
  simpa using hlim

/-- **`(66)`: the even-leading boundary layer has coherence limit `|G|²/(ρ A H)`.** -/
theorem tendsto_coherenceQuotient_even {r : ℕ} {ρ A G H : ℝ} (hA : 0 < A) (hH : 0 < H)
    (hρ : 0 < ρ) {δ num anc vec : ℝ → ℝ}
    (hδ : Tendsto (fun c => c ^ (2 * r) / δ c) (𝓝[>] (0 : ℝ)) (𝓝 ρ⁻¹))
    (hnum : Tendsto (fun c => δ c * num c / c ^ r) (𝓝[>] (0 : ℝ)) (𝓝 G))
    (hanc : Tendsto anc (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hvec : Tendsto (fun c => δ c * vec c) (𝓝[>] (0 : ℝ)) (𝓝 H))
    (hδ0 : ∀ᶠ c in 𝓝[>] (0 : ℝ), δ c ≠ 0) :
    Tendsto (fun c => coherenceQuotient (num c) (anc c) (vec c)) (𝓝[>] (0 : ℝ))
      (𝓝 (G ^ (2 : ℕ) / (ρ * A * H))) := by
  have hc0 : ∀ᶠ c in 𝓝[>] (0 : ℝ), c ≠ 0 :=
    eventually_nhdsWithin_of_forall fun c hc => ne_of_gt hc
  have heq : (fun c => (δ c * num c / c ^ r) ^ (2 : ℕ) * (c ^ (2 * r) / δ c)
      / (anc c * (δ c * vec c)))
      =ᶠ[𝓝[>] (0 : ℝ)] fun c => coherenceQuotient (num c) (anc c) (vec c) := by
    filter_upwards [hc0, hδ0] with c hc hδc
    exact (coherenceQuotient_even_factor (r := r) hc hδc).symm
  refine Tendsto.congr' heq ?_
  have hlim : Tendsto (fun c => (δ c * num c / c ^ r) ^ (2 : ℕ) * (c ^ (2 * r) / δ c)
      / (anc c * (δ c * vec c))) (𝓝[>] (0 : ℝ)) (𝓝 (G ^ (2 : ℕ) * ρ⁻¹ / (A * H))) :=
    ((hnum.pow 2).mul hδ).div (hanc.mul hvec) (by positivity)
  have hval : G ^ (2 : ℕ) * ρ⁻¹ / (A * H) = G ^ (2 : ℕ) / (ρ * A * H) := by
    field_simp
  rwa [hval] at hlim

/-! ## The coherence floor -/

/-- **The ground Fourier bottleneck.**  A nonvanishing ground overlap gives a positive coherence
floor throughout the boundary layer. -/
theorem eventually_coherenceQuotient_pos {L : ℝ} (hL : 0 < L)
    {f : ℝ → ℝ} (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ), L / 2 < f c := by
  exact hf.eventually (eventually_gt_nhds (by linarith))

end RHTower
