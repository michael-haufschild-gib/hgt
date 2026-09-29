import GaloisForLFunctions.HTGeometry.RittPoincareRittForm
import GaloisForLFunctions.HTGeometry.RittTreeChannelLinearizer

/-!
# The exact clock, beta field and Poincaré function of an interior tree channel

For an interior binary channel `−1 < v < u < 1` on a `p`-ary tree (`p ≥ 2`), the belief-propagation
map `R(y) = ((1+uy)^p − (1+vy)^p)/((1+uy)^p + (1+vy)^p)` has multiplier `λ = p(u − v)/2` at the
uninformative message `0`.  Away from the parabolic value `λ = 1`, let `κ` be a linearizer on an open
connected `U ∋ 0` (`κ(R(y)) = q·κ(y)`, `κ(0) = 0`) and `Φ` its inverse on an open connected `V`
(the Schröder function for `λ < 1`, the Poincaré function for `λ > 1`).  Then:

* `κ` satisfies no algebraic differential equation on any nonempty open subset of `U`;
* `Φ` satisfies none on any nonempty open subset of `V`;
* the exact beta field `β = (log λ)·κ/κ'` satisfies none on any open connected subset of `U` where
  `κ` and `κ'` do not vanish.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The exact clock, beta field and conjugacy of an interior tree channel are hypertranscendental.** -/
theorem treeRG_interior_clock_hypertranscendental {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1) (hpar : (p : ℝ) * (u - v) / 2 ≠ 1)
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hVo : IsOpen V)
    (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite) {Φ κ : ℂ → ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U) (hκV : MapsTo κ U V)
    (hΦU : MapsTo Φ V U) (hΦκ : ∀ t ∈ U, Φ (κ t) = t) (hκΦ : ∀ z ∈ V, κ (Φ z) = z)
    (h0U : (0 : ℂ) ∈ U) {q : ℂ} (hq : q ≠ 0)
    (hfe : ∀ᶠ y in 𝓝 (0 : ℂ), κ (((1 + u * y) ^ p - (1 + v * y) ^ p)
      / ((1 + u * y) ^ p + (1 + v * y) ^ p)) = q * κ y) :
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn κ W) ∧
      (∀ W ⊆ V, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn Φ W) ∧
      (∀ W ⊆ U, IsOpen W → IsPreconnected W → W.Nonempty → W.Infinite →
        (∀ t ∈ W, κ t ≠ 0) → (∀ t ∈ W, deriv κ t ≠ 0) →
        ∀ {lamLog : ℂ}, lamLog ≠ 0 → ¬ DifferentiallyAlgebraicOn (rgBeta lamLog κ) W) := by
  -- the derivative of the linearizer at the fixed point
  have h0V : κ 0 ∈ V := hκV h0U
  have hchain : deriv Φ (κ 0) * deriv κ 0 = 1 := by
    have hev : (Φ ∘ κ) =ᶠ[𝓝 0] id := by
      filter_upwards [hUo.mem_nhds h0U] with w hw using hΦκ w hw
    have h1 := Filter.EventuallyEq.deriv_eq hev
    rw [deriv_comp 0 (hΦ _ h0V).differentiableAt (hκ 0 h0U).differentiableAt, deriv_id] at h1
    exact h1
  have hκ' : deriv κ 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hchain
    exact zero_ne_one hchain
  have hκU : ¬ DifferentiallyAlgebraicOn κ U := fun hDA =>
    not_differentiallyAlgebraicOn_linearizer_treeRG_interior hp hv huv hu hpar (hκ 0 h0U) hκ' hq
      hfe (hUo.mem_nhds h0U) hDA
  have hκW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ¬ DifferentiallyAlgebraicOn κ W :=
    fun W hWU hWo hWne hDA => hκU (differentiallyAlgebraicOn_mono_of_isPreconnected hUc hκ hWo hWne
      hWU hDA)
  refine ⟨hκW, fun W hWV hWo hWne hDA => ?_, fun W hWU hWo hWc hWne hWinf hκne hκ'ne lamLog hlam
    hDA => ?_⟩
  · exact hκU (differentiallyAlgebraicOn_of_localInverse hVo hVc hVne hVinf hκ hΦ hΦU hκV hκΦ hΦκ
      (differentiallyAlgebraicOn_mono_of_isPreconnected hVc hΦ hWo hWne hWV hDA))
  · exact hκW W hWU hWo hWne (differentiallyAlgebraicOn_of_rgBeta hWo hWc hWne hWinf
      (hκ.mono hWU) hκne hκ'ne hlam hDA)

end

end GaloisForLFunctions.HTGeometry
