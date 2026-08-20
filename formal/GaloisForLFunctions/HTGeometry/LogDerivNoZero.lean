/-
# A holomorphic logarithmic derivative forbids zeros

If `Y` is analytic on a preconnected open set, does not vanish identically, and satisfies
`Y' = G · Y` with `G` analytic there, then `Y` has no zero at all: at a zero of order `m + 1` the
left side has order `m` while the right side has order at least `m + 1`.
-/
import Mathlib

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **No zeros from a holomorphic logarithmic derivative.** -/
theorem ne_zero_of_deriv_eq_mul {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcon : IsPreconnected Ω)
    {Y G : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y Ω) (hG : AnalyticOnNhd ℂ G Ω)
    (hrel : ∀ z ∈ Ω, deriv Y z = G z * Y z)
    {w : ℂ} (hw : w ∈ Ω) (hYw : Y w ≠ 0) :
    ∀ z ∈ Ω, Y z ≠ 0 := by
  intro z hz hYz
  have hYa : AnalyticAt ℂ Y z := hY z hz
  have hGa : AnalyticAt ℂ G z := hG z hz
  have htop : analyticOrderAt Y z ≠ ⊤ := by
    intro h
    have hev : Y =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp h
    exact hYw (hY.eqOn_zero_of_preconnected_of_eventuallyEq_zero hcon hz hev hw)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hnz : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    exact (hYa.analyticOrderAt_eq_zero.mp hn.symm) hYz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hord : analyticOrderAt Y z = (m : ℕ∞) + 1 := by
    rw [← hn]
    push_cast
    ring
  have hd : analyticOrderAt (deriv Y) z = (m : ℕ∞) := analyticOrderAt_deriv_of_pos hYa hord
  have hfun : deriv Y =ᶠ[𝓝 z] G * Y := by
    filter_upwards [hΩ.mem_nhds hz] with u hu
    exact hrel u hu
  have hd2 : analyticOrderAt (deriv Y) z = analyticOrderAt (G * Y) z :=
    analyticOrderAt_congr hfun
  rw [hd2, analyticOrderAt_mul hGa hYa, hord] at hd
  cases hGord : analyticOrderAt G z with
  | top =>
      rw [hGord] at hd
      simp at hd
  | coe k =>
      rw [hGord] at hd
      have : (k : ℕ∞) + ((m : ℕ∞) + 1) = ((k + m + 1 : ℕ) : ℕ∞) := by push_cast; ring
      rw [this] at hd
      have hkm : k + m + 1 = m := by exact_mod_cast hd
      omega

end GaloisForLFunctions.HTGeometry
