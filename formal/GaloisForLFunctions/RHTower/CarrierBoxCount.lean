/-
Reading the enclosed off-line order of the completed carrier off a boundary contour integral.

The completed carrier factors as `completedGN N = archFactor · gN`, where the archimedean dressing
`archFactor = s(s−1)/2 · Γ_ℝ(s)` is analytic and zero-free away from `{0,1}` and the `Γ_ℝ` poles.
On a region `U` avoiding those points the Euler head therefore contributes no zeros: every zero of
`completedGN` in `U` is a zero of `gN`.  Peeling `gN`'s finitely many `U`-zeros off a nonvanishing
analytic cofactor and absorbing `archFactor` into it gives
`completedGN N = (∏_{w} (·−w)^{m w}) · (archFactor · h)` with `archFactor · h` analytic and zero-free.

Feeding this factorization to the rectangle zero-count `rectIntegral_logDeriv_boxCount`, the boundary
contour integral of the logarithmic derivative reads off the exact integer total order of the
enclosed off-line zeros: `∮_{∂R} (completedGN)'/(completedGN) = 2πi · Σ_w m w`.  The mod-`n` deck
cocycle sees only `Σ_w m w mod n`; the contour integral recovers the full integer count.
-/
import GaloisForLFunctions.RHTower.RectangleResidue
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Set

namespace RHTower

/-- **The Euler-head cofactor factorization of the completed carrier.**  On an open `U` avoiding the
`Γ_ℝ` poles of both `s` and `1−s` and the trivial points `{0,1}`, whose `gN`-zeros lie in a finite
set `t` of finite order, the completed carrier factors through those zeros with the archimedean
factor absorbed into a nonvanishing analytic cofactor:
`completedGN N = (∏_{w∈t} (·−w)^{m w}) · h`, `m` the vanishing orders, `h = archFactor · (gN cofactor)`. -/
theorem completedGN_offline_factor {N : ℕ} {U : Set ℂ} (hUopen : IsOpen U)
    (hGa : ∀ z ∈ U, Gammaℝ z ≠ 0) (hGb : ∀ z ∈ U, Gammaℝ (1 - z) ≠ 0)
    (hz0 : ∀ z ∈ U, z ≠ 0) (hz1 : ∀ z ∈ U, z ≠ 1)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ U)
    (hzeros : ∀ z ∈ U, gN N z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt (gN N) w ≠ ⊤) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h U ∧ (∀ z ∈ U, h z ≠ 0) ∧
      ∀ z ∈ U, completedGN N z = (∏ w ∈ t, (z - w) ^ m w) * h z := by
  have hgN_an : AnalyticOnNhd ℂ (gN N) U := fun z hz => gN_analyticAt (hGb z hz)
  have harch_an : AnalyticOnNhd ℂ archFactor U := by
    intro z hz
    have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) z :=
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).div_const 2
    exact hpoly.mul (Gammaℝ_analyticAt (hGa z hz))
  obtain ⟨m, hg, hgan, hg0, hgfact⟩ := exists_multi_peel hUopen hgN_an t htU hzeros hord
  refine ⟨m, fun z => archFactor z * hg z, fun z hz => (harch_an z hz).mul (hgan z hz),
    fun z hz => mul_ne_zero (archFactor_ne_zero (hz0 z hz) (hz1 z hz) (hGa z hz)) (hg0 z hz),
    fun z hz => ?_⟩
  rw [completedGN, hgfact z hz]; ring

/-- **The completed carrier's enclosed off-line order is a boundary contour integral.**  For a
rectangle strictly inside a region `U` avoiding the `Γ_ℝ` poles and trivial points, on which the
`gN`-zeros form a finite interior set `t` of finite order, the boundary contour integral of the
logarithmic derivative of `completedGN N` equals `2πi · Σ_{w∈t} m w`, the exact integer total order
of the enclosed off-line zeros.  This gives the box-level zero-count directly, whereas the deck
cocycle recovers only its reduction `Σ_w m w mod n`. -/
theorem completedGN_rectIntegral_logDeriv {N : ℕ} {z₁ z₂ : ℂ} {U : Set ℂ} (hUopen : IsOpen U)
    (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U)
    (hGa : ∀ z ∈ U, Gammaℝ z ≠ 0) (hGb : ∀ z ∈ U, Gammaℝ (1 - z) ≠ 0)
    (hz0 : ∀ z ∈ U, z ≠ 0) (hz1 : ∀ z ∈ U, z ≠ 1)
    (t : Finset ℂ)
    (hin : ∀ w ∈ t, z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im)
    (hzeros : ∀ z ∈ U, gN N z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt (gN N) w ≠ ⊤) :
    ∃ m : ℂ → ℕ, rectIntegral (logDeriv (completedGN N)) z₁ z₂ =
      2 * Real.pi * I * (∑ w ∈ t, (m w : ℂ)) := by
  have htU : ∀ w ∈ t, w ∈ U := fun w hw => by
    obtain ⟨hr1, hr2, hi1, hi2⟩ := hin w hw
    exact hsub (Complex.mem_reProdIm.mpr
      ⟨mem_uIcc.mpr (Or.inl ⟨hr1.le, hr2.le⟩), mem_uIcc.mpr (Or.inl ⟨hi1.le, hi2.le⟩)⟩)
  obtain ⟨m, h, han, h0, hfact⟩ :=
    completedGN_offline_factor hUopen hGa hGb hz0 hz1 t htU hzeros hord
  exact ⟨m, rectIntegral_logDeriv_boxCount t (fun w => w) m hUopen hin hsub han h0 hfact⟩

end RHTower
