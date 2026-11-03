import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheFrozenFormGluesTwoWindows

/-!
# The frozen two-collar form in closed form

On a stage test `x_L + y + x_R` of stage `n` (collars `[−log n − ε, −log n]`, `[−ε, 0]`, interior
`[−log n, −ε]`) the frozen two-collar form is (`frozenTwoCollar_eq_transmitted`)

`F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L), ν(y)⟩ + ⟨μ(y), ν(x_R)⟩ + ⟨μ(x_L), ν(x_R)⟩)
      − 2Σ_{m < n} Λ(m)m^{−1/2} (⟨x_L, τ_m y⟩ + ⟨y, τ_m x_R⟩)`,

`⟨f, τ_m g⟩ = ∫ f(u) g(u + log m)`: the interior receives from each collar exactly its
**trivial-divisor moments** and its **transports by the earlier folds**. The archimedean place and the
pole enter only through the moments; the arithmetic of the frozen datum only through the folds
`m < n`; the new fold `n` only through `⟨x_L, τ_n x_R⟩`.

* **First stage** (`n = 2`, `firstStage_frozenTwoCollar_eq`): no fold precedes `2`, so
  `F = Q(x_L) + Q(y) + Q(x_R) + 2(⟨μ(x_L), ν(y)⟩ + ⟨μ(y), ν(x_R)⟩ + ⟨μ(x_L), ν(x_R)⟩)` and
  `F − Q(x_L) − Q(x_R)` depends on the collars only through their moment sequences
  (`firstStage_frozen_congr`): the two-collar complement `inf_y F` is
  `Q(x_L) + Q(x_R) + Φ_ε(μ(x_L), ν(x_R))` for one function `Φ_ε` of the moments.
* **Second stage** (`n = 3`, `secondStage_frozenTwoCollar_eq`): the fold `T₂` is the only earlier
  fold, `F = (first-stage expression) − 2w₂(⟨x_L, τ₂ y⟩ + ⟨y, τ₂ x_R⟩)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology RHTower
open scoped Real

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

open SpacingScaleHarmonicAnalysis

variable {a : ℝ} {f g : ℝ → ℝ}

/-- An ordered pair seeing no lag `log m` with `m ≥ n` couples through the moments and the folds
`m < n`. -/
theorem orderedCoupling_eq_of_lags (hfg : OrderedAt a f g) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {n : ℕ}
    (hlag : ∀ m : ℕ, n ≤ m → crossCorr f g (Real.log m) = 0) :
    orderedCoupling f g = momentPairing f g -
      ∑ m ∈ Finset.range n, vonMangoldtAtom m * crossCorr f g (Real.log m) := by
  rw [orderedCoupling, hfg.integral_collarKernel_mul_eq_moments hf hfc hg hgc, momentPairing]
  congr 1
  refine tsum_eq_sum fun m hm => ?_
  rw [hlag m (by simpa using hm), mul_zero]

/-- **The frozen two-collar form transmits moments and earlier folds.** -/
theorem frozenTwoCollar_eq_transmitted {n : ℕ} (hn : 2 ≤ n) {ε : ℝ}
    (hεn : Real.log n + ε < Real.log (n + 1)) {xL y xR : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hL : ∀ u, u ∉ Icc (-Real.log n - ε) (-Real.log n) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log n) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    frozenTwoCollar xL y xR =
      weilQuad xL + weilQuad y + weilQuad xR +
        2 * (momentPairing xL y + momentPairing y xR + momentPairing xL xR) -
        2 * ∑ m ∈ Finset.range n, vonMangoldtAtom m *
          (crossCorr xL y (Real.log m) + crossCorr y xR (Real.log m)) := by
  have hεl := stage_eps_lt_log hn hεn
  have oLI : OrderedAt (-Real.log n) xL y :=
    ⟨fun u hu => hL u fun hm => by linarith [hm.2], fun u hu => hI u fun hm => by linarith [hm.1]⟩
  have oIR : OrderedAt (-ε) y xR :=
    ⟨fun u hu => hI u fun hm => by linarith [hm.2], fun u hu => hR u fun hm => by linarith [hm.1]⟩
  have cL := hasCompactSupport_of_vanish_off_Icc hL
  have cI := hasCompactSupport_of_vanish_off_Icc hI
  have cR := hasCompactSupport_of_vanish_off_Icc hR
  have hlog : ∀ m : ℕ, n ≤ m → Real.log n ≤ Real.log m := fun m hm =>
    Real.log_le_log (by have h2 : (2 : ℝ) ≤ n := (by exact_mod_cast hn); linarith)
      (by exact_mod_cast hm)
  have e1 := weilQuad_add_of_ordered oLI hxL cL hy cI
  have e2 := weilQuad_add_of_ordered oIR hy cI hxR cR
  rw [orderedCoupling_eq_of_lags oLI hxL cL hy cI (n := n) fun m hm =>
    crossCorr_eq_zero_of_lag hxL.continuous hy.continuous hL hI (Or.inr (by
      have := hlog m hm; linarith))] at e1
  rw [orderedCoupling_eq_of_lags oIR hy cI hxR cR (n := n) fun m hm =>
    crossCorr_eq_zero_of_lag hy.continuous hxR.continuous hI hR (Or.inr (by
      have := hlog m hm; linarith))] at e2
  unfold frozenTwoCollar
  have hs : ∑ m ∈ Finset.range n, vonMangoldtAtom m *
      (crossCorr xL y (Real.log m) + crossCorr y xR (Real.log m)) =
      (∑ m ∈ Finset.range n, vonMangoldtAtom m * crossCorr xL y (Real.log m)) +
        ∑ m ∈ Finset.range n, vonMangoldtAtom m * crossCorr y xR (Real.log m) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [e1, e2, hs]
  ring

/-- **First stage in closed form**: at `n = 2` the frozen form reads only `Q` of the pieces and the
trivial-divisor moments. -/
theorem firstStage_frozenTwoCollar_eq {ε : ℝ}
    (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1)) {xL y xR : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hL : ∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    frozenTwoCollar xL y xR =
      weilQuad xL + weilQuad y + weilQuad xR +
        2 * (momentPairing xL y + momentPairing y xR + momentPairing xL xR) := by
  rw [frozenTwoCollar_eq_transmitted le_rfl hεn hxL hy hxR hL hI hR]
  have : ∑ m ∈ Finset.range 2, vonMangoldtAtom m *
      (crossCorr xL y (Real.log m) + crossCorr y xR (Real.log m)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [vonMangoldtAtom_eq_zero_of_lt_two (by simpa using hm), zero_mul]
  rw [this, mul_zero, sub_zero]

/-- **The first-stage frozen form sees the collars only through `Q` and their moments**: collar data
with equal moment sequences give the same frozen form up to their own `Q`. -/
theorem firstStage_frozen_congr {ε : ℝ}
    (hεn : Real.log (2 : ℕ) + ε < Real.log ((2 : ℕ) + 1)) {xL xL' y xR xR' : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hxL' : ContDiff ℝ 2 xL') (hy : ContDiff ℝ 2 y)
    (hxR : ContDiff ℝ 2 xR) (hxR' : ContDiff ℝ 2 xR')
    (hL : ∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL u = 0)
    (hL' : ∀ u, u ∉ Icc (-Real.log (2 : ℕ) - ε) (-Real.log (2 : ℕ)) → xL' u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log (2 : ℕ)) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) (hR' : ∀ u, u ∉ Icc (-ε) 0 → xR' u = 0)
    (hμ : leftMoment xL = leftMoment xL') (hν : rightMoment xR = rightMoment xR') :
    frozenTwoCollar xL y xR - weilQuad xL - weilQuad xR =
      frozenTwoCollar xL' y xR' - weilQuad xL' - weilQuad xR' := by
  rw [firstStage_frozenTwoCollar_eq hεn hxL hy hxR hL hI hR,
    firstStage_frozenTwoCollar_eq hεn hxL' hy hxR' hL' hI hR']
  simp only [momentPairing, hμ, hν]
  ring

/-- **Second stage in closed form**: at `n = 3` the only earlier fold is `T₂`. -/
theorem secondStage_frozenTwoCollar_eq {ε : ℝ}
    (hεn : Real.log (3 : ℕ) + ε < Real.log ((3 : ℕ) + 1)) {xL y xR : ℝ → ℝ}
    (hxL : ContDiff ℝ 2 xL) (hy : ContDiff ℝ 2 y) (hxR : ContDiff ℝ 2 xR)
    (hL : ∀ u, u ∉ Icc (-Real.log (3 : ℕ) - ε) (-Real.log (3 : ℕ)) → xL u = 0)
    (hI : ∀ u, u ∉ Icc (-Real.log (3 : ℕ)) (-ε) → y u = 0)
    (hR : ∀ u, u ∉ Icc (-ε) 0 → xR u = 0) :
    frozenTwoCollar xL y xR =
      weilQuad xL + weilQuad y + weilQuad xR +
        2 * (momentPairing xL y + momentPairing y xR + momentPairing xL xR) -
        2 * vonMangoldtAtom 2 * (crossCorr xL y (Real.log 2) + crossCorr y xR (Real.log 2)) := by
  rw [frozenTwoCollar_eq_transmitted (by norm_num) hεn hxL hy hxR hL hI hR]
  have : ∑ m ∈ Finset.range 3, vonMangoldtAtom m *
      (crossCorr xL y (Real.log m) + crossCorr y xR (Real.log m)) =
      vonMangoldtAtom 2 * (crossCorr xL y (Real.log 2) + crossCorr y xR (Real.log 2)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : 0 < 2),
      vonMangoldtAtom_eq_zero_of_lt_two (by norm_num : 1 < 2)]
    push_cast
    ring
  rw [this]
  ring

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
