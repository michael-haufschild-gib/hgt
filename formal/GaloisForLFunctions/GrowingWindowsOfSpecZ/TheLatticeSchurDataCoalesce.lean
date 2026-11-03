import GaloisForLFunctions.GrowingWindowsOfSpecZ.ForbiddingLatticeZeroModesIsRH

/-!
# Lattice Schur data coalesce under refinement

What survives the continuum limit `h → 0` of the lattice canonical system? Not the Schur parameters at
a fixed index:

* **The first reflection coefficient tends to `1`** (`tendsto_reflCoeff_zero`): `γ_0(φ, h) = c(h)/c(0)`
  and the orbit correlation is continuous, so `γ_0(φ, h) → 1` as `h → 0`, for every bump with
  `Q(φ) ≠ 0`.
* **Every fixed-index margin vanishes** (`tendsto_levinsonErr_one`, `tendsto_levinsonErr_of_rh`):
  `E_1(φ, h) → 0`, and under RH `E_n(φ, h) → 0` as `h → 0` for every `n ≥ 1`: translates at a fixed
  number of sites coalesce and the lattice window degenerates.

So a continuous Schur function of Weil's distribution is not a pointwise limit of lattice Schur
parameters at fixed index; the invariant that converges is the margin at fixed total length
(`tendsto_levinsonErr_dyadic_contMargin`), where the number of sites grows as the step shrinks. The
continuum canonical system is the limit of the lattice systems along fixed total length, and only
there.
-/

noncomputable section

open Filter Topology Set

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

variable {φ : ℝ → ℝ}

/-- The first reflection coefficient is the normalized orbit correlation: `γ_0 = c(h)/c(0)`. -/
theorem reflCoeff_zero_eq (φ : ℝ → ℝ) (h : ℝ) :
    reflCoeff (weilSeq φ h) 0 = weilOrbitCorr φ h / weilQuad φ := by
  have h0 : weilSeq φ h 0 = weilQuad φ := by rw [weilSeq, latticeTranslate_zero]; rfl
  have hs : schurParam (weilSeq φ h) 0 = weilOrbitCorr φ h := by
    simp only [schurParam, schurCoupling, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      Nat.cast_zero, zero_add]
    exact weilSeq_one φ h
  rw [reflCoeff, hs, levinsonErr_zero, h0]

/-- `c(0) = Q(φ)`. -/
theorem weilOrbitCorr_zero (φ : ℝ → ℝ) : weilOrbitCorr φ 0 = weilQuad φ := by
  show weilPair (scaleShift 0 φ) φ = weilQuad φ
  rw [scaleShift_zero]; rfl

/-- **The first reflection coefficient tends to `1` under refinement.** -/
theorem tendsto_reflCoeff_zero (hφ : φ ∈ realTests) (hQ : weilQuad φ ≠ 0) :
    Tendsto (fun h => reflCoeff (weilSeq φ h) 0) (𝓝 0) (𝓝 1) := by
  have hc := (continuous_weilOrbitCorr hφ).tendsto 0
  rw [weilOrbitCorr_zero] at hc
  have := hc.div_const (weilQuad φ)
  rw [div_self hQ] at this
  simpa only [reflCoeff_zero_eq] using this

/-- **The two-site margin vanishes under refinement**: `E_1(φ, h) → 0` as `h → 0`. -/
theorem tendsto_levinsonErr_one (hφ : φ ∈ realTests) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) 1) (𝓝 0) (𝓝 0) := by
  have hc := (continuous_weilOrbitCorr hφ).tendsto 0
  rw [weilOrbitCorr_zero] at hc
  have := (tendsto_const_nhds (x := weilQuad φ)).sub ((hc.pow 2).div_const (weilQuad φ))
  rw [show weilQuad φ - weilQuad φ ^ 2 / weilQuad φ = 0 by
    rcases eq_or_ne (weilQuad φ) 0 with h | h
    · rw [h]; ring
    · field_simp; ring] at this
  simpa only [levinsonErr_one] using this

/-- **Under RH every fixed-index margin vanishes under refinement**: `E_n(φ, h) → 0` as `h → 0⁺` for
every `n ≥ 1`. -/
theorem tendsto_levinsonErr_of_rh (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) n) (𝓝[>] 0) (𝓝 0) := by
  have hpos : ∀ h : ℝ, 0 < h → ∀ m, 0 < levinsonErr (weilSeq φ h) m := fun h hh m =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh m
  have h1 := (tendsto_levinsonErr_one hφ).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hpos h hh n).le
  · filter_upwards [self_mem_nhdsWithin] with h hh
    -- the margins decrease in the number of sites
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simp
    | succ k ih =>
      exact (levinsonErr_succ_le (hpos h hh _)).trans (ih (by omega))

end GaloisForLFunctions.GrowingWindowsOfSpecZ
