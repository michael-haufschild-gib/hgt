import GaloisForLFunctions.GrowingWindowsOfSpecZ.ForbiddingLatticeZeroModesIsRH

/-!
# RH is decided on two sites

The lattice evolution of Spec ℤ is positive at every index iff RH holds
(`riemannHypothesis_iff_levinsonErr_pos`). Its first index already decides:

* **Strict orbit Cauchy–Schwarz** (`abs_weilOrbitCorr_lt`): under RH, `|c_φ(t)| < Q(φ)` for every
  nonzero bump and every `t ≠ 0`; the two-site margin is `E_1 = (Q(φ)² − c_φ(h)²)/Q(φ)`.
* **Off RH it is an equality** (`exists_abs_weilOrbitCorr_eq`): a short generic bump `ψ` and a step
  `s > 0` have `0 < Q(ψ)` and `|c_ψ(s)| = Q(ψ)`, from the exact two-site degeneration of
  `exists_degenerate_lattice_of_not_riemannHypothesis`.
* **RH on two sites** (`riemannHypothesis_iff_abs_weilOrbitCorr_lt`,
  `riemannHypothesis_iff_two_site_posDef`): RH holds iff the orbit correlation of every nonzero bump
  stays strictly below its value at `0`, iff every two-site lattice window is positive definite.

A first failure of Spec ℤ, if it exists, is therefore realized on two sites: its zero mode
`(1, ∓1)` has no interior, and the degenerate window is the curve with the single angle `±1`
(`degenerate_window_is_curve` at `n = 0`). Unique continuation across interior gaps, which fails
structurally (`curveThree_first_critical`), is not needed to decide RH: the interior of a window never
carries the first failure that matters.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis

variable {φ : ℝ → ℝ}

/-- The two-site margin as a difference of squares. -/
theorem levinsonErr_one_mul (φ : ℝ → ℝ) (h : ℝ) (hQ : weilQuad φ ≠ 0) :
    levinsonErr (weilSeq φ h) 1 * weilQuad φ = weilQuad φ ^ 2 - weilOrbitCorr φ h ^ 2 := by
  rw [levinsonErr_one]
  field_simp

/-- **Strict orbit Cauchy–Schwarz** (under RH): `|c_φ(t)| < Q(φ)` for `φ ≠ 0`, `t ≠ 0`. -/
theorem abs_weilOrbitCorr_lt (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    {t : ℝ} (ht : t ≠ 0) : |weilOrbitCorr φ t| < weilQuad φ := by
  -- reduce to `t > 0` by evenness
  wlog htp : 0 < t generalizing t
  · have := this (neg_ne_zero.mpr ht) (by
      rcases lt_or_gt_of_ne ht with h | h
      · linarith
      · exact absurd h htp)
    rwa [weilOrbitCorr_neg] at this
  have hpos := riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 t htp
  have hQ : 0 < weilQuad φ := by
    have := hpos 0
    rwa [levinsonErr_zero, weilSeq, latticeTranslate_zero] at this
  have h1 := levinsonErr_one_mul φ t hQ.ne'
  have hsq : weilOrbitCorr φ t ^ 2 < weilQuad φ ^ 2 := by nlinarith [hpos 1]
  exact abs_lt_of_sq_lt_sq hsq hQ.le

/-- **Off RH the orbit Cauchy–Schwarz inequality is an equality** for some short bump and step. -/
theorem exists_abs_weilOrbitCorr_eq (hRH : ¬ RiemannHypothesis) :
    ∃ ψ ∈ realTests, ψ ≠ 0 ∧ ∃ s : ℝ, 0 < s ∧ 0 < weilQuad ψ ∧
      |weilOrbitCorr ψ s| = weilQuad ψ := by
  obtain ⟨ψ, hψ, hψ0, s, hs, hpd, h0⟩ := exists_degenerate_lattice_of_not_riemannHypothesis hRH
  have hQ : 0 < weilQuad ψ := by
    have := hpd (fun _ => 1) fun h => one_ne_zero (congrFun h 0)
    simp only [toeplitzForm, Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, sub_self, mul_one,
      weilSeq, latticeTranslate_zero] at this
    exact this
  refine ⟨ψ, hψ, hψ0, s, hs, hQ, ?_⟩
  have h1 := levinsonErr_one_mul ψ s hQ.ne'
  rw [h0, zero_mul] at h1
  have hsq : weilOrbitCorr ψ s ^ 2 = weilQuad ψ ^ 2 := by linarith
  rw [← abs_of_pos hQ]
  exact sq_eq_sq_iff_abs_eq_abs _ _ |>.mp hsq

/-- **RH is strict orbit Cauchy–Schwarz**: RH holds iff `|c_φ(t)| < Q(φ)` for every nonzero bump
`φ` and every `t ≠ 0`. -/
theorem riemannHypothesis_iff_abs_weilOrbitCorr_lt :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 → ∀ t : ℝ, t ≠ 0 → |weilOrbitCorr φ t| < weilQuad φ := by
  refine ⟨fun hRH φ hφ hφ0 t ht => abs_weilOrbitCorr_lt hRH hφ hφ0 ht, fun H => ?_⟩
  by_contra hRH
  obtain ⟨ψ, hψ, hψ0, s, hs, -, heq⟩ := exists_abs_weilOrbitCorr_eq hRH
  exact (H ψ hψ hψ0 s hs.ne').ne heq

/-- **RH is two-site positivity**: RH holds iff every two-site lattice window of every nonzero bump is
positive definite. -/
theorem riemannHypothesis_iff_two_site_posDef :
    RiemannHypothesis ↔ ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h → ToeplitzPosDef (weilSeq φ h) 2 := by
  refine ⟨fun hRH φ hφ hφ0 h hh => (toeplitzForm_posDef_iff (weilSeq_isEven φ h) 1).mpr
    fun k _ => riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh k, fun H => ?_⟩
  by_contra hRH
  obtain ⟨ψ, hψ, hψ0, s, hs, -, h0⟩ := exists_degenerate_lattice_of_not_riemannHypothesis hRH
  have := (toeplitzForm_posDef_iff (weilSeq_isEven ψ s) 1).mp (H ψ hψ hψ0 s hs) 1 le_rfl
  exact this.ne' h0

end GaloisForLFunctions.GrowingWindowsOfSpecZ
