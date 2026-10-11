import GaloisForLFunctions.RHTower.JointAncestryQuasiRHChainExclusion
import GaloisForLFunctions.RHTower.JointAncestryChainFreeHalfPlane

/-!
# The JAS abscissa takes no value in `(0, ½)`

For the positivity abscissa `σ* = jasAbscissa` of the dressed JAS aggregate:

* `σ* = 0 ∨ ½ ≤ σ*` (`jasAbscissa_eq_zero_or_half_le`), so `RH ⟺ σ* < ½`
  (`riemannHypothesis_iff_jasAbscissa_lt_half`);
* under a half-plane bound `Re ρ ≤ ½ + α` with `α < ½`, `σ* = 0 ∨ 1 + δ* ≤ σ*` with
  `δ* = sup |Re ρ − ½|` (`jasAbscissa_eq_zero_or_one_add_sSup_le`);
* consequently `0 < σ* ≤ 1` forces `sup Re ρ = 1`: no half-plane bound `α < ½` holds
  (`riemannHypothesis_or_forall_not_xiZeroHalfPlaneBound_of_jasAbscissa_le_one`).

**Proof.**  If `σ* < ½`, positivity at `σ*` bounds every zero by `Re ρ ≤ ½ + σ*`, a half-plane
bound below `1`.  Under such a bound, off-line chains force `σ* ≥ 1 + δ*`, and so does a farthest
off-line zero; since `σ* ≤ 1`, neither occurs and RH holds.
-/

namespace RHTower

/-- Under a half-plane bound `α < ½`, either RH holds or `σ* ≥ 1 + sup |Re ρ − ½|`. -/
theorem jasAbscissa_eq_zero_or_one_add_sSup_le {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) :
    jasAbscissa = 0 ∨
      1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ jasAbscissa := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl (riemannHypothesis_iff_jasAbscissa_eq_zero.mp hRH)
  right
  by_cases hch : JasOffLineChain
  · exact one_add_sSup_le_of_jasDressedPSD_of_chain halpha0 halpha hXi jasDressedPSD_jasAbscissa hch
  · obtain ⟨q₀, hoff, hmax⟩ := exists_farthest_offLine_of_not_jasOffLineChain hch hRH
    have h := le_jasAbscissa_of_maximal_offLine q₀ hoff hmax
    have hs : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤
        |(q₀.1 : ℂ).re - 1 / 2| :=
      csSup_le (Set.range_nonempty _) (by rintro _ ⟨q, rfl⟩; exact hmax q)
    linarith

/-- **RH ⟺ `σ* < ½`.** -/
theorem riemannHypothesis_iff_jasAbscissa_lt_half : RiemannHypothesis ↔ jasAbscissa < 1 / 2 := by
  constructor
  · intro h
    rw [riemannHypothesis_iff_jasAbscissa_eq_zero.mp h]
    norm_num
  · intro h
    have hXi := xiZeroHalfPlaneBound_of_jasDressedPSD zero_le_jasAbscissa h jasDressedPSD_jasAbscissa
    exact riemannHypothesis_iff_jasDressedPSD_one_and_quasi.mpr
      ⟨jasDressedPSD_iff_jasAbscissa_le.mpr (by linarith), _, zero_le_jasAbscissa, h, hXi⟩

/-- **The abscissa gap.**  `σ* = 0` or `σ* ≥ ½`. -/
theorem jasAbscissa_eq_zero_or_half_le : jasAbscissa = 0 ∨ 1 / 2 ≤ jasAbscissa := by
  rcases lt_or_ge jasAbscissa (1 / 2) with h | h
  · exact Or.inl (riemannHypothesis_iff_jasAbscissa_eq_zero.mp
      (riemannHypothesis_iff_jasAbscissa_lt_half.mpr h))
  · exact Or.inr h

/-- If `σ* ≤ 1`, then RH holds or the zeros accumulate at `Re s = 1`: no half-plane bound
`α < ½` holds. -/
theorem riemannHypothesis_or_forall_not_xiZeroHalfPlaneBound_of_jasAbscissa_le_one
    (h : jasAbscissa ≤ 1) :
    RiemannHypothesis ∨ ∀ alpha : ℝ, alpha < 1 / 2 → ¬ XiZeroHalfPlaneBound alpha := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  intro alpha halpha hXi
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have halpha0 : 0 ≤ alpha := by
    have := hXi _ (xi_xiZeroCopy_eq_zero q)
    linarith
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have hq' : 0 < |(q.1 : ℂ).re - 1 / 2| := abs_pos.mpr (by linarith)
  have hs := le_csSup hbdd ⟨q, rfl⟩
  rcases jasAbscissa_eq_zero_or_one_add_sSup_le halpha0 halpha hXi with h0 | h1
  · exact hRH (riemannHypothesis_iff_jasAbscissa_eq_zero.mpr h0)
  · simp only at hs
    linarith

end RHTower
