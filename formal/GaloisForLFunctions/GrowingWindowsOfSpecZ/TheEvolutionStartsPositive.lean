import GaloisForLFunctions.GrowingWindowsOfSpecZ.AWindowIsTheUnionOfItsLattices
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.LiouvilleOddWindowRefutationAndSelectiveFullPositivity
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.SinglePrimeWindowJumpGraphAndObstructions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryApplications

/-!
# The evolution starts positive

Every real `C²` test supported in an interval of length `181/250 ≈ 0.724` has Weil energy at least
`‖F‖²/5000` (SPATL `fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths`). For the lattice
canonical system of Spec ℤ this is the unconditional base of the evolution:

* **Short lattices are positive** (`toeplitzPosDef_of_short`, `levinsonErr_pos_of_short`): for a bump
  `φ ≠ 0` supported in `[−r, 0]` and a step `h > 0`, every margin `E_k(φ, h)` with
  `kh + r ≤ 181/250` is positive.
* **Every stage of a short lattice admits its kick** (`abs_schurParam_lt_of_short`): if
  `(m + 1)h + r ≤ 181/250` then `|β_m| < E_m`. Since `log 2 < 181/250`, this covers the stage at
  which the first prime enters every lattice of total length below `181/250`: the kick of `2`
  lands in its prediction interval there. The first open stages are those of total length beyond
  `181/250`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri

variable {φ : ℝ → ℝ} {h r : ℝ}

/-- **Short tests are positive**: a nonzero real test supported in an interval of length at most
`181/250` has positive Weil energy. -/
theorem weilQuad_pos_of_short {G : ℝ → ℝ} (hG : G ∈ realTests) (hG0 : G ≠ 0) {c L : ℝ}
    (hL : L ≤ 181 / 250) (hsupp : ∀ u, u ∉ Icc (c - L) c → G u = 0) : 0 < weilQuad G := by
  -- centre the support at the origin
  set F : ℝ → ℝ := fun x => G (x - (L / 2 - c))
  have hF : F ∈ realTests :=
    ⟨hG.1.comp (contDiff_id.sub contDiff_const), hG.2.comp_homeomorph
      (Homeomorph.addRight (-(L / 2 - c)))⟩
  have hF0 : F ≠ 0 := fun h0 => hG0 (funext fun u => by
    have := congrFun h0 (u + (L / 2 - c))
    simpa [F] using this)
  have hFs : ∀ x, 181 / 500 < |x| → F x = 0 := fun x hx => hsupp _ fun hm => by
    rcases lt_abs.mp hx with hx | hx <;> linarith [hm.1, hm.2]
  have hcoer := SelectivePositivityAndThresholdLaws.fullZeroForm_ge_of_support_le_threeHundredSixtyTwoThousandths
    hF.1 hF.2 hFs
  rw [← LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm hF] at hcoer
  have hpos := integral_sq_pos_of_realTest_ne_zero ⟨F, hF⟩ fun h0 => hF0 (congrArg Subtype.val h0)
  have hQ : weilQuad G = weilPair F F := (weilQuad_comp_sub G (L / 2 - c)).symm
  rw [hQ]
  have : (0 : ℝ) < 1 / 5000 * ∫ x, F x ^ 2 := by positivity
  linarith

/-- **Short lattices are positive definite.** If `nh + r ≤ 181/250`, the lattice window of size
`n + 1` of a nonzero bump supported in `[−r, 0]` is positive definite. -/
theorem toeplitzPosDef_of_short (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    (hsupp : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 < h) {n : ℕ}
    (hlen : n * h + r ≤ 181 / 250) : ToeplitzPosDef (weilSeq φ h) (n + 1) := by
  intro x hx
  rw [← weilQuad_latticeTest hφ h x]
  exact weilQuad_pos_of_short (latticeTest_mem hφ x) (latticeTest_ne_zero hφ hφ0 hh hx) hlen
    fun u hu => latticeTest_eq_zero_of_not_mem hsupp hh.le x hu

/-- **The evolution starts positive**: every margin `E_k(φ, h)` with `kh + r ≤ 181/250` is
positive. -/
theorem levinsonErr_pos_of_short (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    (hsupp : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 < h) {n : ℕ}
    (hlen : n * h + r ≤ 181 / 250) : ∀ k ≤ n, 0 < levinsonErr (weilSeq φ h) k :=
  (toeplitzForm_posDef_iff (weilSeq_isEven φ h) n).mp (toeplitzPosDef_of_short hφ hφ0 hsupp hh hlen)

/-- **Every stage of a short lattice admits its kick**: if `(m + 1)h + r ≤ 181/250`, the newest
datum lies in the prediction interval, `|β_m| < E_m`. -/
theorem abs_schurParam_lt_of_short (hφ : φ ∈ realTests) (hφ0 : φ ≠ 0)
    (hsupp : ∀ y, y ∉ Icc (-r) 0 → φ y = 0) (hh : 0 < h) {m : ℕ}
    (hlen : ((m : ℝ) + 1) * h + r ≤ 181 / 250) :
    |schurParam (weilSeq φ h) m| < levinsonErr (weilSeq φ h) m := by
  have hm1 : (m : ℝ) * h + r ≤ 181 / 250 := by nlinarith
  have hm2 : ((m + 1 : ℕ) : ℝ) * h + r ≤ 181 / 250 := by push_cast; linarith
  exact (posDef_succ_iff_abs_schur_lt (weilSeq_isEven φ h)
    (toeplitzPosDef_of_short hφ hφ0 hsupp hh hm1)).mp
    (toeplitzPosDef_of_short hφ hφ0 hsupp hh hm2)

end GaloisForLFunctions.GrowingWindowsOfSpecZ
