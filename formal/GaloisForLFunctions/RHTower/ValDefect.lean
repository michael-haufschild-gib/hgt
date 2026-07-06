import GaloisForLFunctions.RHTower.ValLimit

/-!
# The liminf mean-valuation density and the density–depth defect

Two asymptotic invariants of the mean-valuation density.

The **liminf mean density** `meanValLiminf ∈ ℝ≥0∞` is the eventual floor of the mean 2-adic
valuation over cofinal heights.  A zero-free window is rung-clean, so the density there is set to `⊤`
(no violation); with this normalisation the level-1 rung (every enclosed jump has even order) forces
`meanValE T ≥ 1` at every height, hence `1 ≤ meanValLiminf`: a single line-native invariant whose
positivity is implied by the graded rung.

The **density–depth defect** `defect T = meanVal T − windowDepth T ≥ 0` measures the spread between
the average and the minimal enclosed valuation.  It is nonnegative, and vanishes exactly on the
**equal-order windows** — those whose enclosed jumps all share one 2-adic valuation.  The locus of
such heights is a rigidity object: where it holds the atomic measure is a single-weight counting
measure.
-/

namespace RHTower

open Complex Set Metric Filter
open scoped ENNReal Topology

/-! ## (a) The liminf mean-valuation density -/

/-- The mean-valuation density lifted to `ℝ≥0∞`, with a zero-free (rung-clean) window sent to `⊤`. -/
noncomputable def meanValE (T : ℝ) : ℝ≥0∞ :=
  if ((boxFinset T).image Complex.im).card = 0 then ⊤ else ENNReal.ofReal (meanVal T)

/-- **The level-1 rung floors the density.**  If `V 1 T = 0` (every enclosed jump has even order),
the lifted mean density at `T` is at least `1`. -/
theorem one_le_meanValE_of_V_one_eq_zero {T : ℝ} (h : V 1 T = 0) : 1 ≤ meanValE T := by
  rw [meanValE]
  split_ifs with hcard
  · exact le_top
  · have hne : ((boxFinset T).image Complex.im).Nonempty := by
      rw [← Finset.card_pos]; omega
    have hdepth : (1 : ℕ∞) ≤ windowDepth T := (V_one_eq_zero_iff_one_le_windowDepth T).mp h
    have hmean : (1 : ℚ) ≤ meanVal T := by
      have := le_meanVal_of_le_windowDepth hne (by exact_mod_cast hdepth)
      exact_mod_cast this
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from (ENNReal.ofReal_one).symm]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hmean)

/-- **The liminf mean-valuation density**: the eventual floor of the mean 2-adic valuation over the
heights, a single `ℝ≥0∞` invariant of ξ. -/
noncomputable def meanValLiminf : ℝ≥0∞ := liminf (fun n : ℕ => meanValE (n : ℝ)) atTop

/-- **The level-1 rung forces positive liminf density.**  If `RHLadder 1` holds — every off-line
ξ-zero has even order — then the liminf mean density is at least `1`. -/
theorem one_le_meanValLiminf_of_rhLadder_one (h : RHLadder 1) : 1 ≤ meanValLiminf := by
  refine le_liminf_of_le (h := ?_)
  filter_upwards with n
  exact one_le_meanValE_of_V_one_eq_zero
    (V_eq_zero_of_windowCertificate ((rhLadder_iff_forall_windowCertificate 1).mp h (n : ℝ)))

/-! ## (b) The density–depth defect -/

/-- The window depth as a natural number (`0` on a zero-free window). -/
noncomputable def windowDepthNat (T : ℝ) : ℕ := (windowDepth T).toNat

/-- **The density–depth defect**: the gap between the average and the minimal enclosed valuation. -/
noncomputable def defect (T : ℝ) : ℚ := meanVal T - (windowDepthNat T : ℚ)

/-- **The defect is nonnegative.**  The average valuation is at least the minimal one. -/
theorem defect_nonneg (T : ℝ) : 0 ≤ defect T := by
  rw [defect, sub_nonneg]
  by_cases hne : ((boxFinset T).image Complex.im).Nonempty
  · have hne_top : windowDepth T ≠ ⊤ := ((windowDepth_lt_top_iff T).mpr hne).ne
    have hcoe : (windowDepthNat T : ℕ∞) = windowDepth T := ENat.coe_toNat hne_top
    have := le_meanVal_of_le_windowDepth (k := windowDepthNat T) hne (le_of_eq hcoe)
    exact_mod_cast this
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hcard : ((boxFinset T).image Complex.im).card = 0 := Finset.card_eq_zero.mpr hne
    have hmean : meanVal T = 0 := by rw [meanVal, hcard, Nat.cast_zero, div_zero]
    have hdepth : windowDepthNat T = 0 := by
      rw [windowDepthNat, (windowDepth_eq_top_iff T).mpr ((image_im_eq_empty_iff T).mp hne),
        ENat.toNat_top]
    rw [hmean, hdepth, Nat.cast_zero]

/-- **The defect vanishes exactly on the equal-order windows.**  For a window carrying zeros, the
average valuation equals the minimal one iff every enclosed jump shares the same 2-adic valuation. -/
theorem defect_eq_zero_iff_equalOrder {T : ℝ}
    (hne : ((boxFinset T).image Complex.im).Nonempty) :
    defect T = 0 ↔ ∀ t ∈ (boxFinset T).image Complex.im, filtrationLength t = windowDepthNat T := by
  set s := (boxFinset T).image Complex.im with hs
  have hne_top : windowDepth T ≠ ⊤ := ((windowDepth_lt_top_iff T).mpr hne).ne
  have hcoe : (windowDepthNat T : ℕ∞) = windowDepth T := ENat.coe_toNat hne_top
  have hcardpos : 0 < s.card := Finset.card_pos.mpr hne
  have hcardQ : (s.card : ℚ) ≠ 0 := by exact_mod_cast hcardpos.ne'
  have hle : ∀ t ∈ s, windowDepthNat T ≤ filtrationLength t := by
    intro t ht
    have hx := windowDepth_le_filtrationLength (T := T) ht
    rw [← hcoe] at hx
    exact_mod_cast hx
  have hnat : valMass T = s.card * windowDepthNat T ↔
      ∀ t ∈ s, filtrationLength t = windowDepthNat T := by
    rw [valMass, ← hs, ← smul_eq_mul, ← Finset.sum_const, eq_comm,
      Finset.sum_eq_sum_iff_of_le hle]
    exact forall₂_congr fun t _ => eq_comm
  rw [defect, sub_eq_zero, meanVal, ← hs, div_eq_iff hcardQ, ← hnat]
  constructor
  · intro h
    have : (valMass T : ℚ) = ((s.card * windowDepthNat T : ℕ) : ℚ) := by push_cast; rw [h]; ring
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring

/-- **The equal-order locus**: the heights whose window has all enclosed jumps of one valuation — a
rigidity locus of the atomic measure. -/
def equalOrderLocus : Set ℝ := {T : ℝ | defect T = 0}

end RHTower
