import GaloisForLFunctions.RHTower.SymmetricShiftAnalyticClass
import GaloisForLFunctions.RHTower.DeckChargeInvariant

/-!
# Exact divisor multiplicities under symmetric translation

This leaf upgrades support-level zero transport to an exact analytic-order identity.  It records
the extra multiplicity caused by accidental overlap, proves preservation in the no-overlap case,
and proves exact doubling at the collision parameter.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Exact divisor law for a symmetric translation product. -/
theorem analyticOrderAt_symmetricShiftProduct
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (a : ℝ) (z : ℂ) :
    analyticOrderAt (symmetricShiftProduct F a) z =
      analyticOrderAt F (z + (a : ℂ)) +
        analyticOrderAt F (z - (a : ℂ)) := by
  have hplus : AnalyticAt ℂ (fun w : ℂ => F (w + (a : ℂ))) z :=
    (analyticAt_comp_add_iff F (a : ℂ) z).mpr (hF _ (by simp))
  have hminus : AnalyticAt ℂ (fun w : ℂ => F (w - (a : ℂ))) z := by
    have h := (analyticAt_comp_add_iff F (-(a : ℂ)) z).mpr (hF _ (by simp))
    simpa only [sub_eq_add_neg] using h
  unfold symmetricShiftProduct
  change analyticOrderAt
    ((fun w : ℂ => F (w + (a : ℂ))) * (fun w : ℂ => F (w - (a : ℂ)))) z = _
  rw [analyticOrderAt_mul hplus hminus, analyticOrderAt_comp_add F (a : ℂ) z]
  have horder := analyticOrderAt_comp_add F (-(a : ℂ)) z
  change analyticOrderAt (fun w : ℂ => F (w - (a : ℂ))) z =
    analyticOrderAt F (z - (a : ℂ)) at horder
  rw [horder]

/-- Every original divisor multiplicity survives at both translated locations. -/
theorem analyticOrderAt_le_symmetricShiftProduct_pair
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (a : ℝ) (rho : ℂ) :
    analyticOrderAt F rho ≤
        analyticOrderAt (symmetricShiftProduct F a) (rho + (a : ℂ)) ∧
      analyticOrderAt F rho ≤
        analyticOrderAt (symmetricShiftProduct F a) (rho - (a : ℂ)) := by
  constructor
  · rw [analyticOrderAt_symmetricShiftProduct hF]
    have hargPlus : rho + (a : ℂ) + (a : ℂ) = rho + 2 * (a : ℂ) := by ring
    have hargMinus : rho + (a : ℂ) - (a : ℂ) = rho := by ring
    rw [hargPlus, hargMinus]
    exact le_add_self
  · rw [analyticOrderAt_symmetricShiftProduct hF]
    have hargPlus : rho - (a : ℂ) + (a : ℂ) = rho := by ring
    have hargMinus : rho - (a : ℂ) - (a : ℂ) = rho - 2 * (a : ℂ) := by ring
    rw [hargPlus, hargMinus]
    exact le_self_add

/-- With no accidental translated zero, multiplicity is preserved exactly at both copies. -/
theorem analyticOrderAt_symmetricShiftProduct_pair_eq_of_no_overlap
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (a : ℝ) (rho : ℂ)
    (hplus : F (rho + 2 * (a : ℂ)) ≠ 0)
    (hminus : F (rho - 2 * (a : ℂ)) ≠ 0) :
    analyticOrderAt (symmetricShiftProduct F a) (rho + (a : ℂ)) =
        analyticOrderAt F rho ∧
      analyticOrderAt (symmetricShiftProduct F a) (rho - (a : ℂ)) =
        analyticOrderAt F rho := by
  have hplusOrder : analyticOrderAt F (rho + 2 * (a : ℂ)) = 0 :=
    (hF _ (by simp)).analyticOrderAt_eq_zero.mpr hplus
  have hminusOrder : analyticOrderAt F (rho - 2 * (a : ℂ)) = 0 :=
    (hF _ (by simp)).analyticOrderAt_eq_zero.mpr hminus
  constructor
  · rw [analyticOrderAt_symmetricShiftProduct hF]
    have hargPlus : rho + (a : ℂ) + (a : ℂ) = rho + 2 * (a : ℂ) := by ring
    have hargMinus : rho + (a : ℂ) - (a : ℂ) = rho := by ring
    rw [hargPlus, hargMinus, hplusOrder, zero_add]
  · rw [analyticOrderAt_symmetricShiftProduct hF]
    have hargPlus : rho - (a : ℂ) + (a : ℂ) = rho := by ring
    have hargMinus : rho - (a : ℂ) - (a : ℂ) = rho - 2 * (a : ℂ) := by ring
    rw [hargPlus, hargMinus, hminusOrder, add_zero]

/-- At collision, symmetric translation doubles every analytic multiplicity exactly. -/
theorem analyticOrderAt_symmetricShiftProduct_zero_shift
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ) (rho : ℂ) :
    analyticOrderAt (symmetricShiftProduct F 0) rho =
      2 * analyticOrderAt F rho := by
  rw [analyticOrderAt_symmetricShiftProduct hF]
  simp [two_mul]

/-- Unconditional Xi specialization of exact translated-divisor multiplicity. -/
theorem analyticOrderAt_xi_symmetricShiftProduct (a : ℝ) (z : ℂ) :
    analyticOrderAt (symmetricShiftProduct xi a) z =
      analyticOrderAt xi (z + (a : ℂ)) +
        analyticOrderAt xi (z - (a : ℂ)) :=
  analyticOrderAt_symmetricShiftProduct xi_analyticOnNhd_univ a z

/-- Xi multiplicities double exactly at the collision parameter. -/
theorem analyticOrderAt_xi_symmetricShiftProduct_zero_shift (rho : ℂ) :
    analyticOrderAt (symmetricShiftProduct xi 0) rho =
      2 * analyticOrderAt xi rho :=
  analyticOrderAt_symmetricShiftProduct_zero_shift xi_analyticOnNhd_univ rho

end

end RHTower
