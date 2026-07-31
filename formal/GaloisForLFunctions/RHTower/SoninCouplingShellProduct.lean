import GaloisForLFunctions.RHTower.SoninLayerShellCongruence

/-!
# The coupling is a shell–dilation–shell product modulo the ideal

Both aperture layers of the coupling are two-polarization shells modulo the relative ideal, and the
ideal is two-sided, so the coupling itself is congruent to a product of two explicit shells with the
dilation between them.

The Fourier duals of the disjoint-shell vanishing laws are supplied here as well; together with
the physical ones already in the corpus they are what makes the shell product computable.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- Fourier shells with the first ceiling below the second floor are disjoint. -/
theorem evenFourierShell_mul_eq_zero_of_left_ceiling_le_right_floor
    (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v) (htu : t ≤ u) :
    (evenFourierCutoff t - evenFourierCutoff s) *
        (evenFourierCutoff v - evenFourierCutoff u) = 0 := by
  rw [evenFourierCutoff_generalShellProduct s t u v hst huv]
  have htv : t ≤ v := htu.trans huv
  rw [min_eq_left htv]
  have htmax : t ≤ max s u := htu.trans (le_max_right _ _)
  rw [min_eq_right htmax, sub_self]

/-- Fourier shells with the second ceiling below the first floor are disjoint. -/
theorem evenFourierShell_mul_eq_zero_of_right_ceiling_le_left_floor
    (s t u v : ℝ) (hst : s ≤ t) (huv : u ≤ v) (hvs : v ≤ s) :
    (evenFourierCutoff t - evenFourierCutoff s) *
        (evenFourierCutoff v - evenFourierCutoff u) = 0 := by
  rw [evenFourierCutoff_generalShellProduct s t u v hst huv]
  have hvt : v ≤ t := hvs.trans hst
  rw [min_eq_right hvt]
  have hvmax : v ≤ max s u := hvs.trans (le_max_left _ _)
  rw [min_eq_right hvmax, sub_self]

/-- **Shell product form of the coupling.**  Modulo the relative ideal the successive-layer
coupling is the product of the two two-polarization shells with the dilation between them. -/
theorem evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_shellProduct
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr =ᵣ
      evenTwoPolarizationShell a b * evenDilationSum r hr *
        evenTwoPolarizationShell b c := by
  have h1 := evenSoninApertureLayer_principalRelativeEq_twoPolarizationShell ha hb hab
  have h2 := evenSoninApertureLayer_principalRelativeEq_twoPolarizationShell hb hc hbc
  unfold evenSoninApertureSuccessiveLayerTransition
  exact (h1.mul (SoninPrincipalRelativeEq.refl (evenDilationSum r hr))).mul h2

/-- The same statement read as membership: the coupling and the shell product differ by an element
of the concrete relative ideal. -/
theorem isSoninPrincipalRelativeIdeal_coupling_sub_shellProduct
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    IsSoninPrincipalRelativeIdeal
      (evenSoninApertureSuccessiveLayerTransition a b c r hr -
        evenTwoPolarizationShell a b * evenDilationSum r hr *
          evenTwoPolarizationShell b c) :=
  evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_shellProduct
    ha hb hc hab hbc hr

end RHTower
