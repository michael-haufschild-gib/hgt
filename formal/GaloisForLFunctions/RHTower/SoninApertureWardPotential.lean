import GaloisForLFunctions.RHTower.SoninApertureWardCurvature

/-!
# Exact Ward potential for Sonin aperture curvature

The operator-valued aperture curvature is a two-coboundary and therefore obeys an exact Bianchi
identity.  Its trace is the negative Hilbert--Schmidt energy of the successive-layer transition.
Combining these facts gives a quadrilateral conservation law for that energy.

On every ordered aperture chamber, choosing any smaller base aperture produces an explicit Ward
potential whose coboundary is the curvature energy.  Changing the base changes this potential only
by a vertex coboundary.  Hence the scalar aperture curvature is globally exact, not merely
triple-by-triple cancellable.  Any arithmetic obstruction in Suzuki's lane must therefore enter
through the source normalization or the prime--Gamma/co-Poisson floor, not through this scalar
aperture curvature alone.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- Operator-valued Bianchi identity for aperture restriction curvature. -/
theorem evenSoninApertureRestrictionCurvature_bianchi
    (o a b c r : ℝ) (hr : 1 < r) :
    evenSoninApertureRestrictionCurvature o b c r hr +
        evenSoninApertureRestrictionCurvature o a b r hr =
      evenSoninApertureRestrictionCurvature o a c r hr +
        evenSoninApertureRestrictionCurvature a b c r hr := by
  unfold evenSoninApertureRestrictionCurvature
  abel

/-- Exact quadrilateral conservation law for successive-layer Hilbert--Schmidt energies. -/
theorem hsNormSq_evenSoninApertureSuccessiveLayerTransition_bianchi
    {o a b c r : ℝ} (ho : 0 < o) (hoa : o < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * o) :
    hsNormSq (evenSoninApertureSuccessiveLayerTransition o b c r hr) +
        hsNormSq (evenSoninApertureSuccessiveLayerTransition o a b r hr) =
      hsNormSq (evenSoninApertureSuccessiveLayerTransition o a c r hr) +
        hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have ha : 0 < a := ho.trans hoa
  have hob : o < b := hoa.trans hab
  have hac : a < c := hab.trans hbc
  have hbr : b < r * o := hbc.trans hcr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hcra : c < r * a := hcr.trans (mul_lt_mul_of_pos_left hoa hr0)
  let K_obc := evenSoninApertureRestrictionCurvature o b c r hr
  let K_oab := evenSoninApertureRestrictionCurvature o a b r hr
  let K_oac := evenSoninApertureRestrictionCurvature o a c r hr
  let K_abc := evenSoninApertureRestrictionCurvature a b c r hr
  have hK_obc : MemSchattenClass 1 K_obc := by
    simpa only [K_obc] using
      evenSoninApertureRestrictionCurvature_memSchattenClass_one
        ho hob hbc hr hcr
  have hK_oab : MemSchattenClass 1 K_oab := by
    simpa only [K_oab] using
      evenSoninApertureRestrictionCurvature_memSchattenClass_one
        ho hoa hab hr hbr
  have hK_oac : MemSchattenClass 1 K_oac := by
    simpa only [K_oac] using
      evenSoninApertureRestrictionCurvature_memSchattenClass_one
        ho hoa hac hr hcr
  have hK_abc : MemSchattenClass 1 K_abc := by
    simpa only [K_abc] using
      evenSoninApertureRestrictionCurvature_memSchattenClass_one
        ha hab hbc hr hcra
  have hop : opTrace K_obc + opTrace K_oab =
      opTrace K_oac + opTrace K_abc := by
    rw [← opTrace_add_of_memSchattenClass_one hK_obc hK_oab,
      ← opTrace_add_of_memSchattenClass_one hK_oac hK_abc]
    exact congrArg opTrace
      (evenSoninApertureRestrictionCurvature_bianchi o a b c r hr)
  have hre := congrArg Complex.re hop
  have hE_obc :=
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ho hob hbc hr hcr
  have hE_oab :=
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ho hoa hab hr hbr
  have hE_oac :=
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ho hoa hac hr hcr
  have hE_abc :=
    re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
      ha hab hbc hr hcra
  simp only [Complex.add_re] at hre
  dsimp only [K_obc, K_oab, K_oac, K_abc] at hre
  rw [hE_obc, hE_oab, hE_oac, hE_abc] at hre
  linarith

/-- Base-aperture Ward potential on an aperture edge. -/
def evenSoninApertureWardPotential
    (o a b r : ℝ) (hr : 1 < r) : ℝ :=
  hsNormSq (evenSoninApertureSuccessiveLayerTransition o a b r hr)

/-- Vertex gauge controlling a change of base aperture. -/
def evenSoninApertureWardGauge
    (o p x r : ℝ) (hr : 1 < r) : ℝ :=
  hsNormSq (evenSoninApertureSuccessiveLayerTransition o p x r hr)

/-- The Ward potential integrates the successive-layer curvature energy. -/
theorem evenSoninApertureWardPotential_coboundary
    {o a b c r : ℝ} (ho : 0 < o) (hoa : o < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * o) :
    evenSoninApertureWardPotential o a b r hr +
        evenSoninApertureWardPotential o b c r hr -
          evenSoninApertureWardPotential o a c r hr =
      hsNormSq (evenSoninApertureSuccessiveLayerTransition a b c r hr) := by
  have h := hsNormSq_evenSoninApertureSuccessiveLayerTransition_bianchi
    ho hoa hab hbc hr hcr
  unfold evenSoninApertureWardPotential
  linarith

/-- Adding the base-aperture Ward potential makes scalar aperture transport exactly flat. -/
theorem re_opTrace_apertureCurvature_add_WardPotential_coboundary_eq_zero
    {o a b c r : ℝ} (ho : 0 < o) (hoa : o < a) (hab : a < b) (hbc : b < c)
    (hr : 1 < r) (hcr : c < r * o) :
    (opTrace (evenSoninApertureRestrictionCurvature a b c r hr)).re +
        evenSoninApertureWardPotential o a b r hr +
          evenSoninApertureWardPotential o b c r hr -
            evenSoninApertureWardPotential o a c r hr = 0 := by
  have ha : 0 < a := ho.trans hoa
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hcra : c < r * a := hcr.trans (mul_lt_mul_of_pos_left hoa hr0)
  rw [re_opTrace_evenSoninApertureRestrictionCurvature_eq_neg_hsNormSq
    ha hab hbc hr hcra]
  have hpot := evenSoninApertureWardPotential_coboundary
    ho hoa hab hbc hr hcr
  linarith

/-- Changing base aperture changes the Ward potential by an exact vertex coboundary. -/
theorem evenSoninApertureWardPotential_base_change
    {o p a b r : ℝ} (ho : 0 < o) (hop : o < p) (hpa : p < a) (hab : a < b)
    (hr : 1 < r) (hbr : b < r * o) :
    evenSoninApertureWardPotential o a b r hr -
        evenSoninApertureWardPotential p a b r hr =
      evenSoninApertureWardGauge o p b r hr -
        evenSoninApertureWardGauge o p a r hr := by
  have h := hsNormSq_evenSoninApertureSuccessiveLayerTransition_bianchi
    ho hop hpa hab hr hbr
  unfold evenSoninApertureWardPotential evenSoninApertureWardGauge
  linarith

end RHTower
