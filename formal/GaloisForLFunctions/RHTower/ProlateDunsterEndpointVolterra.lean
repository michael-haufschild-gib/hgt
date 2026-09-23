import GaloisForLFunctions.RHTower.ProlateDunsterEndpointWronskian

/-!
# Endpoint-anchored Volterra identities for radial prolate profiles

Finite-interval Wronskian transport is passed to the regular singular endpoint.  The endpoint
values proved in `ProlateDunsterEndpointWronskian` supply the two integration constants `0` and
`pi/4`; no boundary datum for the transformed equation is assumed.
-/

open Filter Set Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Transport against the regular Bessel branch, anchored at the singular endpoint as an
improper interval-integral limit. -/
theorem tendsto_integral_lgBesselWronskian_at_endpoint
    {s c B : ℝ} {U DU a : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hB : 1 < B)
    (hU : ∀ x : ℝ, 1 < x → HasDerivAt U (DU x) x)
    (hDU : ∀ x : ℝ, 1 < x → HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + a x) * U x) x)
    (ha : ContinuousOn a (Ioi 1))
    (hend : Tendsto (fun x : ℝ => lgWeight s x *
        (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds 0)) :
    Tendsto (fun A : ℝ => ∫ t in A..B,
        lgWeight s t * a t * (U t * lgBesselModel s c t))
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgWeight s B *
        (U B * lgBesselModelDeriv s c B - DU B * lgBesselModel s c B))) := by
  let W : ℝ → ℝ := fun x => lgWeight s x *
    (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x)
  have hend' : Tendsto W (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa only [W] using hend
  have hlim : Tendsto (fun A : ℝ => W B - W A)
      (nhdsWithin 1 (Ioi 1)) (nhds (W B)) := by
    have hconst : Tendsto (fun _ : ℝ => W B) (nhdsWithin 1 (Ioi 1)) (nhds (W B)) :=
      tendsto_const_nhds
    have h := hconst.sub hend'
    simpa only [sub_zero] using h
  apply hlim.congr'
  have hAB : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1), A ≤ B := by
    have hid : Tendsto (fun A : ℝ => A) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
      tendsto_id.mono_left inf_le_left
    exact (hid.eventually (Iio_mem_nhds hB)).mono fun _ h => h.le
  filter_upwards [self_mem_nhdsWithin, hAB] with A hA hAle
  have hsub : uIcc A B ⊆ Ioi 1 := by
    rw [uIcc_of_le hAle]
    exact fun x hx => lt_of_lt_of_le hA hx.1
  have hUc : ContinuousOn U (uIcc A B) :=
    fun x hx => ((hU x (hsub hx)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel s c t)) volume A B :=
    (((continuousOn_lgWeight hs0 hs1).mono hsub).mul (ha.mono hsub) |>.mul
      (hUc.mul ((continuousOn_lgBesselModel hs0).mono hsub))).intervalIntegrable
  simpa only [W] using (integral_lgBesselWronskian hs0 hs1 hc hAle hA
    (fun x hx => hU x (hsub hx)) (fun x hx => hDU x (hsub hx)) hint).symm

/-- Transport against the logarithmic Bessel branch, anchored at the singular endpoint with
the exact Green constant `pi/4`. -/
theorem tendsto_integral_lgBessel2Wronskian_at_endpoint
    {s c B : ℝ} {U DU a : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hB : 1 < B)
    (hU : ∀ x : ℝ, 1 < x → HasDerivAt U (DU x) x)
    (hDU : ∀ x : ℝ, 1 < x → HasDerivAt DU
      (-(lgFirstOrderCoeff s x) * DU x - (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + a x) * U x) x)
    (ha : ContinuousOn a (Ioi 1))
    (hend : Tendsto (fun x : ℝ => lgWeight s x *
        (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.pi / 4))) :
    Tendsto (fun A : ℝ => ∫ t in A..B,
        lgWeight s t * a t * (U t * lgBesselModel2 s c t))
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgWeight s B *
          (U B * lgBesselModel2Deriv s c B - DU B * lgBesselModel2 s c B)
        - Real.pi / 4)) := by
  let W : ℝ → ℝ := fun x => lgWeight s x *
    (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x)
  have hlim : Tendsto (fun A : ℝ => W B - W A)
      (nhdsWithin 1 (Ioi 1)) (nhds (W B - Real.pi / 4)) :=
    tendsto_const_nhds.sub hend
  apply hlim.congr'
  have hAB : ∀ᶠ A : ℝ in nhdsWithin 1 (Ioi 1), A ≤ B := by
    have hid : Tendsto (fun A : ℝ => A) (nhdsWithin 1 (Ioi 1)) (nhds 1) :=
      tendsto_id.mono_left inf_le_left
    exact (hid.eventually (Iio_mem_nhds hB)).mono fun _ h => h.le
  filter_upwards [self_mem_nhdsWithin, hAB] with A hA hAle
  have hsub : uIcc A B ⊆ Ioi 1 := by
    rw [uIcc_of_le hAle]
    exact fun x hx => lt_of_lt_of_le hA hx.1
  have hUc : ContinuousOn U (uIcc A B) :=
    fun x hx => ((hU x (hsub hx)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable
      (fun t : ℝ => lgWeight s t * a t * (U t * lgBesselModel2 s c t)) volume A B :=
    (((continuousOn_lgWeight hs0 hs1).mono hsub).mul (ha.mono hsub) |>.mul
      (hUc.mul ((continuousOn_lgBesselModel2 hs0 hs1 hc).mono hsub))).intervalIntegrable
  simpa only [W] using (integral_lgBessel2Wronskian hs0 hs1 hc hAle hA
    (fun x hx => hU x (hsub hx)) (fun x hx => hDU x (hsub hx)) hint).symm

/-- Endpoint-anchored regular-branch defect integral, represented by its exact transported
Wronskian value. -/
def lgEndpointRegularIntegral (s c : ℝ) (U DU : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgWeight s x * (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x)

/-- Endpoint-anchored logarithmic-branch defect integral, represented after subtracting the
endpoint Green constant. -/
def lgEndpointLogIntegral (s c : ℝ) (U DU : ℝ → ℝ) (x : ℝ) : ℝ :=
  lgWeight s x * (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x)
    - Real.pi / 4

/-- Exact endpoint-anchored Volterra reconstruction.  The unperturbed term is the regular Bessel
branch and both correction coefficients are the transported improper defect integrals. -/
theorem lgEndpointVolterraReconstruction
    {s c x : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    U x = lgBesselModel s c x +
      (lgEndpointLogIntegral s c U DU x * lgBesselModel s c x -
        lgEndpointRegularIntegral s c U DU x * lgBesselModel2 s c x) /
          (Real.pi / 4) := by
  have hrec := lgReconstruction_eq (U := U) (DU := DU) hs0 hs1 hx hc
  rw [besselWronskian_eq_pi_div_four
    (mul_pos hc (xiEndpointPhase_pos hs0 hs1 hx))] at hrec
  rw [hrec, lgEndpointLogIntegral, lgEndpointRegularIntegral]
  field_simp [Real.pi_ne_zero]
  ring

/-- First endpoint-anchored transport law for an actual radial prolate solution. -/
theorem radialProlate_tendsto_integral_lgBesselWronskian_at_endpoint
    {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hB : 1 < B)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1) (hR1 : R 1 = 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x)
    (hDR : ∀ x : ℝ, 1 < x → HasDerivAt DR (DDR x) x)
    (hode : ∀ x : ℝ, 1 < x →
      (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x -
        (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    Tendsto (fun A : ℝ => ∫ t in A..B,
        lgWeight s t * lgNormalFormDefect s c (radialProlateQ s c) t *
          (comparisonSol (prolateNormalFormSol R) s t * lgBesselModel s c t))
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgWeight s B *
        (comparisonSol (prolateNormalFormSol R) s B * lgBesselModelDeriv s c B -
          comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s B *
            lgBesselModel s c B))) := by
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  have hpole : ∀ x : ℝ, 1 < x →
      HasDerivAt U (DU x) x ∧ HasDerivAt DU
        (-(lgFirstOrderCoeff s x) * DU x -
          (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + lgNormalFormDefect s c (radialProlateQ s c) x) * U x) x := by
    intro x hx
    have h := radialProlate_comparison_pole_uniform hs0 hs1 hx (hR x hx) (hDR x hx) (hode x hx)
    exact ⟨h.1, h.2.1⟩
  apply tendsto_integral_lgBesselWronskian_at_endpoint hs0 hs1 hc hB
    (fun x hx => (hpole x hx).1) (fun x hx => (hpole x hx).2)
    (continuousOn_lgNormalFormDefect_radialProlate hs0 hs1)
  exact prolateComparison_lgBesselWronskian_tendsto_zero hs0 hs1 hRc hDRc hR1 hR

/-- Second endpoint-anchored transport law for an actual radial prolate solution. -/
theorem radialProlate_tendsto_integral_lgBessel2Wronskian_at_endpoint
    {s c B : ℝ} {R DR DDR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hB : 1 < B)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1) (hR1 : R 1 = 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x)
    (hDR : ∀ x : ℝ, 1 < x → HasDerivAt DR (DDR x) x)
    (hode : ∀ x : ℝ, 1 < x →
      (x ^ (2 : ℕ) - 1) * DDR x + 2 * x * DR x -
        (s * c ^ (2 : ℕ) - c ^ (2 : ℕ) * x ^ (2 : ℕ)) * R x = 0) :
    Tendsto (fun A : ℝ => ∫ t in A..B,
        lgWeight s t * lgNormalFormDefect s c (radialProlateQ s c) t *
          (comparisonSol (prolateNormalFormSol R) s t * lgBesselModel2 s c t))
      (nhdsWithin 1 (Ioi 1))
      (nhds (lgWeight s B *
          (comparisonSol (prolateNormalFormSol R) s B * lgBesselModel2Deriv s c B -
            comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s B *
              lgBesselModel2 s c B)
        - Real.pi / 4)) := by
  let U := comparisonSol (prolateNormalFormSol R) s
  let DU := comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s
  have hpole : ∀ x : ℝ, 1 < x →
      HasDerivAt U (DU x) x ∧ HasDerivAt DU
        (-(lgFirstOrderCoeff s x) * DU x -
          (c ^ (2 : ℕ) * xiSpeed s x ^ (2 : ℕ) + lgNormalFormDefect s c (radialProlateQ s c) x) * U x) x := by
    intro x hx
    have h := radialProlate_comparison_pole_uniform hs0 hs1 hx (hR x hx) (hDR x hx) (hode x hx)
    exact ⟨h.1, h.2.1⟩
  apply tendsto_integral_lgBessel2Wronskian_at_endpoint hs0 hs1 hc hB
    (fun x hx => (hpole x hx).1) (fun x hx => (hpole x hx).2)
    (continuousOn_lgNormalFormDefect_radialProlate hs0 hs1)
  exact prolateComparison_lgBessel2Wronskian_tendsto_pi_div_four
    hs0 hs1 hc hRc hDRc hR1 hR

end GaloisForLFunctions.RHTower

end
