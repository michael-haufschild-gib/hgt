import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFinitePoleMellin

/-!
# The actual finite-pole theta defect

Mellin inversion on both boundary lines identifies the full residue packet of
the actual quotient. No inverse-transform, contour estimate, or residue-order
assumption is imposed on the original cubic datum.
-/

noncomputable section

open Complex Set Filter MeasureTheory Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilHigherDenominator

/-- Reflection on the boundary pair, with no assertion about pointwise values at poles. -/
theorem poleClearedDegreeTwoCompletion_reflection_right {E H : ℂ → ℂ} {ε : ℂ}
    (hfe : ∀ z, E (1 - z) = ε * E z) (P : Polynomial ℂ)
    (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {s : ℂ} (hs : 2 ≤ s.re) :
    poleClearedDegreeTwoCompletion P H (1 - s) = ε * poleClearedDegreeTwoCompletion P H s := by
  have hx := xi_ne_zero_right hs
  have hxr : xi (1 - s) ≠ 0 := by simpa only [xi_one_sub] using hx
  have hp := deficitPolynomial_ne_zero_right P hord hs
  have hpr := deficitPolynomial_ne_zero_left P hord
    (s := 1 - s) (by simp only [sub_re, one_re]; linarith)
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; norm_num [h] at hs)
  have hr0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (by intro h; exact hs1 (by rw [← h]; ring))
  have hr1 : (1 : ℂ) - s - 1 ≠ 0 := by
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    exact neg_ne_zero.mpr hs0
  have hHs : H s = P.eval s * E s / xi s := (eq_div_iff hx).mpr (hfac s).symm
  have hHr : H (1 - s) = P.eval (1 - s) * E (1 - s) / xi (1 - s) :=
    (eq_div_iff hxr).mpr (hfac (1 - s)).symm
  rw [poleClearedDegreeTwoCompletion, poleClearedDegreeTwoCompletion, hHs, hHr,
    hfe, xi_one_sub]
  field_simp; ring

private lemma inverse_line_of_hasMellin {F : ℂ → ℂ} {f : ℝ → ℂ} {σ x : ℝ}
    (hx : 0 < x) (htrans : ∀ s : ℂ, s.re = σ → HasMellin f s ((1 / 4 : ℂ) * F s))
    (hvert : Integrable fun t : ℝ => F ((σ : ℂ) + t * I)) (hc : ContinuousAt f x) :
    f x = (1 / (2 * Real.pi)) • ((1 / 4 : ℂ) *
      ∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + t * I)) * F ((σ : ℂ) + t * I)) := by
  have hconv : MellinConvergent f σ := (htrans σ (by simp)).1
  have hm : Complex.VerticalIntegrable (mellin f) σ := by
    refine (hvert.const_mul (1 / 4 : ℂ)).congr (Eventually.of_forall fun t => ?_)
    exact ((htrans _ (by simp)).2).symm
  rw [← mellinInv_mellin_eq σ f hx hconv hm hc, mellinInv]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [(htrans _ (by simp)).2]
  simp only [smul_eq_mul]
  ring

/-- The actual theta inversion defect is exactly the full finite Laurent residue packet. -/
theorem degreeTwoQuotient_theta_defect {g : ℕ → ℂ} {E H : ℂ → ℂ} {ε : ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hfe : ∀ z, E (1 - z) = ε * E z)
    (P : Polynomial ℂ) (hP : P ≠ 0) (hH : Differentiable ℂ H)
    (hHfinite : FiniteOrderEnvelope H) (hfac : ∀ z, P.eval z * E z = H z * xi z)
    (hord : ∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞))
    {x : ℝ} (hx : 0 < x) :
    MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x -
        ε * ((x : ℂ) ^ (-1 : ℂ) * MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x⁻¹) =
      (1 / 4 : ℂ) * ∑ p ∈ degreeTwoPoleSet P,
        laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) p (-1) := by
  have hsum := fun σ hσ => degreeTwoQuotientCoeff_weighted_summable hD (σ := σ) hσ
  have hR : ∀ s : ℂ, s.re = 2 →
      HasMellin (MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g)) s
        ((1 / 4 : ℂ) * poleClearedDegreeTwoCompletion P H s) :=
    fun _ hs => hasMellin_poleClearedDegreeTwoCompletion hD P hfac hord hs.ge
  have hL : ∀ s : ℂ, s.re = -1 → HasMellin
      (fun y : ℝ => ε * ((y : ℂ) ^ (-1 : ℂ) * MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) y⁻¹)) s
      ((1 / 4 : ℂ) * poleClearedDegreeTwoCompletion P H s) := by
    intro s hs
    have hs' : 2 ≤ (1 - s).re := by norm_num [hs]
    have h := MaassThetaRelation.hasMellin_const_mul (MaassGammaCorrections.hasMellin_dual_inv
      (hasMellin_poleClearedDegreeTwoCompletion hD P hfac hord hs')) ε
    have hf := poleClearedDegreeTwoCompletion_reflection_right hfe P hfac hord hs'
    simp only [sub_sub_cancel] at hf
    rw [hf]
    convert h using 1; ring
  have hcR : ContinuousAt (MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g)) x :=
    (MaassThetaMellin.continuousOn_kTheta hsum).continuousAt (Ioi_mem_nhds hx)
  have hcI : ContinuousAt (fun y : ℝ => MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) y⁻¹) x :=
    ((MaassThetaMellin.continuousOn_kTheta hsum).continuousAt (Ioi_mem_nhds (inv_pos.mpr hx))).comp
      (continuousAt_inv₀ hx.ne')
  have hcp : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-1 : ℂ)) x :=
    Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
  have hcL := (hcp.mul hcI).const_mul ε
  have hv : ∀ σ : ℝ, σ = -1 ∨ σ = 2 →
      Integrable fun t : ℝ => poleClearedDegreeTwoCompletion P H ((σ : ℂ) + t * I) := by
    intro σ hσ
    simpa using poleClearedDegreeTwoCompletion_integrable_line hD P hP hH hHfinite hfac hord
      hσ (x := 1) one_pos
  rw [inverse_line_of_hasMellin hx hR (hv 2 (Or.inr rfl)) hcR,
    inverse_line_of_hasMellin hx hL (hv (-1) (Or.inl rfl)) hcL, ← smul_sub, ← mul_sub]
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_one]
  rw [poleClearedDegreeTwoCompletion_contour_shift hD P hP hH hHfinite hfac hord hx]
  rw [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The original datum yields either infinitely many deficits or the actual finite-residue defect. -/
theorem degreeThree_infiniteDeficits_or_thetaDefect {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (hE1 : E 1 ≠ 0) :
    (xiDeficitSupport E).Infinite ∨
      ∃ (P : Polynomial ℂ) (H : ℂ → ℂ) (ε : ℂ), P.Monic ∧ ‖ε‖ = 1 ∧
        (∀ z, analyticOrderAt (fun w => P.eval w) z = (xiDeficit E z : ℕ∞)) ∧
        Differentiable ℂ H ∧ FiniteOrderEnvelope H ∧ H 1 ≠ 0 ∧
        (∀ z, P.eval z * E z = H z * xi z) ∧
        ∀ x : ℝ, 0 < x →
          MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x -
              ε * ((x : ℂ) ^ (-1 : ℂ) * MaassThetaMellin.kTheta (degreeTwoQuotientCoeff g) x⁻¹) =
            (1 / 4 : ℂ) * ∑ p ∈ degreeTwoPoleSet P,
              laurentCoeff (fun s => (x : ℂ) ^ (-s) * poleClearedDegreeTwoCompletion P H s) p (-1) := by
  rcases degreeThree_infiniteDeficits_or_poleCleared hD hE1 with hi | ⟨P, H, hm, _, ho, hd, hg, h₁, hf⟩
  · exact Or.inl hi
  · obtain ⟨ε, hε, he⟩ := hD.exists_sign
    exact Or.inr ⟨P, H, ε, hm, hε, ho, hd, hg, h₁, hf,
      fun _ hx => degreeTwoQuotient_theta_defect hD he P hm.ne_zero hd hg hf ho hx⟩

end RHTower.WeilHigherDenominator
