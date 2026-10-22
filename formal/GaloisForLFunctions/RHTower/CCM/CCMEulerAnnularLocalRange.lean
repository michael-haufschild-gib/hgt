import GaloisForLFunctions.RHTower.SoninAnnularDilationNilpotent
import GaloisForLFunctions.RHTower.CCM.CCMEulerDenominatorCarrier

/-!
# Actual local Euler boundary surjectivity

The nilpotent forward annular factor solves the boundary equation of the
original inverse-dilation Euler polynomial. Upper-cutoff absorption permits
composition along genuine finite prime insertion.
-/

noncomputable section

namespace RHTower

private theorem localEuler_cutoff_formula (p : ℝ) (hp : 1 < p) (c : ℝ)
    (f : evenSubspace) :
    evenFourierCutoff c (evenPrimeLocalFactor p hp f) =
      evenFourierCutoff c f - (Real.sqrt p : ℂ)⁻¹ •
        (evenDilationUnitary p (zero_lt_one.trans hp)).symm
          (evenFourierCutoff (p * c) f) := by
  have hcov := DFunLike.congr_fun
    (evenFourierCutoff_mul_evenDilationCLM c p⁻¹
      (inv_pos.mpr (zero_lt_one.trans hp))) f
  simp only [_root_.mul_apply_eq_comp, inv_inv] at hcov
  simp only [evenPrimeLocalFactor, _root_.sub_apply, one_apply_eq_self,
    _root_.smul_apply, map_sub, map_smul]
  change evenFourierCutoff c f - (Real.sqrt p : ℂ)⁻¹ •
    evenFourierCutoff c (evenDilationCLM p⁻¹ (inv_pos.mpr (zero_lt_one.trans hp)) f) = _
  rw [hcov]
  rfl

/-- The local boundary sees only the prime-expanded upper band. -/
theorem evenPrimeLocalFactor_cutoff_absorb (p : ℝ) (hp : 1 < p)
    (c : ℝ) (hc : 0 ≤ c) (f : evenSubspace) :
    evenFourierCutoff c (evenPrimeLocalFactor p hp (evenFourierCutoff (p * c) f)) =
      evenFourierCutoff c (evenPrimeLocalFactor p hp f) := by
  have hcp : c ≤ p * c := by nlinarith
  rw [localEuler_cutoff_formula, localEuler_cutoff_formula]
  have hsmall := DFunLike.congr_fun (evenFourierCutoff_mul_of_le c (p * c) hcp) f
  have hlarge := DFunLike.congr_fun (evenFourierCutoff_mul_of_le (p * c) (p * c) le_rfl) f
  change evenFourierCutoff c (evenFourierCutoff (p * c) f) = evenFourierCutoff c f at hsmall
  change evenFourierCutoff (p * c) (evenFourierCutoff (p * c) f) =
    evenFourierCutoff (p * c) f at hlarge
  rw [hsmall, hlarge]

/-- Every datum in the output annulus has an actual finite-band Euler preimage. -/
theorem exists_annular_evenPrimeLocalFactor_preimage (p : ℝ) (hp : 1 < p)
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) {u : evenSubspace}
    (hulo : evenFourierCutoff (p⁻¹ * b) u = 0)
    (huhi : evenFourierCutoff c u = u) :
    ∃ w : evenSubspace, evenFourierCutoff b w = 0 ∧
      evenFourierCutoff (p * c) w = w ∧
      evenFourierCutoff c (evenPrimeLocalFactor p hp w) = u := by
  let U := evenDilationUnitary p (zero_lt_one.trans hp)
  let v := U u
  let W := evenAnnularForwardDilation b (p * c) p (zero_lt_one.trans hp)
  let s : ℂ := Real.sqrt p
  have hs : s ≠ 0 := by
    change (Real.sqrt p : ℂ) ≠ 0
    exact_mod_cast (Real.sqrt_pos.mpr (zero_lt_one.trans hp)).ne'
  have hscale : p⁻¹ * (p * c) = c := by
    rw [← mul_assoc, inv_mul_cancel₀ (zero_lt_one.trans hp).ne', one_mul]
  have hvlo : evenFourierCutoff b v = 0 := by
    have hcov := DFunLike.congr_fun
      (evenFourierCutoff_mul_evenDilationCLM b p (zero_lt_one.trans hp)) u
    change evenFourierCutoff b v = U (evenFourierCutoff (p⁻¹ * b) u) at hcov
    rw [hulo, map_zero] at hcov
    exact hcov
  have hvhi : evenFourierCutoff (p * c) v = v := by
    have hcov := DFunLike.congr_fun
      (evenFourierCutoff_mul_evenDilationCLM (p * c) p (zero_lt_one.trans hp)) u
    change evenFourierCutoff (p * c) v = U (evenFourierCutoff (p⁻¹ * (p * c)) u) at hcov
    rwa [hscale, huhi] at hcov
  have hWlo (f : evenSubspace) : evenFourierCutoff b (W f) = 0 :=
    DFunLike.congr_fun
      (evenFourierCutoff_mul_evenAnnularForwardDilation b (p * c) p hb.le hp.le) f
  have hWhi (f : evenSubspace) : evenFourierCutoff (p * c) (W f) = W f := by
    change evenFourierCutoff (p * c)
      (evenFourierCutoff (p * c) (evenDilationCLM p (zero_lt_one.trans hp)
        ((1 - evenFourierCutoff b) f))) = _
    exact DFunLike.congr_fun (evenFourierCutoff_mul_of_le (p * c) (p * c) le_rfl) _
  have hunit : IsUnit (1 - s • W) :=
    isUnit_one_sub_smul_evenAnnularForwardDilation b (p * c) p hb
      (mul_pos (zero_lt_one.trans hp) hc).le hp s
  obtain ⟨w, hw⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2 ((-s) • v)
  change w - s • W w = (-s) • v at hw
  have hwlo : evenFourierCutoff b w = 0 := by
    have heq := congrArg (evenFourierCutoff b) hw
    simpa only [map_sub, map_smul, hWlo, hvlo, smul_zero, sub_zero] using heq
  have hwhi : evenFourierCutoff (p * c) w = w := by
    have heq := congrArg (evenFourierCutoff (p * c)) hw
    simp only [map_sub, map_smul, hWhi, hvhi] at heq
    have hcancel := congrArg (fun x : evenSubspace => x + s • W w) (heq.trans hw.symm)
    simpa only [sub_add_cancel] using hcancel
  have hforward : W w - s⁻¹ • w = v := by
    have heq := congrArg (fun x : evenSubspace => s⁻¹ • x) hw
    simp only [smul_sub, smul_smul, mul_neg, inv_mul_cancel₀ hs, one_smul,
      neg_one_smul] at heq
    have hneg := congrArg Neg.neg heq
    simpa only [neg_sub, neg_neg] using hneg
  have hWw : W w = U (evenFourierCutoff c w) := by
    have hgap : (1 - evenFourierCutoff b) w = w := by
      simp only [_root_.sub_apply, one_apply_eq_self, hwlo, sub_zero]
    change evenFourierCutoff (p * c)
      (evenDilationCLM p (zero_lt_one.trans hp) ((1 - evenFourierCutoff b) w)) = _
    rw [hgap]
    have hcov := DFunLike.congr_fun
      (evenFourierCutoff_mul_evenDilationCLM (p * c) p (zero_lt_one.trans hp)) w
    change evenFourierCutoff (p * c) (U w) =
      U (evenFourierCutoff (p⁻¹ * (p * c)) w) at hcov
    change evenFourierCutoff (p * c) (U w) = U (evenFourierCutoff c w)
    simpa only [hscale] using hcov
  have hreturned := congrArg U.symm hforward
  rw [map_sub, map_smul, hWw, LinearIsometryEquiv.symm_apply_apply] at hreturned
  change evenFourierCutoff c w - s⁻¹ • U.symm w = U.symm (U u) at hreturned
  rw [LinearIsometryEquiv.symm_apply_apply] at hreturned
  refine ⟨w, hwlo, hwhi, ?_⟩
  rw [localEuler_cutoff_formula, hwhi]
  exact hreturned

end RHTower
