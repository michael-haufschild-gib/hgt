import GaloisForLFunctions.HTGeometry.StrelitzJetCurveCoefficientPhase

/-!
# Logarithmically normalized Strelitz jet-curve roots

After Newton-slope extraction, divide a numerical second-jet root by the corresponding real power
of the escaping first-jet norm.  The normalized root has logarithmic exponent zero.  This exact
identity is the scale separation needed before the finite Newton-face compactness argument.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- A numerical second-jet root with its extracted Newton power removed. -/
def strelitzJetCurveNormalizedRoot
    (u root : ℕ → ℂ) (p : ℝ) (n : ℕ) : ℂ :=
  root n / ((‖u n‖ ^ p : ℝ) : ℂ)

/-- Removing the exact real Newton power leaves logarithmic exponent zero relative to the escaping
first-jet norm. -/
theorem tendsto_strelitzJetCurveNormalizedRootLogSlope_zero
    {u root : ℕ → ℂ} {p : ℝ} {ns : ℕ → ℕ} (hns : StrictMono ns)
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0)
    (hslope : Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k))
      atTop (nhds p)) :
    Tendsto (fun k =>
      Real.log ‖strelitzJetCurveNormalizedRoot u root p (ns k)‖ /
        Real.log ‖u (ns k)‖) atTop (nhds 0) := by
  have huTopSub : Tendsto (fun k => ‖u (ns k)‖) atTop atTop :=
    huTop.comp hns.tendsto_atTop
  have huLarge : ∀ᶠ k : ℕ in atTop, 1 < ‖u (ns k)‖ :=
    huTopSub.eventually_gt_atTop 1
  have hroot0Sub : ∀ᶠ k : ℕ in atTop, root (ns k) ≠ 0 :=
    hns.tendsto_atTop.eventually hroot0
  have heq : ∀ᶠ k : ℕ in atTop,
      Real.log ‖strelitzJetCurveNormalizedRoot u root p (ns k)‖ /
          Real.log ‖u (ns k)‖ =
        strelitzJetCurveRootLogSlope u root (ns k) - p := by
    filter_upwards [huLarge, hroot0Sub] with k huk hrk
    have huPos : 0 < ‖u (ns k)‖ := lt_trans zero_lt_one huk
    have hpowPos : 0 < ‖u (ns k)‖ ^ p := Real.rpow_pos_of_pos huPos p
    have hlogNe : Real.log ‖u (ns k)‖ ≠ 0 := ne_of_gt (Real.log_pos huk)
    rw [strelitzJetCurveNormalizedRoot, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpowPos, Real.log_div (norm_ne_zero_iff.mpr hrk) hpowPos.ne',
      Real.log_rpow huPos]
    rw [strelitzJetCurveRootLogSlope]
    field_simp
  have hdiff := hslope.sub_const p
  have hzero : Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k) - p)
      atTop (nhds 0) := by simpa using hdiff
  exact Tendsto.congr' (heq.mono fun _ hk => hk.symm) hzero

end


end GaloisForLFunctions.HTGeometry
