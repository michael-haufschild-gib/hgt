import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# Universal arithmetic component of Narain averages

Each target average splits into a dilation of the unit-height mean and an explicit correction analytic at every arithmetic resonance.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The target dilation multiplying the universal arithmetic mean. -/
def narainMeanTargetDilation (Y Z : Height) (u : ℂ) : ℂ :=
  (Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 - u)

/-- The arithmetic dilation depends only on the product of target heights. -/
theorem narainMeanTargetDilation_eq_product (Y Z : Height) (u : ℂ) :
    narainMeanTargetDilation Y Z u = ((Y.val * Z.val : ℝ) : ℂ) ^ (1 / 2 - u) := by
  rw [narainMeanTargetDilation, ← Complex.mul_cpow_ofReal_nonneg Y.property.le Z.property.le,
    ← Complex.ofReal_mul]

/-- The explicit correction after removal of the universal arithmetic quotient. -/
def narainMeanTargetCorrection (Y Z : Height) (u : ℂ) : ℂ :=
  2 / (u * (1 + 2 * u)) *
    (xi (1 + 2 * u) *
      ((Y.val : ℂ) ^ (1 / 2 + u) * (Z.val : ℂ) ^ (1 / 2 + u) -
        (Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 - u)) +
      ((1 + 2 * u) / (2 * u - 1) * xi (2 * u)) *
        ((Y.val : ℂ) ^ (1 / 2 + u) * (Z.val : ℂ) ^ (1 / 2 - u) +
          (Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 + u) -
            2 * ((Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 - u))))

private theorem product_quotient_decomposition (A B p q r s K : ℂ) (hA : A ≠ 0) :
    K * ((p * A + B * q) * (r * A + B * s) / A) =
      q * s * (K * ((A + B) * (A + B) / A)) +
        K * (A * (p * r - q * s) + B * (p * s + q * r - 2 * (q * s))) := by
  field_simp [hA]
  ring

/-- Away from the arithmetic divisor, all target dependence splits into a universal dilation and an explicit correction. -/
theorem narainMellinMean_target_decomposition (Y Z : Height) {u : ℂ}
    (hu : xi (1 + 2 * u) ≠ 0) :
    narainMellinMean Y Z u = narainMeanTargetDilation Y Z u *
      narainMellinMean ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ u +
        narainMeanTargetCorrection Y Z u := by
  unfold narainMellinMean meanQuotient numeratorMean
    narainMeanTargetDilation narainMeanTargetCorrection
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul]
  have h := product_quotient_decomposition (xi (1 + 2 * u))
    ((1 + 2 * u) / (2 * u - 1) * xi (2 * u))
    ((Y.val : ℂ) ^ (1 / 2 + u)) ((Y.val : ℂ) ^ (1 / 2 - u))
    ((Z.val : ℂ) ^ (1 / 2 + u)) ((Z.val : ℂ) ^ (1 / 2 - u))
    (2 / (u * (1 + 2 * u))) hu
  convert h using 1 <;> ring

/-- The actual convergent Mellin mean has the universal target decomposition on its convergence half-plane. -/
theorem narainMellinMean_target_decomposition_of_re (Y Z : Height) {u : ℂ}
    (hu : 1 / 2 < u.re) :
    narainMellinMean Y Z u = narainMeanTargetDilation Y Z u *
      narainMellinMean ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ u +
        narainMeanTargetCorrection Y Z u := by
  apply narainMellinMean_target_decomposition
  apply xi_ne_zero_of_one_le_re
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofNat_re,
    Complex.ofNat_im, zero_mul, sub_zero]
  linarith only [hu]

private theorem differentiable_target_power (Y : Height) (ε : ℂ) :
    Differentiable ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 + ε * u)) := by
  intro u
  exact (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + ε * u) u).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Y.property.ne'))

/-- The target dilation is entire. -/
theorem differentiable_narainMeanTargetDilation (Y Z : Height) :
    Differentiable ℂ (narainMeanTargetDilation Y Z) := by
  simpa only [narainMeanTargetDilation, neg_one_mul, ← sub_eq_add_neg] using
    (differentiable_target_power Y (-1)).mul (differentiable_target_power Z (-1))

/-- The literal averaged continuation is meromorphic on the whole plane. -/
theorem meromorphic_narainMellinMean (Y Z : Height) :
    Meromorphic (narainMellinMean Y Z) := by
  intro u
  have hN (W : Height) : MeromorphicAt (fun v : ℂ => numeratorMean v W) u := by
    have hp : AnalyticAt ℂ (fun v : ℂ => (W.val : ℂ) ^ (1 / 2 + v)) u := by
      simpa only [one_mul] using (differentiable_target_power W 1).analyticAt u
    have hm : AnalyticAt ℂ (fun v : ℂ => (W.val : ℂ) ^ (1 / 2 - v)) u := by
      simpa only [neg_one_mul, ← sub_eq_add_neg] using (differentiable_target_power W (-1)).analyticAt u
    have hplus : AnalyticAt ℂ (fun v : ℂ => 1 + 2 * v) u := by fun_prop
    have hminus : AnalyticAt ℂ (fun v : ℂ => 2 * v - 1) u := by fun_prop
    have hxi : AnalyticAt ℂ (fun v : ℂ => xi (2 * v)) u :=
      (xi_differentiable.comp (by fun_prop)).analyticAt u
    exact ((hp.mul (differentiable_xi_shift.analyticAt u)).meromorphicAt).add
      (((hplus.meromorphicAt.div hminus.meromorphicAt).mul hxi.meromorphicAt).mul hm.meromorphicAt)
  have hD : AnalyticAt ℂ (fun v : ℂ => v * (1 + 2 * v)) u := by fun_prop
  exact (analyticAt_const.meromorphicAt.mul
    (((hN Y).mul (hN Z)).div (differentiable_xi_shift.analyticAt u).meromorphicAt)).div hD.meromorphicAt

/-- The correction has no arithmetic pole; its displayed representative is analytic at every resonance. -/
theorem analyticAt_narainMeanTargetCorrection_resonance (Y Z : Height) (p : Resonance) :
    AnalyticAt ℂ (narainMeanTargetCorrection Y Z) p.val := by
  have hr := re_neg_of_xi_shift_eq_zero p.property
  have hl := re_gt_of_xi_shift_eq_zero p.property
  have h0 : p.val ≠ 0 := by intro h; simp [h] at hr
  have hm : 2 * p.val - 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith only [hh, hr]
  have hp : 1 + 2 * p.val ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith only [hh, hl]
  have hYp : AnalyticAt ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 + u)) p.val := by
    simpa only [one_mul] using (differentiable_target_power Y 1).analyticAt p.val
  have hYm : AnalyticAt ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 - u)) p.val := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using (differentiable_target_power Y (-1)).analyticAt p.val
  have hZp : AnalyticAt ℂ (fun u : ℂ => (Z.val : ℂ) ^ (1 / 2 + u)) p.val := by
    simpa only [one_mul] using (differentiable_target_power Z 1).analyticAt p.val
  have hZm : AnalyticAt ℂ (fun u : ℂ => (Z.val : ℂ) ^ (1 / 2 - u)) p.val := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using (differentiable_target_power Z (-1)).analyticAt p.val
  have hK : AnalyticAt ℂ (fun u : ℂ => 2 / (u * (1 + 2 * u))) p.val :=
    analyticAt_const.div (by fun_prop) (mul_ne_zero h0 hp)
  have hB : AnalyticAt ℂ (fun u : ℂ => (1 + 2 * u) / (2 * u - 1) * xi (2 * u)) p.val :=
    ((by fun_prop : AnalyticAt ℂ (fun u : ℂ => 1 + 2 * u) p.val).div
      (by fun_prop) hm).mul
        ((xi_differentiable.comp (by fun_prop : Differentiable ℂ (fun u : ℂ => 2 * u))).analyticAt p.val)
  exact hK.mul (((differentiable_xi_shift.analyticAt p.val).mul
    ((hYp.mul hZp).sub (hYm.mul hZm))).add
      (hB.mul (((hYp.mul hZm).add (hYm.mul hZp)).sub
        (analyticAt_const.mul (hYm.mul hZm)))))

/-- Near an arithmetic resonance the mean differs from its universal dilation by the analytic correction. -/
theorem narainMellinMean_target_decomposition_germ (Y Z : Height) (p : Resonance) :
    narainMellinMean Y Z =ᶠ[𝓝[≠] p.val] fun u => narainMeanTargetDilation Y Z u *
      narainMellinMean ⟨1, by norm_num [Height]⟩ ⟨1, by norm_num [Height]⟩ u +
        narainMeanTargetCorrection Y Z u := by
  have ha := differentiable_xi_shift.analyticAt p.val
  have hn : analyticOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val ≠ ⊤ := by
    obtain ⟨n, g, horder, _⟩ := exists_xi_shift_factor p.property
    rw [horder]
    exact ENat.coe_ne_top
  have hne : ∀ᶠ u in 𝓝[≠] p.val, xi (1 + 2 * u) ≠ 0 := by
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim (hn (analyticOrderAt_eq_top.mpr hzero))
    · exact hne
  filter_upwards [hne] with u hu
  exact narainMellinMean_target_decomposition Y Z hu

#print axioms meromorphic_narainMellinMean
#print axioms narainMellinMean_target_decomposition
#print axioms narainMellinMean_target_decomposition_of_re
#print axioms analyticAt_narainMeanTargetCorrection_resonance
#print axioms narainMellinMean_target_decomposition_germ
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
