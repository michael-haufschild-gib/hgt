import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaFullPairedAdjoint

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaMellinDualDensity (a x : ℝ) : ℝ := x^(2*a)*Real.exp (-x+1/x)

theorem pwGammaMellinDualDensity_pos (a : ℝ) {x : ℝ} (hx : 0<x) :
    0<pwGammaMellinDualDensity a x :=
  mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

theorem pwGammaMellinDualDensity_lower (a : ℝ) (n : ℕ) {x : ℝ}
    (hx : 0<x) (hx1 : x<1) :
    (Real.exp (-1)/(n.factorial:ℝ))*x^(2*a-(n:ℝ)) ≤ pwGammaMellinDualDensity a x := by
  have hn : (0:ℝ)<n.factorial := by positivity
  have he := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx).le n
  have he' : 1/(x^n*(n.factorial:ℝ)) ≤ Real.exp (1/x) := by
    simpa only [inv_pow, one_div, div_eq_mul_inv, mul_inv_rev, mul_one, one_mul,
      mul_comm] using he
  calc
    _ = x^(2*a)*(Real.exp (-1)*(1/(x^n*(n.factorial:ℝ)))) := by
      rw [Real.rpow_sub hx,Real.rpow_natCast]
      ring
    _ ≤ x^(2*a)*(Real.exp (-x)*Real.exp (1/x)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
      exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) he' (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; rfl

theorem pwGammaMellinDualDensity_not_integrable (a : ℝ) :
    ¬ IntegrableOn (pwGammaMellinDualDensity a) (Ioo 0 1) := by
  intro hi
  obtain ⟨n,hn⟩ := exists_nat_gt (2*a+1)
  have hc : 0<Real.exp (-1)/(n.factorial:ℝ) := by positivity
  have hp : IntegrableOn (fun x : ℝ => x^(2*a-(n:ℝ))) (Ioo 0 1) := by
    apply (hi.div_const (Real.exp (-1)/(n.factorial:ℝ))).mono'
      (show Measurable (fun x : ℝ => x^(2*a-(n:ℝ))) by fun_prop).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using
      pwGammaMellinDualDensity_lower a n hx.1 hx.2)
  have ht := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by positivity)).mp hp
  linarith

theorem pwGammaMellinDualDensity_compact_admission (a : ℝ) {c d : ℝ} (hc : 0<c) :
    IntegrableOn (pwGammaMellinDualDensity a) (Icc c d) := by
  apply ContinuousOn.integrableOn_Icc
  have hi : ContinuousOn (fun x : ℝ => x) (Icc c d) := continuousOn_id
  unfold pwGammaMellinDualDensity
  exact (hi.rpow_const (fun x hx => Or.inl (hc.trans_le hx.1).ne')).mul
    ((hi.neg.add (continuousOn_const.div hi (fun x hx => (hc.trans_le hx.1).ne'))).rexp)

theorem pwGammaMobiusGroundQuotient_weighted_square_integrable (z : ℂ) :
    IntegrableOn (fun x => pwGammaReversibleDensity x*
      ‖pwGammaMobiusTilt z x/pwGammaRaySource x‖^2) (Ioi 0) := by
  have hi : IntegrableOn (fun x => ‖pwGammaMobiusReversiblePairDensity z z x‖) (Ioi 0) :=
    (pwGammaMobiusReversiblePairDensity_integrable z z).norm
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  unfold pwGammaMobiusReversiblePairDensity
  dsimp only
  rw [norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,
    Real.norm_of_nonneg (pwGammaReversibleDensity_pos hx).le,pow_two,mul_assoc]

theorem pwGammaMellinDualDensity_source_eq (s : ℂ) {x : ℝ} (hx : 0<x) :
    ‖(x:ℂ)^(s-1)*pwGammaRaySource x‖^2/pwGammaReversibleDensity x =
      pwGammaMellinDualDensity s.re x := by
  have hk : ‖(x:ℂ)^(s-1)*pwGammaRaySource x‖ = x^(s.re-1/2)*Real.exp (-x) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,pwGammaRaySource_eq hx,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤Real.sqrt x*Real.exp (-x)),
      Real.sqrt_eq_rpow,← mul_assoc,← Real.rpow_add hx]
    rw [show (s-1).re+1/2=s.re-1/2 by simp only [Complex.sub_re,Complex.one_re]; ring]
  have hp : (x^(s.re-1/2))^2*x=x^(2*s.re) := by
    rw [← Real.rpow_natCast (x^(s.re-1/2)) 2,← Real.rpow_mul hx.le]
    simp only [Nat.cast_ofNat]
    calc
      _ = x^((s.re-1/2)*(2:ℝ))*x^(1:ℝ) := by rw [Real.rpow_one]
      _ = x^((s.re-1/2)*2+1) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  have he : Real.exp (-x)^2/Real.exp (-x-x⁻¹)=Real.exp (-x+1/x) := by
    rw [pow_two,← Real.exp_add,← Real.exp_sub]
    congr 1
    simp only [one_div]
    ring
  rw [hk,mul_pow,pwGammaReversibleDensity]
  calc
    _ = ((x^(s.re-1/2))^2*x)*(Real.exp (-x)^2/Real.exp (-x-x⁻¹)) := by
      field_simp
    _ = _ := by rw [hp,he]; rfl

theorem pwGammaMellinDualDensity_source_not_integrable (s : ℂ) :
    ¬ IntegrableOn (fun x : ℝ => ‖(x:ℂ)^(s-1)*pwGammaRaySource x‖^2/
      pwGammaReversibleDensity x) (Ioo 0 1) := by
  intro h
  apply pwGammaMellinDualDensity_not_integrable s.re
  exact h.congr_fun (fun x hx => pwGammaMellinDualDensity_source_eq s hx.1) measurableSet_Ioo

end
end RHTower
