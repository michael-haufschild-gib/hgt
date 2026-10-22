import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceMidCertificate
/-! Middle-clock exclusion of a zero of the nonlinear forcing. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem mid_force_neg {h v q : ℝ} (hh0 : 2/3≤h) (hh1 : h<3/4)
    (hv0 : 0≤v) (hv1 : v<9) (hq0 : b h≤q) (hq1 : q<(6/5)*b h) :
    quadraticBoundaryCore h v q<0 := by
  let s : ℝ := (h-2/3)/(3/4-h)
  let t : ℝ := v/(9-v)
  let z : ℝ := (q-b h)/((6/5)*b h-q)
  have hsden : 0<3/4-h := by linarith only [hh1]
  have htden : 0<9-v := by linarith only [hv1]
  have hzden : 0<(6/5)*b h-q := by linarith only [hq1]
  have hs : 0≤s := div_nonneg (sub_nonneg.mpr hh0) hsden.le
  have ht : 0≤t := div_nonneg hv0 htden.le
  have hz : 0≤z := div_nonneg (sub_nonneg.mpr hq0) hzden.le
  have hes : s*(3/4-h)=h-2/3 := by exact div_mul_cancel₀ _ hsden.ne'
  have het : t*(9-v)=v := by exact div_mul_cancel₀ _ htden.ne'
  have hez : z*((6/5)*b h-q)=q-b h := by exact div_mul_cancel₀ _ hzden.ne'
  have hs1 : 0<1+s := by linarith only [hs]
  have ht1 : 0<1+t := by linarith only [ht]
  have hz1 : 0<1+z := by linarith only [hz]
  have heh : (2/3+(3/4)*s)/(1+s)=h := by
    apply (div_eq_iff hs1.ne').2
    nlinarith only [hes]
  have hev : 9*t/(1+t)=v := by
    apply (div_eq_iff ht1.ne').2
    nlinarith only [het]
  have heq : b h*(1+(6/5)*z)/(1+z)=q := by
    apply (div_eq_iff hz1.ne').2
    nlinarith only [hez]
  have hn := mid_force_projective_neg s t z hs ht hz
  rw [heh,hev,heq] at hn
  exact hn

end
end HTGeometry.ThetaCriticalBarrier
