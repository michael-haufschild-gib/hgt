import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioAffineSlopeSecondJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioInfinityCone
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology


def affineLineCoord (r : ℂ) : Coord → Polynomial ℂ
  | .U => Polynomial.X
  | .K => Polynomial.C r
  | .J => 0
def affineLine (r : ℂ) : Poly →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C (affineLineCoord r)
@[simp] theorem affineLine_C (r c : ℂ) : affineLine r (C c)=Polynomial.C c := by simp [affineLine]
@[simp] theorem affineLine_X (r : ℂ) (i : Coord) : affineLine r (X i)=affineLineCoord r i := by simp [affineLine]

theorem affineLine_eval (P : Poly) (h r : ℂ) :
    (affineLine r P).eval h=eval (basePoint h r 0) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,affineLineCoord,basePoint]

theorem affineLine_derivative (P : Poly) (r : ℂ) :
    (affineLine r P).derivative=affineLine r (pderiv Coord.U P) := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.derivative_mul,pderiv_mul,map_add,affineLine_X,hp]
    cases i <;> simp [affineLineCoord,pderiv_X,Pi.single_apply,hk,hj]

theorem affineSlope_coeff_zero (r : ℂ) : (affineLine r (affineShift scaledSlope)).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,affineLine_eval]
  exact affineSlope_zero r

theorem affineSlope_coeff_one (r : ℂ) : (affineLine r (affineShift scaledSlope)).coeff 1=0 := by
  have he : ((affineLine r (affineShift scaledSlope)).derivative).eval 0=0 := by
    rw [affineLine_derivative,affineLine_eval]
    exact affineSlope_first r
  simpa [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] using he

theorem affineSlope_coeff_two (r : ℂ) :
    (affineLine r (affineShift scaledSlope)).coeff 2= -54*principalMass*r^2 := by
  have he : ((affineLine r (affineShift scaledSlope)).derivative.derivative).eval 0=
      -108*principalMass*r^2 := by
    rw [affineLine_derivative,affineLine_derivative,affineLine_eval]
    exact affineSlope_second r
  norm_num [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
  linear_combination he/2

def affineSlopeCore (r : ℂ) : Polynomial ℂ := (affineLine r (affineShift scaledSlope)).divX.divX

theorem affineSlope_factor (r : ℂ) :
    affineLine r (affineShift scaledSlope)=Polynomial.X^2*affineSlopeCore r := by
  have h1 : affineLine r (affineShift scaledSlope)=Polynomial.X*(affineLine r (affineShift scaledSlope)).divX := by
    simpa [affineSlope_coeff_zero] using (Polynomial.X_mul_divX_add (affineLine r (affineShift scaledSlope))).symm
  have h2 : (affineLine r (affineShift scaledSlope)).divX=Polynomial.X*affineSlopeCore r := by
    simpa [affineSlopeCore,Polynomial.coeff_divX,affineSlope_coeff_one] using
      (Polynomial.X_mul_divX_add (affineLine r (affineShift scaledSlope)).divX).symm
  rw [h1,h2]
  ring

theorem affineSlopeCore_zero (r : ℂ) : (affineSlopeCore r).eval 0= -54*principalMass*r^2 := by
  simpa [affineSlopeCore,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_divX] using
    affineSlope_coeff_two r

theorem affineSlope_eventually_neg {r : ℝ} (hr : r≠0) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), regularSlopeValue h r (r*(1/12-7*h/72))<0 := by
  have hz : ((affineSlopeCore (r:ℂ)).eval 0).re<0 := by
    rw [affineSlopeCore_zero,principalMass_real]
    have hs : 0<r^2 := sq_pos_of_ne_zero hr
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_neg,
      ← Complex.ofReal_ofNat,Complex.ofReal_re]
    have hc : 0<(54:ℝ)*((6:ℝ)^24*1990656*1679616) := by positivity
    nlinarith [mul_pos hc hs]
  have hc : Continuous (fun h : ℝ => ((affineSlopeCore (r:ℂ)).eval (h:ℂ)).re) :=
    Complex.continuous_re.comp ((affineSlopeCore (r:ℂ)).continuous.comp Complex.continuous_ofReal)
  have hn := hc.continuousAt.eventually_lt_const hz
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
  have he := congrArg (Polynomial.eval (h:ℂ)) (affineSlope_factor (r:ℂ))
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,affineLine_eval,affineShift_eval,zero_add] at he
  have hre := congrArg Complex.re he
  have hcst : (r:ℂ)*(1/12-7*(h:ℂ)/72)=((r*(1/12-7*h/72):ℝ):ℂ) := by push_cast; ring
  rw [hcst] at hre
  change regularSlopeValue h r (r*(1/12-7*h/72))=
    (((h:ℂ)^2)*(affineSlopeCore (r:ℂ)).eval (h:ℂ)).re at hre
  rw [hre]
  have hp : 0<h^2 := sq_pos_of_pos hh
  simpa only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] using mul_neg_of_pos_of_neg hp hn

end
end HTGeometry.ThetaRatioInfinity
