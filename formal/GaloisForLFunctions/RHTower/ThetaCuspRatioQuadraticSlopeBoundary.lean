import GaloisForLFunctions.RHTower.ThetaCuspRatioAffineSlopeBoundary
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

@[simp] private theorem pd_nat74 (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def quadraticCoord (a : ℂ) : Coord → Poly
  | .U => X .U
  | .K => X .K
  | .J => X .J+C a*(X .U)^2
def quadraticShift (a : ℂ) : Poly →+* Poly := eval₂Hom C (quadraticCoord a)
@[simp] theorem quadraticShift_C (a c : ℂ) : quadraticShift a (C c)=C c := by simp [quadraticShift]
@[simp] theorem quadraticShift_X (a : ℂ) (i : Coord) : quadraticShift a (X i)=quadraticCoord a i := by simp [quadraticShift]

theorem quadraticShift_eval (P : Poly) (a h r s : ℂ) :
    eval (basePoint h r s) (quadraticShift a P)=eval (basePoint h r (s+a*h^2)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => cases i <;> simp [hp,quadraticCoord,basePoint]

theorem quadraticShift_U (P : Poly) (a : ℂ) :
    pderiv Coord.U (quadraticShift a P)=quadraticShift a (pderiv Coord.U P)+
      2*C a*X Coord.U*quadraticShift a (pderiv Coord.J P) := by
  have hk : Coord.K≠Coord.U := by intro h; cases h
  have hj : Coord.J≠Coord.U := by intro h; cases h
  have hk' : Coord.K≠Coord.J := by intro h; cases h
  have hu' : Coord.U≠Coord.J := by intro h; cases h
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq]; ring
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,quadraticShift_X,hp]
    cases i <;> simp [quadraticCoord,pderiv_mul,pderiv_pow,pderiv_X,Pi.single_apply,hk,hj,hk',hu'] <;> ring

theorem quadraticShift_zero (P : Poly) (a r : ℂ) :
    planeValue r (quadraticShift a P)=planeValue r P := by
  simp [planeValue,quadraticShift_eval]

theorem quadraticShift_first (P : Poly) (a r : ℂ) :
    planeJet1 r (quadraticShift a P)=planeJet1 r P := by
  simp [planeJet1,planeValue,quadraticShift_U,quadraticShift_eval,basePoint]

theorem quadraticShift_second (P : Poly) (a r : ℂ) :
    planeJet2 r (quadraticShift a P)=planeJet2 r P+2*a*planeValue r (pderiv Coord.J P) := by
  simp [planeJet2,planeValue,quadraticShift_U,quadraticShift_eval,pderiv_mul,pderiv_X,basePoint]
  ring

theorem planeSlope_J (r : ℂ) :
    planeValue r (pderiv Coord.J (affineShift scaledSlope))=7776*principalMass := by
  have hd := critical_partial_J scaledSlope r (r/12)
  simp_rw [scaledSlope_zero] at hd
  have hc := ((hasDerivAt_const (r/12) r).sub ((hasDerivAt_id (r/12)).const_mul 12)).const_mul
    (-648*principalMass)
  have he := hd.unique hc
  unfold planeValue
  rw [affineShift_J,affineShift_eval]
  convert he using 1 <;> first | rfl | ring

theorem quadraticSlope_second (r a : ℂ) :
    planeJet2 r (quadraticShift a (affineShift scaledSlope))=
      108*principalMass*(144*a-r^2) := by
  rw [quadraticShift_second,affineSlope_second,planeSlope_J]
  ring

def quadraticSlopeCore (r a : ℂ) : Polynomial ℂ :=
  (affineLine r (quadraticShift a (affineShift scaledSlope))).divX.divX

theorem quadraticSlope_coeff_zero (r a : ℂ) :
    (affineLine r (quadraticShift a (affineShift scaledSlope))).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,affineLine_eval]
  exact (quadraticShift_zero _ a r).trans (affineSlope_zero r)

theorem quadraticSlope_coeff_one (r a : ℂ) :
    (affineLine r (quadraticShift a (affineShift scaledSlope))).coeff 1=0 := by
  have he : ((affineLine r (quadraticShift a (affineShift scaledSlope))).derivative).eval 0=0 := by
    rw [affineLine_derivative,affineLine_eval]
    exact (quadraticShift_first _ a r).trans (affineSlope_first r)
  simpa [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] using he

theorem quadraticSlope_coeff_two (r a : ℂ) :
    (affineLine r (quadraticShift a (affineShift scaledSlope))).coeff 2=
      54*principalMass*(144*a-r^2) := by
  have he : ((affineLine r (quadraticShift a (affineShift scaledSlope))).derivative.derivative).eval 0=
      108*principalMass*(144*a-r^2) := by
    rw [affineLine_derivative,affineLine_derivative,affineLine_eval]
    exact quadraticSlope_second r a
  norm_num [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
  linear_combination he/2

theorem quadraticSlope_factor (r a : ℂ) :
    affineLine r (quadraticShift a (affineShift scaledSlope))=Polynomial.X^2*quadraticSlopeCore r a := by
  have h1 : affineLine r (quadraticShift a (affineShift scaledSlope))=
      Polynomial.X*(affineLine r (quadraticShift a (affineShift scaledSlope))).divX := by
    simpa [quadraticSlope_coeff_zero] using
      (Polynomial.X_mul_divX_add (affineLine r (quadraticShift a (affineShift scaledSlope)))).symm
  have h2 : (affineLine r (quadraticShift a (affineShift scaledSlope))).divX=
      Polynomial.X*quadraticSlopeCore r a := by
    simpa [quadraticSlopeCore,Polynomial.coeff_divX,quadraticSlope_coeff_one] using
      (Polynomial.X_mul_divX_add (affineLine r (quadraticShift a (affineShift scaledSlope))).divX).symm
  rw [h1,h2]
  ring

theorem quadraticSlopeCore_zero (r a : ℂ) :
    (quadraticSlopeCore r a).eval 0=54*principalMass*(144*a-r^2) := by
  simpa [quadraticSlopeCore,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_divX] using
    quadraticSlope_coeff_two r a

theorem quadraticSlope_value (h r a : ℝ) :
    regularSlopeValue h r (r*(1/12-7*h/72)+a*h^2)=
      h^2*((quadraticSlopeCore (r:ℂ) (a:ℂ)).eval (h:ℂ)).re := by
  have he := congrArg (Polynomial.eval (h:ℂ)) (quadraticSlope_factor (r:ℂ) (a:ℂ))
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    affineLine_eval,quadraticShift_eval,affineShift_eval,zero_add] at he
  have hcst : (a:ℂ)*(h:ℂ)^2+(r:ℂ)*(1/12-7*(h:ℂ)/72)=
      ((r*(1/12-7*h/72)+a*h^2:ℝ):ℂ) := by push_cast; ring
  rw [hcst] at he
  have hre := congrArg Complex.re he
  simpa only [regularSlopeValue,← Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre

theorem quadraticSlopeCore_real_zero (r a : ℝ) :
    ((quadraticSlopeCore (r:ℂ) (a:ℂ)).eval 0).re=
      54*((6:ℝ)^24*1990656*1679616)*(144*a-r^2) := by
  rw [quadraticSlopeCore_zero,principalMass_real]
  norm_cast

/-- Both signs survive; the second transverse sheet has an exact threshold. -/
theorem quadraticSlope_sign (r a : ℝ) :
    (r^2<144*a → ∀ᶠ h in 𝓝[>] (0:ℝ), 0<regularSlopeValue h r (r*(1/12-7*h/72)+a*h^2)) ∧
    (144*a<r^2 → ∀ᶠ h in 𝓝[>] (0:ℝ), regularSlopeValue h r (r*(1/12-7*h/72)+a*h^2)<0) := by
  have hc : Continuous (fun h : ℝ => ((quadraticSlopeCore (r:ℂ) (a:ℂ)).eval (h:ℂ)).re) :=
    Complex.continuous_re.comp ((quadraticSlopeCore (r:ℂ) (a:ℂ)).continuous.comp Complex.continuous_ofReal)
  have hC : 0<(54:ℝ)*((6:ℝ)^24*1990656*1679616) := by positivity
  constructor
  · intro ha
    have hz : 0<((quadraticSlopeCore (r:ℂ) (a:ℂ)).eval 0).re := by
      rw [quadraticSlopeCore_real_zero]
      exact mul_pos hC (sub_pos.mpr ha)
    have hn := hc.continuousAt.eventually_const_lt hz
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
    rw [quadraticSlope_value]
    exact mul_pos (sq_pos_of_pos hh) hn
  · intro ha
    have hz : ((quadraticSlopeCore (r:ℂ) (a:ℂ)).eval 0).re<0 := by
      rw [quadraticSlopeCore_real_zero]
      exact mul_neg_of_pos_of_neg hC (sub_neg.mpr ha)
    have hn := hc.continuousAt.eventually_lt_const hz
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
    rw [quadraticSlope_value]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hh) hn

end
end HTGeometry.ThetaRatioInfinity
