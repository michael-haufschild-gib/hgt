import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalSecondJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioAxisSlope
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare


@[simp] private theorem pd_nat71 (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

theorem partials_commute (i j : Coord) (P : Poly) :
    pderiv i (pderiv j P)=pderiv j (pderiv i P) := by
  have hc : ∀ a b c : Coord,
      pderiv a ((Pi.single b 1 : Coord → Poly) c)=0 := by
    intro a b c
    rw [Pi.single_apply]
    split <;> simp
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p l hp =>
    simp only [Derivation.leibniz,pderiv_X,map_add,smul_eq_mul,hc,mul_zero,zero_add]
    rw [hp]
    ring

def affineD (r : ℂ) (P : Poly) : Poly := pderiv Coord.U P-C (7*r/72)*pderiv Coord.J P
def criticalValue (r : ℂ) (P : Poly) : ℂ := eval (basePoint 0 r (r/12)) P
def affineJet1 (r : ℂ) (P : Poly) : ℂ := criticalValue r (affineD r P)
def affineJet2 (r : ℂ) (P : Poly) : ℂ := criticalValue r (affineD r (affineD r P))

@[simp] theorem affineJet1_add (r : ℂ) (P Q : Poly) :
    affineJet1 r (P+Q)=affineJet1 r P+affineJet1 r Q := by
  simp [affineJet1,affineD,criticalValue]; ring
@[simp] theorem affineJet1_sub (r : ℂ) (P Q : Poly) :
    affineJet1 r (P-Q)=affineJet1 r P-affineJet1 r Q := by
  simp [affineJet1,affineD,criticalValue]; ring
@[simp] theorem affineJet1_neg (r : ℂ) (P : Poly) :
    affineJet1 r (-P)= -affineJet1 r P := by
  simp [affineJet1,affineD,criticalValue]; ring
@[simp] theorem affineJet1_mul (r : ℂ) (P Q : Poly) :
    affineJet1 r (P*Q)=affineJet1 r P*criticalValue r Q+
      criticalValue r P*affineJet1 r Q := by
  simp [affineJet1,affineD,criticalValue,pderiv_mul]; ring
@[simp] theorem affineJet2_add (r : ℂ) (P Q : Poly) :
    affineJet2 r (P+Q)=affineJet2 r P+affineJet2 r Q := by
  simp [affineJet2,affineD,criticalValue,pderiv_mul]; ring
@[simp] theorem affineJet2_sub (r : ℂ) (P Q : Poly) :
    affineJet2 r (P-Q)=affineJet2 r P-affineJet2 r Q := by
  simp [affineJet2,affineD,criticalValue,pderiv_mul]; ring
@[simp] theorem affineJet2_neg (r : ℂ) (P : Poly) :
    affineJet2 r (-P)= -affineJet2 r P := by
  simp [affineJet2,affineD,criticalValue,pderiv_mul]; ring
@[simp] theorem affineJet2_mul (r : ℂ) (P Q : Poly) :
    affineJet2 r (P*Q)=affineJet2 r P*criticalValue r Q+
      2*affineJet1 r P*affineJet1 r Q+criticalValue r P*affineJet2 r Q := by
  simp [affineJet2,affineJet1,affineD,criticalValue,pderiv_mul]; ring
@[simp] theorem affineJet1_C (r c : ℂ) : affineJet1 r (C c)=0 := by
  simp [affineJet1,affineD,criticalValue]
@[simp] theorem affineJet2_C (r c : ℂ) : affineJet2 r (C c)=0 := by
  simp [affineJet2,affineD,criticalValue]
@[simp] theorem affineJet1_nat (r : ℂ) (n : ℕ) [n.AtLeastTwo] :
    affineJet1 r (ofNat(n) : Poly)=0 := by simp [affineJet1,affineD,criticalValue]
@[simp] theorem affineJet2_nat (r : ℂ) (n : ℕ) [n.AtLeastTwo] :
    affineJet2 r (ofNat(n) : Poly)=0 := by simp [affineJet2,affineD,criticalValue]
@[simp] theorem affineJet1_h (r : ℂ) : affineJet1 r (X Coord.U)=1 := by
  simp [affineJet1,affineD,criticalValue,pderiv_X,Pi.single_apply]
@[simp] theorem affineJet2_h (r : ℂ) : affineJet2 r (X Coord.U)=0 := by
  have huj : Coord.U≠Coord.J := by intro h; cases h
  norm_num [affineJet2,affineD,criticalValue,pderiv_X,Pi.single_apply,huj]

/-- Differentiation in t of the exact critical-face moment identity. -/
theorem critical_partial_J (P : Poly) (r t : ℂ) :
    HasDerivAt (fun s => eval (basePoint 0 r s) P)
      (eval (basePoint 0 r t) (pderiv Coord.J P)) t := by
  have hd : HasDerivAt (fun s => basePoint 0 r s)
      (fun i => if i=Coord.J then (1:ℂ) else 0) t := by
    apply hasDerivAt_pi.mpr
    intro i
    cases i with
    | U => simpa [basePoint] using hasDerivAt_const t (0:ℂ)
    | K => simpa [basePoint] using hasDerivAt_const t r
    | J =>
      convert hasDerivAt_id t using 1 <;> first | rfl | simp [basePoint]
  have he := GaloisForLFunctions.HTGeometry.hasDerivAt_mvPolynomial_eval_comp P hd
  simpa [Finset.sum_ite_eq'] using he

theorem criticalMoment10_J (r : ℂ) :
    criticalValue r (pderiv Coord.J scaledMoment10)= -(12:ℂ)*6^12*1679616 := by
  have hd := critical_partial_J scaledMoment10 r (r/12)
  simp_rw [scaledMoment10_zero] at hd
  have hc := ((hasDerivAt_const (r/12) r).sub ((hasDerivAt_id (r/12)).const_mul 12)).const_mul
    ((6:ℂ)^12*1679616)
  convert hd.unique hc using 1 <;> simp [criticalValue] <;> ring

theorem criticalMoment8_J (r : ℂ) :
    criticalValue r (pderiv Coord.J scaledMoment8)= -(12:ℂ)*6^10*46656 := by
  have hd := critical_partial_J scaledMoment8 r (r/12)
  simp_rw [scaledMoment8_zero] at hd
  have hc := ((hasDerivAt_const (r/12) r).sub ((hasDerivAt_id (r/12)).const_mul 12)).const_mul
    ((6:ℂ)^10*46656)
  convert hd.unique hc using 1 <;> simp [criticalValue] <;> ring

theorem affineMoment10_first (r : ℂ) : affineJet1 r scaledMoment10=0 := by
  have hU := criticalMoment10First_eq r
  have hJ := criticalMoment10_J r
  change criticalValue r (pderiv Coord.U scaledMoment10)=_ at hU
  simp only [affineJet1,affineD,criticalValue,map_sub,map_mul,eval_C]
  change criticalValue r (pderiv Coord.U scaledMoment10)-7*r/72*
    criticalValue r (pderiv Coord.J scaledMoment10)=0
  rw [hU,hJ]
  ring

theorem affineMoment8_first (r : ℂ) : affineJet1 r scaledMoment8=(6:ℂ)^10*105*24^4 := by
  have hJ := criticalMoment8_J r
  simp only [affineJet1,affineD,criticalValue,map_sub,map_mul,eval_C]
  change jet8U r-7*r/72*criticalValue r (pderiv Coord.J scaledMoment8)=_
  rw [(jet8UNorm r).property,hJ]
  norm_num [jet8UNorm]
  ring

theorem affineMoment10_second (r : ℂ) :
    affineJet2 r scaledMoment10= -2*(6:ℂ)^12*945*24^5+
      ((6:ℂ)^12*1679616/6)*r^2 := by
  have he : affineJet2 r scaledMoment10=jet10UU r-(7*r/36)*jet10UJ r+
      (7*r/72)^2*jet10JJ r := by
    simp [affineJet2,affineD,criticalValue,partials_commute Coord.J Coord.U,
      jet10UU,jet10UJ,jet10JJ]
    ring
  rw [he,(jet10UUNorm r).property,(jet10UJNorm r).property,(jet10JJNorm r).property]
  norm_num [jet10UUNorm,jet10UJNorm,jet10JJNorm]
  ring

theorem affineMinor_second (r : ℂ) :
    affineJet2 r scaledMinor=2*axisMinorMass-(principalMass/6)*r^2 := by
  have hz : r-12*(r/12)=0 := by ring
  simp only [scaledMinor,pow_succ,affineJet2_add,affineJet2_sub,affineJet2_neg,
    affineJet2_mul,affineJet1_neg,affineJet1_mul,
    affineMoment10_first,affineMoment10_second,affineMoment8_first,
    affineJet1_h,affineJet2_h,affineJet1_nat,affineJet2_nat]
  norm_num [criticalValue,basePoint,scaledMoment2_zero,scaledMoment4_zero,
    scaledMoment6_zero,scaledMoment8_zero,scaledMoment10_zero,hz,
    axisMinorMass,principalMass]
  ring

end
end HTGeometry.ThetaRatioInfinity
