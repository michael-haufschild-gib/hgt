import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioDeterminantSeam
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

private theorem univ_eq : (Finset.univ : Finset Coord)={.U,.K,.J} := by
  ext i
  cases i <;> simp

@[simp] private theorem pd_ofNat (i : Coord) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : Poly)=0 := (pderiv i).map_natCast n

def seamSlopeAlpha (k : ℂ) : ℂ :=
  (6*k-1)*(54*k*(detSeamUU k).val+6*(9*k^2-6*k-4)*(detSeamUJ k).val)

def seamSlopeBeta (k : ℂ) : ℂ :=
  (6*k-1)*(54*k*(detSeamJU k).val+6*(9*k^2-6*k-4)*(detSeamJJ k).val+
    (12*k+4)*(detSeamK k).val)-6*(detSeamValue k).val*(72*k+24)

theorem seamSlopeAlpha_eq (k : ℂ) :
    eval (seamPoint k) (pderiv Coord.U integerThirdSlope)=seamSlopeAlpha k := by
  have hu : eval (seamPoint k) (pderiv Coord.U seamDetModel)=0 := by
    rw [(detSeamU k).property]
    rfl
  have hj : eval (seamPoint k) (pderiv Coord.J seamDetModel)=0 := by
    rw [(detSeamJ k).property]
    rfl
  unfold integerThirdSlope
  rw [integerThirdMinor_model]
  simp [integerLie,univ_eq,integerField,integerJet,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,
    seamPoint,hu,hj,(detSeamUU k).property,(detSeamUJ k).property,seamSlopeAlpha]
  ring_nf <;> simp

theorem seamSlopeBeta_eq (k : ℂ) :
    eval (seamPoint k) (pderiv Coord.J integerThirdSlope)=seamSlopeBeta k := by
  have hu : eval (seamPoint k) (pderiv Coord.U seamDetModel)=0 := by
    rw [(detSeamU k).property]
    rfl
  have hj : eval (seamPoint k) (pderiv Coord.J seamDetModel)=0 := by
    rw [(detSeamJ k).property]
    rfl
  unfold integerThirdSlope
  rw [integerThirdMinor_model]
  simp [integerLie,univ_eq,integerField,integerJet,pderiv_X,Pi.single_apply,pderiv_one,pderiv_C,pderiv_mul,pderiv_pow,
    seamPoint,hu,hj,(detSeamJU k).property,(detSeamJJ k).property,
    (detSeamK k).property,(detSeamValue k).property,seamSlopeBeta]
  ring_nf <;> simp

def seamAlphaNorm (k : ℂ) : {a : ℂ // seamSlopeAlpha k=a} := by
  have h : seamSlopeAlpha k=seamSlopeAlpha k := rfl
  conv at h =>
    rhs
    dsimp only [seamSlopeAlpha,detSeamUU,detSeamUJ]
    ring_nf
  exact ⟨_,h⟩

def seamBetaNorm (k : ℂ) : {a : ℂ // seamSlopeBeta k=a} := by
  have h : seamSlopeBeta k=seamSlopeBeta k := rfl
  conv at h =>
    rhs
    dsimp only [seamSlopeBeta,detSeamJU,detSeamJJ,detSeamK,detSeamValue]
    ring_nf
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
