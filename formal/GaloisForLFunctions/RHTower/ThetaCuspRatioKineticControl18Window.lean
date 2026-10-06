import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticControl18Defect
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false

def control18NegativeWindow (t : ℝ) : ℝ :=
  -control18DefectQuotient (1/10+t/40) (361/25)

def control18NegativeWindowNorm (t : ℝ) : {c : ℝ // control18NegativeWindow t=c} := by
  have he : control18NegativeWindow t=control18NegativeWindow t := rfl
  conv at he =>
    rhs
    dsimp only [control18NegativeWindow,control18DefectQuotient,control18DefectRow4,control18DefectRow5,control18DefectRow6,control18DefectRow7,control18DefectRow8,control18DefectRow9,control18DefectRow10,control18DefectRow11,control18DefectRow12,control18DefectRow13,control18DefectRow14,control18DefectRow15,control18DefectRow16,control18DefectRow17,control18DefectRow18,control18DefectRow19,control18DefectRow20,control18DefectRow21,control18DefectRow22,control18DefectRow23,control18DefectRow24,control18DefectRow25,control18DefectRow26,control18DefectRow27,control18DefectRow28,control18DefectRow29,control18DefectRow30,control18DefectRow31,control18DefectRow32,control18DefectRow33,control18DefectRow34,control18DefectRow35,control18DefectRow36,control18DefectRow37,control18DefectRow38,control18DefectRow39,control18DefectRow40,control18DefectRow41,control18DefectRow42]
    norm_num [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioKineticContraction
