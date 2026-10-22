import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioIntegerReflections
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioJetTenBalanced
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioProductBalanced1
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioProductBalanced2
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioProductBalanced3
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioProductBalanced4
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioProductBalanced5
/-! # Exact algebraic certificate supporting the ratio-source third-slope seam cone. -/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial

private theorem reflection_ten_split : integerReflection 10=
    2*(integerJet 0*integerJet 10)-20*(integerJet 1*integerJet 9)+
    90*(integerJet 2*integerJet 8)-240*(integerJet 3*integerJet 7)+
    420*(integerJet 4*integerJet 6)-252*(integerJet 5*integerJet 5) := by
  norm_num [integerReflection,Finset.sum_range_succ,Nat.choose]
  ring

def reflectionNorm10 : {P : Poly // integerReflection 10=P} := by
  have h : integerReflection 10=integerReflection 10 := rfl
  conv at h =>
    rhs
    rw [reflection_ten_split,productBalanced1_eq,productBalanced2_eq,
      productBalanced3_eq,productBalanced4_eq,productBalanced5_eq,
      jetNorm0.property,jetTenBalanced_eq]
    dsimp only [jetNorm0,jetTenBalanced,productBalanced1,productBalanced2,productBalanced3,productBalanced4,productBalanced5,product1Part0,product1Part1,product1Part2,product1Part3,product1Part4,product1Part5,product1Part6,product1Part7,product1Part8,product1Part9,product1Part10,product1Part11,product1Part12,product1Part13,product1Part14,product1Part15,product1Part16,product1Part17,product1Part18,product1Part19,product1Part20,product1Part21,product1Part22,product1Part23,product2Part0,product2Part1,product2Part2,product2Part3,product2Part4,product2Part5,product2Part6,product2Part7,product2Part8,product2Part9,product2Part10,product2Part11,product2Part12,product2Part13,product2Part14,product2Part15,product2Part16,product2Part17,product2Part18,product2Part19,product2Part20,product2Part21,product2Part22,product2Part23,product2Part24,product3Part0,product3Part1,product3Part2,product3Part3,product3Part4,product3Part5,product3Part6,product3Part7,product3Part8,product3Part9,product3Part10,product3Part11,product3Part12,product3Part13,product3Part14,product3Part15,product3Part16,product3Part17,product3Part18,product3Part19,product3Part20,product3Part21,product3Part22,product3Part23,product4Part0,product4Part1,product4Part2,product4Part3,product4Part4,product4Part5,product4Part6,product4Part7,product4Part8,product4Part9,product4Part10,product4Part11,product4Part12,product4Part13,product4Part14,product4Part15,product4Part16,product4Part17,product4Part18,product4Part19,product4Part20,product4Part21,product4Part22,product4Part23,product4Part24,product5Part0,product5Part1,product5Part2,product5Part3,product5Part4,product5Part5,product5Part6,product5Part7,product5Part8,product5Part9,product5Part10,product5Part11,product5Part12,product5Part13,product5Part14,product5Part15,product5Part16,product5Part17,product5Part18,product5Part19,product5Part20,product5Part21,product5Part22,product5Part23,jetTenPart0,jetTenPart1,jetTenPart2,jetTenPart3,jetTenPart4,jetTenPart5,jetTenPart6,jetTenPart7,jetTenPart8,jetTenPart9,jetTenPart10,jetTenPart11,jetTenPart12,jetTenPart13,jetTenPart14,jetTenPart15,jetTenPart16,jetTenPart17,jetTenPart18,jetTenPart19,jetTenPart20,jetTenPart21]
    norm_num only [Nat.rawCast,Int.rawCast]
    ring_nf (config := {mode := .raw})
  exact ⟨_,h⟩

end
end HTGeometry.ThetaRatioSource
