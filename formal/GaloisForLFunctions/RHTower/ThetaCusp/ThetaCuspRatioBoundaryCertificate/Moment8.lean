import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Dynamics
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundaryMoment8ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).re=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,moment8,moment8Part0,moment8Part1,moment8Part2,moment8Part3,moment8Part4,moment8Part5,moment8Part6,moment8Part7,moment8Part8,moment8Part9,moment8Part10,moment8Part11,moment8Part12,moment8Part13,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryMoment8ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).im=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k moment8).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,moment8,moment8Part0,moment8Part1,moment8Part2,moment8Part3,moment8Part4,moment8Part5,moment8Part6,moment8Part7,moment8Part8,moment8Part9,moment8Part10,moment8Part11,moment8Part12,moment8Part13,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroup8_0 : Poly := moment8Part0+moment8Part1+moment8Part2+moment8Part3

def boundaryGroupFlow8_0ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).re=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).re := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_0,moment8Part0,moment8Part1,moment8Part2,moment8Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupFlow8_0ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).im=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_0)).im := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_0,moment8Part0,moment8Part1,moment8Part2,moment8Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩
def boundaryGroup8_1 : Poly := moment8Part4+moment8Part5+moment8Part6+moment8Part7

def boundaryGroupFlow8_1ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).re=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).re := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_1,moment8Part4,moment8Part5,moment8Part6,moment8Part7,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupFlow8_1ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).im=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_1)).im := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_1,moment8Part4,moment8Part5,moment8Part6,moment8Part7,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩
def boundaryGroup8_2 : Poly := moment8Part8+moment8Part9+moment8Part10+moment8Part11

def boundaryGroupFlow8_2ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).re=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).re := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_2,moment8Part8,moment8Part9,moment8Part10,moment8Part11,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupFlow8_2ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).im=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_2)).im := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_2,moment8Part8,moment8Part9,moment8Part10,moment8Part11,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩
def boundaryGroup8_3 : Poly := moment8Part12+moment8Part13

def boundaryGroupFlow8_3ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).re=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).re := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_3,moment8Part12,moment8Part13,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupFlow8_3ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).im=((6:ℂ)^(8+2)*24^(8/2))⁻¹*(boundaryHom v k (squareLie boundaryGroup8_3)).im := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,boundaryGroup8_3,moment8Part12,moment8Part13,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩
def boundaryFlow8ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).re=c} := by
  have hs : moment8=boundaryGroup8_0+boundaryGroup8_1+boundaryGroup8_2+boundaryGroup8_3 := by unfold moment8 boundaryGroup8_0 boundaryGroup8_1 boundaryGroup8_2 boundaryGroup8_3; ring
  have he : ((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).re=((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).re := rfl
  conv at he =>
    rhs
    rw [hs]
    simp only [squareLie,flow_add,map_add,QuadraticAlgebra.re_add,mul_add]
    rw [(boundaryGroupFlow8_0ReNorm v k).property,(boundaryGroupFlow8_1ReNorm v k).property,(boundaryGroupFlow8_2ReNorm v k).property,(boundaryGroupFlow8_3ReNorm v k).property]
    norm_num [boundaryGroupFlow8_0ReNorm,boundaryGroupFlow8_1ReNorm,boundaryGroupFlow8_2ReNorm,boundaryGroupFlow8_3ReNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryFlow8ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).im=c} := by
  have hs : moment8=boundaryGroup8_0+boundaryGroup8_1+boundaryGroup8_2+boundaryGroup8_3 := by unfold moment8 boundaryGroup8_0 boundaryGroup8_1 boundaryGroup8_2 boundaryGroup8_3; ring
  have he : ((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).im=((6:ℂ)^10*24^4)⁻¹*(boundaryHom v k (squareLie moment8)).im := rfl
  conv at he =>
    rhs
    rw [hs]
    simp only [squareLie,flow_add,map_add,QuadraticAlgebra.im_add,mul_add]
    rw [(boundaryGroupFlow8_0ImNorm v k).property,(boundaryGroupFlow8_1ImNorm v k).property,(boundaryGroupFlow8_2ImNorm v k).property,(boundaryGroupFlow8_3ImNorm v k).property]
    norm_num [boundaryGroupFlow8_0ImNorm,boundaryGroupFlow8_1ImNorm,boundaryGroupFlow8_2ImNorm,boundaryGroupFlow8_3ImNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
