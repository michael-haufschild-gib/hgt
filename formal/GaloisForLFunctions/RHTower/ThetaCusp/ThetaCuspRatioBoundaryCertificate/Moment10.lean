import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.Flow10
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundaryGroupMoment10_0ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_0,moment10Part0,moment10Part1,moment10Part2,moment10Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_0ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_0).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_0,moment10Part0,moment10Part1,moment10Part2,moment10Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryGroupMoment10_1ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_1,moment10Part4,moment10Part5,moment10Part6,moment10Part7,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_1ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_1).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_1,moment10Part4,moment10Part5,moment10Part6,moment10Part7,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryGroupMoment10_2ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_2,moment10Part8,moment10Part9,moment10Part10,moment10Part11,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_2ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_2).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_2,moment10Part8,moment10Part9,moment10Part10,moment10Part11,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryGroupMoment10_3ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_3,moment10Part12,moment10Part13,moment10Part14,moment10Part15,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_3ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_3).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_3,moment10Part12,moment10Part13,moment10Part14,moment10Part15,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryGroupMoment10_4ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_4,moment10Part16,moment10Part17,moment10Part18,moment10Part19,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_4ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_4).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_4,moment10Part16,moment10Part17,moment10Part18,moment10Part19,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryGroupMoment10_5ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).re=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_5,moment10Part20,moment10Part21,moment10Part22,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryGroupMoment10_5ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).im=((6:ℂ)^(10+2)*24^(10/2))⁻¹*(boundaryHom v k boundaryGroup10_5).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,boundaryGroup10_5,moment10Part20,moment10Part21,moment10Part22,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩


def boundaryMoment10ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).re=c} := by
  have hs : moment10=boundaryGroup10_0+boundaryGroup10_1+boundaryGroup10_2+boundaryGroup10_3+boundaryGroup10_4+boundaryGroup10_5 := by
    unfold moment10 boundaryGroup10_0 boundaryGroup10_1 boundaryGroup10_2 boundaryGroup10_3 boundaryGroup10_4 boundaryGroup10_5
    ring
  have he : ((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).re=((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).re := rfl
  conv at he =>
    rhs
    rw [hs]
    simp only [map_add,QuadraticAlgebra.re_add,mul_add]
    rw [(boundaryGroupMoment10_0ReNorm v k).property,(boundaryGroupMoment10_1ReNorm v k).property,(boundaryGroupMoment10_2ReNorm v k).property,(boundaryGroupMoment10_3ReNorm v k).property,(boundaryGroupMoment10_4ReNorm v k).property,(boundaryGroupMoment10_5ReNorm v k).property]
    norm_num [boundaryGroupMoment10_0ReNorm,boundaryGroupMoment10_1ReNorm,boundaryGroupMoment10_2ReNorm,boundaryGroupMoment10_3ReNorm,boundaryGroupMoment10_4ReNorm,boundaryGroupMoment10_5ReNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryMoment10ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).im=c} := by
  have hs : moment10=boundaryGroup10_0+boundaryGroup10_1+boundaryGroup10_2+boundaryGroup10_3+boundaryGroup10_4+boundaryGroup10_5 := by
    unfold moment10 boundaryGroup10_0 boundaryGroup10_1 boundaryGroup10_2 boundaryGroup10_3 boundaryGroup10_4 boundaryGroup10_5
    ring
  have he : ((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).im=((6:ℂ)^12*24^5)⁻¹*(boundaryHom v k moment10).im := rfl
  conv at he =>
    rhs
    rw [hs]
    simp only [map_add,QuadraticAlgebra.im_add,mul_add]
    rw [(boundaryGroupMoment10_0ImNorm v k).property,(boundaryGroupMoment10_1ImNorm v k).property,(boundaryGroupMoment10_2ImNorm v k).property,(boundaryGroupMoment10_3ImNorm v k).property,(boundaryGroupMoment10_4ImNorm v k).property,(boundaryGroupMoment10_5ImNorm v k).property]
    norm_num [boundaryGroupMoment10_0ImNorm,boundaryGroupMoment10_1ImNorm,boundaryGroupMoment10_2ImNorm,boundaryGroupMoment10_3ImNorm,boundaryGroupMoment10_4ImNorm,boundaryGroupMoment10_5ImNorm]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

end
end HTGeometry.ThetaRatioInfinity
