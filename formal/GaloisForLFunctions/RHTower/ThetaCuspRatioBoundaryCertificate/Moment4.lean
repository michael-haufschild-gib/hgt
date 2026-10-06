import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Dynamics
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundaryMoment4ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).re=((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).re := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,moment4,moment4Part0,moment4Part1,moment4Part2,moment4Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryMoment4ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).im=((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k moment4).im := rfl
  conv at he =>
    rhs
    norm_num [boundaryHom,boundaryCoord,moment4,moment4Part0,moment4Part1,moment4Part2,moment4Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryFlow4ReNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).re=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).re=((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).re := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,moment4,moment4Part0,moment4Part1,moment4Part2,moment4Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def boundaryFlow4ImNorm (v k : ℂ) : {c : ℂ // ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).im=c} := by
  have hu : (Finset.univ : Finset Coord)={.U,.K,.J} := by ext i; cases i <;> simp
  have hUK : Coord.U ≠ Coord.K := by intro h; cases h
  have hUJ : Coord.U ≠ Coord.J := by intro h; cases h
  have hKU : Coord.K ≠ Coord.U := by intro h; cases h
  have hKJ : Coord.K ≠ Coord.J := by intro h; cases h
  have hJU : Coord.J ≠ Coord.U := by intro h; cases h
  have hJK : Coord.J ≠ Coord.K := by intro h; cases h
  have he : ((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).im=((6:ℂ)^(4+2)*24^(4/2))⁻¹*(boundaryHom v k (squareLie moment4)).im := rfl
  conv at he =>
    rhs
    rw [squareFlow_explicit75]
    norm_num [boundaryHom,boundaryCoord,moment4,moment4Part0,moment4Part1,moment4Part2,moment4Part3,
      squareLie,flow,squareField,hu,Finset.sum_insert,Finset.sum_singleton,pderiv_X,Pi.single_apply,pderiv_pow,hUK,hUJ,hKU,hKJ,hJU,hJK,(boundaryPowRe0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm0Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm1Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm2Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm3Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm4Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm5Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm6Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm7Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm8Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm9Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm10Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowRe11Norm (boundaryA v k) (boundaryB k)).property,(boundaryPowIm11Norm (boundaryA v k) (boundaryB k)).property]
    norm_num [boundaryA,boundaryB,boundaryMass,boundaryPowRe0Norm,boundaryPowIm0Norm,boundaryPowRe1Norm,boundaryPowIm1Norm,boundaryPowRe2Norm,boundaryPowIm2Norm,boundaryPowRe3Norm,boundaryPowIm3Norm,boundaryPowRe4Norm,boundaryPowIm4Norm,boundaryPowRe5Norm,boundaryPowIm5Norm,boundaryPowRe6Norm,boundaryPowIm6Norm,boundaryPowRe7Norm,boundaryPowIm7Norm,boundaryPowRe8Norm,boundaryPowIm8Norm,boundaryPowRe9Norm,boundaryPowIm9Norm,boundaryPowRe10Norm,boundaryPowIm10Norm,boundaryPowRe11Norm,boundaryPowIm11Norm]
    ring_nf (config := {mode := .raw})
    norm_num
    try ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩
end
end HTGeometry.ThetaRatioInfinity
