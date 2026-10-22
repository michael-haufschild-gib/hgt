import GaloisForLFunctions.RHTower.KRealTensorProduct
import GaloisForLFunctions.RHTower.CCM.CCMRationalArchimedeanSchwartzReal
import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteBruhatReal

/-!
# Real structure on rational adelic Bruhat simple tensors

This file combines the actual archimedean Schwartz factor and actual rational finite-adele
compactly supported locally constant factor by their algebraic complex tensor product.
The tensorwise sign-reflection is an even `KRealStructure`.

This is the algebraic simple-tensor core of `𝒮(𝔸_ℚ)`. Identification with the completed
Bruhat--Schwartz restricted tensor product and its LF topology remains outside this leaf. No
positivity, zero spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Algebraic rational adelic Bruhat--Schwartz simple-tensor carrier. -/
abbrev CCMRationalAdelicBruhatSimpleTensor :=
  TensorProduct ℂ CCMRationalArchimedeanSchwartz
    CCMRationalFiniteBruhatSchwartz

/-- Even Real structure on rational adelic Bruhat simple tensors. -/
def ccmRationalAdelicBruhatSimpleTensorKRealEven :
    KRealStructure false CCMRationalAdelicBruhatSimpleTensor :=
  kRealEvenTensorProduct
    ccmRationalArchimedeanSchwartzKRealEven
    ccmRationalFiniteBruhatKRealEven

@[simp]
theorem ccmRationalAdelicBruhatSimpleTensor_sigma_tmul
    (f : CCMRationalArchimedeanSchwartz)
    (g : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
      (f ⊗ₜ[ℂ] g) =
      ccmRationalArchimedeanSchwartzReflection f ⊗ₜ[ℂ]
        ccmRationalFiniteBruhatReflection g :=
  rfl

/-- Rational adelic simple-tensor reflection squares to the identity. -/
theorem ccmRationalAdelicBruhatSimpleTensor_sigma_sq
    (x : CCMRationalAdelicBruhatSimpleTensor) :
    ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
      (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x) = x :=
  ccmRationalAdelicBruhatSimpleTensorKRealEven.sq x

end RHTower
end GaloisForLFunctions
