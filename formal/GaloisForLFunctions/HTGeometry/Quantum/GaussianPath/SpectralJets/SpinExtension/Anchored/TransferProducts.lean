import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.SpinProducts

/-! # Both transverse responses at one physical spin background -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M := Matrix I I ℂ

/-- At W = V = I + X the ZX bond changes both transverse blocks by Z.
Their ordered product changes by twice Z. -/
theorem marked_product_velocity (X Z : M) (ha : Z*X=-(X*Z)) :
    Z*(1+X)+(1+X)*Z=(2:ℂ) • Z := by
  rw [mul_add,add_mul,one_mul,mul_one,ha,two_smul]
  abel

/-- The YY bond gives opposite imaginary increments. The sector sign
in their product cancels the sign of the virtual energy denominator. -/
theorem unmarked_product_velocity (X Y Z : M) (hxy : X*Y=Complex.I • Z)
    (hyx : Y*X=(-Complex.I) • Z) (τ : ℂ) :
    ((-(Complex.I*τ)) • Y)*(1+X)+(1+X)*((Complex.I*τ) • Y)=(-2*τ) • Z := by
  rw [Matrix.smul_mul,Matrix.mul_smul,mul_add,add_mul,one_mul,mul_one,hxy,hyx]
  simp only [smul_add,smul_smul]
  have h₁ : -(Complex.I*τ)*(-Complex.I) = -τ := by
    calc _ = (Complex.I*Complex.I)*τ := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  have h₂ : (Complex.I*τ)*Complex.I = -τ := by
    calc _ = (Complex.I*Complex.I)*τ := by ring
         _ = _ := by rw [Complex.I_mul_I]; ring
  rw [h₁,h₂]
  module

#print axioms marked_product_velocity
#print axioms unmarked_product_velocity
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.Anchored
