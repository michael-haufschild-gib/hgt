import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Powers
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
@[simp] theorem quadratic_re_ofNat (a b : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : QuadraticAlgebra ℂ a b).re=(ofNat(n) : ℂ) := rfl
@[simp] theorem quadratic_im_ofNat (a b : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : QuadraticAlgebra ℂ a b).im=0 := rfl
@[simp] theorem quadratic_re_rawCast (a b : ℂ) (n : ℕ) :
    (Nat.rawCast n : QuadraticAlgebra ℂ a b).re=(Nat.rawCast n : ℂ) := rfl
@[simp] theorem quadratic_im_rawCast (a b : ℂ) (n : ℕ) :
    (Nat.rawCast n : QuadraticAlgebra ℂ a b).im=0 := rfl
end
end HTGeometry.ThetaRatioInfinity
