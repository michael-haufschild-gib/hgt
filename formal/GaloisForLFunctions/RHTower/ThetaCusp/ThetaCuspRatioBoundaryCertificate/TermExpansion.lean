import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryCertificate.RealCore
import Mathlib.Data.Nat.Choose.Sum
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open scoped BigOperators

def boundaryTerm77 (c : ℝ) (a p j : ℕ) (h s : ℝ) : ℝ :=
  c*h^a*s^p*(boundaryR77 h s)^j

def boundaryTermScalar77 (c : ℝ) (j l m : ℕ) : ℝ :=
  c*(j.choose l:ℝ)*(l.choose m:ℝ)*(-1/12)^(l-m)*(7/72)^m

theorem boundaryTerm77_expansion (c : ℝ) (a p j : ℕ) (h s : ℝ) :
    boundaryTerm77 c a p j h s=
      ∑ l ∈ Finset.range (j+1), ∑ m ∈ Finset.range (l+1),
        boundaryTermScalar77 c j l m*h^(a+2*l+m)*s^(p+j+l) := by
  have hR : boundaryR77 h s=s*((7/72*h^3*s+(-1/12)*h^2*s)+1) := by
    unfold boundaryR77
    ring
  calc
    _ = c*h^a*s^(p+j)*((7/72*h^3*s+(-1/12)*h^2*s)+1)^j := by
      rw [boundaryTerm77,hR,mul_pow,pow_add]
      ring
    _ = c*h^a*s^(p+j)*
        (∑ l ∈ Finset.range (j+1),
          (7/72*h^3*s+(-1/12)*h^2*s)^l*1^(j-l)*(j.choose l:ℝ)) := by
      rw [add_pow]
    _ = ∑ l ∈ Finset.range (j+1),
        c*h^a*s^(p+j)*((7/72*h^3*s+(-1/12)*h^2*s)^l*(j.choose l:ℝ)) := by
      simp only [one_pow,mul_one,Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [add_pow]
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hml : m≤l := by have := Finset.mem_range.mp hm; omega
      have hh : h^(a+2*l+m)=h^a*(h^3)^m*(h^2)^(l-m) := by
        rw [←pow_mul,←pow_mul,←pow_add,←pow_add]
        congr 1
        omega
      have hs : s^(p+j+l)=s^(p+j)*s^m*s^(l-m) := by
        rw [←pow_add,←pow_add]
        congr 1
        omega
      rw [hh,hs]
      simp only [mul_pow,boundaryTermScalar77]
      ring

end
end HTGeometry.ThetaRatioInfinity
