import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactBernstein.Basis
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open Finset EvenCompactBernstein

def kineticBernstein (n : ℕ) (f : ℕ → ℝ) (e : ℝ) : ℝ :=
  ∑ i ∈ range (n+1), f i*unscaledBernstein n i e

def kineticBernsteinDifference (n : ℕ) (f : ℕ → ℝ) (e : ℝ) : ℝ :=
  ∑ i ∈ range n, (f i-(n.choose i:ℝ)*f n)*unscaledBernstein (n-1) i e

theorem bernstein_partition (n : ℕ) (e : ℝ) :
    ∑ i ∈ range (n+1), (n.choose i:ℝ)*unscaledBernstein n i e=1 := by
  simpa [degreeElevationCoefficient] using monomial_bernstein_reconstruction n 0 (by omega) e

theorem bernstein_drop (n i : ℕ) (hi : i<n) (e : ℝ) :
    unscaledBernstein n i e=(1-e)*unscaledBernstein (n-1) i e := by
  have he : n-i=(n-1-i)+1 := by omega
  simp only [unscaledBernstein,he,pow_succ]
  ring

theorem complete_bernstein_difference (n : ℕ) (f : ℕ → ℝ) (e : ℝ) :
    kineticBernstein n f e-f n=(1-e)*kineticBernsteinDifference n f e := by
  have hfull : kineticBernstein n f e-f n=
      ∑ i ∈ range (n+1), (f i-(n.choose i:ℝ)*f n)*unscaledBernstein n i e := by
    simp only [kineticBernstein,sub_mul,sum_sub_distrib]
    have hc : ∑ i ∈ range (n+1), (n.choose i:ℝ)*f n*unscaledBernstein n i e=f n := by
      calc
        _ = f n*(∑ i ∈ range (n+1), (n.choose i:ℝ)*unscaledBernstein n i e) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _ = f n := by rw [bernstein_partition,mul_one]
    rw [hc]
  rw [hfull,sum_range_succ]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,sub_self,zero_mul,add_zero]
  unfold kineticBernsteinDifference
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [bernstein_drop n i (mem_range.mp hi)]
  ring

end
end HTGeometry.ThetaRatioKineticContraction
