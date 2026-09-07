import GaloisForLFunctions.HTGeometry.MiddleHankelPerturbation

/-! # Exact binomial collapse of the reflected two-atom error majorant -/
namespace HTGeometry

/-- The two linear tail contributions and all five quadratic contributions sum exactly. -/
theorem twoAtom_reflected_majorant_eq (n : ℕ) (a b δ : ℝ) :
    (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
      (((0 : ℝ)^i+a^i/100+2*b^i*δ)*(b^(n-i)*δ)+
        (b^i*δ)*((0 : ℝ)^(n-i)+a^(n-i)/100+2*b^(n-i)*δ)+
        (b^i*δ)*(b^(n-i)*δ))) =
      2*b^n*δ+(a+b)^n*δ/50+5*(b+b)^n*δ^2 := by
  have he : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
      (((0 : ℝ)^i+a^i/100+2*b^i*δ)*(b^(n-i)*δ)+
        (b^i*δ)*((0 : ℝ)^(n-i)+a^(n-i)/100+2*b^(n-i)*δ)+
        (b^i*δ)*(b^(n-i)*δ))) =
      (0+b)^n*δ+(b+0)^n*δ+(a+b)^n*δ/100+(b+a)^n*δ/100+5*(b+b)^n*δ^2 := by
    simp only [add_pow, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  simp only [zero_add, add_zero, add_comm b a]
  ring

end HTGeometry
