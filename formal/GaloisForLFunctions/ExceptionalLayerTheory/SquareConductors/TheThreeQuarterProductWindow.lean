import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ClippedProductMeans
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SmoothedLongProducts

/-!
# The three-quarter product window on square conductors

Writing x=n², the fixed spline charges a bounded primitive at rate
x^(-3/2). The PVC factorial weight on products up to U has primitive
of size U² log U. Consequently all clipped coprime products up to
n floor(√n) have a logarithmic budget at both dilations together.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem reading_prefix_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0<n → ∀ (f : ℕ → ℝ) {M : ℝ}, 0 ≤ M →
    (∀ j : ℕ, j ≤ splineHorizon n → |∑ k ∈ Icc 1 j, f k| ≤ M) →
    |splineCountReading n f| ≤ C*M/(n:ℝ)^3 := by
  obtain ⟨A,hA,hbound⟩ := GaloisForLFunctions.CountingHolography.Sections.successorSquare_window_bound
  obtain ⟨B,D,hB,hD,hΔ⟩ := sampledSpline_differences
  refine ⟨A^2*D+B,by positivity,fun {n} hn f {M} hM hf => ?_⟩
  let L := splineHorizon n
  let g (k : ℕ) := sampledSpline n k-sampledSpline n (k+1)
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have ht : |(∑ k ∈ Icc 1 L, f k)*g (L+1)| ≤ M*(B/(n:ℝ)^3) := by
    rw [abs_mul]
    exact mul_le_mul (hf L le_rfl) (hΔ hn (L+1)).1 (abs_nonneg _) hM
  have hs : |∑ j ∈ Icc 1 L, (∑ k ∈ Icc 1 j, f k)*(g j-g (j+1))| ≤
      (A*n)^2*(M*(D/(n:ℝ)^5)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _j ∈ Icc 1 L, M*(D/(n:ℝ)^5) := by
            apply sum_le_sum; intro j hj
            rw [abs_mul]
            exact mul_le_mul (hf j (mem_Icc.mp hj).2) (hΔ hn j).2 (abs_nonneg _) hM
         _ ≤ _ := by
            rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
            exact mul_le_mul_of_nonneg_right (hbound hn) (by positivity)
  change |∑ k ∈ Icc 1 L, f k*g k| ≤ _
  rw [HTGeometry.sum_mul_eq_partial_mul_diff_ring]
  apply (abs_add_le _ _).trans ((add_le_add hs ht).trans_eq _)
  field_simp

/-- Before choosing the product scale, the spline pays U²/n³ times
the reciprocal-prime logarithm and the two stencil costs. -/
theorem spline_clipped_product_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n R U : ℕ}, 0<n → 1≤R → 1≤U →
      ∀ (D F : ℕ) (lo hi : ℕ → ℕ → ℕ),
      |splineCountReading n (clippedPrimeProducts D R F U lo hi)| ≤
        C*(2*(1+mass (D+1)))*(125*(1+mass R)*(128*(128*(R:ℝ)^2+1)))*
          (1+Real.log U)*(U:ℝ)^2/(n:ℝ)^3 := by
  obtain ⟨C,hC,h⟩ := reading_prefix_bound
  let E := Real.log 4+4
  have hE : 0≤E := by
    dsimp [E]; linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]
  refine ⟨C*E,mul_nonneg hC hE,fun {n R U} hn hR hU D F lo hi => ?_⟩
  let A := 2*(1+mass (D+1))
  let B := 125*(1+mass R)*(128*(128*(R:ℝ)^2+1))
  have hA : 0≤A := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hB : 0≤B := by dsimp [B]; positivity
  have hlog := Real.log_natCast_nonneg U
  let M := A*B*(U:ℝ)^2*(E*(1+Real.log U))
  have hM : 0≤M := by dsimp only [M]; positivity
  have hb := h hn (clippedPrimeProducts D R F U lo hi) hM fun j _ => by
    rw [show Icc 1 j=Ico 1 (j+1) by ext k; simp]
    exact clippedPrimeProducts_interval hR hU D F lo hi 1 (j+1)
  apply hb.trans_eq
  change C*(A*B*(U:ℝ)^2*(E*(1+Real.log U)))/(n:ℝ)^3 =
    C*E*A*B*(1+Real.log U)*(U:ℝ)^2/(n:ℝ)^3
  ring

/-- Uniform bound for the original signed spline, all first-prime
thresholds, and arbitrary pair-dependent sharp horizon intervals.
The divisor stencils retain their explicit parameter costs. -/
theorem spline_three_quarter_product_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n R U : ℕ}, 0<n → 1≤R → 1≤U → U≤n*n.sqrt →
      ∀ (D F : ℕ) (lo hi : ℕ → ℕ → ℕ),
      |splineCountReading n (clippedPrimeProducts D R F U lo hi)| ≤
        C*(2*(1+mass (D+1)))*(125*(1+mass R)*(128*(128*(R:ℝ)^2+1)))*(1+Real.log U) := by
  obtain ⟨C,hC,h⟩ := spline_clipped_product_bound
  refine ⟨C,hC,fun {n R U} hn hR hU hcut D F lo hi => ?_⟩
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hs : (U:ℝ)^2 ≤ (n:ℝ)^3 := by
    have hu : (U:ℝ)≤(n:ℝ)*n.sqrt := by exact_mod_cast hcut
    have hsq : (n.sqrt:ℝ)^2 ≤ n := by exact_mod_cast (show n.sqrt^2 ≤ n by simpa only [sq] using Nat.sqrt_le n)
    apply (pow_le_pow_left₀ (Nat.cast_nonneg U) hu 2).trans
    rw [mul_pow,pow_succ (n:ℝ) 2]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have hA := (abs_nonneg _).trans (innerJump_pointwise_bound D 0)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hlog := Real.log_natCast_nonneg U
  apply (h hn hR hU D F lo hi).trans
  exact (div_le_iff₀ (pow_pos hn' 3)).mpr (mul_le_mul_of_nonneg_left hs (by positivity))

#print axioms spline_clipped_product_bound
#print axioms spline_three_quarter_product_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
