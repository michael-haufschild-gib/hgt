import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianConeRigidity

/-!
# A fixed Gaussian probe reads the zero width on a natural two-prime cone

The Gaussian-damped actual spline kernel has natural-cone coupling of rate
`σ` exactly when the actual zero width is at most `σ`. Four forward
coupling differences recover the shifted moments; absolute summation gives
the converse. Bounded coupling is therefore equivalent to RH for every
fixed positive damping parameter, without an attained-width assumption.
-/

open Complex Finset
open Zeta23
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling

/-- The actual spline kernel with a fixed Gaussian spectral multiplier. -/
def gaussianConeKernel (τ t : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, mult t ρ*gaussianSplineWeight τ ρ

/-- Mixed coupling of the Gaussian-damped kernel on the positive natural cone. -/
def gaussianConeCoupling (τ a b : ℝ) (m n : ℕ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier,
    (mult a ρ^m-1)*(mult b ρ^n-1)*gaussianSplineWeight τ ρ

lemma summable_gaussian_base_moment {τ : ℝ} (hτ : 0 ≤ τ)
    (a b : ℝ) (m n : ℕ) : Summable fun ρ : zetaZeroConfig.carrier =>
      mult a ρ^m*mult b ρ^n*gaussianSplineWeight τ ρ := by
  apply Summable.of_norm
  have hs := (summable_mult_pow a b m n).norm.mul_left (Real.exp (τ/4))
  refine hs.of_nonneg_of_le (fun ρ => norm_nonneg _) fun ρ => ?_
  have he : mult a ρ^m*mult b ρ^n*gaussianSplineWeight τ ρ =
      gaussianDamping τ ρ*(mult a ρ^m*mult b ρ^n*wt ρ) := by
    unfold gaussianSplineWeight
    ring
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_gaussianDamping_le_constant hτ ρ) (norm_nonneg _)

lemma summable_gaussian_coupling {τ : ℝ} (hτ : 0 ≤ τ)
    (a b : ℝ) (m n : ℕ) : Summable fun ρ : zetaZeroConfig.carrier =>
      (mult a ρ^m-1)*(mult b ρ^n-1)*gaussianSplineWeight τ ρ := by
  have hs := (((summable_gaussian_base_moment hτ a b m n).sub
    (summable_gaussian_base_moment hτ a b m 0)).sub
    (summable_gaussian_base_moment hτ a b 0 n)).add
    (summable_gaussian_base_moment hτ a b 0 0)
  refine hs.congr fun ρ => ?_
  simp only [pow_zero,mul_one,one_mul]
  ring

lemma gaussianConeKernel_natural (τ a b : ℝ) (m n : ℕ) :
    gaussianConeKernel τ ((m:ℝ)*a+(n:ℝ)*b) =
      ∑' ρ : zetaZeroConfig.carrier, mult a ρ^m*mult b ρ^n*gaussianSplineWeight τ ρ := by
  apply tsum_congr
  intro ρ
  congr 1
  unfold mult
  rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul,← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The spectral coupling is exactly the four-term difference of the scalar kernel. -/
lemma gaussianConeCoupling_eq_kernel_difference {τ : ℝ} (hτ : 0 ≤ τ)
    (a b : ℝ) (m n : ℕ) :
    gaussianConeCoupling τ a b m n =
      gaussianConeKernel τ ((m:ℝ)*a+(n:ℝ)*b)-gaussianConeKernel τ ((m:ℝ)*a)-
        gaussianConeKernel τ ((n:ℝ)*b)+gaussianConeKernel τ 0 := by
  have hKm := gaussianConeKernel_natural τ a b m 0
  have hKn := gaussianConeKernel_natural τ a b 0 n
  have hK0 := gaussianConeKernel_natural τ a b 0 0
  simp only [Nat.cast_zero,zero_mul,add_zero,zero_add] at hKm hKn hK0
  rw [gaussianConeKernel_natural,hKm,hKn,hK0,
    ← ((((summable_gaussian_base_moment hτ a b m n).hasSum.sub
      (summable_gaussian_base_moment hτ a b m 0).hasSum).sub
      (summable_gaussian_base_moment hτ a b 0 n).hasSum).add
      (summable_gaussian_base_moment hτ a b 0 0).hasSum).tsum_eq]
  apply tsum_congr
  intro ρ
  simp only [pow_zero,mul_one,one_mul]
  ring

/-- Mixed forward differences recover the Gaussian-damped residue moments. -/
lemma gaussian_mixed_moment_eq_coupling_difference {τ : ℝ} (hτ : 0 ≤ τ)
    (a b : ℝ) (m n : ℕ) :
    (∑' ρ : zetaZeroConfig.carrier, gaussianMixedResidue τ a b ρ*mult a ρ^m*mult b ρ^n) =
      gaussianConeCoupling τ a b (m+1) (n+1)-gaussianConeCoupling τ a b (m+1) n-
        gaussianConeCoupling τ a b m (n+1)+gaussianConeCoupling τ a b m n := by
  unfold gaussianConeCoupling
  rw [← ((((summable_gaussian_coupling hτ a b (m+1) (n+1)).hasSum.sub
    (summable_gaussian_coupling hτ a b (m+1) n).hasSum).sub
    (summable_gaussian_coupling hτ a b m (n+1)).hasSum).add
    (summable_gaussian_coupling hτ a b m n).hasSum).tsum_eq]
  apply tsum_congr
  intro ρ
  simp only [gaussianMixedResidue,gaussianSplineWeight,mixedResidue,pow_succ]
  ring

lemma shifted_gaussian_moment_eq (τ σ a b : ℝ) (m n : ℕ) :
    (∑' ρ : zetaZeroConfig.carrier, gaussianMixedResidue τ a b ρ*
      shiftedClock σ a ρ^m*shiftedClock σ b ρ^n) =
    Complex.exp (((-σ*((m:ℝ)*a+(n:ℝ)*b):ℝ):ℂ))*
      (∑' ρ : zetaZeroConfig.carrier, gaussianMixedResidue τ a b ρ*mult a ρ^m*mult b ρ^n) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro ρ
  have hc : shiftedClock σ a ρ^m*shiftedClock σ b ρ^n =
      Complex.exp (((-σ*((m:ℝ)*a+(n:ℝ)*b):ℝ):ℂ))*(mult a ρ^m*mult b ρ^n) := by
    simp only [shiftedClock,mult,zeroOffset,← Complex.exp_nat_mul,← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = gaussianMixedResidue τ a b ρ*(shiftedClock σ a ρ^m*shiftedClock σ b ρ^n) := by ring
    _ = _ := by rw [hc]; ring

/-- Four coupling bounds give a uniform bound for the radially shifted Gaussian moments. -/
lemma gaussian_shifted_moment_bound_of_cone_rate {τ σ a b M : ℝ}
    (hτ : 0 ≤ τ)
    (hM : ∀ m n : ℕ, ‖gaussianConeCoupling τ a b m n‖ ≤
      M*Real.exp (σ*((m:ℝ)*a+(n:ℝ)*b))) (m n : ℕ) :
    ‖∑' ρ : zetaZeroConfig.carrier, gaussianMixedResidue τ a b ρ*
      shiftedClock σ a ρ^m*shiftedClock σ b ρ^n‖ ≤
      M*(Real.exp (σ*(a+b))+Real.exp (σ*a)+Real.exp (σ*b)+1) := by
  let r := Real.exp (-σ*((m:ℝ)*a+(n:ℝ)*b))
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hinc (i j : ℕ) : r*‖gaussianConeCoupling τ a b (m+i) (n+j)‖ ≤
      M*Real.exp (σ*((i:ℝ)*a+(j:ℝ)*b)) := by
    calc
      _ ≤ r*(M*Real.exp (σ*(((m+i:ℕ):ℝ)*a+((n+j:ℕ):ℝ)*b))) :=
        mul_le_mul_of_nonneg_left (hM (m+i) (n+j)) hr
      _ = _ := by
        have he : r*Real.exp (σ*(((m+i:ℕ):ℝ)*a+((n+j:ℕ):ℝ)*b)) =
            Real.exp (σ*((i:ℝ)*a+(j:ℝ)*b)) := by
          dsimp only [r]
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        calc
          _ = M*(r*Real.exp (σ*(((m+i:ℕ):ℝ)*a+((n+j:ℕ):ℝ)*b))) := by ring
          _ = _ := by rw [he]
  have h11 := hinc 1 1
  have h10 := hinc 1 0
  have h01 := hinc 0 1
  have h00 := hinc 0 0
  simp only [Nat.cast_zero,Nat.cast_one,zero_mul,mul_zero,one_mul,add_zero,zero_add,Real.exp_zero,mul_one] at h11 h10 h01 h00
  rw [shifted_gaussian_moment_eq,norm_mul,Complex.norm_exp,Complex.ofReal_re,
    gaussian_mixed_moment_eq_coupling_difference hτ]
  change r*‖gaussianConeCoupling τ a b (m+1) (n+1)-gaussianConeCoupling τ a b (m+1) n-
    gaussianConeCoupling τ a b m (n+1)+gaussianConeCoupling τ a b m n‖ ≤ _
  calc
    _ ≤ r*(‖gaussianConeCoupling τ a b (m+1) (n+1)‖+‖gaussianConeCoupling τ a b (m+1) n‖+
        ‖gaussianConeCoupling τ a b m (n+1)‖+‖gaussianConeCoupling τ a b m n‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_sub_add_le _ _ _ _) hr
    _ = r*‖gaussianConeCoupling τ a b (m+1) (n+1)‖+r*‖gaussianConeCoupling τ a b (m+1) n‖+
        r*‖gaussianConeCoupling τ a b m (n+1)‖+r*‖gaussianConeCoupling τ a b m n‖ := by ring
    _ ≤ M*Real.exp (σ*(a+b))+M*Real.exp (σ*a)+M*Real.exp (σ*b)+M :=
      add_le_add (add_le_add (add_le_add h11 h10) h01) h00
    _ = _ := by ring

/-- A zero-width bound controls the Gaussian cone coupling by absolute summation. -/
lemma norm_gaussianConeCoupling_le_of_width {τ σ a b : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hwidth : zetaZeroWidth ≤ σ) (m n : ℕ) :
    ‖gaussianConeCoupling τ a b m n‖ ≤
      (4*(∑' ρ : zetaZeroConfig.carrier, ‖gaussianSplineWeight τ ρ‖))*
        Real.exp (σ*((m:ℝ)*a+(n:ℝ)*b)) := by
  have hclock (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (ρ : zetaZeroConfig.carrier) :
      ‖mult c ρ^k-1‖ ≤ 2*Real.exp (σ*(k:ℝ)*c) := by
    have hδ := (zeroOffset_re_le_width ρ).trans hwidth
    have hpow : ‖mult c ρ‖^k ≤ Real.exp (σ*(k:ℝ)*c) := by
      rw [norm_mult,← zeroOffset_re,← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hδ (mul_nonneg (Nat.cast_nonneg k) hc)
      nlinarith only [hh]
    have he : 1 ≤ Real.exp (σ*(k:ℝ)*c) := Real.one_le_exp_iff.mpr (by positivity)
    have ht := norm_sub_le (mult c ρ^k) (1:ℂ)
    rw [norm_pow,norm_one] at ht
    linarith only [ht,hpow,he]
  let K := 4*Real.exp (σ*((m:ℝ)*a+(n:ℝ)*b))
  have hpoint (ρ : zetaZeroConfig.carrier) :
      ‖(mult a ρ^m-1)*(mult b ρ^n-1)*gaussianSplineWeight τ ρ‖ ≤
        K*‖gaussianSplineWeight τ ρ‖ := by
    rw [norm_mul,norm_mul]
    have hh := mul_le_mul (hclock a ha m ρ) (hclock b hb n ρ) (norm_nonneg _) (by positivity)
    have he : (2*Real.exp (σ*(m:ℝ)*a))*(2*Real.exp (σ*(n:ℝ)*b))=K := by
      calc
        _ = 4*(Real.exp (σ*(m:ℝ)*a)*Real.exp (σ*(n:ℝ)*b)) := by ring
        _ = K := by
          rw [← Real.exp_add]
          dsimp only [K]
          congr 2
          ring
    rw [he] at hh
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  have hs := (summable_gaussian_coupling hτ a b m n).norm
  have hmajor := (summable_norm_gaussianSplineWeight hτ).mul_left K
  calc
    _ ≤ ∑' ρ : zetaZeroConfig.carrier,
        ‖(mult a ρ^m-1)*(mult b ρ^n-1)*gaussianSplineWeight τ ρ‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' ρ : zetaZeroConfig.carrier, K*‖gaussianSplineWeight τ ρ‖ := hs.tsum_le_tsum hpoint hmajor
    _ = _ := by rw [tsum_mul_left]; dsimp only [K]; ring

/-- For every fixed positive Gaussian damping, natural two-prime cone growth
reads the full actual zero width, without an attainment assumption. -/
theorem zetaZeroWidth_le_iff_gaussian_coneCoupling_rate {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {τ σ : ℝ}
    (hτ : 0 < τ) (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∃ M : ℝ, ∀ m n : ℕ,
      ‖gaussianConeCoupling τ (Real.log p) (Real.log q) m n‖ ≤
        M*Real.exp (σ*((m:ℝ)*Real.log p+(n:ℝ)*Real.log q)) := by
  constructor
  · intro hwidth
    refine ⟨4*(∑' ρ : zetaZeroConfig.carrier, ‖gaussianSplineWeight τ ρ‖),?_⟩
    intro m n
    exact norm_gaussianConeCoupling_le_of_width hτ.le hσ
      (Real.log_pos (by exact_mod_cast hp.one_lt)).le
      (Real.log_pos (by exact_mod_cast hq.one_lt)).le hwidth m n
  · rintro ⟨M,hM⟩
    apply (zetaZeroWidth_le_iff_bounded_gaussian_moments hp hq hpq hτ hσ).mpr
    refine ⟨M*(Real.exp (σ*(Real.log p+Real.log q))+Real.exp (σ*Real.log p)+
      Real.exp (σ*Real.log q)+1),?_⟩
    exact gaussian_shifted_moment_bound_of_cone_rate hτ.le hM

/-- A fixed Gaussian-damped spline probe detects RH from bounded coupling on
one natural two-prime cone. The zeros themselves are not deformed. -/
theorem riemannHypothesis_iff_bounded_gaussian_coneCoupling {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {τ : ℝ} (hτ : 0 < τ) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ m n : ℕ,
      ‖gaussianConeCoupling τ (Real.log p) (Real.log q) m n‖ ≤ M := by
  have he := zetaZeroWidth_le_iff_gaussian_coneCoupling_rate hp hq hpq hτ (σ := 0) le_rfl
  simp only [zero_mul,Real.exp_zero,mul_one] at he
  constructor
  · intro hRH
    apply he.mp
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH]
  · intro hbound
    apply riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    exact le_antisymm (he.mpr hbound) zetaZeroWidth_nonneg

#print axioms gaussianConeCoupling_eq_kernel_difference
#print axioms zetaZeroWidth_le_iff_gaussian_coneCoupling_rate
#print axioms riemannHypothesis_iff_bounded_gaussian_coneCoupling
#print axioms gaussian_shifted_moment_bound_of_cone_rate
#print axioms gaussian_mixed_moment_eq_coupling_difference
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
