import GaloisForLFunctions.CompletedArithmeticForms.WickCauchyPayment

/-!
# Exact Hermite coordinates for an entire moment source

Multiplication by `exp (-4z²)` is a monic triangular change of polynomial
coordinates. Its mixed generating kernel is the complete congruence of the
source moment form; every mixed coefficient and every lower coefficient is retained.
-/

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower.ThetaCuspGaussianLimit

/-- Gaussian multiplier generating the monic Hermite coordinate change. -/
def wickAmplitude (z : ℂ) : ℂ := Complex.exp (-4 * z ^ 2)

theorem wickAmplitude_entire : Differentiable ℂ wickAmplitude := by
  unfold wickAmplitude
  fun_prop

/-- The Hermite multiplier has the literal real Gaussian jets. -/
theorem wickAmplitude_jet (n : ℕ) :
    iteratedDeriv n wickAmplitude 0 = ((iteratedDeriv n profile (0 : ℝ) : ℝ) : ℂ) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) profile := by unfold profile; fun_prop
  have h := congrFun (_root_.HTGeometry.iteratedDeriv_comp_ofReal n wickAmplitude_entire) 0
  have he : (fun t : ℝ => wickAmplitude (t : ℂ)) =
      fun t : ℝ => (profile t : ℂ) := by
    funext t
    simp only [wickAmplitude, profile, Complex.ofReal_exp, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_pow]
  rw [he, GaloisForLFunctions.iteratedDeriv_ofReal_comp hp n] at h
  exact h.symm

/-- Coefficient of the degree `k` monomial in the monic degree `n` Hermite polynomial. -/
def hermiteJetCoefficient (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * iteratedDeriv (n - k) profile 0

theorem hermiteJetCoefficient_complex (n k : ℕ) :
    (hermiteJetCoefficient n k : ℂ) =
      (n.choose k : ℂ) * iteratedDeriv (n - k) wickAmplitude 0 := by
  rw [wickAmplitude_jet]
  simp only [hermiteJetCoefficient, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem hermiteJetCoefficient_zero_of_lt {n k : ℕ} (h : n < k) :
    hermiteJetCoefficient n k = 0 := by
  simp only [hermiteJetCoefficient, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul]

theorem hermiteJetCoefficient_diag (n : ℕ) : hermiteJetCoefficient n n = 1 := by
  simp [hermiteJetCoefficient, profile]

/-- A uniform coefficient envelope for transporting exponentially small source tails. -/
theorem hermiteJetCoefficient_abs_le (n k : ℕ) :
    |hermiteJetCoefficient n k| ≤ (n.factorial : ℝ) * Real.exp 4 := by
  have hc : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖wickAmplitude z‖ ≤ Real.exp 4 := by
    intro z hz
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    unfold wickAmplitude
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow, hzn, one_pow, mul_one]
    exact le_rfl
  have hj := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n - k)
    (by norm_num : (0 : ℝ) < 1) wickAmplitude_entire.diffContOnCl hc
  rw [wickAmplitude_jet, Complex.norm_real, Real.norm_eq_abs] at hj
  simp only [one_pow, div_one] at hj
  have hfac : (n.choose k : ℝ) * ((n - k).factorial : ℝ) ≤ (n.factorial : ℝ) := by
    by_cases hk : k ≤ n
    · have he : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
          (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
      have h1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by
        exact_mod_cast (show 1 ≤ k.factorial from k.factorial_pos)
      have hm := mul_le_mul_of_nonneg_left h1
        (show 0 ≤ (n.choose k : ℝ) * ((n - k).factorial : ℝ) by positivity)
      nlinarith only [he, hm]
    · simp only [Nat.choose_eq_zero_of_lt (by omega : n < k), Nat.cast_zero, zero_mul]
      positivity
  rw [hermiteJetCoefficient, _root_.abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (n.choose k : ℝ) * (((n - k).factorial : ℝ) * Real.exp 4) :=
      mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg _)
    _ = ((n.choose k : ℝ) * ((n - k).factorial : ℝ)) * Real.exp 4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le

/-- Entire two-variable kernel of the complete Hermite coordinate change. -/
def wickSourceKernel (F : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  wickAmplitude p.2 * (F (p.1 + p.2) * wickAmplitude p.1)

theorem contDiff_wickSourceKernel {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    ContDiff ℂ ∞ (wickSourceKernel F) := by
  have hf : ContDiff ℂ ∞ F := hF.contDiff
  have hg : ContDiff ℂ ∞ wickAmplitude := wickAmplitude_entire.contDiff
  unfold wickSourceKernel
  fun_prop

/-- The generic Hermite kernel is exactly the literal physical first-atom kernel. -/
theorem wickSourceKernel_firstAtom (x : ℝ) (p : ℂ × ℂ) :
    wickSourceKernel (firstAtomNormalizedRotatedPair x) p =
      firstAtomWickKernel x p.1 p.2 := by
  unfold wickSourceKernel wickAmplitude firstAtomWickKernel
  calc
    _ = (Complex.exp (-4 * p.1 ^ 2) * Complex.exp (-4 * p.2 ^ 2)) *
        firstAtomNormalizedRotatedPair x (p.1 + p.2) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

/-- The Gaussian comparison kernel is diagonal in the same exact coordinates. -/
theorem wickSourceKernel_gaussian (p : ℂ × ℂ) :
    wickSourceKernel (fun z : ℂ => Complex.exp (4 * z ^ 2)) p =
      Complex.exp (8 * p.1 * p.2) := by
  unfold wickSourceKernel wickAmplitude
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- The first mixed direction retains every lower Hermite coefficient. -/
theorem firstComplexJet_wickSourceKernel {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (i : ℕ) (w : ℂ) :
    firstComplexJet (wickSourceKernel F) i (0, w) =
      ∑ a ∈ range (i + 1), (hermiteJetCoefficient i a : ℂ) *
        (iteratedDeriv a F w * wickAmplitude w) := by
  rw [firstComplexJet_eq_iteratedDeriv]
  change iteratedDeriv i (fun z : ℂ => wickAmplitude w *
    (F (z + w) * wickAmplitude z)) 0 = _
  rw [_root_.iteratedDeriv_const_mul_field]
  have hf : Differentiable ℂ (fun z : ℂ => F (z + w)) := hF.comp (by fun_prop)
  rw [iteratedDeriv_fun_mul hf.contDiff.contDiffAt wickAmplitude_entire.contDiff.contDiffAt,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have ht := congrFun (iteratedDeriv_comp_add_const a F w) 0
  simp only [zero_add] at ht
  rw [ht, hermiteJetCoefficient_complex]
  ring

private theorem iteratedDeriv_iterated_add (F : ℂ → ℂ) (a b : ℕ) :
    iteratedDeriv b (iteratedDeriv a F) 0 = iteratedDeriv (a + b) F 0 := by
  simp only [iteratedDeriv_eq_iterate]
  rw [Nat.add_comm a b, Function.iterate_add_apply]

/-- Exact double coefficient identity for the complete mixed jet. -/
theorem mixedKernelJet_wickSourceKernel {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (i j : ℕ) :
    mixedKernelJet (wickSourceKernel F) i j =
      ∑ a ∈ range (i + 1), ∑ b ∈ range (j + 1),
        (hermiteJetCoefficient i a : ℂ) * (hermiteJetCoefficient j b : ℂ) *
          iteratedDeriv (a + b) F 0 := by
  have hd (a : ℕ) : Differentiable ℂ (iteratedDeriv a F) :=
    ContDiff.differentiable_iteratedDeriv' a hF.contDiff
  have he : (fun w : ℂ => firstComplexJet (wickSourceKernel F) i (0, w)) =
      fun w : ℂ => ∑ a ∈ range (i + 1), (hermiteJetCoefficient i a : ℂ) *
        (iteratedDeriv a F w * wickAmplitude w) :=
    funext (firstComplexJet_wickSourceKernel hF i)
  rw [mixedKernelJet, he]
  have hterm (a : ℕ) : ContDiffAt ℂ j
      (fun w : ℂ => (hermiteJetCoefficient i a : ℂ) *
        (iteratedDeriv a F w * wickAmplitude w)) 0 := by
    have ha := hd a
    have hg := wickAmplitude_entire
    have hc : Differentiable ℂ (fun w : ℂ => (hermiteJetCoefficient i a : ℂ) *
        (iteratedDeriv a F w * wickAmplitude w)) := by fun_prop
    exact hc.contDiff.contDiffAt
  rw [iteratedDeriv_fun_sum (f := fun a w => (hermiteJetCoefficient i a : ℂ) *
    (iteratedDeriv a F w * wickAmplitude w)) (fun a _ => hterm a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [_root_.iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (hd a).contDiff.contDiffAt wickAmplitude_entire.contDiff.contDiffAt,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [iteratedDeriv_iterated_add]
  simp only [hermiteJetCoefficient_complex]
  ring

/-- Finite triangular Hermite coefficient matrix in the literal real coordinates. -/
def hermiteJetMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => hermiteJetCoefficient i.val j.val

theorem hermiteJetMatrix_lowerTriangular (N : ℕ) :
    (hermiteJetMatrix N).BlockTriangular OrderDual.toDual := by
  intro i j hij
  exact hermiteJetCoefficient_zero_of_lt hij

theorem hermiteJetMatrix_det (N : ℕ) : (hermiteJetMatrix N).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (hermiteJetMatrix_lowerTriangular N)]
  simp only [hermiteJetMatrix, hermiteJetCoefficient_diag, Finset.prod_const_one]

/-- The Hermite change loses no polynomial direction at any finite rank. -/
theorem hermiteJetMatrix_transpose_injective (N : ℕ) :
    Function.Injective (hermiteJetMatrix N).transpose.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_transpose, hermiteJetMatrix_det]
  exact isUnit_one

theorem hermiteJetMatrix_transpose_surjective (N : ℕ) :
    Function.Surjective (hermiteJetMatrix N).transpose.mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    Matrix.det_transpose, hermiteJetMatrix_det]
  exact isUnit_one

private theorem sum_range_eq_of_zero_after {f : ℕ → ℂ} {m N : ℕ} (hm : m ≤ N)
    (hf : ∀ k, m ≤ k → f k = 0) : ∑ k ∈ range N, f k = ∑ k ∈ range m, f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro k hkN hkm
  exact hf k (by simpa only [Finset.mem_range, not_lt] using hkm)

/-- A finite head contains the full Hermite expansion of every one of its entries. -/
theorem mixedKernelJet_wickSourceKernel_eq_finite_sum {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {N i j : ℕ} (hi : i < N) (hj : j < N) :
    mixedKernelJet (wickSourceKernel F) i j =
      ∑ a ∈ range N, ∑ b ∈ range N,
        (hermiteJetCoefficient i a : ℂ) * (hermiteJetCoefficient j b : ℂ) *
          iteratedDeriv (a + b) F 0 := by
  rw [mixedKernelJet_wickSourceKernel hF]
  symm
  calc
    _ = ∑ a ∈ range (i + 1), ∑ b ∈ range N,
        (hermiteJetCoefficient i a : ℂ) * (hermiteJetCoefficient j b : ℂ) *
          iteratedDeriv (a + b) F 0 := by
      apply sum_range_eq_of_zero_after (by omega)
      intro a ha
      simp only [hermiteJetCoefficient_zero_of_lt (by omega : i < a),
        Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply sum_range_eq_of_zero_after (by omega)
      intro b hb
      simp only [hermiteJetCoefficient_zero_of_lt (by omega : j < b),
        Complex.ofReal_zero, mul_zero, zero_mul]

/-- Real moment head of an entire source, before any polynomial coordinate change. -/
def realEntireMomentMatrix (F : ℂ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (iteratedDeriv (i.val + j.val) F 0).re

/-- Complete mixed Hermite head of the same source. -/
def realWickJetMatrix (F : ℂ → ℂ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (mixedKernelJet (wickSourceKernel F) i.val j.val).re

/-- Exact complete-form congruence; lower coefficients and all cross terms remain present. -/
theorem realWickJetMatrix_eq_congruence {F : ℂ → ℂ} (hF : Differentiable ℂ F) (N : ℕ) :
    realWickJetMatrix F N =
      hermiteJetMatrix N * realEntireMomentMatrix F N * (hermiteJetMatrix N).transpose := by
  ext i j
  change (mixedKernelJet (wickSourceKernel F) i.val j.val).re =
    ∑ b : Fin N, (∑ a : Fin N, hermiteJetCoefficient i.val a.val *
      (iteratedDeriv (a.val + b.val) F 0).re) * hermiteJetCoefficient j.val b.val
  rw [mixedKernelJet_wickSourceKernel_eq_finite_sum hF i.isLt j.isLt]
  have hsum (s : Finset ℕ) (f : ℕ → ℂ) :
      (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := map_sum Complex.reAddGroupHom _ _
  simp only [hsum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => ∑ a : Fin N,
    (hermiteJetCoefficient i.val a.val * (iteratedDeriv (a.val + b) F 0).re) *
      hermiteJetCoefficient j.val b) N]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
    (hermiteJetCoefficient i.val a * (iteratedDeriv (a + b) F 0).re) *
      hermiteJetCoefficient j.val b) N]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The real Hermite comparison head is exactly diagonal, including its factorial norm. -/
theorem realWickJetMatrix_gaussian (N : ℕ) :
    realWickJetMatrix (fun z : ℂ => Complex.exp (4 * z ^ 2)) N =
      Matrix.diagonal (fun i : Fin N => (8 : ℝ) ^ i.val * (i.val.factorial : ℝ)) := by
  have he : wickSourceKernel (fun z : ℂ => Complex.exp (4 * z ^ 2)) =
      fun p : ℂ × ℂ => Complex.exp (8 * p.1 * p.2) := funext wickSourceKernel_gaussian
  ext i j
  rw [realWickJetMatrix, he, mixedKernelJet_gaussian]
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    change ((8 : ℂ) ^ i.val * (i.val.factorial : ℂ)).re =
      (8 : ℝ) ^ i.val * (i.val.factorial : ℝ)
    norm_cast
  · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hv]

#print axioms mixedKernelJet_wickSourceKernel
#print axioms hermiteJetMatrix_det
#print axioms hermiteJetMatrix_transpose_injective
#print axioms hermiteJetMatrix_transpose_surjective
#print axioms hermiteJetCoefficient_abs_le
#print axioms realWickJetMatrix_eq_congruence
#print axioms realWickJetMatrix_gaussian

end GaloisForLFunctions.CompletedArithmeticForms
