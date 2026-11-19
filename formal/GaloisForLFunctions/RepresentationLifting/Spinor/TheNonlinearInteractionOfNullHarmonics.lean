import GaloisForLFunctions.RepresentationLifting.Spinor.SphericalNullHarmonics

/-!
# Nonlinear interaction of homogeneous null harmonics

The critical-jet obstruction for planar p-harmonic functions in Lemma 2.1
of arXiv:2611.24842 leads to an explicit polynomial test on null lifts.
A single null wave annihilates the complexified principal polynomial for
every p. A pair interacts through exactly the square of its bilinear overlap.
For real-valued polynomials this is the usual p-Laplacian multiplied by the
gradient norm to the power 4−p wherever the gradient is nonzero.
-/

noncomputable section
open MvPolynomial Finset
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
namespace GaloisForLFunctions.RepresentationLifting.Spinor
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hessian evaluated twice on the gradient, using the bilinear polynomial extension. -/
def infinityPolynomial (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  ∑ i, ∑ j, pderiv i P*pderiv j P*pderiv i (pderiv j P)

/-- Polynomial form of the p-Laplacian with the singular gradient factor cleared. -/
def clearedPLaplacian (p : ℂ) (P : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  (∑ i, (pderiv i P)^2)*euclideanPolynomialLaplacian P+C (p-2)*infinityPolynomial P

/-- Complex bilinear overlap of the polarizations. -/
def waveOverlap (a b : ι → ℂ) : ℂ := ∑ i, a i*b i

private lemma grad_wave (a : ι → ℂ) (m : ℕ) (i : ι) :
    pderiv i (momentLinearForm ℂ a^(m+1)) =
      C (a i)*(C ((m+1:ℕ):ℂ)*momentLinearForm ℂ a^m) := by
  rw [pderiv_pow,pderiv_momentLinearForm,Nat.add_sub_cancel,map_natCast]
  ring

private lemma hess_wave (a : ι → ℂ) (m : ℕ) (i j : ι) :
    pderiv i (pderiv j (momentLinearForm ℂ a^(m+2))) =
      (C (((m+2)*(m+1):ℕ):ℂ)*momentLinearForm ℂ a^m)*(C (a i)*C (a j)) := by
  rw [grad_wave a (m+1),pderiv_C_mul,pderiv_C_mul,grad_wave]
  simp only [Nat.cast_mul,map_mul]
  ring

private lemma rank_one_contraction {R : Type*} [CommRing R] (a g : ι → R) (c : R) :
    (∑ i, ∑ j, g i*g j*(c*(a i*a j))) = c*(∑ i, a i*g i)^2 := by
  rw [sq,Finset.sum_mul,Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  exact sum_congr rfl fun j _ => by ring

private lemma wave_direction (a b : ι → ℂ) (m : ℕ) :
    (∑ i, C (a i)*pderiv i (momentLinearForm ℂ b^(m+1))) =
      C (waveOverlap a b)*(C ((m+1:ℕ):ℂ)*momentLinearForm ℂ b^m) := by
  simp only [grad_wave, ← mul_assoc, ← Finset.sum_mul, ← map_mul, ← map_sum,waveOverlap]

private theorem overlap_self_zero (q : Fin d → ℝ) :
    waveOverlap (nullPolarization q) (nullPolarization q)=0 := by
  have hh := nullPolarization_square q
  rw [euclideanComplexForm_apply] at hh
  simpa only [waveOverlap,← sq,Fintype.sum_option] using hh

/-- A single isotropic wave has zero gradient square as well as zero
ordinary Laplacian, so it survives every complexified polynomial p-test. -/
theorem null_wave_cleared_p_laplacian (q : Fin d → ℝ) (m : ℕ) (p : ℂ) :
    clearedPLaplacian p (momentLinearForm ℂ (nullPolarization q)^(m+2))=0 := by
  rw [clearedPLaplacian,nullPolarization_harmonic,mul_zero,zero_add]
  simp only [infinityPolynomial,hess_wave,rank_one_contraction,wave_direction,overlap_self_zero,
    map_zero,zero_mul,zero_pow (by decide : 2 ≠ 0),mul_zero]

/-- Exact nonlinear interaction of two null waves. The overlap enters
quadratically and no self-interaction survives. -/
theorem null_pair_cleared_p_laplacian (q r : Fin d → ℝ) (m : ℕ) (p : ℂ) :
    let a := nullPolarization q
    let b := nullPolarization r
    let L := momentLinearForm ℂ a
    let M := momentLinearForm ℂ b
    clearedPLaplacian p (L^(m+2)+M^(m+2)) =
      C ((p-2)*(((m+2:ℕ):ℂ)^3)*((m+1:ℕ):ℂ)*(waveOverlap a b)^2)*
        (L*M)^m*(L^(m+2)+M^(m+2)) := by
  dsimp only
  let a := nullPolarization q
  let b := nullPolarization r
  let L := momentLinearForm ℂ a
  let M := momentLinearForm ℂ b
  let P := L^(m+2)+M^(m+2)
  have hl : euclideanPolynomialLaplacian P=0 := by
    simp only [P,euclideanPolynomialLaplacian,map_add,sum_add_distrib]
    change euclideanPolynomialLaplacian (L^(m+2))+euclideanPolynomialLaplacian (M^(m+2))=0
    rw [nullPolarization_harmonic,nullPolarization_harmonic,add_zero]
  have hab : waveOverlap b a=waveOverlap a b := sum_congr rfl fun i _ => mul_comm _ _
  have d₁ : (∑ i, C (a i)*pderiv i P)=C (waveOverlap a b)*(C ((m+2:ℕ):ℂ)*M^(m+1)) := by
    simp only [P,map_add,mul_add,sum_add_distrib,L,M,wave_direction,overlap_self_zero,
      map_zero,zero_mul,zero_add,a,b]
  have d₂ : (∑ i, C (b i)*pderiv i P)=C (waveOverlap a b)*(C ((m+2:ℕ):ℂ)*L^(m+1)) := by
    simp only [P,map_add,mul_add,sum_add_distrib,L,M,wave_direction,overlap_self_zero,
      map_zero,zero_mul,add_zero,hab,a,b]
  change clearedPLaplacian p P = _
  rw [clearedPLaplacian,hl,mul_zero,zero_add]
  have hh (i j : Option (Fin d)) : pderiv i (pderiv j P) =
      (C (((m+2)*(m+1):ℕ):ℂ)*L^m)*(C (a i)*C (a j))+
      (C (((m+2)*(m+1):ℕ):ℂ)*M^m)*(C (b i)*C (b j)) := by
    simp only [P,map_add,L,M,hess_wave]
  simp only [infinityPolynomial,hh,mul_add,sum_add_distrib,rank_one_contraction,d₁,d₂]
  change _ = C _*(L*M)^m*(L^(m+2)+M^(m+2))
  simp only [map_mul,map_pow,Nat.cast_mul,mul_pow,pow_succ L,pow_succ M]
  ring

private lemma eval_linear (a b : ι → ℂ) :
    MvPolynomial.eval b (momentLinearForm ℂ a)=waveOverlap a b := by
  simp [momentLinearForm_apply,smul_eq_C_mul,waveOverlap]

/-- The interacting pair survives exactly at the linear exponent p=2 or
at zero bilinear overlap. Evaluation in the opposite null direction
certifies the polynomial factors whenever the overlap is nonzero. -/
theorem null_pair_p_harmonic_iff (q r : Fin d → ℝ) (m : ℕ) (p : ℂ) :
    let L := momentLinearForm ℂ (nullPolarization q)
    let M := momentLinearForm ℂ (nullPolarization r)
    clearedPLaplacian p (L^(m+2)+M^(m+2))=0 ↔
      p=2 ∨ waveOverlap (nullPolarization q) (nullPolarization r)=0 := by
  dsimp only
  rw [null_pair_cleared_p_laplacian]
  by_cases hc : waveOverlap (nullPolarization q) (nullPolarization r)=0
  · simp [hc]
  let a := nullPolarization q
  let b := nullPolarization r
  have hba : waveOverlap b a ≠ 0 := by
    rw [show waveOverlap b a=waveOverlap a b from sum_congr rfl fun _ _ => mul_comm _ _]
    exact hc
  have hL : momentLinearForm ℂ a ≠ 0 := fun h => hc (by rw [← eval_linear a b,h,map_zero])
  have hM : momentLinearForm ℂ b ≠ 0 := fun h => hba (by rw [← eval_linear b a,h,map_zero])
  have hS : momentLinearForm ℂ a^(m+2)+momentLinearForm ℂ b^(m+2) ≠ 0 := by
    intro he
    have h := congrArg (MvPolynomial.eval b) he
    simp only [map_add,map_pow,eval_linear,overlap_self_zero,map_zero,zero_pow (by omega : m+2 ≠ 0),add_zero] at h
    exact pow_ne_zero _ hc h
  change _ ↔ p=2 ∨ waveOverlap a b=0
  simp [hc,hL,hM,hS,mul_eq_zero,sub_eq_zero,a,b] at *

#print axioms null_wave_cleared_p_laplacian
#print axioms null_pair_p_harmonic_iff

end GaloisForLFunctions.RepresentationLifting.Spinor
