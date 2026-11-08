import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveTwoPrimeAnnihilators
import GaloisForLFunctions.RHTower.EisensteinHeckeOperator

/-!
# Positive Hecke annihilators of finite resonances

A finite set of nontrivial zeta zeros can be annihilated by a polynomial with
nonnegative coefficients in the Hecke eigenvalues at two and three. Its constant
coefficient is one. Powers impose arbitrary prescribed zero multiplicities.

The eigenvalues `p^u+p^(-u)` at `u=(ρ-1)/2` cannot both lie on the nonnegative
real axis. A power of a nontrivial unit phase enters the left half-plane; the
quadratic with that root and its conjugate then has positive coefficients.
-/

set_option autoImplicit false

open Complex Finset
open scoped NNReal

noncomputable section
namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

open ArithmeticPositiveDuality.PositiveAnnihilator

/-- The two Hecke eigenvalues, in an entire exponential parametrization. -/
def eigenvalue (i : Fin 2) (u : ℂ) : ℂ :=
  Complex.exp ((Real.log (primeBase i) : ℂ) * u) +
    Complex.exp (-((Real.log (primeBase i) : ℂ) * u))

/-- Evaluation of a positive polynomial on the two Hecke eigenvalues. -/
def spectralEval (u : ℂ) : MvPolynomial (Fin 2) ℝ≥0 →+* ℂ :=
  MvPolynomial.eval₂Hom (Complex.ofRealHom.comp NNReal.toRealHom)
    (fun i => eigenvalue i u)

private theorem exp_pair_not_nonnegative_real {L : ℝ} (hL : 0 < L) {u : ℂ}
    (hu : u.re < 0)
    (hphase : Complex.exp (-(L : ℂ) * (u.im : ℂ) * I) ≠ 1) :
    (Complex.exp ((L : ℂ) * u) + Complex.exp (-((L : ℂ) * u))).im ≠ 0 ∨
      (Complex.exp ((L : ℂ) * u) + Complex.exp (-((L : ℂ) * u))).re < 0 := by
  by_contra! h
  have ha : Real.exp (L * u.re) < Real.exp (-(L * u.re)) := by
    apply Real.exp_lt_exp.mpr
    have hn := mul_neg_of_pos_of_neg hL hu
    linarith only [hn]
  have him :
      (Complex.exp ((L : ℂ) * u) + Complex.exp (-((L : ℂ) * u))).im =
        (Real.exp (L * u.re) - Real.exp (-(L * u.re))) * Real.sin (L * u.im) := by
    simp only [Complex.add_im, Complex.exp_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      Complex.neg_re, Complex.neg_im, Real.sin_neg]
    ring
  have hre :
      (Complex.exp ((L : ℂ) * u) + Complex.exp (-((L : ℂ) * u))).re =
        (Real.exp (L * u.re) + Real.exp (-(L * u.re))) * Real.cos (L * u.im) := by
    simp only [Complex.add_re, Complex.exp_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      Complex.neg_re, Complex.neg_im, Real.cos_neg]
    ring
  have hs : Real.sin (L * u.im) = 0 := by
    rw [him] at h
    exact (mul_eq_zero.mp h.1).resolve_left (sub_ne_zero.mpr ha.ne)
  have hc : 0 ≤ Real.cos (L * u.im) := by
    rw [hre] at h
    exact nonneg_of_mul_nonneg_right h.2
      (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have hc1 : Real.cos (L * u.im) = 1 := by
    have hsq := Real.sin_sq_add_cos_sq (L * u.im)
    rw [hs] at hsq
    nlinarith only [hsq, hc]
  apply hphase
  apply Complex.ext <;>
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, hc1, hs]

/-- Off the unitary axis, a nonzero imaginary parameter gives a usable Hecke place. -/
theorem exists_eigenvalue_outside_nonnegative_ray {u : ℂ}
    (hu : u.re < 0) (hi : u.im ≠ 0) :
    ∃ i : Fin 2, (eigenvalue i u).im ≠ 0 ∨ (eigenvalue i u).re < 0 := by
  obtain ⟨i, hphase⟩ : ∃ i : Fin 2,
      Complex.exp (-(Real.log (primeBase i) : ℂ) * (u.im : ℂ) * I) ≠ 1 := by
    rcases two_three_phase_ne_one hi with h | h
    · exact ⟨0, by simpa only [primeBase, ↓reduceIte] using h⟩
    · exact ⟨1, by simpa [primeBase] using h⟩
  refine ⟨i, exp_pair_not_nonnegative_real ?_ hu hphase⟩
  apply Real.log_pos
  dsimp [primeBase]
  split_ifs <;> norm_num

private theorem positive_polynomial_at_coordinate (z : Fin 2 → ℂ) (i : Fin 2)
    (hi : (z i).im ≠ 0 ∨ (z i).re < 0) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      MvPolynomial.eval₂Hom (Complex.ofRealHom.comp NNReal.toRealHom) z P = 0 := by
  have hz : z i ≠ 0 := by
    intro h
    rcases hi with hi | hi <;> simp [h] at hi
  have hn : ‖z i‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : ℂ := (‖z i‖ : ℂ)⁻¹ * z i
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]
  have hw1 : w ≠ 1 := by
    intro h
    have hzreal : z i = (‖z i‖ : ℂ) := by
      have hnC : (‖z i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
      calc
        z i = (‖z i‖ : ℂ) * w := by dsimp [w]; field_simp
        _ = (‖z i‖ : ℂ) := by rw [h, mul_one]
    rcases hi with hi | hi
    · exact hi (by rw [hzreal]; rfl)
    · have hnn : 0 ≤ (z i).re := by rw [hzreal, Complex.ofReal_re]; exact norm_nonneg _
      exact (not_lt_of_ge hnn) hi
  obtain ⟨k, hk, hkw⟩ := exists_large_pow_re_neg hw hw1 1
  have hk0 : k ≠ 0 := by omega
  let r : ℝ≥0 := ⟨‖z i‖⁻¹, inv_nonneg.mpr (norm_nonneg _)⟩
  let c : ℝ≥0 := ⟨-2 * (w ^ k).re, by linarith only [hkw]⟩
  let V : MvPolynomial (Fin 2) ℝ≥0 := MvPolynomial.C r * MvPolynomial.X i
  let P : MvPolynomial (Fin 2) ℝ≥0 := 1 + MvPolynomial.C c * V ^ k + (V ^ k) ^ 2
  refine ⟨P, by simp [P, V, hk0], ?_⟩
  have hV : MvPolynomial.eval₂Hom (Complex.ofRealHom.comp NNReal.toRealHom) z V = w := by
    simp only [V, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    change ((‖z i‖⁻¹ : ℝ) : ℂ) * z i = (‖z i‖ : ℂ)⁻¹ * z i
    rw [Complex.ofReal_inv]
  simp only [P, map_add, map_one, map_mul, map_pow, MvPolynomial.eval₂Hom_C, hV]
  exact unit_quadratic (by rw [norm_pow, hw, one_pow])

/-- A positive Hecke polynomial annihilates any finite set of nonreal left parameters. -/
theorem exists_finite_annihilator (F : Finset ℂ)
    (hF : ∀ u ∈ F, u.re < 0 ∧ u.im ≠ 0) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      ∀ u ∈ F, spectralEval u P = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | @insert u F hu ih =>
      obtain ⟨Q, hQc, hQ⟩ := ih (fun v hv => hF v (Finset.mem_insert_of_mem hv))
      have hu' := hF u (Finset.mem_insert_self _ _)
      obtain ⟨i, hi⟩ := exists_eigenvalue_outside_nonnegative_ray hu'.1 hu'.2
      obtain ⟨P, hPc, hP⟩ := positive_polynomial_at_coordinate (fun i => eigenvalue i u) i hi
      refine ⟨P * Q, by rw [map_mul, hPc, hQc, one_mul], ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · rw [map_mul, show spectralEval v P = 0 from hP, zero_mul]
      · rw [map_mul, hQ v hv, mul_zero]

/-- The Eisenstein parameter attached to a nontrivial zeta zero. -/
def zeroParameter (ρ : ℂ) : ℂ := (ρ - 1) / 2

/-- Every finite set of actual zeta zeros admits a positive Hecke annihilator. -/
theorem exists_xi_zero_annihilator (F : Finset {ρ : ℂ // RHTower.xi ρ = 0}) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      ∀ ρ ∈ F, spectralEval (zeroParameter ρ) P = 0 := by
  classical
  have hF : ∀ u ∈ F.image
      (fun ρ : {ρ : ℂ // RHTower.xi ρ = 0} => zeroParameter (ρ : ℂ)),
      u.re < 0 ∧ u.im ≠ 0 := by
    intro u hu
    obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hu
    have hr := (RHTower.xi_zero_re_mem_open_unit ρ.property).2
    have hi : (ρ : ℂ).im ≠ 0 := by
      intro hi
      have heq : (((ρ : ℂ).re : ℝ) : ℂ) = ρ := by
        apply Complex.ext
        · rfl
        · simpa only [Complex.ofReal_im] using hi.symm
      exact RHTower.xi_ne_zero_of_real (ρ : ℂ).re (by rw [heq]; exact ρ.property)
    constructor
    · simpa [zeroParameter] using (div_neg_of_neg_of_pos (sub_neg.mpr hr)
        (by norm_num : (0 : ℝ) < 2))
    · simpa [zeroParameter] using hi
  obtain ⟨P, hPc, hP⟩ := exists_finite_annihilator _ hF
  exact ⟨P, hPc, fun ρ hρ => hP _ (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩)⟩

/-- Every positive Hecke polynomial is entire in the spectral parameter. -/
theorem differentiable_spectralEval (P : MvPolynomial (Fin 2) ℝ≥0) :
    Differentiable ℂ (fun u => spectralEval u P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simpa only [spectralEval, MvPolynomial.eval₂Hom_C] using
        (differentiable_const ((Complex.ofRealHom.comp NNReal.toRealHom) c))
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P i hP =>
      have hX : Differentiable ℂ (fun u => spectralEval u (MvPolynomial.X i)) := by
        simp only [spectralEval, MvPolynomial.eval₂Hom_X', eigenvalue]
        fun_prop
      simp only [map_mul]
      exact hP.mul hX

/-- Arbitrary finite multiplicities can be imposed without losing coefficient positivity. -/
theorem exists_xi_zero_annihilator_with_multiplicities
    (F : Finset {ρ : ℂ // RHTower.xi ρ = 0})
    (m : {ρ : ℂ // RHTower.xi ρ = 0} → ℕ) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      ∀ ρ ∈ F, spectralEval (zeroParameter ρ) P = 0 ∧
        (m ρ : ℕ∞) ≤ analyticOrderAt (fun u => spectralEval u P) (zeroParameter ρ) := by
  classical
  obtain ⟨Q, hQc, hQ⟩ := exists_xi_zero_annihilator F
  let M := F.sup m + 1
  have hfun : (fun u : ℂ => spectralEval u (Q ^ M)) =
      (fun u : ℂ => spectralEval u Q) ^ M := by
    funext u
    exact map_pow (spectralEval u) Q M
  refine ⟨Q ^ M, by rw [map_pow, hQc, one_pow], ?_⟩
  intro ρ hρ
  refine ⟨?_, ?_⟩
  · rw [map_pow, hQ ρ hρ]
    simp [M]
  · rw [hfun]
    have hm : m ρ ≤ M := (Finset.le_sup hρ).trans (Nat.le_succ _)
    have hm' : (m ρ : ℕ∞) ≤ (M : ℕ∞) := by exact_mod_cast hm
    exact hm'.trans
      (GaloisForLFunctions.RHTower.Matveev.natCast_le_analyticOrderAt_pow
        ((differentiable_spectralEval Q).analyticAt _) (hQ ρ hρ) M)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.PositiveHecke.exists_xi_zero_annihilator_with_multiplicities
