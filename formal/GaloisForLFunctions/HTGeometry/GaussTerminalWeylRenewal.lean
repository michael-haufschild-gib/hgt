import GaloisForLFunctions.HTGeometry.GaussTerminalSourceResistance
import GaloisForLFunctions.HTGeometry.ComplexChristoffelDarboux

/-!
# Gauss terminal-source Weyl renewal

Terminal source resistance is not merely a probability reported from a finite Gauss face.  Its
Cauchy aggregate is exactly the adjacent monic-orthogonal-polynomial ratio.  Consequently the
aggregate renews across degree by the nonlinear Jacobi coefficient-stripping law

`W_{m+1}(z) = 1 / (z - alpha_{m+1} - beta_{m+1} W_m(z))`.

Everything is proved inside one finite positive moment block.  No representing measure, infinite
moment extension, limiting argument, or computation is used.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Cauchy aggregate of terminal source resistance at one admitted Gauss face. -/
noncomputable def gaussTerminalWeylTransform
    (s : ℕ → ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  ∑ x ∈ gaussNodes s m, gaussTerminalSourceResistance s m x / (z - x)

/-- Pointwise Christoffel--Darboux landing of one terminal atom. -/
private theorem prev_mul_gaussBasis_eval_eq_terminal_atom {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x z : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) (hxz : z - x ≠ 0) :
    (monicOrtho s m).eval x * (gaussBasis s m x).eval z =
      (monicOrtho s (m + 1)).eval z *
        (gaussTerminalSourceResistance s m x / (z - x)) := by
  have hnorm : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  have hcd := christoffelDarboux_below h m hmN x z
  rw [← cdKernel_eval] at hcd
  rw [hroot, zero_mul, zero_sub] at hcd
  rw [gaussBasis, Polynomial.eval_smul, smul_eq_mul,
    gaussTerminalSourceResistance]
  simp only [monicOrthoNormSq] at hnorm ⊢
  field_simp [hxz, hnorm] at hcd ⊢
  linear_combination -christoffel s m x * (monicOrtho s m).eval x * hcd

/-- **Terminal-source Weyl identity.**  The admission-sensitive terminal-resistance aggregate is
the preceding/current monic admission ratio. -/
theorem gaussTerminalWeylTransform_eq_ratio {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℝ}
    (hz : (monicOrtho s (m + 1)).eval z ≠ 0) :
    gaussTerminalWeylTransform s m z =
      (monicOrtho s m).eval z / (monicOrtho s (m + 1)).eval z := by
  classical
  have hinterp := gauss_interpolation_below h m hmN (monicOrtho s m) (by
    rw [monicOrtho_degree]
    exact_mod_cast Nat.lt_succ_self m)
  have heval := congrArg (Polynomial.eval z) hinterp
  rw [Polynomial.eval_finsetSum] at heval
  simp only [Polynomial.eval_smul, smul_eq_mul] at heval
  have hsum :
      (monicOrtho s m).eval z =
        (monicOrtho s (m + 1)).eval z * gaussTerminalWeylTransform s m z := by
    rw [heval, gaussTerminalWeylTransform, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hroot : (monicOrtho s (m + 1)).eval x = 0 :=
      (mem_gaussNodes_iff m x).mp hx
    have hxz : z - x ≠ 0 := by
      intro hzx
      have : z = x := sub_eq_zero.mp hzx
      exact hz (this ▸ hroot)
    exact prev_mul_gaussBasis_eval_eq_terminal_atom h hmN hroot hxz
  rw [eq_div_iff hz]
  simpa [mul_comm] using hsum.symm

/-- **Nonlinear degree renewal.**  Terminal source survives admission change by the finite Jacobi
Riccati law, rather than through a fixed linear reporter. -/
theorem gaussTerminalWeylTransform_renewal {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {z : ℝ}
    (hzCurrent : (monicOrtho s (m + 1)).eval z ≠ 0)
    (hzNext : (monicOrtho s (m + 2)).eval z ≠ 0) :
    gaussTerminalWeylTransform s (m + 1) z =
      1 / (z - monicOrthoAlpha s (m + 1) -
        monicOrthoBeta s (m + 1) * gaussTerminalWeylTransform s m z) := by
  rw [gaussTerminalWeylTransform_eq_ratio h (by omega) hzNext,
    gaussTerminalWeylTransform_eq_ratio h (by omega) hzCurrent]
  have hrec := congrArg (Polynomial.eval z)
    (X_mul_monicOrtho_below h (n := m + 1) (by omega))
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul, Nat.add_sub_cancel] at hrec
  rw [show m + 1 + 1 = m + 2 by omega] at hrec
  have hden :
      z - monicOrthoAlpha s (m + 1) -
          monicOrthoBeta s (m + 1) *
            ((monicOrtho s m).eval z / (monicOrtho s (m + 1)).eval z) =
        (monicOrtho s (m + 2)).eval z / (monicOrtho s (m + 1)).eval z := by
    field_simp [hzCurrent]
    linear_combination hrec
  rw [show m + 1 + 1 = m + 2 by omega, hden]
  field_simp [hzCurrent, hzNext]

/-! ## Complex source continuation and exact Poisson renewal -/

/-- Analytic continuation of terminal-source Weyl aggregate.  Its real boundary values agree with
the literal terminal-resistance Cauchy sum wherever that sum has no pole. -/
noncomputable def gaussTerminalWeylTransformComplex
    (s : ℕ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  monicOrthoC s m z / monicOrthoC s (m + 1) z

/-- The complex ratio is the analytic continuation of terminal-source Cauchy aggregate. -/
theorem gaussTerminalWeylTransformComplex_ofReal {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℝ}
    (hz : (monicOrtho s (m + 1)).eval z ≠ 0) :
    gaussTerminalWeylTransformComplex s m z =
      (gaussTerminalWeylTransform s m z : ℂ) := by
  rw [gaussTerminalWeylTransform_eq_ratio h hmN hz]
  have heval (p : Polynomial ℝ) :
      Polynomial.aeval (z : ℂ) p = ((Polynomial.eval z p : ℝ) : ℂ) := by
    change Polynomial.aeval (algebraMap ℝ ℂ z) p =
      algebraMap ℝ ℂ (Polynomial.eval z p)
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval z p
  rw [gaussTerminalWeylTransformComplex, monicOrthoC, monicOrthoC, heval, heval]
  push_cast
  rfl

/-- Literal complex Cauchy sum of terminal-source resistance atoms. -/
noncomputable def gaussTerminalWeylSourceSumComplex
    (s : ℕ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ x ∈ gaussNodes s m,
    (gaussTerminalSourceResistance s m x : ℂ) / (z - (x : ℂ))

/-- Christoffel--Darboux at a current root, retained as a polynomial identity so it can be
evaluated at complex apertures. -/
private theorem root_cdKernel_polynomial_identity {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x : ℝ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) :
    (C x - X) * cdKernel s m x * C (monicOrthoNormSq s m) =
      -C ((monicOrtho s m).eval x) * monicOrtho s (m + 1) := by
  apply Polynomial.funext
  intro y
  have hnorm : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  have hcd := christoffelDarboux_below h m hmN x y
  rw [← cdKernel_eval, hroot, zero_mul, zero_sub] at hcd
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_neg]
  simp only [monicOrthoNormSq] at hnorm hcd ⊢
  field_simp [hnorm] at hcd ⊢
  linear_combination hcd

/-- Complex pointwise landing of one terminal source atom. -/
private theorem prev_mul_gaussBasis_aeval_eq_terminal_atom {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {x : ℝ} {z : ℂ}
    (hroot : (monicOrtho s (m + 1)).eval x = 0) (hxz : z - (x : ℂ) ≠ 0) :
    ((Polynomial.eval x (monicOrtho s m) : ℝ) : ℂ) *
        Polynomial.aeval z (gaussBasis s m x) =
      monicOrthoC s (m + 1) z *
        ((gaussTerminalSourceResistance s m x : ℂ) / (z - (x : ℂ))) := by
  have hnormR : monicOrthoNormSq s m ≠ 0 :=
    ne_of_gt (monicOrthoNorm_pos_below h (by omega))
  have hpoly := congrArg (Polynomial.aeval z)
    (root_cdKernel_polynomial_identity h hmN hroot)
  simp only [map_mul, map_sub, map_neg, Polynomial.aeval_C, Polynomial.aeval_X] at hpoly
  rw [gaussBasis, map_smul, Algebra.smul_def,
    gaussTerminalSourceResistance]
  simp only [monicOrthoC]
  push_cast
  field_simp [hxz, hnormR] at hpoly ⊢
  linear_combination -((christoffel s m x : ℝ) : ℂ) *
    ((Polynomial.eval x (monicOrtho s m) : ℝ) : ℂ) * hpoly

/-- **Literal source continuation.**  The complex terminal-resistance Cauchy sum is exactly the
analytic Weyl ratio at every nonreal aperture. -/
theorem gaussTerminalWeylSourceSumComplex_eq_transform {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℂ}
    (hz : z.im ≠ 0) :
    gaussTerminalWeylSourceSumComplex s m z =
      gaussTerminalWeylTransformComplex s m z := by
  classical
  have hcurrent : monicOrthoC s (m + 1) z ≠ 0 :=
    monicOrtho_aeval_ne_zero_below h hmN hz
  have hinterp := gauss_interpolation_below h m hmN (monicOrtho s m) (by
    rw [monicOrtho_degree]
    exact_mod_cast Nat.lt_succ_self m)
  have heval := congrArg (Polynomial.aeval z) hinterp
  simp [Algebra.smul_def] at heval
  have hsum : monicOrthoC s m z =
      monicOrthoC s (m + 1) z * gaussTerminalWeylSourceSumComplex s m z := by
    rw [monicOrthoC, heval, gaussTerminalWeylSourceSumComplex, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hroot : (monicOrtho s (m + 1)).eval x = 0 :=
      (mem_gaussNodes_iff m x).mp hx
    have hxz : z - (x : ℂ) ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
      exact hz him
    exact prev_mul_gaussBasis_aeval_eq_terminal_atom h hmN hroot hxz
  rw [gaussTerminalWeylTransformComplex, eq_div_iff hcurrent]
  simpa [mul_comm] using hsum.symm

/-- **Poisson localization of terminal source.**  Negative imaginary Weyl density is exactly the
positive Poisson smoothing of admission-dependent source atoms. -/
theorem neg_im_gaussTerminalWeylTransformComplex_eq_poisson_sum {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℂ}
    (hz : z.im ≠ 0) :
    -(gaussTerminalWeylTransformComplex s m z).im =
      ∑ x ∈ gaussNodes s m,
        gaussTerminalSourceResistance s m x * z.im /
          ((z.re - x) ^ 2 + z.im ^ 2) := by
  rw [← gaussTerminalWeylSourceSumComplex_eq_transform h hmN hz,
    gaussTerminalWeylSourceSumComplex]
  simp only [Complex.im_sum, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, zero_mul, sub_zero, Complex.normSq_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [zero_div, zero_sub, neg_neg, pow_two]

/-- Complex Jacobi coefficient stripping for the terminal-source continuation. -/
theorem gaussTerminalWeylTransformComplex_renewal {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {z : ℂ}
    (hzCurrent : monicOrthoC s (m + 1) z ≠ 0)
    (hzNext : monicOrthoC s (m + 2) z ≠ 0) :
    gaussTerminalWeylTransformComplex s (m + 1) z =
      1 / (z - (monicOrthoAlpha s (m + 1) : ℂ) -
        (monicOrthoBeta s (m + 1) : ℂ) * gaussTerminalWeylTransformComplex s m z) := by
  rw [gaussTerminalWeylTransformComplex, gaussTerminalWeylTransformComplex]
  have hrec : z * monicOrthoC s (m + 1) z =
      monicOrthoC s (m + 2) z + (monicOrthoAlpha s (m + 1) : ℂ) *
        monicOrthoC s (m + 1) z + (monicOrthoBeta s (m + 1) : ℂ) *
          monicOrthoC s m z := by
    simpa [monicOrthoC, Algebra.smul_def, Complex.coe_algebraMap] using
      congrArg (Polynomial.aeval z)
        (X_mul_monicOrtho_below h (n := m + 1) (by omega))
  change monicOrthoC s (m + 1) z / monicOrthoC s (m + 2) z = _
  have hden :
      z - (monicOrthoAlpha s (m + 1) : ℂ) -
          (monicOrthoBeta s (m + 1) : ℂ) *
            (monicOrthoC s m z / monicOrthoC s (m + 1) z) =
        monicOrthoC s (m + 2) z / monicOrthoC s (m + 1) z := by
    field_simp [hzCurrent]
    linear_combination hrec
  rw [hden]
  field_simp [hzCurrent, hzNext]

/-- **Poissonized source renewal.**  Negative imaginary terminal-source density renews by a
strictly positive aperture injection plus the preceding density transported through the newborn
Jacobi edge. -/
theorem neg_im_gaussTerminalWeylTransformComplex_renewal {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {z : ℂ}
    (hzCurrent : monicOrthoC s (m + 1) z ≠ 0)
    (hzNext : monicOrthoC s (m + 2) z ≠ 0) :
    -(gaussTerminalWeylTransformComplex s (m + 1) z).im =
      Complex.normSq (gaussTerminalWeylTransformComplex s (m + 1) z) *
        (z.im + monicOrthoBeta s (m + 1) *
          (-(gaussTerminalWeylTransformComplex s m z).im)) := by
  let D : ℂ := z - (monicOrthoAlpha s (m + 1) : ℂ) -
    (monicOrthoBeta s (m + 1) : ℂ) * gaussTerminalWeylTransformComplex s m z
  have hrenew := gaussTerminalWeylTransformComplex_renewal h hmN hzCurrent hzNext
  have hWnext : gaussTerminalWeylTransformComplex s (m + 1) z ≠ 0 := by
    rw [gaussTerminalWeylTransformComplex]
    exact div_ne_zero hzCurrent hzNext
  have hD : D ≠ 0 := by
    intro hzero
    apply hWnext
    rw [hrenew, show z - (monicOrthoAlpha s (m + 1) : ℂ) -
      (monicOrthoBeta s (m + 1) : ℂ) * gaussTerminalWeylTransformComplex s m z = D by rfl,
      hzero, div_zero]
  rw [hrenew]
  rw [show z - (monicOrthoAlpha s (m + 1) : ℂ) -
    (monicOrthoBeta s (m + 1) : ℂ) * gaussTerminalWeylTransformComplex s m z = D by rfl]
  simp only [one_div]
  change -((D⁻¹).im) = Complex.normSq D⁻¹ * _
  rw [Complex.inv_im, Complex.normSq_inv]
  simp only [D, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul, add_zero]
  field_simp [(Complex.normSq_pos.mpr hD).ne']
  ring

/-- Every finite terminal-source continuation is strictly anti-Herglotz on the upper half-plane. -/
theorem neg_im_gaussTerminalWeylTransformComplex_pos {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℂ}
    (hz : 0 < z.im) :
    0 < -(gaussTerminalWeylTransformComplex s m z).im := by
  induction m with
  | zero =>
      have hden : monicOrthoC s 1 z ≠ 0 :=
        monicOrtho_aeval_ne_zero_below h hmN hz.ne'
      rw [gaussTerminalWeylTransformComplex]
      have hzero : monicOrthoC s 0 z = 1 := by simp [monicOrthoC]
      rw [hzero, one_div, Complex.inv_im]
      have hnorm : 0 < Complex.normSq (monicOrthoC s 1 z) :=
        Complex.normSq_pos.mpr hden
      have him : (monicOrthoC s 1 z).im = z.im := by
        rw [monicOrthoC, monicOrtho_eq s 1]
        simp
      rw [him]
      simpa only [neg_div, neg_neg] using div_pos hz hnorm
  | succ m ih =>
      have hcurrent : monicOrthoC s (m + 1) z ≠ 0 :=
        monicOrtho_aeval_ne_zero_below h (by omega) hz.ne'
      have hnext : monicOrthoC s (m + 2) z ≠ 0 :=
        monicOrtho_aeval_ne_zero_below h hmN hz.ne'
      have hidentity := neg_im_gaussTerminalWeylTransformComplex_renewal
        h hmN hcurrent hnext
      rw [hidentity]
      have hbeta : 0 < monicOrthoBeta s (m + 1) :=
        monicOrthoBeta_pos_below h (by omega) (by omega)
      have hprev : 0 < -(gaussTerminalWeylTransformComplex s m z).im :=
        ih (by omega)
      have hWnext : gaussTerminalWeylTransformComplex s (m + 1) z ≠ 0 := by
        rw [gaussTerminalWeylTransformComplex]
        exact div_ne_zero hcurrent hnext
      exact mul_pos (Complex.normSq_pos.mpr hWnext)
        (add_pos_of_pos_of_nonneg hz (mul_nonneg hbeta.le hprev.le))

/-- **Exact normalized source increment.**  After undoing current Riccati transmission, every
strict degree renewal injects exactly the aperture height `Im z`; no source term is discarded. -/
theorem gaussTerminalWeylTransformComplex_normalized_source_increment {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 2 < N) {z : ℂ}
    (hz : 0 < z.im) :
    -(gaussTerminalWeylTransformComplex s (m + 1) z).im /
          Complex.normSq (gaussTerminalWeylTransformComplex s (m + 1) z) -
        monicOrthoBeta s (m + 1) *
          (-(gaussTerminalWeylTransformComplex s m z).im) = z.im := by
  have hcurrent : monicOrthoC s (m + 1) z ≠ 0 :=
    monicOrtho_aeval_ne_zero_below h (by omega) hz.ne'
  have hnext : monicOrthoC s (m + 2) z ≠ 0 :=
    monicOrtho_aeval_ne_zero_below h hmN hz.ne'
  have hidentity := neg_im_gaussTerminalWeylTransformComplex_renewal
    h hmN hcurrent hnext
  have hWnext : gaussTerminalWeylTransformComplex s (m + 1) z ≠ 0 := by
    rw [gaussTerminalWeylTransformComplex]
    exact div_ne_zero hcurrent hnext
  rw [hidentity]
  field_simp [(Complex.normSq_pos.mpr hWnext).ne']
  ring

end HTGeometry
