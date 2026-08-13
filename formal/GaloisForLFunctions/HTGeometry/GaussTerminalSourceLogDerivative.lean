import GaloisForLFunctions.HTGeometry.GaussTerminalWeylRenewal

/-!
# De-resisted terminal source and the admission log derivative

Terminal Weyl renewal has total mass one, but an individual resistance share can vanish.  The
source amplification identity supplies its exact inverse inertia.  Cancelling resistance against
completed source leaves one unit atom at every admitted root.  This file identifies the resulting
faithful finite carrier with the logarithmic derivative of the current monic admission.

The theorem is generic finite positive-block infrastructure.  It uses no representing measure,
infinite moment extension, limit, or computation.
-/

open scoped BigOperators
open Polynomial Complex

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Finite-block factorization of the current monic admission over its Gauss nodes. -/
theorem monicOrtho_eq_prod_gaussNodes_below {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) :
    monicOrtho s (m + 1) = ∏ x ∈ gaussNodes s m, (X - C x) := by
  classical
  have hmonic : (monicOrtho s (m + 1)).Monic := monicOrtho_monic s (m + 1)
  have hcard : (monicOrtho s (m + 1)).roots.card =
      (monicOrtho s (m + 1)).natDegree :=
    (monicOrtho_splits_below h hmN).natDegree_eq_card_roots.symm
  have hfac := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
  rw [← hfac, gaussNodes, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr (monicOrtho_roots_nodup_below h hmN)]

/-- Complex evaluation of finite-block Gauss-node factorization. -/
theorem monicOrthoC_eq_prod_gaussNodes_below {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) (z : ℂ) :
    monicOrthoC s (m + 1) z = ∏ x ∈ gaussNodes s m, (z - (x : ℂ)) := by
  rw [monicOrthoC, monicOrtho_eq_prod_gaussNodes_below h hmN, map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  simp

/-- Unit-pole transform of every current admitted root.  Unlike terminal resistance, this carrier
does not lose a root whose admission share tends to zero. -/
noncomputable def gaussUnitPoleTransformComplex
    (s : ℕ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑ x ∈ gaussNodes s m, 1 / (z - (x : ℂ))

/-- **Faithful source/log-derivative identity.**  Unit mass at every admitted node is exactly the
logarithmic derivative of current monic admission. -/
theorem gaussUnitPoleTransformComplex_eq_logDerivative {N m : ℕ}
    (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N) {z : ℂ}
    (hz : z.im ≠ 0) :
    gaussUnitPoleTransformComplex s m z =
      Polynomial.aeval z (monicOrtho s (m + 1)).derivative /
        monicOrthoC s (m + 1) z := by
  classical
  let nodes := gaussNodes s m
  let f : ℝ → Polynomial ℝ := fun x => X - C x
  have hfac : monicOrtho s (m + 1) = ∏ x ∈ nodes, f x := by
    simpa only [nodes, f] using monicOrtho_eq_prod_gaussNodes_below h hmN
  have hderiv := congrArg (fun p : Polynomial ℝ => Polynomial.aeval z p.derivative) hfac
  simp [Polynomial.derivative_prod_finset, f] at hderiv
  have hprod : monicOrthoC s (m + 1) z = ∏ x ∈ nodes, (z - (x : ℂ)) := by
    simpa only [nodes] using monicOrthoC_eq_prod_gaussNodes_below h hmN z
  rw [gaussUnitPoleTransformComplex, show gaussNodes s m = nodes by rfl,
    hderiv, hprod, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  have hxz : z - (x : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
    exact hz him
  have herase : ∏ y ∈ nodes.erase x, (z - (y : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
    exact hz him
  rw [← Finset.mul_prod_erase nodes (fun y => z - (y : ℂ)) hx]
  field_simp [hxz, herase]

/-- Poisson density of faithful unit atoms. -/
noncomputable def gaussUnitPolePoissonDensity
    (s : ℕ → ℝ) (m : ℕ) (a eta : ℝ) : ℝ :=
  ∑ x ∈ gaussNodes s m, eta / ((a - x) ^ 2 + eta ^ 2)

/-- Negative imaginary part of faithful source transform is its positive Poisson density. -/
theorem neg_im_gaussUnitPoleTransformComplex_eq_poissonDensity
    (s : ℕ → ℝ) (m : ℕ) (a eta : ℝ) :
    -(gaussUnitPoleTransformComplex s m (a + eta * I)).im =
      gaussUnitPolePoissonDensity s m a eta := by
  rw [gaussUnitPoleTransformComplex, gaussUnitPolePoissonDensity]
  simp only [Complex.im_sum, Complex.div_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, add_zero, Complex.sub_re,
    Complex.add_im, Complex.mul_im, zero_mul, Complex.sub_im, Complex.normSq_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  norm_num [pow_two]

end HTGeometry
