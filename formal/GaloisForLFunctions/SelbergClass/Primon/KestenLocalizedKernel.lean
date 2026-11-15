import GaloisForLFunctions.SelbergClass.Primon.KestenQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Positive localization at prime Gaussian nodes

Squaring a Gaussian cardinal polynomial and dividing by its Christoffel weight
produces a probability density relative to the prime phase law. Its normalized
Hecke mean is exactly the chosen node. The support interval then bounds its
squared distance from the upper endpoint by four times the node's endpoint gap.
Every orthogonal mode above degree `2n` vanishes. A Chebyshev sign comparison
places a node within a quadratic gap of the endpoint, giving an explicit
`4π²/(n+3)²` squared trace-concentration bound at kernel degree `2n+2`.
Jordan’s inequality also gives angular second moment at most `π⁴/(4(n+3)²)`.
-/

open MeasureTheory Set Polynomial HTGeometry
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- A nonnegative density obtained by squaring a normalized reproducing kernel. -/
def kestenNodeKernel (p : Nat.Primes) (n : ℕ) (r t : ℝ) : ℝ :=
  kestenMcKayDensity p t *
    ((gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t))) ^ 2 /
      christoffel (kestenMoment p) n r

theorem kestenNodeKernel_nonneg (p : Nat.Primes) (n : ℕ) (r t : ℝ) :
    0 ≤ kestenNodeKernel p n r t :=
  div_nonneg (mul_nonneg (kestenMcKayDensity_nonneg p t) (sq_nonneg _))
    (kestenChristoffel_pos p n r).le

private theorem continuous_kestenNodeKernel (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    Continuous (kestenNodeKernel p n r) := by
  unfold kestenNodeKernel
  exact ((continuous_kestenMcKayDensity p).mul (by fun_prop)).div_const _

private theorem integrable_kestenNodeKernel_observable (p : Nat.Primes) (n : ℕ)
    (r : ℝ) (Q : Polynomial ℝ) :
    IntegrableOn (fun t => kestenNodeKernel p n r t * Q.eval (2 * Real.cos (Real.pi * t)))
      (Ioo (0 : ℝ) 1) := by
  have hc : Continuous (fun t => kestenNodeKernel p n r t *
      Q.eval (2 * Real.cos (Real.pi * t))) := by
    exact (continuous_kestenNodeKernel p n r).mul (by fun_prop)
  exact hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- Normalization holds even before restricting the center to a Gauss node. -/
theorem integral_kestenNodeKernel (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p n r t = 1 := by
  have h := christoffel_eq_momentInner_normalisedKernel (kestenMoment_positiveMomentForm p) n r
  change momentInner (kestenMoment p) (gaussBasis (kestenMoment p) n r)
    (gaussBasis (kestenMoment p) n r) = _ at h
  rw [momentInner_def, momentFunctional_kestenMoment] at h
  have hn : (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
      ((gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t))) ^ 2) =
        christoffel (kestenMoment p) n r := by
    simpa only [Polynomial.eval_mul, pow_two] using h
  unfold kestenNodeKernel
  rw [integral_div, hn]
  exact div_self (ne_of_gt (kestenChristoffel_pos p n r))

private theorem kesten_gaussBasis_natDegree_le (p : Nat.Primes) (n : ℕ) (r : ℝ) :
    (gaussBasis (kestenMoment p) n r).natDegree ≤ n := by
  have hBne : gaussBasis (kestenMoment p) n r ≠ 0 := by
    intro hz
    have h := gaussBasis_eval_self (kestenMoment_positiveMomentForm p) n r
    rw [hz, Polynomial.eval_zero] at h
    exact zero_ne_one h
  exact Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hBne).mpr
    (gaussBasis_degree_lt (kestenMoment p) n r))

/-- Squaring a degree-`n` kernel kills every orthogonal mode above degree `2n`. -/
theorem integral_kestenNodeKernel_high_mode (p : Nat.Primes) (n k : ℕ) (r : ℝ) :
    ∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p n r t *
      (kestenPolynomial p (2 * n + 1 + k)).eval (2 * Real.cos (Real.pi * t)) = 0 := by
  have hdeg := kesten_gaussBasis_natDegree_le p n r
  have hmul := Polynomial.natDegree_mul_le
    (p := gaussBasis (kestenMoment p) n r) (q := gaussBasis (kestenMoment p) n r)
  have hBB : (gaussBasis (kestenMoment p) n r * gaussBasis (kestenMoment p) n r).degree <
      ((2 * n + 1 + k : ℕ) : WithBot ℕ) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    exact_mod_cast (by omega :
      (gaussBasis (kestenMoment p) n r * gaussBasis (kestenMoment p) n r).natDegree <
        2 * n + 1 + k)
  have hz := monicOrtho_inner_eq_zero_of_degree_lt (kestenMoment_positiveMomentForm p)
    (2 * n + 1 + k) (2 * n + 1 + k) le_rfl
    (gaussBasis (kestenMoment p) n r * gaussBasis (kestenMoment p) n r) hBB
  rw [monicOrtho_kestenMoment, momentInner_def, momentFunctional_kestenMoment] at hz
  simp only [Polynomial.eval_mul] at hz
  calc
    _ = (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
        ((kestenPolynomial p (2 * n + 1 + k)).eval (2 * Real.cos (Real.pi * t)) *
          ((gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t)) *
            (gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t))))) /
          christoffel (kestenMoment p) n r := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with t
      unfold kestenNodeKernel
      ring
    _ = 0 := by rw [hz, zero_div]

private theorem kesten_gaussBasis_first_moment (p : Nat.Primes) (n : ℕ)
    (r : gaussNodes (kestenMoment p) n) :
    momentFunctional (kestenMoment p)
      (X * (gaussBasis (kestenMoment p) n r * gaussBasis (kestenMoment p) n r)) =
        christoffel (kestenMoment p) n r * r := by
  classical
  have hpos := kestenMoment_positiveMomentForm p
  have hdeg := kesten_gaussBasis_natDegree_le p n r
  have hQdeg : (X * (gaussBasis (kestenMoment p) n r *
      gaussBasis (kestenMoment p) n r)).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    apply lt_of_le_of_lt (Polynomial.degree_le_natDegree)
    have hmul := Polynomial.natDegree_mul_le
      (p := gaussBasis (kestenMoment p) n (r : ℝ))
      (q := gaussBasis (kestenMoment p) n (r : ℝ))
    have hX := Polynomial.natDegree_mul_le (p := (X : Polynomial ℝ))
      (q := gaussBasis (kestenMoment p) n (r : ℝ) * gaussBasis (kestenMoment p) n (r : ℝ))
    rw [Polynomial.natDegree_X] at hX
    exact_mod_cast (by omega :
      (X * (gaussBasis (kestenMoment p) n (r : ℝ) *
        gaussBasis (kestenMoment p) n (r : ℝ))).natDegree < 2 * n + 2)
  rw [momentFunctional_eq_gaussSum hpos n _ hQdeg, Finset.sum_eq_single (r : ℝ)]
  · simp only [Polynomial.eval_mul, Polynomial.eval_X, gaussBasis_eval_self hpos,
      mul_one]
  · intro y hy hyr
    have hz := gaussBasis_eval_of_ne hpos n
      ((mem_gaussNodes_iff n (r : ℝ)).mp r.property)
      ((mem_gaussNodes_iff n y).mp hy) (Ne.symm hyr)
    simp only [Polynomial.eval_mul, hz, mul_zero]
  · exact fun hr => False.elim (hr r.property)

/-- Squared quadrature localization has exactly the selected node as its Hecke mean. -/
theorem integral_kestenNodeKernel_trace (p : Nat.Primes) (n : ℕ)
    (r : gaussNodes (kestenMoment p) n) :
    ∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p n r t * (2 * Real.cos (Real.pi * t)) = r := by
  have h := kesten_gaussBasis_first_moment p n r
  rw [momentFunctional_kestenMoment] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at h
  calc
    _ = (∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity p t *
        ((2 * Real.cos (Real.pi * t)) *
          ((gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t)) *
            (gaussBasis (kestenMoment p) n r).eval (2 * Real.cos (Real.pi * t))))) /
          christoffel (kestenMoment p) n r := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with t
      unfold kestenNodeKernel
      ring
    _ = r := by
      rw [h]
      exact mul_div_cancel_left₀ _ (ne_of_gt (kestenChristoffel_pos p n r))

/-- Endpoint localization follows from the exact mean and the bounded Hecke support. -/
theorem integral_kestenNodeKernel_endpoint_sq_le (p : Nat.Primes) (n : ℕ)
    (r : gaussNodes (kestenMoment p) n) :
    ∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p n r t *
        (2 - 2 * Real.cos (Real.pi * t)) ^ 2 ≤ 4 * (2 - (r : ℝ)) := by
  have i0 : IntegrableOn (kestenNodeKernel p n r) (Ioo (0 : ℝ) 1) := by
    simpa only [Polynomial.eval_one, mul_one] using
      integrable_kestenNodeKernel_observable p n r 1
  have i1 : IntegrableOn (fun t => kestenNodeKernel p n r t *
      (2 * Real.cos (Real.pi * t))) (Ioo (0 : ℝ) 1) := by
    simpa only [Polynomial.eval_X] using integrable_kestenNodeKernel_observable p n r X
  have i2 : IntegrableOn (fun t => kestenNodeKernel p n r t *
      (2 - 2 * Real.cos (Real.pi * t)) ^ 2) (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenNodeKernel p n r).mul (by fun_prop)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hi : ∫ t in Ioo (0 : ℝ) 1, (4 *
      (2 * kestenNodeKernel p n r t - kestenNodeKernel p n r t *
        (2 * Real.cos (Real.pi * t)))) = 4 * (2 - (r : ℝ)) := by
    rw [integral_const_mul, integral_sub (i0.const_mul 2) i1, integral_const_mul,
      integral_kestenNodeKernel, integral_kestenNodeKernel_trace, mul_one]
  rw [← hi]
  apply integral_mono i2 (((i0.const_mul 2).sub i1).const_mul 4)
  intro t
  have hb : (2 - 2 * Real.cos (Real.pi * t)) ^ 2 ≤
      4 * (2 - 2 * Real.cos (Real.pi * t)) := by
    nlinarith only [Real.cos_le_one (Real.pi * t), Real.neg_one_le_cos (Real.pi * t),
      mul_nonneg (sub_nonneg.mpr (Real.cos_le_one (Real.pi * t)))
        (show 0 ≤ 1 + Real.cos (Real.pi * t) by
          linarith only [Real.neg_one_le_cos (Real.pi * t)])]
  have hm := mul_le_mul_of_nonneg_left hb (kestenNodeKernel_nonneg p n r t)
  change kestenNodeKernel p n r t * (2 - 2 * Real.cos (Real.pi * t)) ^ 2 ≤
    4 * (2 * kestenNodeKernel p n r t -
      kestenNodeKernel p n r t * (2 * Real.cos (Real.pi * t)))
  nlinarith only [hm]

/-- Prime quadrature has a node at least as close to the upper edge as the free node. -/
theorem kestenGaussNode_near_edge (p : Nat.Primes) (n : ℕ) :
    ∃ r : gaussNodes (kestenMoment p) (n + 1),
      2 * Real.cos (Real.pi / ((n : ℝ) + 3)) ≤ (r : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < (n : ℝ) + 3 := by linarith only [hn]
  have ht : 0 < Real.pi / ((n : ℝ) + 3) := div_pos Real.pi_pos hd
  have htpi : Real.pi / ((n : ℝ) + 3) < Real.pi := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith only [Real.pi_pos, hn]
  have hphase (k : ℕ) :
      phaseCharacter k (((n : ℝ) + 3)⁻¹) * Real.sin (Real.pi / ((n : ℝ) + 3)) =
        Real.sin (((k : ℝ) + 1) * (Real.pi / ((n : ℝ) + 3))) := by
    simpa only [phaseCharacter, Int.cast_natCast, div_eq_mul_inv] using
      Polynomial.Chebyshev.U_real_cos (Real.pi / ((n : ℝ) + 3)) (k : ℤ)
  have hmul : ((n : ℝ) + 3) * (Real.pi / ((n : ℝ) + 3)) = Real.pi := by
    field_simp [ne_of_gt hd]
  have hsmall : ((n : ℝ) + 1) * (Real.pi / ((n : ℝ) + 3)) < Real.pi := by
    nlinarith only [hmul, ht]
  have hs := Real.sin_pos_of_pos_of_lt_pi ht htpi
  have hs' := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos (by linarith only [hn] : 0 < (n : ℝ) + 1) ht) hsmall
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hip : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by linarith only [hp])
  have hpoly := kestenPolynomial_eval_phase p n (((n : ℝ) + 3)⁻¹)
  rw [← div_eq_mul_inv] at hpoly
  have hneg : (kestenPolynomial p (n + 2)).eval
      (2 * Real.cos (Real.pi / ((n : ℝ) + 3))) < 0 := by
    have he : (kestenPolynomial p (n + 2)).eval
        (2 * Real.cos (Real.pi / ((n : ℝ) + 3))) *
          Real.sin (Real.pi / ((n : ℝ) + 3)) =
        -(p : ℝ)⁻¹ * Real.sin (((n : ℝ) + 1) * (Real.pi / ((n : ℝ) + 3))) := by
      rw [hpoly, sub_mul, mul_assoc, hphase, hphase]
      push_cast
      rw [show (n : ℝ) + 2 + 1 = (n : ℝ) + 3 by ring, hmul, Real.sin_pi]
      ring
    have he' : (kestenPolynomial p (n + 2)).eval
        (2 * Real.cos (Real.pi / ((n : ℝ) + 3))) *
          Real.sin (Real.pi / ((n : ℝ) + 3)) <
        0 * Real.sin (Real.pi / ((n : ℝ) + 3)) := by
      rw [he, zero_mul]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hip) hs'
    by_contra hnot
    have hge := mul_nonneg (le_of_not_gt hnot) hs.le
    rw [zero_mul] at he'
    exact (not_lt_of_ge hge) he'
  have hpos : 0 < (kestenPolynomial p (n + 2)).eval 2 := by
    have he := kestenPolynomial_eval_phase p n 0
    simp only [mul_zero, Real.cos_zero, mul_one, phaseCharacter,
      Polynomial.Chebyshev.U_eval_one, Int.cast_natCast, Nat.cast_add, Nat.cast_ofNat] at he
    push_cast at he
    rw [he]
    have hi : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith only [hp])).mpr hp.le
    have hb := mul_le_mul_of_nonneg_right hi (by linarith only [hn] : 0 ≤ (n : ℝ) + 1)
    nlinarith only [hb]
  have hab : 2 * Real.cos (Real.pi / ((n : ℝ) + 3)) ≤ 2 := by
    linarith only [Real.cos_le_one (Real.pi / ((n : ℝ) + 3))]
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc hab
    (kestenPolynomial p (n + 2)).continuous.continuousOn ⟨hneg.le, hpos.le⟩
  refine ⟨⟨r, ?_⟩, hr.1⟩
  apply (mem_gaussNodes_iff (n + 1) r).mpr
  rw [monicOrtho_kestenMoment, show n + 1 + 1 = n + 2 by omega]
  exact hz

/-- Positive prime-law kernels have an exact mode cutoff and quadratic endpoint concentration. -/
theorem exists_kestenNodeKernel_quadratic_concentration (p : Nat.Primes) (n : ℕ) :
    ∃ r : gaussNodes (kestenMoment p) (n + 1),
      (∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p (n + 1) r t *
        (2 - 2 * Real.cos (Real.pi * t)) ^ 2) ≤
          4 * (Real.pi / ((n : ℝ) + 3)) ^ 2 := by
  obtain ⟨r, hr⟩ := kestenGaussNode_near_edge p n
  refine ⟨r, (integral_kestenNodeKernel_endpoint_sq_le p (n + 1) r).trans ?_⟩
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((n : ℝ) + 3))
  nlinarith only [hr, hc]

/-- The angular second moment is controlled by the exact endpoint gap. -/
theorem integral_kestenNodeKernel_angle_sq_le (p : Nat.Primes) (n : ℕ)
    (r : gaussNodes (kestenMoment p) n) :
    ∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p n r t * (Real.pi * t) ^ 2 ≤
      (Real.pi ^ 2 / 4) * (2 - (r : ℝ)) := by
  have i0 : IntegrableOn (kestenNodeKernel p n r) (Ioo (0 : ℝ) 1) := by
    simpa only [Polynomial.eval_one, mul_one] using
      integrable_kestenNodeKernel_observable p n r 1
  have i1 : IntegrableOn (fun t => kestenNodeKernel p n r t *
      (2 * Real.cos (Real.pi * t))) (Ioo (0 : ℝ) 1) := by
    simpa only [Polynomial.eval_X] using integrable_kestenNodeKernel_observable p n r X
  have it : IntegrableOn (fun t => kestenNodeKernel p n r t * (Real.pi * t) ^ 2)
      (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenNodeKernel p n r).mul (by fun_prop)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hi : (∫ t in Ioo (0 : ℝ) 1, (Real.pi ^ 2 / 4) *
      (2 * kestenNodeKernel p n r t - kestenNodeKernel p n r t *
        (2 * Real.cos (Real.pi * t)))) = (Real.pi ^ 2 / 4) * (2 - (r : ℝ)) := by
    rw [integral_const_mul, integral_sub (i0.const_mul 2) i1, integral_const_mul,
      integral_kestenNodeKernel, integral_kestenNodeKernel_trace, mul_one]
  rw [← hi]
  apply integral_mono_ae it (((i0.const_mul 2).sub i1).const_mul (Real.pi ^ 2 / 4))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hangle : |Real.pi * t| ≤ Real.pi := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le ht.1.le)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2.le Real.pi_pos.le
  have hc := Real.cos_le_one_sub_mul_cos_sq hangle
  have hquot : (2 * (Real.pi * t) ^ 2) / Real.pi ^ 2 ≤
      1 - Real.cos (Real.pi * t) := by
    simpa only [div_mul_eq_mul_div] using
      (show 2 / Real.pi ^ 2 * (Real.pi * t) ^ 2 ≤ 1 - Real.cos (Real.pi * t) by
        linarith only [hc])
  have hb : (Real.pi * t) ^ 2 ≤ (Real.pi ^ 2 / 4) *
      (2 - 2 * Real.cos (Real.pi * t)) := by
    have h := (div_le_iff₀ (sq_pos_of_ne_zero Real.pi_ne_zero)).mp hquot
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_left hb (kestenNodeKernel_nonneg p n r t)
  change kestenNodeKernel p n r t * (Real.pi * t) ^ 2 ≤ (Real.pi ^ 2 / 4) *
    (2 * kestenNodeKernel p n r t - kestenNodeKernel p n r t * (2 * Real.cos (Real.pi * t)))
  nlinarith only [hm]

/-- Angular concentration at a prime Gaussian node has the explicit quadratic rate. -/
theorem exists_kestenNodeKernel_angle_concentration (p : Nat.Primes) (n : ℕ) :
    ∃ r : gaussNodes (kestenMoment p) (n + 1),
      (∫ t in Ioo (0 : ℝ) 1, kestenNodeKernel p (n + 1) r t * (Real.pi * t) ^ 2) ≤
        (Real.pi ^ 2 / 4) * (Real.pi / ((n : ℝ) + 3)) ^ 2 := by
  obtain ⟨r, hr⟩ := kestenGaussNode_near_edge p n
  refine ⟨r, (integral_kestenNodeKernel_angle_sq_le p (n + 1) r).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg Real.pi) (by norm_num))
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((n : ℝ) + 3))
  linarith only [hr, hc]

#print axioms integral_kestenNodeKernel
#print axioms integral_kestenNodeKernel_high_mode
#print axioms integral_kestenNodeKernel_trace
#print axioms integral_kestenNodeKernel_endpoint_sq_le
#print axioms kestenGaussNode_near_edge
#print axioms exists_kestenNodeKernel_quadratic_concentration
#print axioms integral_kestenNodeKernel_angle_sq_le
#print axioms exists_kestenNodeKernel_angle_concentration

end
end GaloisForLFunctions.SelbergClass.Primon
