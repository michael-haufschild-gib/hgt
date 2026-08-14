import GaloisForLFunctions.RHTower.BarnesMellinGenusExpansion
import GaloisForLFunctions.RHTower.BarnesMellinEulerDerivative

/-!
# The genus-`g` Barnes expansion is termwise differentiable

The Euler operator `D = x d/dx` raises the weight of the contour integrand by one, independently of
the abscissa at which the contour sits.  So the identification of the genus-`g` canonical-product
Euler sum with a vertical integral propagates to every Euler derivative, and the finite expansion
obtained by shifting the contour rightwards past the pole of zeta and the integers `-g, -g+1, …`
turns into a Poincaré asymptotic expansion for `D^m` as well.

Together with the genus-zero statement this is the derivative-compatible Barnes expansion for every
positive `s` whose reciprocal is not an integer.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {s : ℝ} {g : ℕ}

/-- The Euler sum of the genus-`g` canonical product: the logarithmic derivative of the Weierstrass
factor of genus `g`, summed over the scales. -/
def barnesGenusEulerSum (s : ℝ) (g : ℕ) : ℝ → ℂ :=
  fun x => ∑' n : ℕ, ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s)

/-- On the positive axis the genus-`g` Euler sum is the contour representation at the initial
abscissa of the ladder. -/
theorem barnesGenusEulerSum_eqOn (hs : 0 < s) (hgl : (g : ℝ) < 1 / s)
    (hgu : 1 / s < (g : ℝ) + 1) :
    Set.EqOn (barnesGenusEulerSum s g)
      (fun x : ℝ => VerticalIntegral' (barnesIntegrandPow s x 0) (genusAbscissa s g 0))
      (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hxpos : (0 : ℝ) < x := hx
  obtain ⟨h1, h2, hsσ⟩ := genusAbscissa_zero_mem hs hgl hgu
  have hbase := hasSum_barnesModel_verticalIntegral' (g := g) (s := s) (x := x)
    (σ := genusAbscissa s g 0) hxpos h1 h2 hsσ
  rw [barnesGenusEulerSum, hbase.tsum_eq]
  exact congrArg (fun f => VerticalIntegral' f (genusAbscissa s g 0))
    (funext fun w => (barnesIntegrandPow_zero s x w).symm)

/-- The initial abscissa of the genus ladder avoids the pole of zeta. -/
theorem genusStart_zeta (hs : 0 < s) (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) :
    -(s : ℝ) * genusAbscissa s g 0 ≠ 1 :=
  mul_genusAbscissa_ne_one hs (genusAbscissa_ne_zetaPole hgl hgu 0)

/-- **Every Euler derivative of the genus-`g` Euler sum is a contour integral.** -/
theorem eulerIterate_barnesGenusEulerSum (hs : 0 < s) (hgl : (g : ℝ) < 1 / s)
    (hgu : 1 / s < (g : ℝ) + 1) (m : ℕ) :
    Set.EqOn (eulerDeriv^[m] (barnesGenusEulerSum s g))
      (fun x : ℝ => VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g 0))
      (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hcongr := eulerDeriv_iterate_congr isOpen_Ioi (barnesGenusEulerSum_eqOn hs hgl hgu) m hx
  have hiter := eulerIterate_barnes hs (genusStart_zeta hs hgl hgu)
    (sin_pi_genusAbscissa_zero_ne_zero hgl hgu) m hx
  rw [hcongr, hiter]

/-- **The genus-`g` Barnes expansion is termwise differentiable.**  For every Euler derivative `D^m`
and every truncation `K` the error after the leading term and the first `K` crossed integers — each
weighted by `(-p)^m` at the crossed point `p` — is `O(x^{-σ_{K+1}})`, uniformly in `x > 0`. -/
theorem barnes_genus_poincare_expansion_euler (hs : 0 < s) (hgl : (g : ℝ) < 1 / s)
    (hgu : 1 / s < (g : ℝ) + 1) (m K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(eulerDeriv^[m] (barnesGenusEulerSum s g)) x
          + barnesLeadingGenusResidue s x m
          + ∑ k ∈ Finset.range K, barnesIntResidue s x m ((k : ℤ) - (g : ℤ))‖
        ≤ C * x ^ (-(genusAbscissa s g (K + 1))) := by
  set σK : ℝ := genusAbscissa s g (K + 1) with hσK
  set C : ℝ :=
    (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖barnesIntegrandPow s 1 m ((σK : ℂ) + (t : ℂ) * I)‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun t => norm_nonneg _)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx
  have hval : (eulerDeriv^[m] (barnesGenusEulerSum s g)) x
      = VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g 0) :=
    eulerIterate_barnesGenusEulerSum hs hgl hgu m hxmem
  rw [hval, verticalIntegral'_genus_finite_expansion hs hx m hgl hgu K]
  have hshape : VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (K + 1))
      - barnesLeadingGenusResidue s x m
      - (∑ k ∈ Finset.range K, barnesIntResidue s x m ((k : ℤ) - (g : ℤ)))
      + barnesLeadingGenusResidue s x m
      + ∑ k ∈ Finset.range K, barnesIntResidue s x m ((k : ℤ) - (g : ℤ))
      = VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (K + 1)) := by ring
  rw [hshape, ← hσK]
  exact norm_verticalIntegral'_barnesPow_le m hx

end

end RHTower
