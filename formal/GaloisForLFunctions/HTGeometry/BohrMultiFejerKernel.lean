import GaloisForLFunctions.HTGeometry.BohrFejerConcentration

/-!
# The multi-dimensional Fejér kernel

The Bochner–Fejér construction uses the product of one-dimensional Fejér kernels over a finite family
of base frequencies `β_j`.  This file builds that product and records its structure:

* it is a nonnegative real, being a product of nonnegative reals;
* it is a trigonometric polynomial whose frequencies are exactly the integer combinations
  `∑_j (a_j − b_j) β_j` with `0 ≤ a_j, b_j ≤ N_j`, so its whole spectrum lies in the `ℤ`-span of the
  base frequencies;
* consequently it is continuous and almost periodic.

Rational independence of the `β_j` will make the zero frequency occur only on the diagonal
`a_j = b_j`, which is what forces the mean of the product to be one.
-/

open Filter Topology ComplexConjugate

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The product of one-dimensional Fejér kernels over a finite family of base frequencies. -/
noncomputable def multiFejerKernel {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) : ℂ :=
  ∏ j : ι, fejerKernel (β j) (N j) u

/-- The multi-dimensional kernel is a nonnegative real. -/
theorem multiFejerKernel_eq_ofReal {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) :
    multiFejerKernel β N u
      = (((∏ j : ι, ‖fejerSum (β j) (N j) u‖ ^ 2 / ((N j : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [multiFejerKernel, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun j _ => fejerKernel_eq_ofReal (β j) (N j) u

theorem multiFejerKernel_nonneg {ι : Type*} [Fintype ι] (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) :
    0 ≤ ∏ j : ι, ‖fejerSum (β j) (N j) u‖ ^ 2 / ((N j : ℝ) + 1) :=
  Finset.prod_nonneg fun j _ => fejerKernel_nonneg (β j) (N j) u

/-- **Expansion of the multi-dimensional kernel.**  Its frequencies are the integer combinations
`∑_j (a_j − b_j) β_j` of the base frequencies. -/
theorem multiFejerKernel_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) (u : ℝ) :
    multiFejerKernel β N u
      = ∑ v ∈ Fintype.piFinset
            (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)),
          (∏ j : ι, ((N j : ℂ) + 1)⁻¹) *
            expChar (∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j) u := by
  classical
  have hfac : ∀ j : ι, fejerKernel (β j) (N j) u
      = ∑ p ∈ Finset.range (N j + 1) ×ˢ Finset.range (N j + 1),
          ((N j : ℂ) + 1)⁻¹ * expChar (((p.1 : ℝ) - (p.2 : ℝ)) * β j) u :=
    fun j => fejerKernel_eq_sum (β j) (N j) u
  rw [multiFejerKernel, Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.prod_mul_distrib, prod_expChar]

/-- The multi-dimensional kernel is continuous. -/
theorem continuous_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) : Continuous (multiFejerKernel β N) := by
  have h : multiFejerKernel β N = fun u => ∑ v ∈ Fintype.piFinset
      (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)),
      (∏ j : ι, ((N j : ℂ) + 1)⁻¹) *
        expChar (∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j) u :=
    funext fun u => multiFejerKernel_eq_sum β N u
  rw [h]
  exact continuous_finsetSum _ fun v _ => continuous_const.mul (continuous_expChar _)

/-- The multi-dimensional kernel is almost periodic. -/
theorem isBohrAlmostPeriodic_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) : HTGeometry.IsBohrAlmostPeriodic (multiFejerKernel β N) := by
  have h : multiFejerKernel β N = fun u => ∑ v ∈ Fintype.piFinset
      (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)),
      (∏ j : ι, ((N j : ℂ) + 1)⁻¹) *
        expChar (∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j) u :=
    funext fun u => multiFejerKernel_eq_sum β N u
  rw [h]
  exact isBohrAlmostPeriodic_sum _ (fun v _ => continuous_const.mul (continuous_expChar _))
    (fun v _ => isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_expChar _))

/-- **Convolution against the multi-dimensional kernel.**  It returns the trigonometric polynomial
whose coefficients are the Bohr coefficients of `f` at the integer combinations of the base
frequencies, weighted by the kernel weights. -/
theorem bohrMean_translate_mul_multiFejerKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → ℝ) (N : ι → ℕ) {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (t : ℝ) :
    bohrMean (fun u => f (u + t) * multiFejerKernel β N u)
      = ∑ v ∈ Fintype.piFinset
            (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)),
          ((∏ j : ι, ((N j : ℂ) + 1)⁻¹) *
              bohrCoefficient f (-(∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j))) *
            expChar (-(∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j)) t := by
  classical
  have h : (fun u => f (u + t) * multiFejerKernel β N u)
      = fun u => f (u + t) * ∑ v ∈ Fintype.piFinset
          (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)),
          (∏ j : ι, ((N j : ℂ) + 1)⁻¹) *
            bohrChar (-(∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j)) u := by
    funext u
    rw [multiFejerKernel_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [expChar_eq_bohrChar]
  rw [h, bohrMean_translate_mul_trigKernel
    (Fintype.piFinset (fun j : ι => Finset.range (N j + 1) ×ˢ Finset.range (N j + 1)))
    (fun _ : ι → ℕ × ℕ => ∏ j : ι, ((N j : ℂ) + 1)⁻¹)
    (fun v : ι → ℕ × ℕ => -(∑ j : ι, (((v j).1 : ℝ) - ((v j).2 : ℝ)) * β j)) hfc hfa t]

end

end GaloisForLFunctions
