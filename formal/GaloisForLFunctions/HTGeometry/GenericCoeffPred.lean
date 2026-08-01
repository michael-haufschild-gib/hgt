import GaloisForLFunctions.HTGeometry.CenteredGenericPolynomial

/-!
# The next-to-leading coefficient of the generic polynomial

The generic polynomial is the product of the linear factors attached to its roots, so its
next-to-leading coefficient is minus the sum of the roots.

Dividing by the degree gives the average, which is the amount by which the polynomial has to be
shifted to be centered.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] {d : ℕ}

/-- **The next-to-leading coefficient is minus the sum of the roots.** -/
theorem coeff_genericMonicF_pred (hd : 0 < d) :
    (genericMonicF K d).coeff (d - 1) = -∑ i : Fin d, genericRoot K d i := by
  classical
  have hcard : (Finset.univ : Finset (Fin d)).card = d := by simp
  have hle : d - 1 ≤ d := by omega
  have hrewrite : genericMonicF K d =
      ∏ i : Fin d, (Polynomial.X + Polynomial.C (-genericRoot K d i)) := by
    rw [genericMonicF]
    exact Finset.prod_congr rfl fun i _ => by rw [map_neg, sub_eq_add_neg]
  rw [hrewrite, Finset.prod_X_add_C_coeff _ _ (by rw [hcard]; exact hle), hcard,
    show d - (d - 1) = 1 from by omega, Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.prod_singleton]
  rw [Finset.sum_neg_distrib]

/-- **The average is minus the next-to-leading coefficient over the degree.** -/
theorem genericAverage_eq (hd : 0 < d) :
    genericAverage K d =
      -(((d : K)⁻¹ : K) • (genericMonicF K d).coeff (d - 1)) := by
  have hcast : algebraMap K (SymmetricRationalField K d) ((d : K)⁻¹) =
      ((d : SymmetricRationalField K d))⁻¹ := by
    rw [map_inv₀, map_natCast]
  rw [coeff_genericMonicF_pred hd, smul_neg, neg_neg, Algebra.smul_def, hcast, genericAverage]
  ring

end GaloisForLFunctions.HTGeometry
