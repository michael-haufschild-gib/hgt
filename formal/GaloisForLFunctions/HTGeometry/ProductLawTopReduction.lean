import GaloisForLFunctions.HTGeometry.ProductLawTranscendence
import GaloisForLFunctions.HTGeometry.AffineTopGeneral

/-!
# The top reduction for the product law

When the terminal factor of the law is linear — which is exactly the case of a cascade of first-order
linear entire maps, where `v_k(X) = X − d_(k−1)` — the newest coordinate is driven affinely,

`δ X_(m+1) = (α·H)·X_(m+1) + (β·H)`,   `H = ∏_(j≤m) Q_j(X_j)`,

with both coefficients free of that coordinate.  The model-independent reduction then applies, with
transcendence of the coordinate over the low subalgebra supplying what the polynomial model got from
substituting a fresh variable.

So one level of the cascade costs one coordinate, and the observability of the newest coordinate
reduces to the observability of its driving product.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- A linear terminal factor evaluates to an affine function of the coordinate. -/
theorem fact_linear {α β : ℂ} {k : ℕ} (hv : v k = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    fact (v k) k = algebraMap ℂ CascadeField α * fx k + algebraMap ℂ CascadeField β := by
  rw [hv, fact_add, fact_C]
  congr 1
  rw [show (Polynomial.C α * Polynomial.X : Polynomial ℂ) = Polynomial.C α * Polynomial.X ^ (1 : ℕ) by
    rw [pow_one], fact_monomial, pow_one]

/-- **The newest coordinate is driven affinely.** -/
theorem prodDerivation_fx_affine {α β : ℂ} {m : ℕ}
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β) :
    prodDerivation Q v (fx (m + 1))
      = (algebraMap ℂ CascadeField α * prodHead Q (m + 1)) * fx (m + 1)
        + algebraMap ℂ CascadeField β * prodHead Q (m + 1) := by
  rw [prodDerivation_fx, prodJet_eq, fact_linear v hv]
  ring

/-- **The top reduction in the rational model.**  With a linear terminal factor, the output-jet
Jacobian of the newest coordinate is nonzero as soon as the Jacobian of the positive homogeneous
coefficients of its driver is. -/
theorem det_ne_zero_of_top_prod {m : ℕ} {α β : ℂ}
    (hv : v (m + 1) = Polynomial.C α * Polynomial.X + Polynomial.C β)
    (hsub : (Matrix.of fun i j : Fin m =>
        fpderiv ((j : ℕ) + 1)
          (genJetA (prodDerivation Q v)
            (algebraMap ℂ CascadeField α * prodHead Q (m + 1)) ((i : ℕ) + 1))).det ≠ 0) :
    (Matrix.of fun i j : Fin (m + 1) =>
        Fin.lastCases (motive := fun _ => CascadeField)
          (fpderiv (m + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          (fun j' : Fin m => fpderiv ((j' : ℕ) + 1)
            (((prodDerivation Q v : CascadeField → CascadeField)^[(i : ℕ)]) (fx (m + 1))))
          j).det ≠ 0 := by
  have hHmem : prodHead Q (m + 1) ∈ lowSub Q v m := by
    refine Subalgebra.prod_mem _ fun j hj => ?_
    have hjm : j < m + 1 := Finset.mem_range.mp hj
    exact fact_mem_lowSub Q v (by omega) (Q j)
  refine det_ne_zero_of_affine_top_general (δ := prodDerivation Q v) (dtop := fpderiv (m + 1))
    (c := fun j : Fin m => fpderiv ((j : ℕ) + 1)) (S := lowSub Q v m)
    (prodDerivation_fx_affine Q v hv)
    (fun z hz => prodDerivation_mem_lowSub Q v hz)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ α) hHmem)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ β) hHmem)
    (fpderiv_fx_self (m + 1))
    (fun z hz => fpderiv_eq_zero_of_mem_lowSub Q v (by omega) hz)
    (fun j => fpderiv_fx_of_ne (by omega))
    (fun j z hz => fpderiv_mem_lowSub Q v hz)
    (injective_aeval_fx Q v m)
    hsub

end GaloisForLFunctions.HTGeometry
