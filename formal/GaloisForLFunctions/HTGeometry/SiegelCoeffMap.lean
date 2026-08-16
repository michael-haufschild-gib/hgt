import GaloisForLFunctions.HTGeometry.SiegelPolynomial
import GaloisForLFunctions.HTGeometry.PolydiscSeriesCoefficients

/-!
# The Taylor-condition map of a Siegel count

The Cauchy coefficients of a polydisc are linear in the integrand, provided the integrands are
continuous so that the torus integrals exist.  Attaching to a coefficient vector the Cauchy
coefficients of the associated combination, at each of finitely many centres and each multi-index of
a prescribed finite set, therefore gives a genuine linear map.

This is the map the counting step is applied to: its source is the coefficient space of the
exponent box and its target the space of Taylor conditions, and `exists_ne_zero_of_siegel_count`
produces a nonzero kernel vector as soon as the dimensions compare.
-/

namespace GaloisForLFunctions.HTGeometry

variable {d : ℕ}

/-- **The Cauchy coefficient is additive in the integrand.** -/
theorem polydiscCoeff_add {F G : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : Continuous F) (hG : Continuous G) (m : Fin d → ℕ) :
    polydiscCoeff (fun ζ => F ζ + G ζ) c R m
      = polydiscCoeff F c R m + polydiscCoeff G c R m := by
  have hmap : Continuous fun θ : Fin d → ℝ => torusMap c (fun _ => R) θ :=
    continuous_torusMap c fun _ => R
  have hFi := polydiscCoeff_integrable (f := F) (c := c) (R := R) (hF.comp hmap) hR m
  have hGi := polydiscCoeff_integrable (f := G) (c := c) (R := R) (hG.comp hmap) hR m
  have hsplit : (fun ζ : Fin d → ℂ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • (F ζ + G ζ))
      = fun ζ : Fin d → ℂ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • F ζ
          + (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • G ζ := by
    funext ζ
    rw [smul_add]
  rw [polydiscCoeff, polydiscCoeff, polydiscCoeff, hsplit, torusIntegral_add hFi hGi, smul_add]

/-- **The Cauchy coefficient is homogeneous in the integrand.** -/
theorem polydiscCoeff_const_smul (a : ℂ) (F : (Fin d → ℂ) → ℂ) (c : Fin d → ℂ) (R : ℝ)
    (m : Fin d → ℕ) :
    polydiscCoeff (fun ζ => a * F ζ) c R m = a * polydiscCoeff F c R m := by
  rw [polydiscCoeff, polydiscCoeff]
  have hsplit : (fun ζ : Fin d → ℂ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • (a * F ζ))
      = fun ζ : Fin d → ℂ => a • ((∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • F ζ) := by
    funext ζ
    simp only [smul_eq_mul]
    ring
  rw [hsplit, torusIntegral_smul a, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

variable {n m : ℕ} {ι : Type*} [Fintype ι]

/-- **The Taylor-condition map.**  A coefficient vector on the exponent box is sent to the Cauchy
coefficients of the associated combination at the prescribed centres and multi-indices. -/
noncomputable def siegelCoeffMap (f : Fin (n + 1) → (Fin d → ℂ) → ℂ)
    (hf : ∀ k, Continuous (f k)) (c : ι → (Fin d → ℂ)) {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin d → ℕ)) :
    ((Fin (n + 1) → Fin (m + 1)) → ℂ) →ₗ[ℂ] ((ι × S) → ℂ) where
  toFun a := fun p => polydiscCoeff (siegelCombination f a) (c p.1) R (p.2 : Fin d → ℕ)
  map_add' a b := by
    funext p
    have hcomb : siegelCombination f (a + b)
        = fun w => siegelCombination f a w + siegelCombination f b w := by
      rw [siegelCombination_add]
      rfl
    rw [hcomb, polydiscCoeff_add hR (continuous_siegelCombination hf a)
      (continuous_siegelCombination hf b)]
    rfl
  map_smul' t a := by
    funext p
    have hcomb : siegelCombination f (t • a) = fun w => t * siegelCombination f a w := by
      rw [siegelCombination_smul]
      funext w
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hcomb, polydiscCoeff_const_smul]
    rfl

omit [Fintype ι] in
@[simp]
theorem siegelCoeffMap_apply (f : Fin (n + 1) → (Fin d → ℂ) → ℂ)
    (hf : ∀ k, Continuous (f k)) (c : ι → (Fin d → ℂ)) {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin d → ℕ)) (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (p : ι × S) :
    siegelCoeffMap f hf c hR S a p
      = polydiscCoeff (siegelCombination f a) (c p.1) R (p.2 : Fin d → ℕ) := rfl

/-- **The counting step, applied to the Taylor-condition map.**  Once there are more coefficients
than conditions, some nonzero polynomial in the given functions has all its Cauchy coefficients of
the prescribed multi-indices vanishing at every centre. -/
theorem exists_ne_zero_poly_polydiscCoeff_eq_zero {N : ℕ}
    (f : Fin (n + 1) → (Fin n → ℂ) → ℂ) (hf : ∀ k, Continuous (f k))
    (c : ι → (Fin n → ℂ)) {R : ℝ} (hR : 0 < R)
    (S : Finset (Fin n → ℕ)) (hS : ∀ β ∈ S, ∑ i, β i < N)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      (∀ i : ι, ∀ β ∈ S, polydiscCoeff (siegelCombination f a) (c i) R β = 0) := by
  obtain ⟨a, ha, hT⟩ :=
    exists_ne_zero_of_siegel_count (n := n) (m := m) (N := N) S hS
      (siegelCoeffMap (n := n) (d := n) f hf c hR S) hcount
  refine ⟨a, ha, ?_⟩
  intro i β hβ
  have := congrFun hT (i, ⟨β, hβ⟩)
  simpa using this

end GaloisForLFunctions.HTGeometry
