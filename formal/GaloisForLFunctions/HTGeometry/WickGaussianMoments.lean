import GaloisForLFunctions.HTGeometry.WickFockModel
import GaloisForLFunctions.HTGeometry.GaussianRealMoments

/-!
# Gaussian moments are vacuum expectation values of a free field

Two statements tie the operator form of Wick's theorem to the probabilistic one.

* `integral_pow_centered_dual`: for a Gaussian measure on a Banach space and one continuous linear
  form `L`, the centred moments of `L` are the complete-pairing sums of its variance.  This is the
  single-functional case of Isserlis' theorem, obtained by pushing `μ` forward along `L` and
  translating to a centred real Gaussian.

* `integral_pow_gaussianReal_eq_vacuum_prod_field`: those same moments are the vacuum expectation
  values of a word of free bosonic fields with propagator `v`.  The field is the concrete one-mode
  operator `v · X · + ∂` on the polynomial Fock space, so the identity is Wick's theorem for a
  creation/annihilation system read as a statement about a Gaussian random variable.
-/

universe u v w

open MeasureTheory ProbabilityTheory MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-! ## The single-functional case of Isserlis' theorem -/

section Dual

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsGaussian μ]

/-- **Wick's theorem for one linear functional of a Gaussian vector.**  The `n`-th centred moment of
a continuous linear form under a Gaussian measure is the sum over the perfect matchings of a word of
`n` copies of it, each pair contributing the variance. -/
theorem integral_pow_centered_dual (L : StrongDual ℝ E) (n : ℕ) :
    ∫ x, (L x - μ[L]) ^ n ∂μ
      = completePairing (fun _ _ : StrongDual ℝ E => Var[L; μ]) (List.replicate n L) := by
  set m : ℝ := μ[L] with hm
  set v : NNReal := (Var[L; μ]).toNNReal with hv
  have hLmeas : Measurable (L : E → ℝ) := L.continuous.measurable
  have hpush : ∫ x, (L x - m) ^ n ∂μ = ∫ y, (y - m) ^ n ∂(μ.map L) := by
    rw [integral_map hLmeas.aemeasurable]
    fun_prop
  have hgauss : μ.map (L : E → ℝ) = gaussianReal m v := IsGaussian.map_eq_gaussianReal L
  have htrans : ∫ y, (y - m) ^ n ∂(gaussianReal m v) = ∫ z, z ^ n ∂(gaussianReal 0 v) := by
    have hmap : (gaussianReal m v).map (fun y => y - m) = gaussianReal 0 v := by
      rw [gaussianReal_map_sub_const]
      simp
    rw [← hmap, integral_map (by fun_prop)]
    fun_prop
  have hvar : ((v : ℝ)) = Var[L; μ] := Real.coe_toNNReal _ (variance_nonneg _ _)
  rw [hpush, hgauss, htrans, integral_pow_gaussianReal_eq_completePairing v L n, hvar]

end Dual

/-! ## A one-mode bosonic field with an arbitrary propagator -/

section Field

variable (K : Type u) [CommRing K]

/-- **A single bosonic mode with propagator `v`**: multiplication by `v · X` creates, `∂` destroys,
and their commutator is `v`. -/
noncomputable def scalarFock (v : K) :
    WickSystem K (Module.End K (MvPolynomial Unit K)) Unit where
  cre _ := LinearMap.mulLeft K (v • (X () : MvPolynomial Unit K))
  ann _ := (pderiv () : Derivation K (MvPolynomial Unit K) (MvPolynomial Unit K)).toLinearMap
  κ _ _ := v
  cre_mul_cre _ _ := rfl
  ann_mul_ann _ _ := rfl
  ann_mul_cre _ _ := by
    refine LinearMap.ext fun p => ?_
    show pderiv () ((v • (X () : MvPolynomial Unit K)) * p)
        = (v • (X () : MvPolynomial Unit K)) * pderiv () p + v • p
    rw [smul_mul_assoc, Derivation.map_smul, pderiv_mul, pderiv_X_self, one_mul, smul_add,
      ← smul_mul_assoc, add_comm]

@[simp] theorem scalarFock_κ (v : K) (i j : Unit) : (scalarFock K v).κ i j = v := rfl

/-- The Fock vacuum of the one-mode system. -/
noncomputable def scalarFockVacuum (v : K) : WickVacuum (scalarFock K v) where
  ω := fockVacuumFunctional K Unit
  ω_one := by simp
  ω_cre i x := by
    simp only [fockVacuumFunctional_apply, Module.End.mul_apply]
    show constantCoeff ((v • (X () : MvPolynomial Unit K)) * x 1) = 0
    rw [map_mul]
    simp
  ω_ann i x := by
    simp only [fockVacuumFunctional_apply, Module.End.mul_apply]
    show constantCoeff (x (pderiv () (1 : MvPolynomial Unit K))) = 0
    rw [pderiv_one, map_zero, map_zero]

/-- **Wick's theorem for a single mode.**  The vacuum expectation of a word of `n` copies of the
field `v · X · + ∂` is the complete-pairing sum of the propagator `v`. -/
theorem scalarFock_vacuum_prod_field (v : K) (n : ℕ) :
    (scalarFockVacuum K v).ω (((List.replicate n ()).map (scalarFock K v).field).prod)
      = completePairing (fun _ _ : Unit => v) (List.replicate n ()) :=
  (scalarFockVacuum K v).vacuum_prod_field _

end Field

/-! ## The bridge -/

/-- **The moments of a centred real Gaussian are vacuum expectation values of a free field.**  The
`n`-th moment of `gaussianReal 0 v` is the vacuum expectation of the product of `n` copies of the
one-mode bosonic field with propagator `v`. -/
theorem integral_pow_gaussianReal_eq_vacuum_prod_field (v : NNReal) (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 v)
      = (scalarFockVacuum ℝ (v : ℝ)).ω
          (((List.replicate n ()).map (scalarFock ℝ (v : ℝ)).field).prod) := by
  rw [scalarFock_vacuum_prod_field, integral_pow_gaussianReal_eq_completePairing v ()]

/-- The same statement for one linear functional of a Gaussian measure on a Banach space. -/
theorem integral_pow_centered_dual_eq_vacuum_prod_field
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) (n : ℕ) :
    ∫ x, (L x - μ[L]) ^ n ∂μ
      = (scalarFockVacuum ℝ Var[L; μ]).ω
          (((List.replicate n ()).map (scalarFock ℝ Var[L; μ]).field).prod) := by
  rw [integral_pow_centered_dual μ L n, scalarFock_vacuum_prod_field]
  exact completePairing_replicate_const _ _ _ _

end GaloisForLFunctions.HTGeometry
