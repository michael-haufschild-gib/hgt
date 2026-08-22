import GaloisForLFunctions.HTGeometry.AbeExponentialDampingJetRecurrence

/-!
# Finite polynomial form of Abe's all-order multiplier jets

For a fixed direction, the factor left after differentiating Abe's exponential multiplier any
finite number of times is a finite polynomial in the damping parameter.  This gives the exact
algebraic coefficient expansion needed before the separate analytic majorant problem can be
addressed.  No growth, convergence, or Poincare-series hypothesis occurs here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A source-valued family has a finite polynomial expansion in its complex parameter. -/
def HasFiniteDampingPolynomial {d : ℕ} (F : ℂ → MultivariateEntire d) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (degree : ι → ℕ) (coefficient : ι → MultivariateEntire d),
    ∀ t, F t = ∑ i, t ^ degree i • coefficient i

/-- Directional differentiation annihilates the zero entire source. -/
theorem partialDerivEntire_zero {d : ℕ} (v : Fin d → ℂ) :
    partialDerivEntire v (0 : MultivariateEntire d) = 0 := by
  ext x
  change fderiv ℂ (fun _ : Fin d → ℂ => 0) x v = 0
  have h : HasFDerivAt (fun _ : Fin d → ℂ => (0 : ℂ))
      (0 : (Fin d → ℂ) →L[ℂ] ℂ) x :=
    hasFDerivAt_const (0 : ℂ) x
  rw [h.fderiv]
  rfl

/-- Directional differentiation is complex-linear on entire sources. -/
theorem partialDerivEntire_smul {d : ℕ} (v : Fin d → ℂ) (t : ℂ)
    (f : MultivariateEntire d) :
    partialDerivEntire v (t • f) = t • partialDerivEntire v f := by
  ext x
  change fderiv ℂ (fun y => t * f.1 y) x v =
    t * fderiv ℂ (f.1 : (Fin d → ℂ) → ℂ) x v
  have hfun : (fun y : Fin d → ℂ => t * f.1 y) =
      t • (f.1 : (Fin d → ℂ) → ℂ) := by
    ext y
    rfl
  rw [hfun]
  have h := ((differentiable_multivariateEntire f x).hasFDerivAt).const_smul t
  rw [h.fderiv]
  rfl

/-- Directional differentiation is additive on entire sources. -/
theorem partialDerivEntire_add {d : ℕ} (v : Fin d → ℂ)
    (f g : MultivariateEntire d) :
    partialDerivEntire v (f + g) =
      partialDerivEntire v f + partialDerivEntire v g := by
  ext x
  change fderiv ℂ (fun y => f.1 y + g.1 y) x v =
    fderiv ℂ (f.1 : (Fin d → ℂ) → ℂ) x v +
      fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) x v
  have hfun : (fun y : Fin d → ℂ => f.1 y + g.1 y) =
      (f.1 : (Fin d → ℂ) → ℂ) + g.1 := by
    rfl
  rw [hfun]
  have h := ((differentiable_multivariateEntire f x).hasFDerivAt).add
      ((differentiable_multivariateEntire g x).hasFDerivAt)
  rw [h.fderiv]
  rfl

/-- Directional differentiation distributes over a finite scalar-weighted source sum. -/
theorem partialDerivEntire_finsetSum_smul {d : ℕ} {ι : Type}
    (v : Fin d → ℂ) (s : Finset ι) (a : ι → ℂ)
    (f : ι → MultivariateEntire d) :
    partialDerivEntire v (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i • partialDerivEntire v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, partialDerivEntire_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, partialDerivEntire_add,
        partialDerivEntire_smul, ih]

/-- Directional differentiation distributes over a finite-type scalar-weighted source sum. -/
theorem partialDerivEntire_fintypeSum_smul {d : ℕ} {ι : Type} [Fintype ι]
    (v : Fin d → ℂ) (a : ι → ℂ) (f : ι → MultivariateEntire d) :
    partialDerivEntire v (∑ i, a i • f i) =
      ∑ i, a i • partialDerivEntire v (f i) := by
  simpa using partialDerivEntire_finsetSum_smul v Finset.univ a f

/-- Pointwise evaluation of a sum of entire sources. -/
theorem multivariateEntire_add_apply {d : ℕ} (f g : MultivariateEntire d)
    (x : Fin d → ℂ) : (f + g).1 x = f.1 x + g.1 x := by
  rfl

/-- Pointwise evaluation of a complex-scaled entire source. -/
theorem multivariateEntire_smul_apply {d : ℕ} (t : ℂ) (f : MultivariateEntire d)
    (x : Fin d → ℂ) : (t • f).1 x = t * f.1 x := by
  rfl

/-- Pointwise evaluation commutes with finite sums of entire sources. -/
theorem multivariateEntire_sum_apply {d : ℕ} {ι : Type} (s : Finset ι)
    (f : ι → MultivariateEntire d) (x : Fin d → ℂ) :
    (∑ i ∈ s, f i).1 x = ∑ i ∈ s, (f i).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        multivariateEntire_add_apply, ih]

/-- Multiplication by `t • A` increases every degree in a finite source polynomial by one. -/
theorem multivariateEntire_mul_t_smul_sum {d : ℕ} {ι : Type} [Fintype ι]
    (t : ℂ) (A : MultivariateEntire d) (degree : ι → ℕ)
    (coefficient : ι → MultivariateEntire d) :
    (t • A) * (∑ i, t ^ degree i • coefficient i) =
      ∑ i, t ^ (degree i + 1) • (A * coefficient i) := by
  classical
  ext x
  rw [multivariateEntire_mul_apply, multivariateEntire_smul_apply,
    multivariateEntire_sum_apply, multivariateEntire_sum_apply]
  simp only [multivariateEntire_smul_apply, multivariateEntire_mul_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [pow_succ]
  ring

/-- The factor left after any finite number of directional derivatives of Abe's multiplier is a
finite polynomial in its damping parameter. -/
theorem hasFiniteDampingPolynomial_abeExponentialDampingJetFactor {d : ℕ}
    (v : Fin d → ℂ) (Θ : MultivariateEntire d) (n : ℕ) :
    HasFiniteDampingPolynomial
      (fun t => abeExponentialDampingJetFactor v t Θ n) := by
  induction n with
  | zero =>
      refine ⟨Unit, inferInstance, fun _ => 0, fun _ => 1, ?_⟩
      intro t
      simp [abeExponentialDampingJetFactor]
  | succ n ih =>
      rcases ih with ⟨ι, hι, degree, coefficient, hpolynomial⟩
      change ∀ t, abeExponentialDampingJetFactor v t Θ n =
        ∑ i, t ^ degree i • coefficient i at hpolynomial
      letI : Fintype ι := hι
      refine ⟨Sum ι ι, inferInstance,
        Sum.elim (fun i => degree i + 1) degree,
        Sum.elim (fun i => (partialDerivEntire v Θ) * coefficient i)
          (fun i => partialDerivEntire v (coefficient i)), ?_⟩
      intro t
      change abeExponentialDampingJetFactor v t Θ (Nat.succ n) = _
      rw [abeExponentialDampingJetFactor.eq_2, hpolynomial t,
        partialDerivEntire_fintypeSum_smul, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [multivariateEntire_mul_t_smul_sum]

/-- The factor left after any finite number of directional derivatives of an Abe-damped seed is a
finite polynomial in its damping parameter. -/
theorem hasFiniteDampingPolynomial_abeExponentialDampingSeedJetFactor {d : ℕ}
    (v : Fin d → ℂ) (Θ seed : MultivariateEntire d) (n : ℕ) :
    HasFiniteDampingPolynomial
      (fun t => abeExponentialDampingSeedJetFactor v t Θ seed n) := by
  induction n with
  | zero =>
      refine ⟨Unit, inferInstance, fun _ => 0, fun _ => seed, ?_⟩
      intro t
      simp [abeExponentialDampingSeedJetFactor]
  | succ n ih =>
      rcases ih with ⟨ι, hι, degree, coefficient, hpolynomial⟩
      change ∀ t, abeExponentialDampingSeedJetFactor v t Θ seed n =
        ∑ i, t ^ degree i • coefficient i at hpolynomial
      letI : Fintype ι := hι
      refine ⟨Sum ι ι, inferInstance,
        Sum.elim (fun i => degree i + 1) degree,
        Sum.elim (fun i => (partialDerivEntire v Θ) * coefficient i)
          (fun i => partialDerivEntire v (coefficient i)), ?_⟩
      intro t
      change abeExponentialDampingSeedJetFactor v t Θ seed (Nat.succ n) = _
      rw [abeExponentialDampingSeedJetFactor.eq_2, hpolynomial t,
        partialDerivEntire_fintypeSum_smul, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [multivariateEntire_mul_t_smul_sum]

end

end GaloisForLFunctions.HTGeometry
