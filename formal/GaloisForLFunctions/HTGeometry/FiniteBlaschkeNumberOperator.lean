import GaloisForLFunctions.HTGeometry.HardyNumberSpectrum
import GaloisForLFunctions.HTGeometry.LpFiniteCoordinateOperator

/-!
# Finite sums of actual Blaschke number operators

The weighted coordinate number operator has its maximal square-summability
domain. Adding the bounded local KMS corrections yields a complete product
eigenbasis on that same domain, with no extra summability assumption on modes.
-/

noncomputable section

open scoped Classical InnerProductSpace LinearPMap

namespace GaloisForLFunctions.HTGeometry

variable {I : Type} [Fintype I]

abbrev FiniteNumberSpace (I : Type) := lp (fun _ : I → ℕ => ℂ) 2

/-- The weighted degree in the original integer-coordinate basis. -/
def finiteNumberDegree (c : I → ℝ) (x : I → ℕ) : ℝ := ∑ i, c i * x i

/-- The complete product of the local ground and excitation bases. -/
def finiteBlaschkeBasis (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) :
    HilbertBasis (I → ℕ) ℂ (FiniteNumberSpace I) :=
  lpFiniteProductBasis I (fun i => hardyNumberBasis (hq i))

/-- The bounded correction from independent geometric kernels and a real offset. -/
def finiteBlaschkeCorrection (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1)
    (c : I → ℝ) (a : ℝ) : FiniteNumberSpace I →L[ℂ] FiniteNumberSpace I :=
  (a : ℂ) • 1 + ∑ i, (c i : ℂ) •
    (1 - lpCoordinateOperator i (hardyGeometricKMS (hq i)))

theorem finiteBlaschkeCorrection_offset
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) :
    finiteBlaschkeCorrection q hq c a =
      (a : ℂ) • 1 + finiteBlaschkeCorrection q hq c 0 := by
  simp only [finiteBlaschkeCorrection, Complex.ofReal_zero, zero_smul, zero_add]

theorem finiteBlaschkeCorrection_isSelfAdjoint
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) :
    IsSelfAdjoint (finiteBlaschkeCorrection q hq c a) := by
  apply IsSelfAdjoint.add
  · exact (show IsSelfAdjoint (a : ℂ) by exact Complex.conj_ofReal a).smul (IsSelfAdjoint.one _)
  · apply isSelfAdjoint_sum
    intro i _
    exact (show IsSelfAdjoint (c i : ℂ) by exact Complex.conj_ofReal (c i)).smul
      ((IsSelfAdjoint.one _).sub (lpCoordinateOperator_isSelfAdjoint i _
        (hardyGeometricKMS_isSelfAdjoint (hq i))))

/-- The actual operator, on the maximal original-coordinate weighted domain. -/
def finiteBlaschkeNumberOperator (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1)
    (c : I → ℝ) (a : ℝ) : FiniteNumberSpace I →ₗ.[ℂ] FiniteNumberSpace I :=
  (finiteBlaschkeCorrection q hq c a).toLinearMap +ᵥ
    RHTower.maximalRealDiagonal (finiteNumberDegree c)

theorem finiteBlaschkeNumberOperator_apply
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ)
    (v : (finiteBlaschkeNumberOperator q hq c a).domain) (x : I → ℕ) :
    finiteBlaschkeNumberOperator q hq c a v x =
      finiteBlaschkeCorrection q hq c a (v : FiniteNumberSpace I) x +
        (finiteNumberDegree c x : ℂ) * (v : FiniteNumberSpace I) x := rfl

theorem finiteBlaschkeNumberOperator_isClosed
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) :
    (finiteBlaschkeNumberOperator q hq c a).IsClosed :=
  LinearPMap.IsClosed.continuousLinearMap_vadd
    (RHTower.maximalRealDiagonal_isSelfAdjoint (finiteNumberDegree c)).isClosed _

theorem finiteBlaschkeNumberOperator_formalSelfAdjoint
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) :
    (finiteBlaschkeNumberOperator q hq c a).IsFormalAdjoint
      (finiteBlaschkeNumberOperator q hq c a) := by
  intro x y
  let D := RHTower.maximalRealDiagonal (finiteNumberDegree c)
  let xD : D.domain := ⟨(x : FiniteNumberSpace I), x.property⟩
  let yD : D.domain := ⟨(y : FiniteNumberSpace I), y.property⟩
  change inner ℂ (finiteBlaschkeCorrection q hq c a (x : FiniteNumberSpace I) + D xD)
      (y : FiniteNumberSpace I) =
    inner ℂ (x : FiniteNumberSpace I)
      (finiteBlaschkeCorrection q hq c a (y : FiniteNumberSpace I) + D yD)
  rw [inner_add_left, inner_add_right]
  apply congrArg₂ (· + ·)
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (finiteBlaschkeCorrection_isSelfAdjoint q hq c a) _ _
  · exact RHTower.maximalRealDiagonal_formalSelfAdjoint (finiteNumberDegree c) xD yD

/-- The sum of the local ground or excitation energies. -/
def finiteBlaschkeEnergy (q c : I → ℝ) (a : ℝ) (e : I → ℕ) : ℝ :=
  a + ∑ i, c i * hardyNumberEnergy (q i) (e i)

theorem finiteBlaschkeCorrection_basis_apply
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ)
    (e x : I → ℕ) :
    finiteBlaschkeCorrection q hq c a (finiteBlaschkeBasis q hq e) x =
      ((finiteBlaschkeEnergy q c a e : ℂ) - (finiteNumberDegree c x : ℂ)) *
        finiteBlaschkeBasis q hq e x := by
  have hlocal (i : I) : lpCoordinateOperator i (hardyGeometricKMS (hq i))
      (finiteBlaschkeBasis q hq e) x =
      ((x i : ℂ) + 1 - (hardyNumberEnergy (q i) (e i) : ℂ)) *
        finiteBlaschkeBasis q hq e x := lpCoordinateOperator_productBasis_multiplier i
    (hardyGeometricKMS (hq i)) (fun i => hardyNumberBasis (hq i)) e
    (fun n => (n : ℂ) + 1 - (hardyNumberEnergy (q i) (e i) : ℂ))
    (hardyGeometricKMS_numberBasis_apply (hq i) (e i)) x
  simp only [finiteBlaschkeCorrection, _root_.add_apply,
    _root_.smul_apply, _root_.one_apply_eq_self, _root_.sum_apply, _root_.sub_apply]
  simp only [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, lp.coeFn_sum,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [hlocal]
  simp only [finiteBlaschkeEnergy, finiteNumberDegree, Complex.ofReal_add,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [sub_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
  conv_rhs => rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Mode-domain membership follows from a bounded image and one scalar multiple. -/
theorem finiteBlaschkeBasis_mem_domain
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) (e : I → ℕ) :
    finiteBlaschkeBasis q hq e ∈ (finiteBlaschkeNumberOperator q hq c a).domain := by
  let v := finiteBlaschkeBasis q hq e
  let y := (finiteBlaschkeEnergy q c a e : ℂ) • v - finiteBlaschkeCorrection q hq c a v
  change Memℓp (fun x => (finiteNumberDegree c x : ℂ) * v x) 2
  have hy : (fun x => (finiteNumberDegree c x : ℂ) * v x) = fun x => y x := by
    funext x
    change (finiteNumberDegree c x : ℂ) * v x =
      (finiteBlaschkeEnergy q c a e : ℂ) * v x - finiteBlaschkeCorrection q hq c a v x
    rw [finiteBlaschkeCorrection_basis_apply]
    ring
  rw [hy]
  exact lp.memℓp y

theorem finiteBlaschkeNumberOperator_basis
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) (e : I → ℕ) :
    finiteBlaschkeNumberOperator q hq c a
      ⟨finiteBlaschkeBasis q hq e, finiteBlaschkeBasis_mem_domain q hq c a e⟩ =
        (finiteBlaschkeEnergy q c a e : ℂ) • finiteBlaschkeBasis q hq e := by
  apply lp.ext
  funext x
  change finiteBlaschkeCorrection q hq c a (finiteBlaschkeBasis q hq e) x +
    (finiteNumberDegree c x : ℂ) * finiteBlaschkeBasis q hq e x =
      (finiteBlaschkeEnergy q c a e : ℂ) * finiteBlaschkeBasis q hq e x
  rw [finiteBlaschkeCorrection_basis_apply]
  ring

/-- The entire original maximal domain has exactly the spectral weighted coordinates. -/
theorem finiteBlaschkeNumberOperator_domain_iff
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ)
    (x : FiniteNumberSpace I) :
    x ∈ (finiteBlaschkeNumberOperator q hq c a).domain ↔
      Memℓp (fun e => (finiteBlaschkeEnergy q c a e : ℂ) *
        (finiteBlaschkeBasis q hq).repr x e) 2 :=
  closed_eigenbasis_domain_iff _ _ _ (finiteBlaschkeNumberOperator_isClosed q hq c a)
    (finiteBlaschkeNumberOperator_formalSelfAdjoint q hq c a)
    (finiteBlaschkeBasis_mem_domain q hq c a) (finiteBlaschkeNumberOperator_basis q hq c a) x

theorem finiteBlaschkeNumberOperator_isSelfAdjoint
    (q : I → ℝ) (hq : ∀ i, ‖(q i : ℂ)‖ < 1) (c : I → ℝ) (a : ℝ) :
    IsSelfAdjoint (finiteBlaschkeNumberOperator q hq c a) :=
  closed_eigenbasis_isSelfAdjoint _ _ _ (finiteBlaschkeNumberOperator_isClosed q hq c a)
    (finiteBlaschkeNumberOperator_formalSelfAdjoint q hq c a)
    (finiteBlaschkeBasis_mem_domain q hq c a) (finiteBlaschkeNumberOperator_basis q hq c a)

end GaloisForLFunctions.HTGeometry
