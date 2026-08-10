import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GasPositivity

/-!
# The adjoint as an involution, and the contraction estimate

The adjoint of the gas algebra is an anti-multiplicative conjugate-linear involution, and for every
monomial `z` the element `z^* z` is a self-adjoint idempotent.  Positivity of the Gibbs functional
therefore gives the contraction estimate `φ((za)^* (za)) ≤ φ(a^* a)`: every monomial acts as a
contraction in the GNS inner product.  This is the boundedness input of the GNS representation.
-/

namespace GaloisForLFunctions.HTGeometry

open GasWord

open scoped ComplexOrder

variable {M : Type*}

/-! ## The adjoint on singles -/

theorem gasAdjoint_single (x : GasWord M) (c : ℂ) :
    gasAdjoint (MonoidAlgebra.single x c)
      = MonoidAlgebra.single (wstar x) ((starRingEnd ℂ) c) := by
  have h : Finsupp.mapDomain wstar
      (Finsupp.mapRange (starRingEnd ℂ) (by simp) (MonoidAlgebra.single x c).coeff)
      = (MonoidAlgebra.single (wstar x) ((starRingEnd ℂ) c)).coeff := by
    show Finsupp.mapDomain wstar
        (Finsupp.mapRange (starRingEnd ℂ) (by simp) (Finsupp.single x c))
      = Finsupp.single (wstar x) ((starRingEnd ℂ) c)
    rw [Finsupp.mapRange_single, Finsupp.mapDomain_single]
  rw [gasAdjoint, h, MonoidAlgebra.ofCoeff_coeff]

theorem gasAdjoint_add (a b : GasAlgebra M) :
    gasAdjoint (a + b) = gasAdjoint a + gasAdjoint b := by
  have hcoeff : (a + b).coeff = a.coeff + b.coeff := rfl
  rw [gasAdjoint, gasAdjoint, gasAdjoint, hcoeff,
    Finsupp.mapRange_add (by intro x y; simp), Finsupp.mapDomain_add]
  rfl

@[simp] theorem gasAdjoint_zero : gasAdjoint (0 : GasAlgebra M) = 0 := by
  have h : ((0 : GasAlgebra M)).coeff = 0 := rfl
  rw [gasAdjoint, h, Finsupp.mapRange_zero, Finsupp.mapDomain_zero]
  rfl

@[simp] theorem gasAdjoint_one : gasAdjoint (1 : GasAlgebra M) = 1 := by
  rw [MonoidAlgebra.one_def, gasAdjoint_single, wstar_one, map_one]

/-- **The adjoint is an involution.** -/
@[simp] theorem gasAdjoint_gasAdjoint (a : GasAlgebra M) : gasAdjoint (gasAdjoint a) = a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [gasAdjoint_add, gasAdjoint_add, hf, hg]
  | single x c => rw [gasAdjoint_single, gasAdjoint_single, wstar_wstar, Complex.conj_conj]

/-- **The adjoint reverses products.** -/
theorem gasAdjoint_mul (a b : GasAlgebra M) :
    gasAdjoint (a * b) = gasAdjoint b * gasAdjoint a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, gasAdjoint_add, hf, hg, gasAdjoint_add, mul_add]
  | single x c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => rw [mul_add, gasAdjoint_add, hf, hg, gasAdjoint_add, add_mul]
    | single y d =>
      rw [MonoidAlgebra.single_mul_single, gasAdjoint_single, gasAdjoint_single,
        gasAdjoint_single, MonoidAlgebra.single_mul_single, wstar_mul, map_mul]
      congr 1
      ring

theorem gasAdjoint_sub (a b : GasAlgebra M) :
    gasAdjoint (a - b) = gasAdjoint a - gasAdjoint b := by
  have h := gasAdjoint_add (a - b) b
  rw [sub_add_cancel] at h
  rw [h]
  abel

/-! ## Monomial projections -/

/-- **`z^* z` is a diagonal word.** -/
theorem wstar_mul_self (x : GasWord M) :
    wstar x * x = ⟨x.lower, x.lower⟩ := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
  · rw [raise_apply_mul, wstar_raise, wstar_lower]
    show x.lower i + (x.raise i - x.raise i) = x.lower i
    omega
  · rw [lower_apply_mul, wstar_lower]
    show x.lower i + (x.raise i - x.raise i) = x.lower i
    omega

theorem diagWord_idem (b : M →₀ ℕ) :
    (⟨b, b⟩ : GasWord M) * ⟨b, b⟩ = ⟨b, b⟩ := by
  refine GasWord.ext ?_ ?_ <;> refine Finsupp.ext fun i => ?_
  · rw [raise_apply_mul]
    show b i + (b i - b i) = b i
    omega
  · rw [lower_apply_mul]
    show b i + (b i - b i) = b i
    omega

theorem wstar_diagWord (b : M →₀ ℕ) : wstar (⟨b, b⟩ : GasWord M) = ⟨b, b⟩ := rfl

/-! ## The contraction estimate -/

/-- **A self-adjoint idempotent cannot increase the Gibbs form.** -/
theorem gibbs_proj_le (θ : AbelianZetaParameters) {p : GasAlgebra AbelianZetaMode}
    (hp : gasAdjoint p = p) (hpp : p * p = p) (a : GasAlgebra AbelianZetaMode) :
    gasGibbs θ (gasAdjoint a * (p * a)) ≤ gasGibbs θ (gasAdjoint a * a) := by
  have hq : gasAdjoint ((1 - p) * a) * ((1 - p) * a)
      = gasAdjoint a * a - gasAdjoint a * (p * a) := by
    rw [gasAdjoint_mul, gasAdjoint_sub, gasAdjoint_one, hp]
    have hsq : (1 - p) * (1 - p) = 1 - p := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, hpp, one_mul]
      abel
    calc gasAdjoint a * (1 - p) * ((1 - p) * a)
        = gasAdjoint a * ((1 - p) * (1 - p)) * a := by noncomm_ring
      _ = gasAdjoint a * (1 - p) * a := by rw [hsq]
      _ = gasAdjoint a * a - gasAdjoint a * (p * a) := by noncomm_ring
  have hpos := gasGibbs_adjoint_mul_self_nonneg θ ((1 - p) * a)
  rw [hq, map_sub] at hpos
  exact sub_nonneg.mp hpos

/-- **Every monomial acts as a contraction in the Gibbs form.** -/
theorem gibbs_contraction (θ : AbelianZetaParameters) (z : GasWord AbelianZetaMode)
    (a : GasAlgebra AbelianZetaMode) :
    gasGibbs θ (gasAdjoint (MonoidAlgebra.single z (1 : ℂ) * a)
        * (MonoidAlgebra.single z (1 : ℂ) * a))
      ≤ gasGibbs θ (gasAdjoint a * a) := by
  set p : GasAlgebra AbelianZetaMode :=
    MonoidAlgebra.single (⟨z.lower, z.lower⟩ : GasWord AbelianZetaMode) (1 : ℂ) with hpdef
  have hp : gasAdjoint p = p := by
    rw [hpdef, gasAdjoint_single, wstar_diagWord, map_one]
  have hpp : p * p = p := by
    rw [hpdef, MonoidAlgebra.single_mul_single, diagWord_idem, mul_one]
  have hrw : gasAdjoint (MonoidAlgebra.single z (1 : ℂ) * a)
      * (MonoidAlgebra.single z (1 : ℂ) * a) = gasAdjoint a * (p * a) := by
    rw [gasAdjoint_mul, gasAdjoint_single, map_one]
    have hz : (p : GasAlgebra AbelianZetaMode)
        = MonoidAlgebra.single (wstar z) (1 : ℂ) * MonoidAlgebra.single z (1 : ℂ) := by
      rw [MonoidAlgebra.single_mul_single, mul_one, wstar_mul_self]
    rw [hz]
    noncomm_ring
  rw [hrw]
  exact gibbs_proj_le θ hp hpp a

/-! ## The Gibbs functional is hermitian -/

/-- **`φ(a^*) = conj φ(a)`.**  The Gibbs weight is adjoint-invariant, so the functional is
hermitian; together with positivity this is the `conj_inner_symm` axiom of a pre-inner product. -/
theorem gibbs_gasAdjoint (q : M → ℂ) (hq : ∀ i, (starRingEnd ℂ) (q i) = q i)
    (a : GasAlgebra M) :
    gibbs q (gasAdjoint a) = (starRingEnd ℂ) (gibbs q a) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [gasAdjoint_add, map_add, hf, hg, map_add, map_add]
  | single x c =>
    rw [gasAdjoint_single, gibbs_single, gibbs_single, map_mul]
    congr 1
    rw [gibbsWeight_wstar]
    exact (gibbsWeight_conj q hq x).symm

end GaloisForLFunctions.HTGeometry
