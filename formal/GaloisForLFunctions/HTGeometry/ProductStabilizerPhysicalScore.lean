import GaloisForLFunctions.HTGeometry.TracelessPauliIdentityCoordinate

/-!
# The literal product-stabilizer two-query score

The physical experiment samples one Pauli string from the dictionary and one product stabilizer
state, applies the same unknown unitary to two copies, measures the sampled Pauli on each output,
and multiplies the two signs.  Its expectation is

`𝒮(U) = M⁻¹ ∑_P 𝔼_u ⟨u| U† P U |u⟩²`.

Writing each product stabilizer state through its density matrix `⊗_s (I + s σ_p)/2` — a Hermitian
idempotent of unit trace, hence a rank-one orthogonal projection — turns `⟨u|Q|u⟩` into a sitewise
product of the exact six-state single-qubit expectations.  Expanding `U† P U` in the Pauli basis
and averaging then produces the weighted coefficient signal already bounded below by the conserved
local coordinate, with the whole Pauli basis in the inner sum instead of only the dictionary.  All
inner terms are nonnegative, so the literal score dominates the dictionary signal.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-! ### Sitewise tensor products of single-qubit matrices -/

/-- Tensor product over sites of arbitrary single-qubit matrices. -/
def qubitLocalTensor (M : σ → Matrix Bool Bool ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  fun x y => ∏ s, M s (x s) (y s)

theorem finitePauliMatrix_eq_qubitLocalTensor (P : σ → Option (Fin 3)) :
    finitePauliMatrix P = qubitLocalTensor fun s => boolPauliOption (P s) := rfl

theorem qubitLocalTensor_mul (M N : σ → Matrix Bool Bool ℂ) :
    qubitLocalTensor M * qubitLocalTensor N = qubitLocalTensor fun s => M s * N s := by
  ext x z
  rw [Matrix.mul_apply]
  simp only [qubitLocalTensor, Matrix.mul_apply]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
    (fun s c => M s (x s) c * N s c (z s)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm

theorem trace_qubitLocalTensor (M : σ → Matrix Bool Bool ℂ) :
    (qubitLocalTensor M).trace = ∏ s, (M s).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, qubitLocalTensor]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool)) (fun s b => M s b b),
    Fintype.piFinset_univ]

omit [DecidableEq σ] in
theorem conjTranspose_qubitLocalTensor (M : σ → Matrix Bool Bool ℂ) :
    (qubitLocalTensor M)ᴴ = qubitLocalTensor fun s => (M s)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, qubitLocalTensor]
  exact star_prod _ _

/-! ### The six single-qubit stabilizer states -/

/-- The eigenvalue sign selected by a stabilizer sample. -/
def stabilizerSign (b : Bool) : ℂ := if b then 1 else -1

/-- Density matrix of the stabilizer eigenstate selected by an axis and a sign. -/
def stabilizerDensity (u : Fin 3 × Bool) : Matrix Bool Bool ℂ :=
  (2 : ℂ)⁻¹ • ((1 : Matrix Bool Bool ℂ) + stabilizerSign u.2 • finiteQubitPauli u.1)

theorem stabilizerDensity_isHermitian (u : Fin 3 × Bool) : (stabilizerDensity u).IsHermitian := by
  obtain ⟨p, b⟩ := u
  rw [Matrix.IsHermitian]
  ext x y
  cases b <;> fin_cases p <;> fin_cases x <;> fin_cases y <;>
    norm_num [stabilizerDensity, stabilizerSign, finiteQubitPauli, Matrix.conjTranspose_apply,
      Matrix.one_apply]

theorem trace_stabilizerDensity (u : Fin 3 × Bool) : (stabilizerDensity u).trace = 1 := by
  obtain ⟨p, b⟩ := u
  cases b <;> fin_cases p <;>
    norm_num [stabilizerDensity, stabilizerSign, finiteQubitPauli, Matrix.trace,
      Fintype.sum_bool, Matrix.one_apply]

theorem stabilizerDensity_mul_self (u : Fin 3 × Bool) :
    stabilizerDensity u * stabilizerDensity u = stabilizerDensity u := by
  obtain ⟨p, b⟩ := u
  ext x y
  cases b <;> fin_cases p <;> fin_cases x <;> fin_cases y <;>
    norm_num [stabilizerDensity, stabilizerSign, finiteQubitPauli, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.one_apply, Complex.ext_iff]

/-- **The exact six-state single-qubit expectation.**  The density matrix of a stabilizer
eigenstate pairs with a Pauli label exactly as the combinatorial sample expectation. -/
theorem trace_stabilizerDensity_mul_boolPauliOption (u : Fin 3 × Bool) (q : Option (Fin 3)) :
    (stabilizerDensity u * boolPauliOption q).trace = ((stabilizerAxisExpectation u q : ℝ) : ℂ) := by
  obtain ⟨p, b⟩ := u
  rcases q with _ | r
  · cases b <;> fin_cases p <;>
      norm_num [stabilizerDensity, stabilizerSign, boolPauliOption, finiteQubitPauli,
        Matrix.trace, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
        stabilizerAxisExpectation]
  · cases b <;> fin_cases p <;> fin_cases r <;>
      norm_num [stabilizerDensity, stabilizerSign, boolPauliOption, finiteQubitPauli,
        Matrix.trace, Matrix.mul_apply, Fintype.sum_bool, Matrix.one_apply,
        stabilizerAxisExpectation] <;>
      (try (ring_nf; simp [Complex.I_sq]))

/-! ### Product stabilizer states -/

/-- Density matrix of a product stabilizer state. -/
def productStabilizerDensity (smpl : σ → Fin 3 × Bool) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  qubitLocalTensor fun s => stabilizerDensity (smpl s)

omit [DecidableEq σ] in
theorem productStabilizerDensity_isHermitian (smpl : σ → Fin 3 × Bool) :
    (productStabilizerDensity smpl).IsHermitian := by
  rw [productStabilizerDensity, Matrix.IsHermitian, conjTranspose_qubitLocalTensor]
  exact congrArg qubitLocalTensor (funext fun s => (stabilizerDensity_isHermitian (smpl s)))

theorem productStabilizerDensity_mul_self (smpl : σ → Fin 3 × Bool) :
    productStabilizerDensity smpl * productStabilizerDensity smpl
      = productStabilizerDensity smpl := by
  rw [productStabilizerDensity, qubitLocalTensor_mul]
  exact congrArg qubitLocalTensor (funext fun s => stabilizerDensity_mul_self (smpl s))

theorem trace_productStabilizerDensity (smpl : σ → Fin 3 × Bool) :
    (productStabilizerDensity smpl).trace = 1 := by
  rw [productStabilizerDensity, trace_qubitLocalTensor]
  refine Finset.prod_eq_one fun s _ => trace_stabilizerDensity (smpl s)

/-- **The product state expectation of a Pauli string factorizes over sites.** -/
theorem trace_productStabilizerDensity_mul_finitePauliMatrix
    (smpl : σ → Fin 3 × Bool) (Q : σ → Option (Fin 3)) :
    (productStabilizerDensity smpl * finitePauliMatrix Q).trace
      = ((∏ s, stabilizerAxisExpectation (smpl s) (Q s) : ℝ) : ℂ) := by
  rw [productStabilizerDensity, finitePauliMatrix_eq_qubitLocalTensor, qubitLocalTensor_mul,
    trace_qubitLocalTensor, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun s _ => trace_stabilizerDensity_mul_boolPauliOption _ _

/-! ### Averaging the squared expectation over product stabilizer samples -/

/-- The uniform product-stabilizer average of a product of local weights factorizes. -/
theorem average_prod_local (f : σ → Fin 3 × Bool → ℝ) :
    (∑ smpl : σ → Fin 3 × Bool, ∏ s, f s (smpl s)) / ((6 : ℝ) ^ Fintype.card σ)
      = ∏ s, (∑ u : Fin 3 × Bool, f s u) / 6 := by
  rw [Finset.prod_div_distrib, Finset.prod_const]
  congr 1
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 3 × Bool))) f,
    Fintype.piFinset_univ]

/-- The uniform product-stabilizer second moment of two Pauli strings is the exact twirl. -/
theorem average_prod_stabilizerAxisExpectation (Q R : σ → Option (Fin 3)) :
    (∑ smpl : σ → Fin 3 × Bool,
        (∏ s, stabilizerAxisExpectation (smpl s) (Q s)) *
          ∏ s, stabilizerAxisExpectation (smpl s) (R s)) / ((6 : ℝ) ^ Fintype.card σ)
      = productStabilizerPauliTwirl Q R := by
  have hcomb : ∀ smpl : σ → Fin 3 × Bool,
      (∏ s, stabilizerAxisExpectation (smpl s) (Q s)) *
          (∏ s, stabilizerAxisExpectation (smpl s) (R s))
        = ∏ s, (stabilizerAxisExpectation (smpl s) (Q s) *
            stabilizerAxisExpectation (smpl s) (R s)) :=
    fun smpl => Finset.prod_mul_distrib.symm
  simp only [hcomb]
  rw [average_prod_local
    (fun s u => stabilizerAxisExpectation u (Q s) * stabilizerAxisExpectation u (R s))]
  rfl


/-! ### The Pauli expansion of a conjugated Pauli string -/

/-- The inclusion of self-adjoint matrices, as a real-linear map. -/
def selfAdjointValLinear (κ : Type*) [Fintype κ] [DecidableEq κ] :
    selfAdjoint (Matrix κ κ ℂ) →ₗ[ℝ] Matrix κ κ ℂ where
  toFun X := (X : Matrix κ κ ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact Pauli-transfer matrix of conjugation by a fixed matrix. -/
def pauliConjugationTransfer
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    Matrix (σ → Option (Fin 3)) (σ → Option (Fin 3)) ℝ :=
  LinearMap.toMatrix (finitePauliSelfAdjointBasis σ) (finitePauliSelfAdjointBasis σ)
    (finiteMatrixSelfAdjointConjugationLinearMap U)

/-- **Conjugation of a Pauli string, expanded in the Pauli basis.** -/
theorem conjugation_finitePauliMatrix_expansion
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (P : σ → Option (Fin 3)) :
    star U * finitePauliMatrix P * U
      = ∑ Q : σ → Option (Fin 3), pauliConjugationTransfer U Q P • finitePauliMatrix Q := by
  have hexp := (finitePauliSelfAdjointBasis σ).sum_repr
    (finiteMatrixSelfAdjointConjugationLinearMap U (finitePauliSelfAdjointBasis σ P))
  have hval := congrArg (selfAdjointValLinear (FiniteQubitConfiguration σ)) hexp
  rw [map_sum] at hval
  have hleft : selfAdjointValLinear (FiniteQubitConfiguration σ)
      (finiteMatrixSelfAdjointConjugationLinearMap U (finitePauliSelfAdjointBasis σ P))
      = star U * finitePauliMatrix P * U := by
    rw [finitePauliSelfAdjointBasis_apply]
    rfl
  rw [hleft] at hval
  rw [← hval]
  have hT : ∀ Q : σ → Option (Fin 3), pauliConjugationTransfer U Q P
      = (finitePauliSelfAdjointBasis σ).repr
          (finiteMatrixSelfAdjointConjugationLinearMap U (finitePauliSelfAdjointBasis σ P)) Q :=
    fun Q => LinearMap.toMatrix_apply _ _ _ _ _
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [map_smul, hT Q]
  simp only [finitePauliSelfAdjointBasis_apply]
  rfl

/-! ### The literal score and its transfer expansion -/

/-- **The literal two-query protocol score.**  One trial samples a dictionary Pauli and a product
stabilizer state, applies the same unitary to two copies, measures the Pauli on each output and
multiplies the signs. -/
def literalTwoQueryScore {ι : Type*} [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) : ℝ :=
  (∑ i : ι,
      (∑ smpl : σ → Fin 3 × Bool,
        ((productStabilizerDensity smpl *
          (star U * finitePauliMatrix (label i) * U)).trace.re) ^ (2 : ℕ))
        / ((6 : ℝ) ^ Fintype.card σ))
    / (Fintype.card ι : ℝ)

theorem trace_productStabilizerDensity_mul_conjugation
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (P : σ → Option (Fin 3)) (smpl : σ → Fin 3 × Bool) :
    (productStabilizerDensity smpl * (star U * finitePauliMatrix P * U)).trace.re
      = ∑ Q : σ → Option (Fin 3),
          pauliConjugationTransfer U Q P * ∏ s, stabilizerAxisExpectation (smpl s) (Q s) := by
  have hcplx : (productStabilizerDensity smpl * (star U * finitePauliMatrix P * U)).trace
      = (((∑ Q : σ → Option (Fin 3),
            pauliConjugationTransfer U Q P *
              ∏ s, stabilizerAxisExpectation (smpl s) (Q s) : ℝ)) : ℂ) := by
    rw [conjugation_finitePauliMatrix_expansion, Finset.mul_sum, Matrix.trace_sum,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul,
      trace_productStabilizerDensity_mul_finitePauliMatrix, Complex.ofReal_mul,
      Complex.real_smul]
  rw [hcplx, Complex.ofReal_re]

/-- The uniform product-stabilizer average of the squared literal expectation is the exactly
twirled transfer signal of the whole Pauli basis. -/
theorem average_sq_trace_eq_sum_twirl
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (P : σ → Option (Fin 3)) :
    (∑ smpl : σ → Fin 3 × Bool,
        ((productStabilizerDensity smpl *
          (star U * finitePauliMatrix P * U)).trace.re) ^ (2 : ℕ))
        / ((6 : ℝ) ^ Fintype.card σ)
      = ∑ Q : σ → Option (Fin 3), ((1 : ℝ) / 3) ^ finitePauliWeight Q *
          (pauliConjugationTransfer U Q P) ^ (2 : ℕ) := by
  classical
  have hsq : ∀ smpl : σ → Fin 3 × Bool,
      ((productStabilizerDensity smpl *
          (star U * finitePauliMatrix P * U)).trace.re) ^ (2 : ℕ)
        = ∑ Q : σ → Option (Fin 3), ∑ R : σ → Option (Fin 3),
            (pauliConjugationTransfer U Q P * pauliConjugationTransfer U R P) *
              ((∏ s, stabilizerAxisExpectation (smpl s) (Q s)) *
                ∏ s, stabilizerAxisExpectation (smpl s) (R s)) := by
    intro smpl
    rw [trace_productStabilizerDensity_mul_conjugation, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun R _ => by ring
  simp only [hsq]
  rw [Finset.sum_comm, Finset.sum_div]
  have hstep : ∀ Q : σ → Option (Fin 3),
      (∑ smpl : σ → Fin 3 × Bool, ∑ R : σ → Option (Fin 3),
          (pauliConjugationTransfer U Q P * pauliConjugationTransfer U R P) *
            ((∏ s, stabilizerAxisExpectation (smpl s) (Q s)) *
              ∏ s, stabilizerAxisExpectation (smpl s) (R s)))
          / ((6 : ℝ) ^ Fintype.card σ)
        = ∑ R : σ → Option (Fin 3),
            (pauliConjugationTransfer U Q P * pauliConjugationTransfer U R P) *
              productStabilizerPauliTwirl Q R := by
    intro Q
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc, average_prod_stabilizerAxisExpectation]
  rw [Finset.sum_congr rfl fun Q _ => hstep Q]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [Finset.sum_eq_single Q]
  · rw [productStabilizerPauliTwirl_self]; ring
  · intro R _ hRQ
    rw [productStabilizerPauliTwirl_eq_zero_of_ne Q R (Ne.symm hRQ), mul_zero]
  · simp

/-! ### The literal score dominates the dictionary transfer signal -/

/-- **The physical score is at least the dictionary transfer signal.**  Both are the same
experiment; the literal score keeps every output Pauli, the transfer signal only those in the
dictionary, and all retained terms are nonnegative. -/
theorem productStabilizerTwoQueryProtocolSignal_le_literalTwoQueryScore
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    productStabilizerTwoQueryProtocolSignal (fun i : {P // p P} => i.1)
        (matrixCoordinateCompression p (pauliConjugationTransfer U))
      ≤ literalTwoQueryScore (fun i : {P // p P} => i.1) U := by
  classical
  rw [productStabilizerTwoQueryProtocolSignal_eq _ Subtype.val_injective,
    twoQueryProductStabilizerSignal, literalTwoQueryScore]
  have hcard : (0 : ℝ) ≤ (Fintype.card {P : σ → Option (Fin 3) // p P} : ℝ) := by positivity
  refine div_le_div_of_nonneg_right ?_ hcard
  refine Finset.sum_le_sum fun i _ => ?_
  rw [average_sq_trace_eq_sum_twirl]
  have hsub : ∑ j : {P : σ → Option (Fin 3) // p P},
        ((1 : ℝ) / 3) ^ finitePauliWeight j.1 *
          (matrixCoordinateCompression p (pauliConjugationTransfer U) j i) ^ (2 : ℕ)
      = ∑ Q ∈ Finset.univ.filter p,
          ((1 : ℝ) / 3) ^ finitePauliWeight Q * (pauliConjugationTransfer U Q i.1) ^ (2 : ℕ) := by
    have hsub2 := Finset.sum_subtype (p := p) (F := inferInstance) (Finset.univ.filter p)
      (fun x => by simp)
      (fun Q => ((1 : ℝ) / 3) ^ finitePauliWeight Q * (pauliConjugationTransfer U Q i.1) ^ (2 : ℕ))
    rw [hsub2]
    rfl
  rw [hsub]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Q _ _ => ?_
  positivity


/-! ### The literal traceless two-query separator -/

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

open NormedSpace

theorem finiteQTracelessPauliTransferMatrix_eq_compression
    (n q : ℕ)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (t : ℝ) :
    finiteQTracelessPauliTransferMatrix n q H t
      = matrixCoordinateCompression (IsFiniteQTracelessPauliLabel n q)
          (pauliConjugationTransfer
            (exp (t • ((-Complex.I) • (H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))))) := rfl

/-- **The boxed lower bound on the literal score.**  Every nonzero traceless Hamiltonian of Pauli
weight at most `q` keeps the actual randomized two-query product-stabilizer score at least
`3^{-q}/M_q`, at every real time. -/
theorem literalTwoQueryScore_ge_of_trace_eq_zero
    (n q : ℕ) [NeZero n] [NeZero q]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (htrace : Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = 0)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ) :
    ((1 : ℝ) / 3) ^ q / (Fintype.card (FiniteQTracelessPauliLabel n q) : ℝ) ≤
      literalTwoQueryScore (fun i : FiniteQTracelessPauliLabel n q => i.1)
        (exp (t • ((-Complex.I) • (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  refine le_trans
    (finiteQTracelessAutonomousTransferSignal_ge_of_trace_eq_zero n q H hH htrace hlocal t) ?_
  rw [finiteQTracelessPauliTransferMatrix_eq_compression]
  exact productStabilizerTwoQueryProtocolSignal_le_literalTwoQueryScore _ _

/-- **The boxed separation on the literal score.**  The same randomized two-query experiment
separates every nonzero traceless `q`-local autonomous evolution from the exact Haar benchmark
`1/(2^n+1)`, at every real time. -/
theorem haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero
    (n q : ℕ) [NeZero n] [NeZero q]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0)
    (htrace : Matrix.trace (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) = 0)
    (hlocal : HasPauliWeightAtMost (Fin n) q H)
    (t : ℝ)
    (hsep : Fintype.card (FiniteQTracelessPauliLabel n q) * 3 ^ q < 2 ^ n + 1) :
    1 / (((2 ^ n + 1 : ℕ) : ℝ)) <
      literalTwoQueryScore (fun i : FiniteQTracelessPauliLabel n q => i.1)
        (exp (t • ((-Complex.I) • (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  refine lt_of_lt_of_le
    (finiteQTracelessAutonomousTransferSignal_gt_haarBenchmark_of_trace_eq_zero
      n q H hH htrace hlocal t hsep) ?_
  rw [finiteQTracelessPauliTransferMatrix_eq_compression]
  exact productStabilizerTwoQueryProtocolSignal_le_literalTwoQueryScore _ _

end

end GaloisForLFunctions.HTGeometry
