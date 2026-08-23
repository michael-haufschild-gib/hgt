import GaloisForLFunctions.HTGeometry.TwoTimeAutonomousEndpointJacobianLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap
import GaloisForLFunctions.HTGeometry.CStarMatrixRealCoordinateLaw
import GaloisForLFunctions.HTGeometry.ConormNormDetLaw
import GaloisForLFunctions.HTGeometry.TwoTimeEndpointGlobalEncodingLaw

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- C*-algebra representation of operators on `n` qubits. -/
abbrev QubitCStarMatrix (n : ℕ) :=
  CStarMatrix (FiniteQubitConfiguration (Fin n))
    (FiniteQubitConfiguration (Fin n)) ℂ

/-- One row of a complex C*-matrix is recovered by applying it to a unit
coordinate vector. -/
theorem cstarMatrix_toCLM_single_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι ℂ) (i : ι) :
    ‖CStarMatrix.toCLM M
        ((WithCStarModule.equiv ℂ (ι → ℂ)).symm (Pi.single i 1))‖ ^ 2 =
      ∑ j, ‖M i j‖ ^ 2 := by
  rw [WithCStarModule.pi_norm_sq]
  simp only [CStarMatrix.toCLM_apply_single_apply, one_mul,
    RCLike.inner_apply]
  simp_rw [RCLike.mul_conj]
  have hcast :
      (∑ j, ((‖M i j‖ : ℝ) : ℂ) ^ 2) =
        ((∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
    norm_cast
  calc
    ‖∑ j, ((‖M i j‖ : ℝ) : ℂ) ^ 2‖ =
        ‖((∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ)‖ := congrArg norm hcast
    _ = ∑ j, ‖M i j‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg ‖M i j‖)]

/-- Hilbert--Schmidt mass is at most dimension times the C*-matrix operator
norm squared.  This is proved directly in the C*-matrix representation rather
than assuming an identification between two independently constructed norms. -/
theorem cstarMatrix_frobSq_le_card_mul_norm_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : CStarMatrix ι ι ℂ) :
    frobSq (CStarMatrix.ofMatrix.symm M) ≤
      (Fintype.card ι : ℝ) * ‖M‖ ^ 2 := by
  have hrow (i : ι) : (∑ j, ‖M i j‖ ^ 2) ≤ ‖M‖ ^ 2 := by
    let e : WithCStarModule ℂ (ι → ℂ) :=
      (WithCStarModule.equiv ℂ (ι → ℂ)).symm (Pi.single i 1)
    have he : ‖e‖ = 1 := by
      simpa [e] using WithCStarModule.norm_single (A := ℂ) i (1 : ℂ)
    have happly := (CStarMatrix.toCLM M).le_opNorm e
    rw [he, mul_one, ← CStarMatrix.norm_def] at happly
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 happly
    have heq : ‖CStarMatrix.toCLM M e‖ ^ 2 = ∑ j, ‖M i j‖ ^ 2 := by
      dsimp only [e]
      exact cstarMatrix_toCLM_single_norm_sq M i
    rw [heq] at hsquare
    exact hsquare
  unfold frobSq
  calc
    (∑ i, ∑ j, ‖(CStarMatrix.ofMatrix.symm M) i j‖ ^ 2) ≤
        ∑ _i : ι, ‖M‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => by simpa using hrow i
    _ = (Fintype.card ι : ℝ) * ‖M‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The ordinary two-local Pauli Hamiltonian, represented in its C*-algebra. -/
def realTwoLocalPauliCStarHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) : QubitCStarMatrix n :=
  CStarMatrix.ofMatrix (realActivePauliHamiltonian x)

/-- Ordinary two-local Pauli Hamiltonian dictionary as a continuous real-linear map. -/
def realTwoLocalPauliCStarHamiltonianCLM (n : ℕ) :
    TwoLocalPauliCoefficientSpace n →L[ℝ] QubitCStarMatrix n :=
  LinearMap.toContinuousLinearMap
    { toFun := realTwoLocalPauliCStarHamiltonian
      map_add' := by
        intro x y
        change CStarMatrix.ofMatrix (realActivePauliHamiltonian (x + y)) = _
        rw [realActivePauliHamiltonian_add]
        rfl
      map_smul' := by
        intro r x
        change CStarMatrix.ofMatrix (realActivePauliHamiltonian (r • x)) =
          r • CStarMatrix.ofMatrix (realActivePauliHamiltonian x)
        rw [realActivePauliHamiltonian_smul]
        ext i j
        simp [smul_eq_mul] }

@[simp] theorem realTwoLocalPauliCStarHamiltonianCLM_apply
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    realTwoLocalPauliCStarHamiltonianCLM n x =
      realTwoLocalPauliCStarHamiltonian x := rfl

/-- Schrödinger generator dictionary `x ↦ -i H(x)`. -/
def realTwoLocalPauliCStarGeneratorCLM (n : ℕ) :
    TwoLocalPauliCoefficientSpace n →L[ℝ] QubitCStarMatrix n :=
  (ContinuousLinearMap.lsmul ℝ ℂ (-Complex.I)).comp
    (realTwoLocalPauliCStarHamiltonianCLM n)

@[simp] theorem realTwoLocalPauliCStarGeneratorCLM_apply
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    realTwoLocalPauliCStarGeneratorCLM n x =
      (-Complex.I) • realTwoLocalPauliCStarHamiltonian x := rfl

theorem norm_realTwoLocalPauliCStarGeneratorCLM_apply
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    ‖realTwoLocalPauliCStarGeneratorCLM n x‖ =
      ‖realTwoLocalPauliCStarHamiltonian x‖ := by
  rw [realTwoLocalPauliCStarGeneratorCLM_apply, norm_smul]
  norm_num

/-- Every real two-local Pauli Hamiltonian is self-adjoint in the C*-matrix
representation. -/
theorem isSelfAdjoint_realTwoLocalPauliCStarHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    IsSelfAdjoint (realTwoLocalPauliCStarHamiltonian x) := by
  rw [IsSelfAdjoint]
  change CStarMatrix.ofMatrix (star (realActivePauliHamiltonian x)) =
    CStarMatrix.ofMatrix (realActivePauliHamiltonian x)
  rw [(isSelfAdjoint_realActivePauliHamiltonian x).star_eq]

/-- Every ordinary two-local Pauli direction is a skew-adjoint generator. -/
theorem realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    realTwoLocalPauliCStarGeneratorCLM n x ∈ skewAdjoint (QubitCStarMatrix n) := by
  rw [realTwoLocalPauliCStarGeneratorCLM_apply, skewAdjoint.mem_iff,
    star_smul,
    (isSelfAdjoint_realTwoLocalPauliCStarHamiltonian x).star_eq]
  simp

/-- Exact coefficient conorm: C*-operator norm of a full active Pauli
Hamiltonian dominates Euclidean coefficient norm. -/
theorem norm_le_realTwoLocalPauliCStarHamiltonian
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    ‖x‖ ≤ ‖realTwoLocalPauliCStarHamiltonian x‖ := by
  have hdim :
      (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) = (2 : ℝ) ^ n := by
    simp
  have hsq := cstarMatrix_frobSq_le_card_mul_norm_sq
    (realTwoLocalPauliCStarHamiltonian x)
  change frobSq (realActivePauliHamiltonian x) ≤
    (Fintype.card (FiniteQubitConfiguration (Fin n)) : ℝ) *
      ‖realTwoLocalPauliCStarHamiltonian x‖ ^ 2 at hsq
  rw [frobSq_realActivePauliHamiltonian, hdim] at hsq
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsq' : ‖x‖ ^ 2 ≤ ‖realTwoLocalPauliCStarHamiltonian x‖ ^ 2 :=
    le_of_mul_le_mul_left hsq hpos
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq'

/-- The skew-generator dictionary retains exact conorm one. -/
theorem norm_le_realTwoLocalPauliCStarGeneratorCLM
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    ‖x‖ ≤ ‖realTwoLocalPauliCStarGeneratorCLM n x‖ := by
  rw [realTwoLocalPauliCStarGeneratorCLM_apply, norm_smul]
  simpa using norm_le_realTwoLocalPauliCStarHamiltonian x

/-- Every C*-represented Pauli word has operator norm one. -/
theorem norm_cstarMatrix_finitePauliMatrix
    {n : ℕ} (P : Fin n → Option (Fin 3)) :
    ‖CStarMatrix.ofMatrix (finitePauliMatrix P)‖ = 1 := by
  have hstar : star (CStarMatrix.ofMatrix (finitePauliMatrix P)) =
      CStarMatrix.ofMatrix (finitePauliMatrix P) := by
    change CStarMatrix.ofMatrix (star (finitePauliMatrix P)) = _
    rw [Matrix.star_eq_conjTranspose, finitePauliMatrix_isHermitian]
  have hu : CStarMatrix.ofMatrix (finitePauliMatrix P) ∈
      unitary (QubitCStarMatrix n) := by
    rw [Unitary.mem_iff, hstar]
    constructor <;> change CStarMatrix.ofMatrix _ = CStarMatrix.ofMatrix 1 <;>
      exact congrArg CStarMatrix.ofMatrix (finitePauliMatrix_mul_self P)
  exact CStarRing.norm_of_mem_unitary hu

/-- C*-operator norm of the ordinary active Hamiltonian is at most coefficient
`ℓ¹` norm. -/
theorem norm_realTwoLocalPauliCStarHamiltonian_le_sum
    {n : ℕ} (x : TwoLocalPauliCoefficientSpace n) :
    ‖realTwoLocalPauliCStarHamiltonian x‖ ≤
      ∑ Q : PauliTracelessLabel n 2, |WithLp.ofLp x Q| := by
  change ‖∑ Q : PauliTracelessLabel n 2,
      (((WithLp.ofLp x Q : ℝ) : ℂ) •
        CStarMatrix.ofMatrix (finitePauliMatrix Q.1))‖ ≤ _
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Q _ => ?_)
  rw [norm_smul, norm_cstarMatrix_finitePauliMatrix, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- Same-draw box gives polynomial energy control in the C*-representation. -/
theorem norm_realTwoLocalPauliCStarHamiltonian_le_eighteen_mul_cube_of_mem_box
    {n : ℕ} (hn : 1 ≤ n) {x : TwoLocalPauliCoefficientSpace n}
    (hx : x ∈ twoLocalPauliCoefficientBox n) :
    ‖realTwoLocalPauliCStarHamiltonian x‖ ≤ 18 * (n : ℝ) ^ 3 := by
  have hcard : Fintype.card (PauliTracelessLabel n 2) ≤ 18 * n ^ 2 := by
    rw [card_pauliTracelessLabel]
    simpa using Quantum.nonidentityPauliWeightCount_le n 2 hn
  calc
    ‖realTwoLocalPauliCStarHamiltonian x‖ ≤
        ∑ Q : PauliTracelessLabel n 2, |WithLp.ofLp x Q| :=
      norm_realTwoLocalPauliCStarHamiltonian_le_sum x
    _ ≤ ∑ _Q : PauliTracelessLabel n 2, (n : ℝ) :=
      Finset.sum_le_sum fun Q _ => hx Q
    _ = (Fintype.card (PauliTracelessLabel n 2) : ℝ) * (n : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((18 * n ^ 2 : ℕ) : ℝ) * (n : ℝ) := by gcongr
    _ = 18 * (n : ℝ) ^ 3 := by
      push_cast
      ring

/-- The paired endpoint map has the stated Fréchet Jacobian for every ordinary
fixed two-local Pauli draw. -/
theorem hasFDerivAt_realTwoLocalPauli_twoTimeEndpoint_zero
    {n : ℕ} (z : TwoLocalPauliCoefficientSpace n)
    {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) :
    HasFDerivAt (𝕜 := ℝ)
      (twoTimeAutonomousLinearGeneratorEndpoint
        (realTwoLocalPauliCStarGeneratorCLM n z)
        (realTwoLocalPauliCStarGeneratorCLM n) t δ)
      (twoTimeAutonomousLinearGeneratorEndpointJacobian
        (realTwoLocalPauliCStarGeneratorCLM n z)
        (realTwoLocalPauliCStarGeneratorCLM n) t δ) 0 := by
  apply hasFDerivAt_twoTimeAutonomousLinearGeneratorEndpoint_zero
  · exact realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint z
  · exact realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint
  · exact ht
  · exact hδ

/-- Two short-separated endpoints of every ordinary fixed two-local Pauli
Hamiltonian have a uniform all-direction Jacobian floor at every base time. -/
theorem realTwoLocalPauli_twoTimeEndpointJacobian_lower
    {n : ℕ} (z : TwoLocalPauliCoefficientSpace n) (t : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * ‖realTwoLocalPauliCStarHamiltonian z‖ ≤ 1)
    (v : TwoLocalPauliCoefficientSpace n) :
    δ / 4 * ‖v‖ ≤
      ‖twoTimeAutonomousLinearGeneratorEndpointJacobian
        (realTwoLocalPauliCStarGeneratorCLM n z)
        (realTwoLocalPauliCStarGeneratorCLM n) t δ v‖ := by
  have hsmall' :
      4 * δ * ‖realTwoLocalPauliCStarGeneratorCLM n z‖ ≤ 1 := by
    rw [norm_realTwoLocalPauliCStarGeneratorCLM_apply]
    exact hsmall
  have hG : ∀ w : TwoLocalPauliCoefficientSpace n,
      (1 : ℝ) * ‖w‖ ≤ ‖realTwoLocalPauliCStarGeneratorCLM n w‖ := by
    intro w
    rw [one_mul]
    exact norm_le_realTwoLocalPauliCStarGeneratorCLM w
  have h := twoTimeAutonomousLinearGeneratorEndpointJacobian_lower
    (A := QubitCStarMatrix n) (E := TwoLocalPauliCoefficientSpace n)
    (realTwoLocalPauliCStarGeneratorCLM n z)
    (realTwoLocalPauliCStarGeneratorCLM n)
    (realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint z)
    hG t hδ hsmall' v
  convert h using 1 <;> ring

/-- System-size short separation guaranteed by the same-draw Gaussian box.
The floor is uniform through all laboratory base times. -/
theorem realTwoLocalPauli_twoTimeEndpointJacobian_lower_of_mem_box
    {n : ℕ} (hn : 1 ≤ n) {z : TwoLocalPauliCoefficientSpace n}
    (hz : z ∈ twoLocalPauliCoefficientBox n) (t : ℝ)
    (v : TwoLocalPauliCoefficientSpace n) :
    (1 / (72 * (n : ℝ) ^ 3)) / 4 * ‖v‖ ≤
      ‖twoTimeAutonomousLinearGeneratorEndpointJacobian
        (realTwoLocalPauliCStarGeneratorCLM n z)
        (realTwoLocalPauliCStarGeneratorCLM n) t
        (1 / (72 * (n : ℝ) ^ 3)) v‖ := by
  apply realTwoLocalPauli_twoTimeEndpointJacobian_lower z t
  · positivity
  · have hnorm :=
      norm_realTwoLocalPauliCStarHamiltonian_le_eighteen_mul_cube_of_mem_box hn hz
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      4 * (1 / (72 * (n : ℝ) ^ 3)) *
          ‖realTwoLocalPauliCStarHamiltonian z‖ ≤
        4 * (1 / (72 * (n : ℝ) ^ 3)) * (18 * (n : ℝ) ^ 3) := by
          gcongr
      _ = 1 := by
        field_simp
        norm_num

/-- Real Euclidean coordinates of the paired endpoint Jacobian.  This is the
finite-dimensional differential to which volume/coarea estimates apply. -/
def realTwoLocalPauliTwoTimeEndpointRealJacobian
    {n : ℕ} (z : TwoLocalPauliCoefficientSpace n) (t δ : ℝ) :
    TwoLocalPauliCoefficientSpace n →L[ℝ]
      EuclideanSpace ℝ
        (Bool × MatrixRealCoordinateIndex (FiniteQubitConfiguration (Fin n))) :=
  (twoTimeCStarMatrixRealCoordinatesCLM
      (FiniteQubitConfiguration (Fin n))).comp
    (twoTimeAutonomousLinearGeneratorEndpointJacobian
      (realTwoLocalPauliCStarGeneratorCLM n z)
      (realTwoLocalPauliCStarGeneratorCLM n) t δ)

/-- The system-size paired endpoint Jacobian remains bounded below after
passing to complete real matrix coordinates.  No dimension-dependent norm
loss is introduced by realification. -/
theorem realTwoLocalPauliTwoTimeEndpointRealJacobian_lower_of_mem_box
    {n : ℕ} (hn : 1 ≤ n) {z : TwoLocalPauliCoefficientSpace n}
    (hz : z ∈ twoLocalPauliCoefficientBox n) (t : ℝ)
    (v : TwoLocalPauliCoefficientSpace n) :
    (1 / (72 * (n : ℝ) ^ 3)) / 4 * ‖v‖ ≤
      ‖realTwoLocalPauliTwoTimeEndpointRealJacobian z t
        (1 / (72 * (n : ℝ) ^ 3)) v‖ := by
  refine (realTwoLocalPauli_twoTimeEndpointJacobian_lower_of_mem_box
    hn hz t v).trans ?_
  exact norm_le_twoTimeCStarMatrixRealCoordinates
    (twoTimeAutonomousLinearGeneratorEndpointJacobian
      (realTwoLocalPauliCStarGeneratorCLM n z)
      (realTwoLocalPauliCStarGeneratorCLM n) t
      (1 / (72 * (n : ℝ) ^ 3)) v)

/-- Coarea-ready growing-dimensional Jacobian floor.  For every draw in the
ordinary coefficient box and every laboratory base time, the exact volume
Jacobian of the paired endpoint observer is at least the one-direction floor
raised to the full number of active Pauli coefficients. -/
theorem realTwoLocalPauliTwoTimeEndpointRealJacobian_normDet_lower_of_mem_box
    {n : ℕ} (hn : 1 ≤ n) {z : TwoLocalPauliCoefficientSpace n}
    (hz : z ∈ twoLocalPauliCoefficientBox n) (t : ℝ) :
    ((1 / (72 * (n : ℝ) ^ 3)) / 4) ^
        Fintype.card (PauliTracelessLabel n 2) ≤
      (realTwoLocalPauliTwoTimeEndpointRealJacobian z t
        (1 / (72 * (n : ℝ) ^ 3))).toLinearMap.normDet := by
  apply linearMap_normDet_lower_of_norm_lower
      (m := Fintype.card (PauliTracelessLabel n 2))
  · simp [TwoLocalPauliCoefficientSpace]
  · positivity
  · exact realTwoLocalPauliTwoTimeEndpointRealJacobian_lower_of_mem_box
      hn hz t

/-- Paired endpoints of one ordinary two-local Pauli draw. -/
def realTwoLocalPauliTwoTimeEndpoint
    {n : ℕ} (z : TwoLocalPauliCoefficientSpace n) (t δ : ℝ) :
    QubitCStarMatrix n × QubitCStarMatrix n :=
  twoTimeAutonomousEndpoint (realTwoLocalPauliCStarGeneratorCLM n z) t δ

/-- **Global same-time no-folding law.**  On the ordinary system-size Pauli
box, two endpoints separated by `1/(144 n³)` distinguish every pair of draws
at every laboratory base time.  Hence every occupied endpoint-pair fibre has
multiplicity at most one; no minimum spectral gap or genericity is required. -/
theorem realTwoLocalPauliTwoTimeEndpoint_lower_of_mem_box
    {n : ℕ} (hn : 1 ≤ n)
    {x y : TwoLocalPauliCoefficientSpace n}
    (hx : x ∈ twoLocalPauliCoefficientBox n)
    (hy : y ∈ twoLocalPauliCoefficientBox n) (t : ℝ) :
    (1 / (144 * (n : ℝ) ^ 3)) / 8 * ‖y - x‖ ≤
      ‖realTwoLocalPauliTwoTimeEndpoint y t
          (1 / (144 * (n : ℝ) ^ 3)) -
        realTwoLocalPauliTwoTimeEndpoint x t
          (1 / (144 * (n : ℝ) ^ 3))‖ := by
  let δ : ℝ := 1 / (144 * (n : ℝ) ^ 3)
  let G := realTwoLocalPauliCStarGeneratorCLM n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := by positivity
  have hGx : ‖G x‖ ≤ 18 * (n : ℝ) ^ 3 := by
    change ‖realTwoLocalPauliCStarGeneratorCLM n x‖ ≤ _
    rw [norm_realTwoLocalPauliCStarGeneratorCLM_apply]
    exact norm_realTwoLocalPauliCStarHamiltonian_le_eighteen_mul_cube_of_mem_box
      hn hx
  have hGy : ‖G y‖ ≤ 18 * (n : ℝ) ^ 3 := by
    change ‖realTwoLocalPauliCStarGeneratorCLM n y‖ ≤ _
    rw [norm_realTwoLocalPauliCStarGeneratorCLM_apply]
    exact norm_realTwoLocalPauliCStarHamiltonian_le_eighteen_mul_cube_of_mem_box
      hn hy
  have hsmallx : 4 * δ * ‖G x‖ ≤ 1 := by
    calc
      4 * δ * ‖G x‖ ≤ 4 * δ * (18 * (n : ℝ) ^ 3) := by gcongr
      _ ≤ 1 := by
        dsimp only [δ]
        field_simp
        norm_num
  have hdiff : ‖G y - G x‖ ≤ 36 * (n : ℝ) ^ 3 := by
    calc
      ‖G y - G x‖ ≤ ‖G y‖ + ‖G x‖ := norm_sub_le _ _
      _ ≤ 18 * (n : ℝ) ^ 3 + 18 * (n : ℝ) ^ 3 :=
        add_le_add hGy hGx
      _ = 36 * (n : ℝ) ^ 3 := by ring
  have hsmallxy : δ * ‖G y - G x‖ ≤ 1 / 4 := by
    calc
      δ * ‖G y - G x‖ ≤ δ * (36 * (n : ℝ) ^ 3) := by gcongr
      _ = 1 / 4 := by
        dsimp only [δ]
        field_simp
        norm_num
  have hglobal := twoTimeAutonomousEndpoint_lower_of_skewAdjoint
    (G x) (G y)
    (realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint x)
    (realTwoLocalPauliCStarGeneratorCLM_mem_skewAdjoint y)
    t hδ hsmallx hsmallxy
  have hconorm : ‖y - x‖ ≤ ‖G y - G x‖ := by
    rw [← G.map_sub]
    exact norm_le_realTwoLocalPauliCStarGeneratorCLM (y - x)
  change δ / 8 * ‖y - x‖ ≤
    ‖twoTimeAutonomousEndpoint (G y) t δ -
      twoTimeAutonomousEndpoint (G x) t δ‖
  refine (mul_le_mul_of_nonneg_left hconorm (by positivity)).trans ?_
  exact hglobal

/-- Every occupied short two-time endpoint fibre in the ordinary Pauli box is
a singleton.  Thus incidence counting loses no unrecorded sheet multiplicity. -/
theorem realTwoLocalPauliTwoTimeEndpoint_injOn_box
    {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Set.InjOn
      (fun z : TwoLocalPauliCoefficientSpace n =>
        realTwoLocalPauliTwoTimeEndpoint z t
          (1 / (144 * (n : ℝ) ^ 3)))
      (twoLocalPauliCoefficientBox n) := by
  intro x hx y hy hxy
  have h := realTwoLocalPauliTwoTimeEndpoint_lower_of_mem_box
    hn hx hy t
  change realTwoLocalPauliTwoTimeEndpoint x t
      (1 / (144 * (n : ℝ) ^ 3)) =
    realTwoLocalPauliTwoTimeEndpoint y t
      (1 / (144 * (n : ℝ) ^ 3)) at hxy
  rw [← hxy, sub_self, norm_zero] at h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale : 0 < (1 / (144 * (n : ℝ) ^ 3)) / 8 := by positivity
  have hproduct : (1 / (144 * (n : ℝ) ^ 3)) / 8 * ‖y - x‖ = 0 :=
    le_antisymm h (mul_nonneg hscale.le (norm_nonneg _))
  have hnorm : ‖y - x‖ = 0 := by
    rcases mul_eq_zero.mp hproduct with hscalezero | hnorm
    · exact (ne_of_gt hscale hscalezero).elim
    · exact hnorm
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

end

end GaloisForLFunctions.HTGeometry
