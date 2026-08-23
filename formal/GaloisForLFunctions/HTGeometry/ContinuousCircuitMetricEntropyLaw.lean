import GaloisForLFunctions.HTGeometry.ParameterCoverageBarrier
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound
import GaloisForLFunctions.HTGeometry.CentralizerBudgetSplit
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitArchitecture
import GaloisForLFunctions.HTGeometry.KroneckerAmplification
import GaloisForLFunctions.HTGeometry.HaferkampTerminalPauliCoordinate
import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness

/-!
# Quantitative metric entropy of continuous two-qubit circuits

Ambient real matrix coordinates give an explicit operator-norm net for `SU(4)`.
Dimension-free lift stability and product telescoping promote it to every
fixed circuit architecture and then to the complete architecture union.
-/

open Matrix Metric Set
open scoped Matrix Matrix.Norms.L2Operator Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Operator norm is bounded by Hilbert--Schmidt norm. -/
theorem l2_opNorm_le_hsNorm (A : Matrix d d ℂ) : ‖A‖ ≤ hsNorm A := by
  rw [Matrix.l2_opNorm_def]
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) A).opNorm_le_bound (hsNorm_nonneg A)
  intro x
  have hcoord (i : d) :
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) A x).ofLp i‖ ≤
        ‖(EuclideanSpace.equiv d ℂ).symm (fun j => star (A i j))‖ * ‖x‖ := by
    have hinner :
        @inner ℂ (EuclideanSpace ℂ d) inferInstance
          ((EuclideanSpace.equiv d ℂ).symm (fun j => star (A i j))) x =
            (Matrix.toEuclideanCLM (𝕜 := ℂ) A x).ofLp i := by
      rw [Matrix.ofLp_toEuclideanCLM]
      simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]
    rw [← hinner]
    exact norm_inner_le_norm _ _
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A x‖ ^ 2 ≤
      (hsNorm A * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), mul_pow,
      hsNorm_sq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := hcoord i
    have hrow :
        ‖(EuclideanSpace.equiv d ℂ).symm (fun j => star (A i j))‖ ^ 2 =
          ∑ j, ‖A i j‖ ^ 2 := by
      rw [norm_sq_euclideanOfFun]
      exact Finset.sum_congr rfl fun j _ => by rw [norm_star]
    calc
      ‖((Matrix.toEuclideanCLM (𝕜 := ℂ) A x).ofLp i)‖ ^ 2 ≤
          (‖(EuclideanSpace.equiv d ℂ).symm
            (fun j => star (A i j))‖ * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = ‖(EuclideanSpace.equiv d ℂ).symm
            (fun j => star (A i j))‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ = (∑ j, ‖A i j‖ ^ 2) * ‖x‖ ^ 2 := by rw [hrow]
  have hsqrt := Real.sqrt_le_sqrt hsq
  simpa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg (hsNorm_nonneg A) (norm_nonneg x))] using hsqrt

abbrev TwoQubitRealCoordinateIndex :=
  (((Bool × Bool) × (Bool × Bool)) × Bool)

/-- The 32 real entry coordinates of a complex two-qubit matrix. -/
def twoQubitMatrixRealCoordinates
  (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    EuclideanSpace ℝ TwoQubitRealCoordinateIndex :=
  (EuclideanSpace.equiv TwoQubitRealCoordinateIndex ℝ).symm fun p =>
    let ij : (Bool × Bool) × (Bool × Bool) := p.1
    if p.2 then (A ij.1 ij.2).im else (A ij.1 ij.2).re

@[simp] theorem twoQubitMatrixRealCoordinates_apply
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (p : TwoQubitRealCoordinateIndex) :
    (twoQubitMatrixRealCoordinates A).ofLp p =
      if p.2 then (A p.1.1 p.1.2).im else (A p.1.1 p.1.2).re := rfl

/-- The real entry encoding is an isometry for Hilbert--Schmidt norm. -/
theorem norm_twoQubitMatrixRealCoordinates
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    ‖twoQubitMatrixRealCoordinates A‖ = hsNorm A := by
  refine (sq_eq_sq₀ (norm_nonneg _) (hsNorm_nonneg A)).mp ?_
  change ‖twoQubitMatrixRealCoordinates A‖ ^ 2 = ‖matVec A‖ ^ 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  calc
    ∑ p : TwoQubitRealCoordinateIndex,
        ‖(twoQubitMatrixRealCoordinates A).ofLp p‖ ^ 2 =
        ∑ ij : (Bool × Bool) × (Bool × Bool),
          ((A ij.1 ij.2).re ^ 2 + (A ij.1 ij.2).im ^ 2) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Fintype.sum_bool]
      simp [Real.norm_eq_abs, sq_abs, add_comm]
    _ = ∑ ij : (Bool × Bool) × (Bool × Bool), ‖A ij.1 ij.2‖ ^ 2 := by
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    _ = ∑ p : (Bool × Bool) × (Bool × Bool),
        ‖((EuclideanSpace.equiv ((Bool × Bool) × (Bool × Bool)) ℂ).symm
          (fun p => A p.1 p.2)).ofLp p‖ ^ 2 := by rfl

/-- The entry encoding turns matrix differences into Euclidean differences. -/
theorem twoQubitMatrixRealCoordinates_sub
    (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    twoQubitMatrixRealCoordinates (A - B) =
      twoQubitMatrixRealCoordinates A - twoQubitMatrixRealCoordinates B := by
  apply (EuclideanSpace.equiv TwoQubitRealCoordinateIndex ℝ).injective
  ext p
  by_cases hp : p.2
  · simp [twoQubitMatrixRealCoordinates, hp]
  · simp [twoQubitMatrixRealCoordinates, hp]

/-- Real coordinates control operator distance with Lipschitz constant one. -/
theorem twoQubit_operatorDist_le_coordinateDist
    (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    dist A B ≤ dist (twoQubitMatrixRealCoordinates A)
      (twoQubitMatrixRealCoordinates B) := by
  rw [dist_eq_norm, dist_eq_norm, ← twoQubitMatrixRealCoordinates_sub,
    norm_twoQubitMatrixRealCoordinates]
  exact l2_opNorm_le_hsNorm _

/-- Reindex the 32 real entry coordinates to a literal `Fin 32` Euclidean space. -/
def twoQubitMatrixFinCoordinates
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    EuclideanSpace ℝ (Fin (Fintype.card TwoQubitRealCoordinateIndex)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fintype.equivFin TwoQubitRealCoordinateIndex)
      (twoQubitMatrixRealCoordinates A)

theorem norm_twoQubitMatrixFinCoordinates
    (A : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    ‖twoQubitMatrixFinCoordinates A‖ = hsNorm A := by
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fintype.equivFin TwoQubitRealCoordinateIndex)).norm_map
        (twoQubitMatrixRealCoordinates A) |>.trans
      (norm_twoQubitMatrixRealCoordinates A)

theorem twoQubit_operatorDist_le_finCoordinateDist
    (A B : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    dist A B ≤ dist (twoQubitMatrixFinCoordinates A)
      (twoQubitMatrixFinCoordinates B) := by
  change dist A B ≤ dist
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fintype.equivFin TwoQubitRealCoordinateIndex))
        (twoQubitMatrixRealCoordinates A))
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (Fintype.equivFin TwoQubitRealCoordinateIndex))
        (twoQubitMatrixRealCoordinates B))
  rw [(LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fintype.equivFin TwoQubitRealCoordinateIndex)).dist_map]
  exact twoQubit_operatorDist_le_coordinateDist A B

/-- Two-qubit unitaries have Hilbert--Schmidt norm two. -/
theorem hsNorm_specialUnitary_boolTwoQubit
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    hsNorm (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = 2 := by
  have hsq : hsNorm (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) ^ 2 = 4 := by
    rw [hsNorm_sq]
    have hrow (i : Bool × Bool) :
        ‖(EuclideanSpace.equiv (Bool × Bool) ℂ).symm
            (fun j => (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j)‖ = 1 := by
      have h := congrArg (fun M : Matrix (Bool × Bool) (Bool × Bool) ℂ => M i i)
        (Matrix.mem_unitaryGroup_iff.mp
          (Matrix.specialUnitaryGroup_le_unitaryGroup U.2))
      have h' : ∑ j, (Complex.normSq
          ((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j) : ℂ) = 1 := by
        simpa only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
          Complex.mul_conj, Matrix.one_apply_eq] using h
      have hnormsq :
          ‖(EuclideanSpace.equiv (Bool × Bool) ℂ).symm
              (fun j => (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j)‖ ^ 2 = 1 := by
        rw [norm_sq_euclideanOfFun]
        calc
          ∑ j, ‖(U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j‖ ^ 2 =
              ∑ j, Complex.normSq
                ((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j) := by
            exact Finset.sum_congr rfl fun j _ => Complex.sq_norm _
          _ = 1 := by exact_mod_cast h'
      nlinarith [norm_nonneg ((EuclideanSpace.equiv (Bool × Bool) ℂ).symm
        (fun j => (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) i j))]
    simp_rw [← norm_sq_euclideanOfFun, hrow]
    norm_num
  nlinarith [hsNorm_nonneg (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)]

/-- Every continuous two-qubit gate set admits a quantitative operator-norm net. -/
theorem exists_specialUnitary_boolTwoQubit_operatorNet_card_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ net : Finset (Matrix.specialUnitaryGroup (Bool × Bool) ℂ),
      (∀ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ, ∃ V ∈ net,
        dist (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) ≤ ε) ∧
      (net.card : ℝ) ≤ (1 + 4 / ε) ^ 32 := by
  classical
  let K : Set (EuclideanSpace ℝ
      (Fin (Fintype.card TwoQubitRealCoordinateIndex))) :=
    (fun U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ =>
      twoQubitMatrixFinCoordinates
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) '' Set.univ
  have hK : K ⊆ closedBall 0 2 := by
    rintro x ⟨U, -, rfl⟩
    rw [mem_closedBall, dist_zero_right, norm_twoQubitMatrixFinCoordinates,
      hsNorm_specialUnitary_boolTwoQubit]
  obtain ⟨T, hTK, hTcard, hTnet⟩ :=
    exists_separated_net
      (m := Fintype.card TwoQubitRealCoordinateIndex) (by simp) hε
        (by norm_num) K hK
  let gateOf : {x // x ∈ T} →
      Matrix.specialUnitaryGroup (Bool × Bool) ℂ := fun x =>
    Classical.choose (show ∃ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
        twoQubitMatrixFinCoordinates
          (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = x.1 by
      rcases hTK x.2 with ⟨U, -, hU⟩
      exact ⟨U, hU⟩)
  let net := T.attach.image gateOf
  refine ⟨net, ?_, ?_⟩
  · intro U
    obtain ⟨x, hxT, hUx⟩ := hTnet (twoQubitMatrixFinCoordinates U)
      ⟨U, Set.mem_univ U, rfl⟩
    let x' : {x // x ∈ T} := ⟨x, hxT⟩
    let V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ := gateOf x'
    have hVcoord : twoQubitMatrixFinCoordinates
        (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) = x := by
      exact Classical.choose_spec (show ∃ U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
          twoQubitMatrixFinCoordinates
            (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) = x'.1 by
        rcases hTK x'.2 with ⟨W, -, hW⟩
        exact ⟨W, hW⟩)
    refine ⟨V, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x', Finset.mem_attach T x', rfl⟩
    · exact (twoQubit_operatorDist_le_finCoordinateDist U V).trans
        (by simpa [hVcoord] using hUx.le)
  · refine le_trans (Nat.cast_le.mpr Finset.card_image_le) ?_
    rw [Finset.card_attach]
    have hpow : 0 < (ε / 2) ^
        Fintype.card TwoQubitRealCoordinateIndex := by positivity
    calc
      (T.card : ℝ) ≤
          (2 + ε / 2) ^ Fintype.card TwoQubitRealCoordinateIndex /
            (ε / 2) ^ Fintype.card TwoQubitRealCoordinateIndex := by
        rw [le_div_iff₀ hpow]
        exact hTcard
      _ = (1 + 4 / ε) ^ 32 := by
        norm_num only [Fintype.card_prod, Fintype.card_bool]
        rw [← div_pow]
        congr 1
        field_simp
        ring

/-- Reindexing a square matrix does not increase its operator norm. -/
theorem l2_opNorm_reindexAlgEquiv_le
    {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A : Matrix I I ℂ) :
    ‖Matrix.reindexAlgEquiv ℂ ℂ e A‖ ≤ ‖A‖ := by
  let V : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ J :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  rw [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def]
  change ‖(Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
      (Matrix.reindexAlgEquiv ℂ ℂ e A)‖ ≤
    ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖
  apply ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
    (Matrix.reindexAlgEquiv ℂ ℂ e A)).opNorm_le_bound (norm_nonneg _)
  intro y
  have hyrel :
      (Matrix.toEuclideanCLM (n := J) (𝕜 := ℂ))
          (Matrix.reindexAlgEquiv ℂ ℂ e A) y =
        V ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A (V.symm y)) := by
    ext j
    simp [V, Matrix.reindex_apply, Matrix.mulVec, Equiv.piCongrLeft']
    unfold dotProduct
    refine (Fintype.sum_equiv e _ _ fun i => ?_).symm
    simp
  rw [hyrel, V.norm_map]
  calc
    ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A (V.symm y)‖ ≤
        ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖ * ‖V.symm y‖ :=
      ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A).le_opNorm _
    _ = ‖(Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ)) A‖ * ‖y‖ := by
      rw [V.symm.norm_map]

/-- Lifting a two-qubit gate to any register pair is dimension-free
one-Lipschitz in operator norm. -/
theorem twoQubitLift_operatorDist_le
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U V : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    dist
        ((twoQubitLift a b hab U : Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ)
        ((twoQubitLift a b hab V : Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) ≤
      dist
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
        (V : Matrix (Bool × Bool) (Bool × Bool) ℂ) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff :
      ((twoQubitLift a b hab U : Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) -
        ((twoQubitLift a b hab V : Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) =
      Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab).symm
        (((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) -
          (V : Matrix (Bool × Bool) (Bool × Bool) ℂ)) ⊗ₖ
            (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
              ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)) := by
    change
      Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab).symm
          ((U : Matrix (Bool × Bool) (Bool × Bool) ℂ) ⊗ₖ
            (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
              ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)) -
        Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab).symm
          ((V : Matrix (Bool × Bool) (Bool × Bool) ℂ) ⊗ₖ
            (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
              ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)) = _
    rw [← map_sub]
    congr 1
    ext x y
    simp [sub_mul]
  rw [hdiff]
  exact (l2_opNorm_reindexAlgEquiv_le _ _).trans
    (l2_opNorm_kronecker_one_le _)

/-- Paired contraction words accumulate at most one error budget per gate. -/
theorem norm_listProd_sub_le_nsmul_of_forall₂
    {A : Type*} [NormedRing A] [NormOneClass A]
    {η : ℝ} (hη : 0 ≤ η) :
    ∀ {W Y : List A},
      List.Forall₂ (fun a b => ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖a - b‖ ≤ η) W Y →
      ‖W.prod - Y.prod‖ ≤ (W.length : ℝ) * η := by
  have hstrong : ∀ {W Y : List A},
      List.Forall₂ (fun a b => ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖a - b‖ ≤ η) W Y →
      ‖W.prod‖ ≤ 1 ∧ ‖Y.prod‖ ≤ 1 ∧
        ‖W.prod - Y.prod‖ ≤ (W.length : ℝ) * η := by
    intro W Y h
    induction h with
    | nil => simp
    | cons hxy htail ih =>
      rename_i x y W Y
      have hWprod : ‖x * W.prod‖ ≤ 1 := by
        exact (norm_mul_le _ _).trans (by
          nlinarith [hxy.1, ih.1, norm_nonneg x, norm_nonneg W.prod])
      have hYprod : ‖y * Y.prod‖ ≤ 1 := by
        exact (norm_mul_le _ _).trans (by
          nlinarith [hxy.2.1, ih.2.1, norm_nonneg y, norm_nonneg Y.prod])
      have hsplit : x * W.prod - y * Y.prod =
          x * (W.prod - Y.prod) + (x - y) * Y.prod := by
        noncomm_ring
      have h1 : ‖x * (W.prod - Y.prod)‖ ≤ ‖W.prod - Y.prod‖ := by
        exact (norm_mul_le _ _).trans (by
          nlinarith [hxy.1, norm_nonneg (W.prod - Y.prod)])
      have h2 : ‖(x - y) * Y.prod‖ ≤ η := by
        exact (norm_mul_le _ _).trans (by
          nlinarith [hxy.2.2, ih.2.1, norm_nonneg (x - y), norm_nonneg Y.prod])
      refine ⟨by simpa using hWprod, by simpa using hYprod, ?_⟩
      rw [List.prod_cons, List.prod_cons, hsplit]
      calc
          ‖x * (W.prod - Y.prod) + (x - y) * Y.prod‖ ≤
              ‖x * (W.prod - Y.prod)‖ + ‖(x - y) * Y.prod‖ := norm_add_le _ _
        _ ≤ ‖W.prod - Y.prod‖ + η := add_le_add h1 h2
        _ ≤ (W.length : ℝ) * η + η := by linarith [ih.2.2]
        _ = ((x :: W).length : ℝ) * η := by simp; ring
  intro W Y h
  exact (hstrong h).2.2

/-- A fixed `R`-gate continuous architecture is `R`-Lipschitz in the
maximum local operator error. -/
theorem TwoQubitArchitecture.contraction_operatorDist_le
    {n R : ℕ} (A : TwoQubitArchitecture n R) {η : ℝ} (hη : 0 ≤ η)
    (gates gates' : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ)
    (hgate : ∀ r, dist
      (gates r : Matrix (Bool × Bool) (Bool × Bool) ℂ)
      (gates' r : Matrix (Bool × Bool) (Bool × Bool) ℂ) ≤ η) :
    dist
        ((A.contraction gates : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
        ((A.contraction gates' : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤
      (R : ℝ) * η := by
  let W : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    (List.ofFn fun r =>
      ((A.gateLift r (gates r) : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).reverse
  let Y : List (Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :=
    (List.ofFn fun r =>
      ((A.gateLift r (gates' r) : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
        Matrix (Fin n → Bool) (Fin n → Bool) ℂ)).reverse
  have hrel0 : List.Forall₂
      (fun X Z : Matrix (Fin n → Bool) (Fin n → Bool) ℂ =>
        ‖X‖ ≤ 1 ∧ ‖Z‖ ≤ 1 ∧ ‖X - Z‖ ≤ η)
      (List.ofFn fun r =>
        ((A.gateLift r (gates r) : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ))
      (List.ofFn fun r =>
        ((A.gateLift r (gates' r) : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    rw [List.forall₂_iff_get]
    constructor
    · simp
    · intro i hi hi'
      simp only [List.length_ofFn] at hi hi'
      let r : Fin R := ⟨i, hi⟩
      simpa [r, dist_eq_norm, TwoQubitArchitecture.gateLift] using And.intro
        (le_of_eq (CStarRing.norm_coe_unitary (A.gateLift r (gates r))))
        (And.intro
          (le_of_eq (CStarRing.norm_coe_unitary (A.gateLift r (gates' r))))
          ((twoQubitLift_operatorDist_le (A.sites r).1 (A.sites r).2
              (A.distinct r) (gates r) (gates' r)).trans
            (hgate r)))
  have hrel : List.Forall₂
      (fun X Z : Matrix (Fin n → Bool) (Fin n → Bool) ℂ =>
        ‖X‖ ≤ 1 ∧ ‖Z‖ ≤ 1 ∧ ‖X - Z‖ ≤ η) W Y := by
    exact List.rel_reverse hrel0
  rw [dist_eq_norm]
  simpa [W, Y, TwoQubitArchitecture.contraction, Function.comp_def] using
    norm_listProd_sub_le_nsmul_of_forall₂ hη hrel

/-- Quantitative robust net for every fixed continuous `R`-gate architecture.
The exponent is linear in gate count, so it survives comparison with
exponentially larger ambient unitary dimension. -/
theorem TwoQubitArchitecture.exists_contraction_operatorNet_card_le
    {n R : ℕ} (A : TwoQubitArchitecture n R) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ net : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ),
      (∀ gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
        ∃ V ∈ net,
          dist
              ((A.contraction gates : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
              (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ ε) ∧
      (net.card : ℝ) ≤ (1 + 4 * (R : ℝ) / ε) ^ (32 * R) := by
  classical
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hη : 0 < ε / (R : ℝ) := div_pos hε hRreal
  obtain ⟨localNet, hlocalNet, hlocalCard⟩ :=
    exists_specialUnitary_boolTwoQubit_operatorNet_card_le hη
  let endpoint : (Fin R → {U // U ∈ localNet}) →
      Matrix.unitaryGroup (Fin n → Bool) ℂ := fun f =>
    A.contraction fun r => (f r).1
  let net : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
    (Finset.univ : Finset (Fin R → {U // U ∈ localNet})).image endpoint
  refine ⟨net, ?_, ?_⟩
  · intro gates
    let approx : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ := fun r =>
      Classical.choose (hlocalNet (gates r))
    have happroxMem (r : Fin R) : approx r ∈ localNet :=
      (Classical.choose_spec (hlocalNet (gates r))).1
    have happroxDist (r : Fin R) :
        dist
          (gates r : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          (approx r : Matrix (Bool × Bool) (Bool × Bool) ℂ) ≤ ε / (R : ℝ) :=
      (Classical.choose_spec (hlocalNet (gates r))).2
    let f : Fin R → {U // U ∈ localNet} := fun r => ⟨approx r, happroxMem r⟩
    refine ⟨A.contraction approx, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨f, Finset.mem_univ f, by
        apply Subtype.ext
        rfl⟩
    · calc
        dist
            ((A.contraction gates : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
            ((A.contraction approx : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
              Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤
            (R : ℝ) * (ε / (R : ℝ)) :=
          A.contraction_operatorDist_le hη.le gates approx happroxDist
        _ = ε := by field_simp
  · have hcardNat : net.card ≤ localNet.card ^ R := by
      calc
        net.card ≤ (Finset.univ : Finset (Fin R → {U // U ∈ localNet})).card :=
          Finset.card_image_le
        _ = localNet.card ^ R := by simp
    have hcardReal : (net.card : ℝ) ≤ (localNet.card : ℝ) ^ R := by
      exact_mod_cast hcardNat
    calc
      (net.card : ℝ) ≤ (localNet.card : ℝ) ^ R := hcardReal
      _ ≤ ((1 + 4 / (ε / (R : ℝ))) ^ 32) ^ R :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hlocalCard R
      _ = (1 + 4 * (R : ℝ) / ε) ^ (32 * R) := by
        rw [← pow_mul]
        congr 2
        field_simp

/-- The number of ordered length-`R` two-qubit architectures is at most the
number of unrestricted ordered site-pair words. -/
noncomputable instance TwoQubitArchitecture.fintypeArchitecture
    (n R : ℕ) : Fintype (TwoQubitArchitecture n R) := Fintype.ofFinite _

theorem card_twoQubitArchitecture_le (n R : ℕ) :
    Fintype.card (TwoQubitArchitecture n R) ≤ (n * n) ^ R := by
  classical
  calc
    Fintype.card (TwoQubitArchitecture n R) ≤
        Fintype.card (Fin R → Fin n × Fin n) :=
      Fintype.card_le_of_injective TwoQubitArchitecture.sites (by
        intro A B h
        cases A with
        | mk As Ad =>
          cases B with
          | mk Bs Bd =>
            simp only at h
            subst Bs
            rfl)
    _ = (n * n) ^ R := by simp

/-- Complete robust metric-entropy law for all continuous two-qubit circuits
with exactly `R` gates, including every ordered architecture. -/
theorem exists_exactContinuousTwoQubitCircuit_operatorNet_card_le
    {n R : ℕ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ net : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ),
      (∀ A : TwoQubitArchitecture n R,
        ∀ gates : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ,
          ∃ V ∈ net,
            dist
                ((A.contraction gates : Matrix.unitaryGroup (Fin n → Bool) ℂ) :
                  Matrix (Fin n → Bool) (Fin n → Bool) ℂ)
                (V : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) ≤ ε) ∧
      (net.card : ℝ) ≤
        ((n * n : ℕ) : ℝ) ^ R *
          (1 + 4 * (R : ℝ) / ε) ^ (32 * R) := by
  classical
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hη : 0 < ε / (R : ℝ) := div_pos hε hRreal
  obtain ⟨localNet, hlocalNet, hlocalCard⟩ :=
    exists_specialUnitary_boolTwoQubit_operatorNet_card_le hη
  let Parameter :=
    TwoQubitArchitecture n R × (Fin R → {U // U ∈ localNet})
  let endpoint : Parameter → Matrix.unitaryGroup (Fin n → Bool) ℂ := fun p =>
    p.1.contraction fun r => (p.2 r).1
  let net : Finset (Matrix.unitaryGroup (Fin n → Bool) ℂ) :=
    (Finset.univ : Finset Parameter).image endpoint
  refine ⟨net, ?_, ?_⟩
  · intro A gates
    let approx : Fin R → Matrix.specialUnitaryGroup (Bool × Bool) ℂ := fun r =>
      Classical.choose (hlocalNet (gates r))
    have happroxMem (r : Fin R) : approx r ∈ localNet :=
      (Classical.choose_spec (hlocalNet (gates r))).1
    have happroxDist (r : Fin R) :
        dist
          (gates r : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          (approx r : Matrix (Bool × Bool) (Bool × Bool) ℂ) ≤ ε / (R : ℝ) :=
      (Classical.choose_spec (hlocalNet (gates r))).2
    let p : Parameter := ⟨A, fun r => ⟨approx r, happroxMem r⟩⟩
    refine ⟨A.contraction approx, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, by
        apply Subtype.ext
        rfl⟩
    · exact (A.contraction_operatorDist_le hη.le gates approx happroxDist).trans_eq
        (by field_simp)
  · have harch := card_twoQubitArchitecture_le n R
    have hcardNat : net.card ≤ (n * n) ^ R * localNet.card ^ R := by
      calc
        net.card ≤ (Finset.univ : Finset Parameter).card := Finset.card_image_le
        _ = Fintype.card (TwoQubitArchitecture n R) * localNet.card ^ R := by
          simp [Parameter]
        _ ≤ (n * n) ^ R * localNet.card ^ R :=
          Nat.mul_le_mul_right _ harch
    have hcardReal :
        (net.card : ℝ) ≤ (((n * n) ^ R * localNet.card ^ R : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    have hlocalPow :
        (localNet.card : ℝ) ^ R ≤
          (1 + 4 * (R : ℝ) / ε) ^ (32 * R) := by
      calc
        (localNet.card : ℝ) ^ R ≤
            ((1 + 4 / (ε / (R : ℝ))) ^ 32) ^ R :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hlocalCard R
        _ = (1 + 4 * (R : ℝ) / ε) ^ (32 * R) := by
          rw [← pow_mul]
          congr 2
          field_simp
    calc
      (net.card : ℝ) ≤ (((n * n) ^ R * localNet.card ^ R : ℕ) : ℝ) := hcardReal
      _ = (((n * n : ℕ) : ℝ) ^ R) * (localNet.card : ℝ) ^ R := by norm_num
      _ ≤ (((n * n : ℕ) : ℝ) ^ R) *
          (1 + 4 * (R : ℝ) / ε) ^ (32 * R) :=
        mul_le_mul_of_nonneg_left hlocalPow (by positivity)

end

end GaloisForLFunctions.HTGeometry
