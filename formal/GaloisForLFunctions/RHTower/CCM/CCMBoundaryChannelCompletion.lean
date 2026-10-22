/-
# CCM boundary-channel completion trichotomy

The finite Connes--Consani--Moscovici construction starts from a symmetric positive-semidefinite
matrix `T`, a symmetric clock `D`, and the rank-two displacement law

`D*T - T*D = |beta><eta| - |eta><beta|`.

The published construction corrects `D` using an even one-dimensional radical vector.  This file
formalizes the unconditional algebra showing that the correction has three branches:

* an `eta` correction when the radical meets the even boundary;
* a `beta` correction when it meets the odd boundary;
* a source-solution correction when both boundary functionals vanish on the radical.

Each completed clock preserves the radical and is self-adjoint for the semidefinite metric:
`T*A = Aᵀ*T`.  No RH statement, zeta-zero predicate, source estimate, parity assumption, or
simplicity assumption appears.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

noncomputable section

namespace RHTower

open Matrix

variable {n : Type*} [Fintype n]

/-- Even CCM boundary completion `D - |De><eta|`. -/
def ccmEvenBoundaryCompletion (D : Matrix n n ℝ) (eta e : n → ℝ) : Matrix n n ℝ :=
  D - Matrix.vecMulVec (D *ᵥ e) eta

/-- Odd CCM boundary completion `D - |Do><beta|`. -/
def ccmOddBoundaryCompletion (D : Matrix n n ℝ) (beta o : n → ℝ) : Matrix n n ℝ :=
  D - Matrix.vecMulVec (D *ᵥ o) beta

/-- Neutral CCM boundary completion `D + |y><eta|`, where the source solution obeys `Ty=beta`. -/
def ccmNeutralBoundaryCompletion (D : Matrix n n ℝ) (y eta : n → ℝ) : Matrix n n ℝ :=
  D + Matrix.vecMulVec y eta

/-- For a symmetric real matrix, row and column multiplication by the same vector agree. -/
lemma ccm_vecMul_eq_mulVec_of_transpose_eq (T : Matrix n n ℝ) (u : n → ℝ)
    (hT : T.transpose = T) :
    u ᵥ* T = T *ᵥ u := by
  calc
    u ᵥ* T = u ᵥ* T.transpose := by rw [hT]
    _ = T *ᵥ u := Matrix.vecMul_transpose T u

/-- **Active-even completion law.**  If `TDe=-beta`, then `D-|De><eta|` is self-adjoint for
the semidefinite metric `T`. -/
theorem ccmEvenBoundaryCompletion_selfAdjoint
    (T D : Matrix n n ℝ) (eta beta e : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta)
    (hboundary : T *ᵥ (D *ᵥ e) = -beta) :
    T * ccmEvenBoundaryCompletion D eta e =
      (ccmEvenBoundaryCompletion D eta e).transpose * T := by
  have hrow : (D *ᵥ e) ᵥ* T = -beta := by
    rw [ccm_vecMul_eq_mulVec_of_transpose_eq T (D *ᵥ e) hT, hboundary]
  rw [ccmEvenBoundaryCompletion, Matrix.transpose_sub, Matrix.transpose_vecMulVec, hD,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    hboundary, hrow]
  have hTD : T * D = D * T +
      (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by
    calc
      T * D = (T * D - D * T) + D * T := by abel
      _ = (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) + D * T := by rw [hcomm]
      _ = D * T + (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by abel
  rw [hTD]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.neg_apply]
  ring

/-- **Active-odd completion law.**  If `TDo=eta`, then `D-|Do><beta|` is self-adjoint for
the semidefinite metric `T`. -/
theorem ccmOddBoundaryCompletion_selfAdjoint
    (T D : Matrix n n ℝ) (eta beta o : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta)
    (hboundary : T *ᵥ (D *ᵥ o) = eta) :
    T * ccmOddBoundaryCompletion D beta o =
      (ccmOddBoundaryCompletion D beta o).transpose * T := by
  have hrow : (D *ᵥ o) ᵥ* T = eta := by
    rw [ccm_vecMul_eq_mulVec_of_transpose_eq T (D *ᵥ o) hT, hboundary]
  rw [ccmOddBoundaryCompletion, Matrix.transpose_sub, Matrix.transpose_vecMulVec, hD,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    hboundary, hrow]
  have hTD : T * D = D * T +
      (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by
    calc
      T * D = (T * D - D * T) + D * T := by abel
      _ = (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) + D * T := by rw [hcomm]
      _ = D * T + (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by abel
  rw [hTD]
  abel

/-- **Neutral completion law.**  If `Ty=beta`, then `D+|y><eta|` is self-adjoint for `T`. -/
theorem ccmNeutralBoundaryCompletion_selfAdjoint
    (T D : Matrix n n ℝ) (eta beta y : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta)
    (hy : T *ᵥ y = beta) :
    T * ccmNeutralBoundaryCompletion D y eta =
      (ccmNeutralBoundaryCompletion D y eta).transpose * T := by
  have hrow : y ᵥ* T = beta := by
    rw [ccm_vecMul_eq_mulVec_of_transpose_eq T y hT, hy]
  rw [ccmNeutralBoundaryCompletion, Matrix.transpose_add, Matrix.transpose_vecMulVec, hD,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hy, hrow]
  have hTD : T * D = D * T +
      (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by
    calc
      T * D = (T * D - D * T) + D * T := by abel
      _ = (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) + D * T := by rw [hcomm]
      _ = D * T + (Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta) := by abel
  rw [hTD]
  abel

/-- The normalized active-even boundary vector is killed by its completed clock. -/
theorem ccmEvenBoundaryCompletion_mulVec_self
    (D : Matrix n n ℝ) (eta e : n → ℝ) (heta : eta ⬝ᵥ e = 1) :
    ccmEvenBoundaryCompletion D eta e *ᵥ e = 0 := by
  rw [ccmEvenBoundaryCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  simp [heta]

/-- The normalized active-odd boundary vector is killed by its completed clock. -/
theorem ccmOddBoundaryCompletion_mulVec_self
    (D : Matrix n n ℝ) (beta o : n → ℝ) (hbeta : beta ⬝ᵥ o = 1) :
    ccmOddBoundaryCompletion D beta o *ᵥ o = 0 := by
  rw [ccmOddBoundaryCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  simp [hbeta]

/-- **Radical transport law.**  Rank-two displacement sends a radical vector through the clock
into the two source directions, with coefficients given by its two boundary pairings. -/
theorem ccmRadicalTransport
    (T D : Matrix n n ℝ) (eta beta k : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (hk : T *ᵥ k = 0) :
    T *ᵥ (D *ᵥ k) =
      -(eta ⬝ᵥ k) • beta + (beta ⬝ᵥ k) • eta := by
  have h := congrArg (fun M : Matrix n n ℝ => M *ᵥ k) hdisp
  change (D * T - T * D) *ᵥ k =
    (Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) *ᵥ k at h
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero, Matrix.vecMulVec_mulVec,
    Matrix.vecMulVec_mulVec] at h
  have hn := congrArg Neg.neg h
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hn

/-- An active even radical vector converts displacement into the source identity `TDe=-beta`. -/
theorem ccmEvenBoundary_source
    (T D : Matrix n n ℝ) (eta beta e : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (he : T *ᵥ e = 0) (heta : eta ⬝ᵥ e = 1) (hbeta : beta ⬝ᵥ e = 0) :
    T *ᵥ (D *ᵥ e) = -beta := by
  rw [ccmRadicalTransport T D eta beta e hdisp he, heta, hbeta]
  simp

/-- An active odd radical vector converts displacement into the source identity `TDo=eta`. -/
theorem ccmOddBoundary_source
    (T D : Matrix n n ℝ) (eta beta o : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (ho : T *ᵥ o = 0) (heta : eta ⬝ᵥ o = 0) (hbeta : beta ⬝ᵥ o = 1) :
    T *ᵥ (D *ᵥ o) = eta := by
  rw [ccmRadicalTransport T D eta beta o hdisp ho, heta, hbeta]
  simp

/-- **Even-channel exclusivity.**  Once an active even radical vector gives `TDe=-beta`, the odd
boundary vector is orthogonal to every radical vector. -/
theorem ccmEvenBoundary_opposite_orthogonal
    (T D : Matrix n n ℝ) (beta e k : n → ℝ)
    (hT : T.transpose = T)
    (hboundary : T *ᵥ (D *ᵥ e) = -beta)
    (hk : T *ᵥ k = 0) :
    beta ⬝ᵥ k = 0 := by
  have hb : beta = -(T *ᵥ (D *ᵥ e)) := by
    rw [hboundary]
    simp
  have hsymm : (T *ᵥ (D *ᵥ e)) ⬝ᵥ k = (D *ᵥ e) ⬝ᵥ (T *ᵥ k) := by
    calc
      (T *ᵥ (D *ᵥ e)) ⬝ᵥ k = k ⬝ᵥ (T *ᵥ (D *ᵥ e)) :=
        dotProduct_comm _ _
      _ = k ⬝ᵥ (T.transpose *ᵥ (D *ᵥ e)) := by rw [hT]
      _ = (D *ᵥ e) ⬝ᵥ (T *ᵥ k) :=
        Matrix.dotProduct_transpose_mulVec T k (D *ᵥ e)
  calc
    beta ⬝ᵥ k = -((T *ᵥ (D *ᵥ e)) ⬝ᵥ k) := by rw [hb]; simp [dotProduct]
    _ = -((D *ᵥ e) ⬝ᵥ (T *ᵥ k)) := by rw [hsymm]
    _ = 0 := by rw [hk]; simp

/-- **Odd-channel exclusivity.**  Once an active odd radical vector gives `TDo=eta`, the even
boundary vector is orthogonal to every radical vector. -/
theorem ccmOddBoundary_opposite_orthogonal
    (T D : Matrix n n ℝ) (eta o k : n → ℝ)
    (hT : T.transpose = T)
    (hboundary : T *ᵥ (D *ᵥ o) = eta)
    (hk : T *ᵥ k = 0) :
    eta ⬝ᵥ k = 0 := by
  have hsymm : (T *ᵥ (D *ᵥ o)) ⬝ᵥ k = (D *ᵥ o) ⬝ᵥ (T *ᵥ k) := by
    calc
      (T *ᵥ (D *ᵥ o)) ⬝ᵥ k = k ⬝ᵥ (T *ᵥ (D *ᵥ o)) :=
        dotProduct_comm _ _
      _ = k ⬝ᵥ (T.transpose *ᵥ (D *ᵥ o)) := by rw [hT]
      _ = (D *ᵥ o) ⬝ᵥ (T *ᵥ k) :=
        Matrix.dotProduct_transpose_mulVec T k (D *ᵥ o)
  rw [← hboundary, hsymm, hk]
  simp

/-- The active-even completed clock maps every radical vector back into the radical. -/
theorem ccmEvenBoundaryCompletion_preserves_radical
    (T D : Matrix n n ℝ) (eta beta e k : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (hk : T *ᵥ k = 0) (hbeta : beta ⬝ᵥ k = 0)
    (hboundary : T *ᵥ (D *ᵥ e) = -beta) :
    T *ᵥ (ccmEvenBoundaryCompletion D eta e *ᵥ k) = 0 := by
  rw [ccmEvenBoundaryCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hboundary,
    ccmRadicalTransport T D eta beta k hdisp hk, hbeta]
  simp

/-- The active-odd completed clock maps every radical vector back into the radical. -/
theorem ccmOddBoundaryCompletion_preserves_radical
    (T D : Matrix n n ℝ) (eta beta o k : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (hk : T *ᵥ k = 0) (heta : eta ⬝ᵥ k = 0)
    (hboundary : T *ᵥ (D *ᵥ o) = eta) :
    T *ᵥ (ccmOddBoundaryCompletion D beta o *ᵥ k) = 0 := by
  rw [ccmOddBoundaryCompletion, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hboundary,
    ccmRadicalTransport T D eta beta k hdisp hk, heta]
  simp

/-- In the neutral channel, both source pairings vanish and the source-solution completion maps
every radical vector back into the radical. -/
theorem ccmNeutralBoundaryCompletion_preserves_radical
    (T D : Matrix n n ℝ) (eta beta y k : n → ℝ)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (hk : T *ᵥ k = 0) (heta : eta ⬝ᵥ k = 0) (hbeta : beta ⬝ᵥ k = 0) :
    T *ᵥ (ccmNeutralBoundaryCompletion D y eta *ᵥ k) = 0 := by
  rw [ccmNeutralBoundaryCompletion, Matrix.add_mulVec, Matrix.vecMulVec_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul,
    ccmRadicalTransport T D eta beta k hdisp hk, heta, hbeta]
  simp

/-- **Complete active-even connector.**  A normalized even-channel radical witness alone produces
metric self-adjointness, kills the witness, and preserves the entire radical. -/
theorem ccmEvenBoundaryCompletion_active
    (T D : Matrix n n ℝ) (eta beta e : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (he : T *ᵥ e = 0) (heta : eta ⬝ᵥ e = 1) (hbeta : beta ⬝ᵥ e = 0) :
    T * ccmEvenBoundaryCompletion D eta e =
        (ccmEvenBoundaryCompletion D eta e).transpose * T ∧
      ccmEvenBoundaryCompletion D eta e *ᵥ e = 0 ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 →
        T *ᵥ (ccmEvenBoundaryCompletion D eta e *ᵥ k) = 0 := by
  have hboundary := ccmEvenBoundary_source T D eta beta e hdisp he heta hbeta
  have hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by
    calc
      T * D - D * T = -(D * T - T * D) := by abel
      _ = -(Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) := by rw [hdisp]
      _ = Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by abel
  refine ⟨ccmEvenBoundaryCompletion_selfAdjoint T D eta beta e hT hD hcomm hboundary,
    ccmEvenBoundaryCompletion_mulVec_self D eta e heta, ?_⟩
  intro k hk
  have hkbeta := ccmEvenBoundary_opposite_orthogonal T D beta e k hT hboundary hk
  exact ccmEvenBoundaryCompletion_preserves_radical
    T D eta beta e k hdisp hk hkbeta hboundary

/-- **Complete active-odd connector.**  A normalized odd-channel radical witness alone produces
metric self-adjointness, kills the witness, and preserves the entire radical. -/
theorem ccmOddBoundaryCompletion_active
    (T D : Matrix n n ℝ) (eta beta o : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta)
    (ho : T *ᵥ o = 0) (heta : eta ⬝ᵥ o = 0) (hbeta : beta ⬝ᵥ o = 1) :
    T * ccmOddBoundaryCompletion D beta o =
        (ccmOddBoundaryCompletion D beta o).transpose * T ∧
      ccmOddBoundaryCompletion D beta o *ᵥ o = 0 ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 →
        T *ᵥ (ccmOddBoundaryCompletion D beta o *ᵥ k) = 0 := by
  have hboundary := ccmOddBoundary_source T D eta beta o hdisp ho heta hbeta
  have hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by
    calc
      T * D - D * T = -(D * T - T * D) := by abel
      _ = -(Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) := by rw [hdisp]
      _ = Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by abel
  refine ⟨ccmOddBoundaryCompletion_selfAdjoint T D eta beta o hT hD hcomm hboundary,
    ccmOddBoundaryCompletion_mulVec_self D beta o hbeta, ?_⟩
  intro k hk
  have hketa := ccmOddBoundary_opposite_orthogonal T D eta o k hT hboundary hk
  exact ccmOddBoundaryCompletion_preserves_radical
    T D eta beta o k hdisp hk hketa hboundary

/-- Even projection for a reflection-graded boundary system. -/
def ccmEvenPart (Gamma : Matrix n n ℝ) (k : n → ℝ) : n → ℝ :=
  (1 / 2 : ℝ) • (k + Gamma *ᵥ k)

/-- Odd projection for a reflection-graded boundary system. -/
def ccmOddPart (Gamma : Matrix n n ℝ) (k : n → ℝ) : n → ℝ :=
  (1 / 2 : ℝ) • (k - Gamma *ᵥ k)

lemma ccm_dot_mulVec_of_symm (Gamma : Matrix n n ℝ) (c k : n → ℝ)
    (hG : Gamma.transpose = Gamma) :
    c ⬝ᵥ (Gamma *ᵥ k) = (Gamma *ᵥ c) ⬝ᵥ k := by
  calc
    c ⬝ᵥ (Gamma *ᵥ k) = c ⬝ᵥ (Gamma.transpose *ᵥ k) := by rw [hG]
    _ = k ⬝ᵥ (Gamma *ᵥ c) := Matrix.dotProduct_transpose_mulVec Gamma c k
    _ = (Gamma *ᵥ c) ⬝ᵥ k := dotProduct_comm _ _

lemma ccmEvenPart_radical (T Gamma : Matrix n n ℝ) (k : n → ℝ)
    (hcomm : T * Gamma = Gamma * T) (hk : T *ᵥ k = 0) :
    T *ᵥ ccmEvenPart Gamma k = 0 := by
  rw [ccmEvenPart, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_mulVec,
    hcomm, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]
  simp

lemma ccmOddPart_radical (T Gamma : Matrix n n ℝ) (k : n → ℝ)
    (hcomm : T * Gamma = Gamma * T) (hk : T *ᵥ k = 0) :
    T *ᵥ ccmOddPart Gamma k = 0 := by
  rw [ccmOddPart, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    hcomm, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]
  simp

lemma ccmEvenPart_eta_pairing (Gamma : Matrix n n ℝ) (eta k : n → ℝ)
    (hG : Gamma.transpose = Gamma) (heta : Gamma *ᵥ eta = eta) :
    eta ⬝ᵥ ccmEvenPart Gamma k = eta ⬝ᵥ k := by
  rw [ccmEvenPart, dotProduct_smul, dotProduct_add,
    ccm_dot_mulVec_of_symm Gamma eta k hG, heta]
  ring

lemma ccmEvenPart_beta_pairing (Gamma : Matrix n n ℝ) (beta k : n → ℝ)
    (hG : Gamma.transpose = Gamma) (hbeta : Gamma *ᵥ beta = -beta) :
    beta ⬝ᵥ ccmEvenPart Gamma k = 0 := by
  rw [ccmEvenPart, dotProduct_smul, dotProduct_add,
    ccm_dot_mulVec_of_symm Gamma beta k hG, hbeta]
  simp [dotProduct]

lemma ccmOddPart_eta_pairing (Gamma : Matrix n n ℝ) (eta k : n → ℝ)
    (hG : Gamma.transpose = Gamma) (heta : Gamma *ᵥ eta = eta) :
    eta ⬝ᵥ ccmOddPart Gamma k = 0 := by
  rw [ccmOddPart, dotProduct_smul, dotProduct_sub,
    ccm_dot_mulVec_of_symm Gamma eta k hG, heta]
  simp

lemma ccmOddPart_beta_pairing (Gamma : Matrix n n ℝ) (beta k : n → ℝ)
    (hG : Gamma.transpose = Gamma) (hbeta : Gamma *ᵥ beta = -beta) :
    beta ⬝ᵥ ccmOddPart Gamma k = beta ⬝ᵥ k := by
  rw [ccmOddPart, dotProduct_smul, dotProduct_sub,
    ccm_dot_mulVec_of_symm Gamma beta k hG, hbeta]
  simp [dotProduct]
  ring

/-- Any radical vector seen by the even source has a normalized even radical projection. -/
theorem ccm_exists_normalized_even_radical
    (T Gamma : Matrix n n ℝ) (eta beta : n → ℝ)
    (hTG : T * Gamma = Gamma * T) (hG : Gamma.transpose = Gamma)
    (heta : Gamma *ᵥ eta = eta) (hbeta : Gamma *ᵥ beta = -beta)
    (k : n → ℝ) (hk : T *ᵥ k = 0) (hketa : eta ⬝ᵥ k ≠ 0) :
    ∃ e : n → ℝ, T *ᵥ e = 0 ∧ eta ⬝ᵥ e = 1 ∧ beta ⬝ᵥ e = 0 := by
  let ep := ccmEvenPart Gamma k
  let e := (eta ⬝ᵥ ep)⁻¹ • ep
  have hepT : T *ᵥ ep = 0 := ccmEvenPart_radical T Gamma k hTG hk
  have hepeta : eta ⬝ᵥ ep = eta ⬝ᵥ k := ccmEvenPart_eta_pairing Gamma eta k hG heta
  have hepbeta : beta ⬝ᵥ ep = 0 := ccmEvenPart_beta_pairing Gamma beta k hG hbeta
  refine ⟨e, ?_, ?_, ?_⟩
  · dsimp [e]
    rw [Matrix.mulVec_smul, hepT]
    simp
  · dsimp [e]
    rw [dotProduct_smul, hepeta]
    exact inv_mul_cancel₀ hketa
  · dsimp [e]
    rw [dotProduct_smul, hepbeta]
    simp

/-- Any radical vector seen by the odd source has a normalized odd radical projection. -/
theorem ccm_exists_normalized_odd_radical
    (T Gamma : Matrix n n ℝ) (eta beta : n → ℝ)
    (hTG : T * Gamma = Gamma * T) (hG : Gamma.transpose = Gamma)
    (heta : Gamma *ᵥ eta = eta) (hbeta : Gamma *ᵥ beta = -beta)
    (k : n → ℝ) (hk : T *ᵥ k = 0) (hkbeta : beta ⬝ᵥ k ≠ 0) :
    ∃ o : n → ℝ, T *ᵥ o = 0 ∧ eta ⬝ᵥ o = 0 ∧ beta ⬝ᵥ o = 1 := by
  let op := ccmOddPart Gamma k
  let o := (beta ⬝ᵥ op)⁻¹ • op
  have hopT : T *ᵥ op = 0 := ccmOddPart_radical T Gamma k hTG hk
  have hopeta : eta ⬝ᵥ op = 0 := ccmOddPart_eta_pairing Gamma eta k hG heta
  have hopbeta : beta ⬝ᵥ op = beta ⬝ᵥ k := ccmOddPart_beta_pairing Gamma beta k hG hbeta
  refine ⟨o, ?_, ?_, ?_⟩
  · dsimp [o]
    rw [Matrix.mulVec_smul, hopT]
    simp
  · dsimp [o]
    rw [dotProduct_smul, hopeta]
    simp
  · dsimp [o]
    rw [dotProduct_smul, hopbeta]
    exact inv_mul_cancel₀ hkbeta

/-- Coordinate Riesz representation for the finite real vector space. -/
lemma ccm_exists_dotProduct_representation
    (ell : (n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ y : n → ℝ, ∀ x : n → ℝ, ell x = y ⬝ᵥ x := by
  classical
  let y : n → ℝ := fun i => ell (Pi.single i 1)
  refine ⟨y, fun x => ?_⟩
  calc
    ell x = ell (∑ i, Pi.single i (x i)) := by rw [LinearMap.sum_single_apply]
    _ = ∑ i, ell (Pi.single i (x i)) := by rw [map_sum]
    _ = ∑ i, x i * ell (Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by
        ext j
        simp [Pi.single_apply]]
      simp
    _ = y ⬝ᵥ x := by
      simp only [y, dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- A vector orthogonal to the radical of a symmetric finite matrix lies in its range.  This
eliminates source-solution existence as a hypothesis in the neutral channel. -/
theorem ccm_exists_source_solution_of_orthogonal_radical
    (T : Matrix n n ℝ) (beta : n → ℝ)
    (hT : T.transpose = T)
    (horth : ∀ k : n → ℝ, T *ᵥ k = 0 → beta ⬝ᵥ k = 0) :
    ∃ y : n → ℝ, T *ᵥ y = beta := by
  classical
  let f : (n → ℝ) →ₗ[ℝ] (n → ℝ) := T.mulVecLin
  let c : (n → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ) beta
  have hc_ann : c ∈ f.ker.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro k hk
    exact horth k (by simpa [f] using hk)
  have hc_range : c ∈ f.dualMap.range := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hc_ann
  rcases hc_range with ⟨ell, hell⟩
  rcases ccm_exists_dotProduct_representation ell with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  have hdot : ∀ x : n → ℝ, (T *ᵥ y) ⬝ᵥ x = beta ⬝ᵥ x := by
    intro x
    have hx := LinearMap.congr_fun hell x
    rw [LinearMap.dualMap_apply] at hx
    change ell (T *ᵥ x) = beta ⬝ᵥ x at hx
    rw [hy] at hx
    calc
      (T *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (T *ᵥ x) := by
        calc
          (T *ᵥ y) ⬝ᵥ x = x ⬝ᵥ (T *ᵥ y) := dotProduct_comm _ _
          _ = x ⬝ᵥ (T.transpose *ᵥ y) := by rw [hT]
          _ = y ⬝ᵥ (T *ᵥ x) := Matrix.dotProduct_transpose_mulVec T x y
      _ = beta ⬝ᵥ x := hx
  funext i
  have hi := hdot (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using hi

/-- Active even and active odd boundary channels cannot coexist. -/
theorem ccmBoundaryActive_mutuallyExclusive
    (T D : Matrix n n ℝ) (eta beta e o : n → ℝ)
    (hT : T.transpose = T)
    (he : T *ᵥ e = 0) (heta : eta ⬝ᵥ e = 1) (hebeta : beta ⬝ᵥ e = 0)
    (ho : T *ᵥ o = 0) (hobeta : beta ⬝ᵥ o = 1)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) : False := by
  have hboundary := ccmEvenBoundary_source T D eta beta e hdisp he heta hebeta
  have horth := ccmEvenBoundary_opposite_orthogonal T D beta e o hT hboundary ho
  linarith

/-- **Boundary-channel completion trichotomy.**  Displacement and reflection grading alone select
an active-even, active-odd, or neutral correction.  Every returned correction is metric-adjoint
and preserves the full radical.  Neutral source existence is a conclusion, not a premise. -/
theorem ccmBoundaryChannelCompletion_trichotomy
    (T D Gamma : Matrix n n ℝ) (eta beta : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hG : Gamma.transpose = Gamma) (hTG : T * Gamma = Gamma * T)
    (hetaG : Gamma *ᵥ eta = eta) (hbetaG : Gamma *ᵥ beta = -beta)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) :
    (∃ e : n → ℝ,
      T *ᵥ e = 0 ∧ eta ⬝ᵥ e = 1 ∧ beta ⬝ᵥ e = 0 ∧
      (∀ k : n → ℝ, T *ᵥ k = 0 → beta ⬝ᵥ k = 0) ∧
      T * ccmEvenBoundaryCompletion D eta e =
        (ccmEvenBoundaryCompletion D eta e).transpose * T ∧
      ccmEvenBoundaryCompletion D eta e *ᵥ e = 0 ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 →
        T *ᵥ (ccmEvenBoundaryCompletion D eta e *ᵥ k) = 0) ∨
    (∃ o : n → ℝ,
      T *ᵥ o = 0 ∧ eta ⬝ᵥ o = 0 ∧ beta ⬝ᵥ o = 1 ∧
      (∀ k : n → ℝ, T *ᵥ k = 0 → eta ⬝ᵥ k = 0) ∧
      T * ccmOddBoundaryCompletion D beta o =
        (ccmOddBoundaryCompletion D beta o).transpose * T ∧
      ccmOddBoundaryCompletion D beta o *ᵥ o = 0 ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 →
        T *ᵥ (ccmOddBoundaryCompletion D beta o *ᵥ k) = 0) ∨
    (∃ y : n → ℝ,
      (∀ k : n → ℝ, T *ᵥ k = 0 → eta ⬝ᵥ k = 0) ∧
      (∀ k : n → ℝ, T *ᵥ k = 0 → beta ⬝ᵥ k = 0) ∧
      T *ᵥ y = beta ∧
      T * ccmNeutralBoundaryCompletion D y eta =
        (ccmNeutralBoundaryCompletion D y eta).transpose * T ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 →
        T *ᵥ (ccmNeutralBoundaryCompletion D y eta *ᵥ k) = 0) := by
  classical
  have hcomm : T * D - D * T =
      Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by
    calc
      T * D - D * T = -(D * T - T * D) := by abel
      _ = -(Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) := by rw [hdisp]
      _ = Matrix.vecMulVec eta beta - Matrix.vecMulVec beta eta := by abel
  by_cases hEta : ∃ k : n → ℝ, T *ᵥ k = 0 ∧ eta ⬝ᵥ k ≠ 0
  · rcases hEta with ⟨k, hk, hketa⟩
    rcases ccm_exists_normalized_even_radical
      T Gamma eta beta hTG hG hetaG hbetaG k hk hketa with ⟨e, he, heta, hbeta⟩
    have hboundary := ccmEvenBoundary_source T D eta beta e hdisp he heta hbeta
    have hbeta0 : ∀ k : n → ℝ, T *ᵥ k = 0 → beta ⬝ᵥ k = 0 :=
      fun k hk => ccmEvenBoundary_opposite_orthogonal T D beta e k hT hboundary hk
    have hactive := ccmEvenBoundaryCompletion_active
      T D eta beta e hT hD hdisp he heta hbeta
    exact Or.inl ⟨e, he, heta, hbeta, hbeta0, hactive.1, hactive.2.1, hactive.2.2⟩
  · by_cases hBeta : ∃ k : n → ℝ, T *ᵥ k = 0 ∧ beta ⬝ᵥ k ≠ 0
    · rcases hBeta with ⟨k, hk, hkbeta⟩
      rcases ccm_exists_normalized_odd_radical
        T Gamma eta beta hTG hG hetaG hbetaG k hk hkbeta with ⟨o, ho, heta, hbeta⟩
      have heta0 : ∀ k : n → ℝ, T *ᵥ k = 0 → eta ⬝ᵥ k = 0 := by
        intro k hk
        by_contra hk0
        exact hEta ⟨k, hk, hk0⟩
      have hactive := ccmOddBoundaryCompletion_active
        T D eta beta o hT hD hdisp ho heta hbeta
      exact Or.inr (Or.inl
        ⟨o, ho, heta, hbeta, heta0, hactive.1, hactive.2.1, hactive.2.2⟩)
    · have heta0 : ∀ k : n → ℝ, T *ᵥ k = 0 → eta ⬝ᵥ k = 0 := by
        intro k hk
        by_contra hk0
        exact hEta ⟨k, hk, hk0⟩
      have hbeta0 : ∀ k : n → ℝ, T *ᵥ k = 0 → beta ⬝ᵥ k = 0 := by
        intro k hk
        by_contra hk0
        exact hBeta ⟨k, hk, hk0⟩
      rcases ccm_exists_source_solution_of_orthogonal_radical T beta hT hbeta0 with ⟨y, hy⟩
      refine Or.inr (Or.inr ⟨y, heta0, hbeta0, hy,
        ccmNeutralBoundaryCompletion_selfAdjoint T D eta beta y hT hD hcomm hy, ?_⟩)
      intro k hk
      exact ccmNeutralBoundaryCompletion_preserves_radical
        T D eta beta y k hdisp hk (heta0 k hk) (hbeta0 k hk)

/-- Existence form consumed by concrete finite CCM matrices: some rank-one completed clock is
metric-adjoint and preserves the entire radical. -/
theorem ccmBoundaryChannelCompletion_exists
    (T D Gamma : Matrix n n ℝ) (eta beta : n → ℝ)
    (hT : T.transpose = T) (hD : D.transpose = D)
    (hG : Gamma.transpose = Gamma) (hTG : T * Gamma = Gamma * T)
    (hetaG : Gamma *ᵥ eta = eta) (hbetaG : Gamma *ᵥ beta = -beta)
    (hdisp : D * T - T * D =
      Matrix.vecMulVec beta eta - Matrix.vecMulVec eta beta) :
    ∃ A : Matrix n n ℝ,
      T * A = A.transpose * T ∧
      ∀ k : n → ℝ, T *ᵥ k = 0 → T *ᵥ (A *ᵥ k) = 0 := by
  rcases ccmBoundaryChannelCompletion_trichotomy T D Gamma eta beta
      hT hD hG hTG hetaG hbetaG hdisp with hE | hO | hN
  · rcases hE with ⟨e, he, heta, hbeta, hbeta0, hadj, hkill, hrad⟩
    exact ⟨ccmEvenBoundaryCompletion D eta e, hadj, hrad⟩
  · rcases hO with ⟨o, ho, heta, hbeta, heta0, hadj, hkill, hrad⟩
    exact ⟨ccmOddBoundaryCompletion D beta o, hadj, hrad⟩
  · rcases hN with ⟨y, heta0, hbeta0, hy, hadj, hrad⟩
    exact ⟨ccmNeutralBoundaryCompletion D y eta, hadj, hrad⟩

end RHTower
