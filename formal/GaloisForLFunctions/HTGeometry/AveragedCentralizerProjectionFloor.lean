import GaloisForLFunctions.HTGeometry.QuenchedCentralizerPropagatorSplit
import Mathlib.Analysis.Convex.Integral

/-!
# The averaged centralizer projector has an unavoidable floor

Removing a fixed subprojector from a family of orthogonal projectors leaves compressed projectors
whose traces are the codimensions of the fixed one inside each member.  Averaging preserves the
trace, so the average of the compressions carries the whole codimension even though no individual
member survives.

A Hermitian matrix has trace at most its rank times its operator norm, because its trace is the sum
of its eigenvalues and every eigenvalue is bounded by the operator norm.  Hence the averaged
compression has operator norm at least the common codimension divided by the dimension of the
quotient: the average cannot decay to zero.
-/

open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {w : Type*} [Fintype w] [DecidableEq w]

/-! ## Traces and eigenvalues of Hermitian matrices -/

private theorem trace_eq_sum_eigenvalues {A : Matrix w w ℂ} (hA : A.IsHermitian) :
    A.trace = ∑ i, (hA.eigenvalues i : ℂ) := by
  conv_lhs => rw [isHermitian_eq_conj_diagonal hA]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_eigenvectorUnitary hA, Matrix.one_mul,
    Matrix.trace_diagonal]

theorem abs_eigenvalue_le_l2_opNorm [Nonempty w] {A : Matrix w w ℂ} (hA : A.IsHermitian) (i : w) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  conv_rhs => rw [isHermitian_eq_conj_diagonal hA]
  rw [l2_opNorm_unitary_conj_eq hA.eigenvectorUnitary.2, Matrix.l2_opNorm_diagonal]
  calc |hA.eigenvalues i| = ‖((hA.eigenvalues i : ℂ))‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ‖fun j => ((hA.eigenvalues j : ℂ))‖ :=
        norm_le_pi_norm (fun j => ((hA.eigenvalues j : ℂ))) i

/-- **A Hermitian matrix has trace at most its rank times its operator norm.** -/
theorem trace_re_le_rank_mul_l2_opNorm [Nonempty w] {A : Matrix w w ℂ} (hA : A.IsHermitian) :
    A.trace.re ≤ (A.rank : ℝ) * ‖A‖ := by
  classical
  have hre : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [trace_eq_sum_eigenvalues hA, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  have hrank : (A.rank : ℝ) = ((Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hsplit : ∑ i, hA.eigenvalues i =
      ∑ i ∈ Finset.univ.filter fun i => hA.eigenvalues i ≠ 0, hA.eigenvalues i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    rw [Finset.mem_filter] at hi
    push Not at hi
    exact hi (Finset.mem_univ i)
  rw [hre, hrank, hsplit]
  calc ∑ i ∈ Finset.univ.filter fun i => hA.eigenvalues i ≠ 0, hA.eigenvalues i
      ≤ ∑ _i ∈ Finset.univ.filter fun i => hA.eigenvalues i ≠ 0, ‖A‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact le_trans (le_abs_self _) (abs_eigenvalue_le_l2_opNorm hA i)
    _ = ((Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) * ‖A‖ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Hermitian idempotents -/

/-- The trace of a Hermitian idempotent is its rank. -/
theorem trace_eq_rank_of_isHermitian_idem {P : Matrix w w ℂ} (hP : P.IsHermitian)
    (hidem : P * P = P) : P.trace = (P.rank : ℂ) := by
  classical
  have hcancel : ∀ f : w → ℂ,
      star (hP.eigenvectorUnitary : Matrix w w ℂ) *
          ((hP.eigenvectorUnitary : Matrix w w ℂ) * Matrix.diagonal f *
            star (hP.eigenvectorUnitary : Matrix w w ℂ)) *
          (hP.eigenvectorUnitary : Matrix w w ℂ) = Matrix.diagonal f := by
    intro f
    calc star (hP.eigenvectorUnitary : Matrix w w ℂ) *
            ((hP.eigenvectorUnitary : Matrix w w ℂ) * Matrix.diagonal f *
              star (hP.eigenvectorUnitary : Matrix w w ℂ)) *
            (hP.eigenvectorUnitary : Matrix w w ℂ)
        = (star (hP.eigenvectorUnitary : Matrix w w ℂ) *
            (hP.eigenvectorUnitary : Matrix w w ℂ)) * Matrix.diagonal f *
            (star (hP.eigenvectorUnitary : Matrix w w ℂ) *
              (hP.eigenvectorUnitary : Matrix w w ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal f := by rw [star_mul_eigenvectorUnitary hP]; simp
  have hPeq : P = (hP.eigenvectorUnitary : Matrix w w ℂ) *
      Matrix.diagonal (fun i => ((hP.eigenvalues i : ℂ))) *
      star (hP.eigenvectorUnitary : Matrix w w ℂ) := isHermitian_eq_conj_diagonal hP
  have h1 : (hP.eigenvectorUnitary : Matrix w w ℂ) *
        Matrix.diagonal (fun i => ((hP.eigenvalues i : ℂ)) * ((hP.eigenvalues i : ℂ))) *
        star (hP.eigenvectorUnitary : Matrix w w ℂ) =
      (hP.eigenvectorUnitary : Matrix w w ℂ) *
        Matrix.diagonal (fun i => ((hP.eigenvalues i : ℂ))) *
        star (hP.eigenvectorUnitary : Matrix w w ℂ) := by
    rw [← conj_diagonal_mul _ (star_mul_eigenvectorUnitary hP)
      (fun i => ((hP.eigenvalues i : ℂ))) (fun i => ((hP.eigenvalues i : ℂ))), ← hPeq]
    exact hidem
  have hsq := congrArg (fun M => star (hP.eigenvectorUnitary : Matrix w w ℂ) * M *
      (hP.eigenvectorUnitary : Matrix w w ℂ)) h1
  rw [hcancel, hcancel] at hsq
  have hev : ∀ i, hP.eigenvalues i * hP.eigenvalues i = hP.eigenvalues i := by
    intro i
    have hentry := congrFun (congrFun hsq i) i
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at hentry
    exact_mod_cast hentry
  have hzeroone : ∀ i, hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
    intro i
    have hfact : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by
      have := hev i
      nlinarith [this]
    rcases mul_eq_zero.mp hfact with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith [sub_eq_zero.mp h])
  rw [trace_eq_sum_eigenvalues hP, hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hzeroone i with h | h <;> simp [h]

/-- Compressing a projector by the complement of a subprojector removes exactly the subprojector's
trace. -/
theorem trace_compression (P Pi : Matrix w w ℂ) (hidem : Pi * Pi = Pi) (hsub : Pi * P = Pi)
    (hsub' : P * Pi = Pi) :
    ((1 - Pi) * P * (1 - Pi)).trace = P.trace - Pi.trace := by
  have hexp : (1 - Pi) * P * (1 - Pi) = P - Pi * P - P * Pi + Pi * (P * Pi) := by
    noncomm_ring
  rw [hexp, hsub, hsub', hidem, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  abel

/-! ## Averaging over a parameter space -/

variable {Θ : Type*} [MeasurableSpace Θ]

theorem isHermitian_integral {μ : Measure Θ} [IsProbabilityMeasure μ] {F : Θ → Matrix w w ℂ}
    (hF : Integrable F μ) (hherm : ∀ θ, (F θ).IsHermitian) :
    (∫ θ, F θ ∂μ).IsHermitian := by
  have hconv : Convex ℝ {A : Matrix w w ℂ | A.IsHermitian} := by
    intro x hx y hy a b _ _ _
    have hx' : xᴴ = x := hx
    have hy' : yᴴ = y := hy
    show (a • x + b • y)ᴴ = a • x + b • y
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hx', hy']
    simp
  have hclosed : IsClosed {A : Matrix w w ℂ | A.IsHermitian} := by
    have hset : {A : Matrix w w ℂ | A.IsHermitian} = (fun A : Matrix w w ℂ => Aᴴ - A) ⁻¹' {0} := by
      ext A
      simp [Matrix.IsHermitian, sub_eq_zero]
    rw [hset]
    exact IsClosed.preimage (continuous_id.matrix_conjTranspose.sub continuous_id)
      isClosed_singleton
  exact hconv.integral_mem hclosed (Filter.Eventually.of_forall fun θ => hherm θ) hF

theorem trace_integral {μ : Measure Θ} {F : Θ → Matrix w w ℂ} (hF : Integrable F μ) :
    (∫ θ, F θ ∂μ).trace = ∫ θ, (F θ).trace ∂μ :=
  ((Matrix.traceLinearMap w ℂ ℂ).toContinuousLinearMap.integral_comp_comm hF).symm

theorem mul_integral {μ : Measure Θ} {F : Θ → Matrix w w ℂ} (hF : Integrable F μ)
    (B : Matrix w w ℂ) : B * (∫ θ, F θ ∂μ) = ∫ θ, B * F θ ∂μ :=
  ((LinearMap.mulLeft ℂ B).toContinuousLinearMap.integral_comp_comm hF).symm

theorem integral_mul {μ : Measure Θ} {F : Θ → Matrix w w ℂ} (hF : Integrable F μ)
    (B : Matrix w w ℂ) : (∫ θ, F θ ∂μ) * B = ∫ θ, F θ * B ∂μ :=
  ((LinearMap.mulRight ℂ B).toContinuousLinearMap.integral_comp_comm hF).symm

/-- **Equations (21)--(22).**  The compression of the averaged projector by the complement of a
common subprojector has operator norm at least the common codimension divided by the dimension of
the quotient. -/
theorem l2_opNorm_averaged_compression_ge [Nonempty w] {μ : Measure Θ} [IsProbabilityMeasure μ]
    {P : Θ → Matrix w w ℂ} (hint : Integrable P μ) (hherm : ∀ θ, (P θ).IsHermitian)
    {Pi : Matrix w w ℂ} (hPiherm : Pi.IsHermitian) (hPiidem : Pi * Pi = Pi)
    (hsub : ∀ θ, Pi * P θ = Pi) (hsub' : ∀ θ, P θ * Pi = Pi)
    {kappa : ℕ} (htrace : ∀ θ, (P θ).trace = (kappa : ℂ))
    (hd : Pi.rank < Fintype.card w) :
    ((kappa : ℝ) - Pi.rank) / ((Fintype.card w : ℝ) - Pi.rank) ≤
      ‖(1 - Pi) * (∫ θ, P θ ∂μ) * (1 - Pi)‖ := by
  classical
  set bar : Matrix w w ℂ := ∫ θ, P θ ∂μ with hbar
  set Q : Matrix w w ℂ := 1 - Pi with hQ
  set A : Matrix w w ℂ := Q * bar * Q with hA
  have hbarherm : bar.IsHermitian := isHermitian_integral hint hherm
  have hQherm : Q.IsHermitian := by
    rw [Matrix.IsHermitian, hQ, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPiherm.eq]
  have hAherm : A.IsHermitian := by
    rw [Matrix.IsHermitian, hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQherm.eq,
      hbarherm.eq]
    simp only [Matrix.mul_assoc]
  have hQidem : Q * Q = Q := by
    have hexp : Q * Q = 1 - Pi - Pi + Pi * Pi := by rw [hQ]; noncomm_ring
    rw [hexp, hPiidem, hQ]
    abel
  have hPibar : Pi * bar = Pi := by
    rw [hbar, mul_integral hint]
    simp only [hsub]
    simp
  have hbarPi : bar * Pi = Pi := by
    rw [hbar, integral_mul hint]
    simp only [hsub']
    simp
  have hbartrace : bar.trace = (kappa : ℂ) := by
    rw [hbar, trace_integral hint]
    simp only [htrace]
    simp
  have hPitrace : Pi.trace = (Pi.rank : ℂ) := trace_eq_rank_of_isHermitian_idem hPiherm hPiidem
  have hAtrace : A.trace = (kappa : ℂ) - (Pi.rank : ℂ) := by
    rw [hA, hQ, trace_compression bar Pi hPiidem hPibar hbarPi, hbartrace, hPitrace]
  have hQtrace : Q.trace = (Fintype.card w : ℂ) - (Pi.rank : ℂ) := by
    rw [hQ, Matrix.trace_sub, Matrix.trace_one, hPitrace]
  have hQrank : Q.rank + Pi.rank = Fintype.card w := by
    have hQr : (Q.rank : ℂ) = (Fintype.card w : ℂ) - (Pi.rank : ℂ) := by
      rw [← trace_eq_rank_of_isHermitian_idem hQherm hQidem, hQtrace]
    have : ((Q.rank + Pi.rank : ℕ) : ℂ) = ((Fintype.card w : ℕ) : ℂ) := by
      push_cast
      rw [hQr]
      ring
    exact_mod_cast this
  have hArank : A.rank ≤ Q.rank := by
    have : A = Q * (bar * Q) := by rw [hA, Matrix.mul_assoc]
    rw [this]
    exact Matrix.rank_mul_le_left _ _
  have hpos : (0 : ℝ) < (Fintype.card w : ℝ) - (Pi.rank : ℝ) := by
    have : (Pi.rank : ℝ) < (Fintype.card w : ℝ) := by exact_mod_cast hd
    linarith
  have hkey : (kappa : ℝ) - (Pi.rank : ℝ) ≤ ((Fintype.card w : ℝ) - (Pi.rank : ℝ)) * ‖A‖ := by
    have hstep := trace_re_le_rank_mul_l2_opNorm hAherm
    have hAre : A.trace.re = (kappa : ℝ) - (Pi.rank : ℝ) := by
      rw [hAtrace]
      simp
    rw [hAre] at hstep
    refine le_trans hstep ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hQr : (Q.rank : ℝ) = (Fintype.card w : ℝ) - (Pi.rank : ℝ) := by
      have : ((Q.rank + Pi.rank : ℕ) : ℝ) = ((Fintype.card w : ℕ) : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hQrank
      push_cast at this
      linarith
    rw [← hQr]
    exact_mod_cast hArank
  rw [div_le_iff₀ hpos, mul_comm]
  exact hkey

/-- **Equation (23).**  At one replica the codimension ratio of the floor is the reciprocal of the
successor of the level count. -/
theorem oneReplica_floor_ratio (D : ℝ) (hD : 1 < D) :
    (D - 1) / (D ^ 2 - 1) = 1 / (D + 1) := by
  have h1 : D - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have h2 : D + 1 ≠ 0 := by intro h; linarith
  rw [show D ^ 2 - 1 = (D - 1) * (D + 1) by ring]
  field_simp

end GaloisForLFunctions.HTGeometry
