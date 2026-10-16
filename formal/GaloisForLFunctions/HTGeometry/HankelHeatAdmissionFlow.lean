import GaloisForLFunctions.HTGeometry.HankelHeatToda
import GaloisForLFunctions.HTGeometry.MonicMomentAdmission
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The forced heat connection on canonical monic admission

For the moment flow `s'ₖ = -sₖ₊₁`, the moving monic admission has only
one lower orthogonal component. Its coefficient is the derivative of
the logarithmic derivative of the Hankel determinant. This formulation
is meromorphic and does not require positivity of the moment functional.
-/

open Filter Topology Matrix Polynomial
open scoped BigOperators

namespace HTGeometry
noncomputable section

theorem analyticAt_realMatrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ → Matrix ι ι ℝ} {a : ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) a) :
    AnalyticAt ℝ (fun t => (A t).det) a := by
  have he : (fun t => (A t).det) = fun t => ∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A t (σ i) i := by
    funext t
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl fun σ _ => by rw [Units.smul_def, zsmul_eq_mul]
  rw [he]
  exact Finset.analyticAt_fun_sum _ fun σ _ =>
    analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => hA (σ i) i)

theorem monicMomentAdmissionCoefficients_cramer (s : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    monicMomentAdmissionCoefficients s n i =
      -((momentHankelMatrix s n).updateCol i (momentHankelTail s n)).det /
        (momentHankelMatrix s n).det := by
  rw [monicMomentAdmissionCoefficients, Matrix.inv_def, Matrix.smul_mulVec,
    ← Matrix.cramer_eq_adjugate_mulVec]
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
    Ring.inverse_eq_inv]
  ring

theorem analyticAt_monicMomentAdmissionCoefficients
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k, AnalyticAt ℝ (fun t => s t k) a)
    {n : ℕ} (hn : (momentHankelMatrix (s a) n).det ≠ 0) (i : Fin n) :
    AnalyticAt ℝ (fun t => monicMomentAdmissionCoefficients (s t) n i) a := by
  simp_rw [monicMomentAdmissionCoefficients_cramer]
  refine (analyticAt_realMatrix_det ?_).neg.div
    (analyticAt_realMatrix_det fun j k => hs (j + k)) hn
  intro j k
  by_cases hk : k = i
  · subst k
    simpa only [Matrix.updateCol_self, momentHankelTail] using hs (j + n)
  · simpa only [Matrix.updateCol_ne hk, momentHankelMatrix] using hs (j + k)

theorem meromorphicAt_monicMomentAdmissionCoefficients
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k, AnalyticAt ℝ (fun t => s t k) a)
    (n : ℕ) (i : Fin n) :
    MeromorphicAt (fun t => monicMomentAdmissionCoefficients (s t) n i) a := by
  simp_rw [monicMomentAdmissionCoefficients_cramer]
  refine (analyticAt_realMatrix_det ?_).neg.meromorphicAt.div
    (analyticAt_realMatrix_det fun (j k : Fin n) => hs (j + k)).meromorphicAt
  intro j k
  by_cases hk : k = i
  · subst k
    simpa only [Matrix.updateCol_self, momentHankelTail] using hs (j + n)
  · simpa only [Matrix.updateCol_ne hk, momentHankelMatrix] using hs (j + k)

theorem monicMomentAdmissionPolynomial_coeff_lt (s : ℕ → ℝ) {n i : ℕ} (hi : i < n) :
    (monicMomentAdmissionPolynomial s n).coeff i =
      monicMomentAdmissionCoefficients s n ⟨i, hi⟩ := by
  rw [monicMomentAdmissionPolynomial_eq, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, if_neg (Nat.ne_of_lt hi),
    Polynomial.ofFn_coeff_eq_val_of_lt _ hi, zero_add]

@[simp] theorem monicMomentAdmissionPolynomial_coeff_self (s : ℕ → ℝ) (n : ℕ) :
    (monicMomentAdmissionPolynomial s n).coeff n = 1 := by
  simpa only [monicMomentAdmissionPolynomial_natDegree] using
    (monicMomentAdmissionPolynomial_monic s n).coeff_natDegree

theorem monicMomentAdmissionPolynomial_coeff_gt (s : ℕ → ℝ) {n i : ℕ} (hi : n < i) :
    (monicMomentAdmissionPolynomial s n).coeff i = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simpa only [monicMomentAdmissionPolynomial_natDegree] using hi

theorem monicMomentAdmissionPolynomial_coeff_fin (s : ℕ → ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    (monicMomentAdmissionPolynomial s n).coeff i = monicMomentAdmissionVector s n i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.val_castSucc, monicMomentAdmissionVector_castSucc]
    exact monicMomentAdmissionPolynomial_coeff_lt s j.isLt

theorem analyticAt_monicMomentAdmissionPolynomial_coeff
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k, AnalyticAt ℝ (fun t => s t k) a)
    {n : ℕ} (hn : (momentHankelMatrix (s a) n).det ≠ 0) (i : ℕ) :
    AnalyticAt ℝ (fun t => (monicMomentAdmissionPolynomial (s t) n).coeff i) a := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · simp_rw [monicMomentAdmissionPolynomial_coeff_lt _ hi]
    exact analyticAt_monicMomentAdmissionCoefficients hs hn _
  · simp only [monicMomentAdmissionPolynomial_coeff_self]
    exact analyticAt_const
  · simp_rw [monicMomentAdmissionPolynomial_coeff_gt _ hi]
    exact analyticAt_const

theorem meromorphicAt_monicMomentAdmissionPolynomial_coeff
    {s : ℝ → ℕ → ℝ} {a : ℝ} (hs : ∀ k, AnalyticAt ℝ (fun t => s t k) a)
    (n i : ℕ) :
    MeromorphicAt (fun t => (monicMomentAdmissionPolynomial (s t) n).coeff i) a := by
  rcases lt_trichotomy i n with hi | rfl | hi
  · simp_rw [monicMomentAdmissionPolynomial_coeff_lt _ hi]
    exact meromorphicAt_monicMomentAdmissionCoefficients hs n _
  · simp only [monicMomentAdmissionPolynomial_coeff_self]
    exact MeromorphicAt.const _ _
  · simp_rw [monicMomentAdmissionPolynomial_coeff_gt _ hi]
    exact MeromorphicAt.const _ _

/-- The subleading coefficient is the heat logarithmic determinant derivative. -/
theorem monicMomentAdmissionCoefficients_last_eq_logDeriv
    {s : ℝ → ℕ → ℝ} {a : ℝ}
    (hs : ∀ k, HasDerivAt (fun t => s t k) (-s a (k + 1)) a) (n : ℕ) :
    monicMomentAdmissionCoefficients (s a) (n + 1) (Fin.last n) =
      logDeriv (fun t => (momentHankelMatrix (s t) (n + 1)).det) a := by
  have hd := hasDerivAt_hankelBorderMatrix_zero hs n 0
  simp only [hankelBorderMatrix_zero_zero] at hd
  rw [logDeriv_apply, hd.deriv, monicMomentAdmissionCoefficients_cramer]
  congr 2
  rw [← hankelBorderMatrix_transpose (s a) n 0 1, Matrix.det_transpose]
  congr 1
  ext i j
  by_cases hj : j = Fin.last n
  · subst j
    simp [hankelBorderMatrix, Matrix.updateCol_self, momentHankelTail]
  · simp only [hankelBorderMatrix, hankelBorderIndex_zero]
    simp [hankelBorderIndex, hj, Matrix.updateCol_ne, momentHankelMatrix]

/-- The first `n` orthogonality equations determine a vector up to its
terminal coordinate, even when that coordinate is zero. -/
theorem eq_smul_monicMomentAdmissionVector_of_lower_orthogonal
    {s : ℕ → ℝ} {n : ℕ} (hn : (momentHankelMatrix s n).det ≠ 0)
    (v : Fin (n + 1) → ℝ)
    (hv : ∀ i : Fin n, ∑ j : Fin (n + 1), s (i + j) * v j = 0) :
    v = v (Fin.last n) • monicMomentAdmissionVector s n := by
  have he : (fun j : Fin n => v j.castSucc) =
      v (Fin.last n) • monicMomentAdmissionCoefficients s n := by
    apply Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn))
    rw [Matrix.mulVec_smul, momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hn]
    funext i
    have h := hv i
    rw [Fin.sum_univ_castSucc] at h
    simp only [Fin.val_castSucc, Fin.val_last] at h
    change (∑ j : Fin n, s (i + j) * v j.castSucc) = _
    simp only [Pi.smul_apply, Pi.neg_apply, momentHankelTail, smul_eq_mul]
    linarith
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa only [Pi.smul_apply, monicMomentAdmissionVector_castSucc] using congrFun he j

/-- Differentiate the lower moment equations. Their shifted source terms
cancel, forcing the velocity into the preceding admission line. -/
theorem deriv_monicMomentAdmissionCoefficients
    {s : ℝ → ℕ → ℝ} {a : ℝ}
    (hs : ∀ k, AnalyticAt ℝ (fun t => s t k) a)
    (hd : ∀ k, HasDerivAt (fun t => s t k) (-s a (k + 1)) a)
    {n : ℕ} (hn : (momentHankelMatrix (s a) n).det ≠ 0)
    (hn1 : (momentHankelMatrix (s a) (n + 1)).det ≠ 0) :
    (fun j => deriv (fun t => monicMomentAdmissionCoefficients (s t) (n + 1) j) a) =
      deriv (fun t => monicMomentAdmissionCoefficients (s t) (n + 1) (Fin.last n)) a •
        monicMomentAdmissionVector (s a) n := by
  apply eq_smul_monicMomentAdmissionVector_of_lower_orthogonal hn
  intro i
  have he : ∀ᶠ t in 𝓝 a,
      (∑ j : Fin (n + 1), s t (i + j) *
        monicMomentAdmissionCoefficients (s t) (n + 1) j) + s t (i + (n + 1)) = 0 := by
    have hnear := (analyticAt_realMatrix_det fun (j k : Fin (n + 1)) =>
      hs (j + k)).continuousAt.eventually_ne hn1
    filter_upwards [hnear] with t ht
    have h := congrFun (momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients ht)
      i.castSucc
    simpa only [Matrix.mulVec, dotProduct, momentHankelMatrix,
      momentHankelTail, Fin.val_castSucc, Pi.neg_apply, add_eq_zero_iff_eq_neg] using h
  have hc (j : Fin (n + 1)) :=
    (analyticAt_monicMomentAdmissionCoefficients hs hn1 j).differentiableAt.hasDerivAt
  have hder := ((HasDerivAt.fun_sum (u := Finset.univ)
    fun (j : Fin (n + 1)) _ => (hd (i + j)).mul (hc j)).add
    (hd (i + (n + 1))))
  have hzero := hder.unique ((hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq he)
  have hshift := congrFun (momentHankelMatrix_mulVec_monicMomentAdmissionCoefficients hn1)
    i.succ
  simp only [Matrix.mulVec, dotProduct, momentHankelMatrix, momentHankelTail,
    Fin.val_succ, Pi.neg_apply] at hshift
  have hshift' : (∑ j : Fin (n + 1), s a (i + j + 1) *
      monicMomentAdmissionCoefficients (s a) (n + 1) j) = -s a (i + (n + 1) + 1) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hshift
  simp only [Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib] at hzero
  rw [hshift'] at hzero
  linarith

end
end HTGeometry
