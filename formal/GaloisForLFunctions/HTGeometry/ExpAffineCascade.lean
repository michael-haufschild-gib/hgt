import GaloisForLFunctions.HTGeometry.ScaledExponentialCascade
import GaloisForLFunctions.HTGeometry.ExactDifferentialOrderAffine
import GaloisForLFunctions.HTGeometry.TranscendentalEntireClosure

/-!
# The affine-exponential cascades

The maps `f_k(w) = exp(a_k w + b_k)` with `a_k ≠ 0` are transcendental entire and satisfy the
first-order equation `f' = a_k f`.  Their cascade's derivative law is therefore

`(Y_k)' = (∏_{j<k} a_j) · Y_1 ⋯ Y_k`,

which is exactly the scaled model derivation evaluated at the states.  The shifts `b_k` do not appear.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The affine-exponential constituent maps. -/
noncomputable def expAffine (a b : ℕ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun w => Complex.exp (a k * w + b k)

theorem differentiable_expAffine (a b : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (expAffine a b k) := by
  refine Complex.differentiable_exp.comp ?_
  exact ((differentiable_const (a k)).mul differentiable_id).add (differentiable_const (b k))

theorem transcendentalEntire_expAffine {a b : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (k : ℕ) :
    TranscendentalEntire (expAffine a b k) :=
  transcendentalEntire_affine_precomp transcendentalEntire_exp (ha k)

theorem expTower_one_eq_exp : expTower 1 = Complex.exp := by
  funext z
  simp

theorem exactDifferentialOrder_one_exp' : ExactDifferentialOrder Complex.exp 1 := by
  have h := exactDifferentialOrder_expTower 0
  rwa [expTower_one_eq_exp] at h

theorem differentiallyAlgebraicOfOrder_one_expAffine {a b : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (k : ℕ) :
    DifferentiallyAlgebraicOfOrder (expAffine a b k) 1 := by
  have h := (exactDifferentialOrder_affine_precomp (f := Complex.exp) (n := 1)
    (a := a k) (b := b k) (ha k)).mpr exactDifferentialOrder_one_exp'
  exact h.1

/-! ## The derivative law -/

theorem differentiable_expAffineCascade (a b : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (entireCascade (expAffine a b) k) := by
  induction k with
  | zero => simp [entireCascade]
  | succ k ih =>
      have hfun : entireCascade (expAffine a b) (k + 1)
          = fun z => expAffine a b k (entireCascade (expAffine a b) k z) := rfl
      rw [hfun]
      exact (differentiable_expAffine a b k).comp ih

/-- **The derivative law of an affine-exponential cascade.** -/
theorem deriv_expAffineCascade (a b : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expAffine a b) k) z
      = scaleWeight a k * ∏ j ∈ Finset.Icc 1 k, entireCascade (expAffine a b) j z := by
  induction k with
  | zero => simp [entireCascade]
  | succ k ih =>
      have hd : HasDerivAt (entireCascade (expAffine a b) k)
          (deriv (entireCascade (expAffine a b) k) z) z :=
        ((differentiable_expAffineCascade a b k) z).hasDerivAt
      have hinner : HasDerivAt
          (fun w => a k * entireCascade (expAffine a b) k w + b k)
          (a k * deriv (entireCascade (expAffine a b) k) z) z := by
        simpa using ((hd.const_mul (a k)).add_const (b k))
      have hc : HasDerivAt
          (fun w => Complex.exp (a k * entireCascade (expAffine a b) k w + b k))
          (Complex.exp (a k * entireCascade (expAffine a b) k z + b k) *
            (a k * deriv (entireCascade (expAffine a b) k) z)) z := hinner.cexp
      have hfun : entireCascade (expAffine a b) (k + 1)
          = fun w => Complex.exp (a k * entireCascade (expAffine a b) k w + b k) := rfl
      have hval : deriv (entireCascade (expAffine a b) (k + 1)) z
          = entireCascade (expAffine a b) (k + 1) z *
            (a k * deriv (entireCascade (expAffine a b) k) z) := by
        rw [hfun]
        exact hc.deriv
      rw [hval, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), scaleWeight_succ]
      ring

/-- **The cascade's derivative law is the scaled model derivation.** -/
theorem law_expAffineCascade (a b : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expAffine a b) k) z
      = evalAt (fun j => entireCascade (expAffine a b) j) z
        (scaledDerivation a (MvPolynomial.X k)) := by
  rw [deriv_expAffineCascade, scaledDerivation_X]
  simp [evalAt, towerMonomial, map_prod]


/-! ## The jets avoid the coordinate -/

theorem pderiv_zero_scaledJet {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) {N : ℕ} (hN : N ≠ 0) (i : ℕ) :
    (MvPolynomial.pderiv 0)
        (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N))
      = 0 := by
  have hCne : (MvPolynomial.C (a N) : MvPolynomial ℕ ℂ) ≠ 0 := by
    intro h
    exact ha N (MvPolynomial.C_eq_zero.mp h)
  have h1 := congrArg (MvPolynomial.pderiv (0 : ℕ)) (scaled_jet_eq a N i)
  rw [pderiv_C_mul, ← map_pow, pderiv_C_mul, pderiv_scaleHom,
    pderiv_zero_towerJet hN i, map_zero, mul_zero, mul_zero] at h1
  exact (mul_eq_zero.mp h1).resolve_left hCne

/-! ## The order statement -/

/-- **No low-order equation for an affine-exponential cascade.** -/
theorem not_differentiallyAlgebraicOfOrder_expAffine {a b : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (m : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder (entireCascade (expAffine a b) (m + 1)) m := by
  classical
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ))
      (fun j : Fin (m + 1) => modelJet (scaledDerivation a) (m + 1) (j : ℕ)) with hv
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ))) (v j) with hM
  have hrow0 : ∀ j : Fin (m + 2), M 0 j = if j = 0 then 1 else 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp [hM, hv]
    · intro l
      have hne : (Fin.succ l : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero l
      simp only [hM, hv, Matrix.of_apply, Fin.cons_succ, Fin.val_zero]
      rw [modelJet, pderiv_zero_scaledJet ha (by omega)]
      simp [hne]
  have hdetM : M.det ≠ 0 := by
    rw [Matrix.det_succ_row_zero]
    have hsum : ∑ j : Fin (m + 2), (-1) ^ (j : ℕ) * M 0 j *
        (M.submatrix Fin.succ j.succAbove).det
        = (M.submatrix Fin.succ (Fin.succAbove 0)).det := by
      rw [Finset.sum_eq_single (0 : Fin (m + 2))]
      · simp [hrow0]
      · intro j _ hj
        rw [hrow0 j]
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin (m + 2))) h
    rw [hsum]
    have hsub : M.submatrix Fin.succ (Fin.succAbove 0)
        = Matrix.of fun i j : Fin (m + 1) =>
            (MvPolynomial.pderiv ((i : ℕ) + 1))
              (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
                (MvPolynomial.X (m + 1))) := by
      funext i j
      simp [hM, hv, Fin.succAbove_zero, modelJet]
    rw [hsub]
    exact scaled_jet_det_ne_zero ha m
  refine not_differentiallyAlgebraicOfOrder_of_model (δ := scaledDerivation a)
    (fun k => differentiable_expAffineCascade a b k)
    (fun k z => law_expAffineCascade a b k z)
    (fun Q hQ => exists_evalAt_ne_zero_of_transcendental
      (fun i => transcendentalEntire_expAffine ha i) hQ) ?_ rfl
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) (R := MvPolynomial ℕ ℂ)
    v (fun i => fun P => (MvPolynomial.pderiv ((i : ℕ))) P) ?_ ?_ ?_ M hdetM ?_
  · intro i x y; simp
  · intro i x y
    rw [Derivation.leibniz]
    simp
  · intro i c
    have hc : (algebraMap ℂ (MvPolynomial ℕ ℂ)) c = MvPolynomial.C c := rfl
    rw [hc]
    simp
  · intro i j; rfl

/-- **The unit-cost law for affine-exponential cascades.**  For any nonzero linear parts `a_k` and any
shifts `b_k`, the length-`n` cascade of `w ↦ exp(a_k w + b_k)` has differential order exactly `n`.
Unconditional. -/
theorem exactDifferentialOrder_expAffineCascade {a b : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (expAffine a b) (m + 1)) (m + 1) := by
  have hall : ∀ i : ℕ, TranscendentalEntire (expAffine a b i) :=
    fun i => transcendentalEntire_expAffine ha i
  have h1 : ∀ k, k < m + 1 → DifferentiallyAlgebraicOfOrder (expAffine a b k) 1 :=
    fun k _ => differentiallyAlgebraicOfOrder_one_expAffine ha k
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1, ?_⟩
  intro k hk hDA
  exact not_differentiallyAlgebraicOfOrder_expAffine ha m (hDA.mono (by omega : k ≤ m))

end GaloisForLFunctions.HTGeometry
