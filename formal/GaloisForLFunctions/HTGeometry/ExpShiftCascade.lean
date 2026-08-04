import GaloisForLFunctions.HTGeometry.ShiftedExponentialCascade
import GaloisForLFunctions.HTGeometry.ExpAffineCascade

/-!
# Cascades of general first-order constant-coefficient maps

Every transcendental entire solution of a constant-coefficient first-order linear equation is
`f(w) = d + c·exp(a w + b)` with `a, c ≠ 0`, and it satisfies `f' = a·(f − d)`.  The cascade of such
maps has the derivative law

`(Y_{k+1})' = a_k·(Y_{k+1} − d_k)·(Y_k)'`,

which is the shifted model.  Its observability determinant is the scaled model's, translated, so the
unit-cost law holds for this whole four-parameter family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The shift carried by each state: none at the coordinate, `d k` at the state produced by `f k`. -/
noncomputable def stateShift (d : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | (k + 1) => d k

/-- The general first-order constant-coefficient entire maps. -/
noncomputable def expShift (a b c d : ℕ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun w => d k + c k * Complex.exp (a k * w + b k)

theorem differentiable_expShift (a b c d : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (expShift a b c d k) := by
  refine (differentiable_const (d k)).add ((differentiable_const (c k)).mul ?_)
  refine Complex.differentiable_exp.comp ?_
  exact ((differentiable_const (a k)).mul differentiable_id).add (differentiable_const (b k))

/-- **The defining first-order equation.** -/
theorem deriv_expShift (a b c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (expShift a b c d k) z = a k * (expShift a b c d k z - d k) := by
  have hinner : HasDerivAt (fun w : ℂ => a k * w + b k) (a k) z := by
    simpa using (((hasDerivAt_id z).const_mul (a k)).add_const (b k))
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (a k * w + b k))
      (Complex.exp (a k * z + b k) * a k) z := hinner.cexp
  have hall : HasDerivAt (expShift a b c d k)
      (c k * (Complex.exp (a k * z + b k) * a k)) z :=
    (hexp.const_mul (c k)).const_add (d k)
  rw [hall.deriv]
  simp [expShift]
  ring

theorem transcendentalEntire_expShift {a b c d : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hc : ∀ k, c k ≠ 0) (k : ℕ) : TranscendentalEntire (expShift a b c d k) := by
  have h1 : TranscendentalEntire (fun w : ℂ => Complex.exp (a k * w + b k)) :=
    transcendentalEntire_affine_precomp transcendentalEntire_exp (ha k)
  have h2 : TranscendentalEntire (fun w : ℂ => c k * Complex.exp (a k * w + b k)) :=
    transcendentalEntire_const_smul h1 (hc k)
  have h3 := transcendentalEntire_add_polynomial h2 (Polynomial.C (d k))
  have hfun : (fun w : ℂ => c k * Complex.exp (a k * w + b k) + (Polynomial.C (d k)).eval w)
      = expShift a b c d k := by
    funext w
    simp [expShift]
    ring
  rwa [hfun] at h3

theorem differentiallyAlgebraicOfOrder_one_expShift (a b c d : ℕ → ℂ) (k : ℕ) :
    DifferentiallyAlgebraicOfOrder (expShift a b c d k) 1 := by
  refine ⟨MvPolynomial.X 2 - MvPolynomial.C (a k) * MvPolynomial.X 1
      + MvPolynomial.C (a k * d k), ?_, ?_⟩
  · intro h0
    have h1 := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → ℂ)) h0
    have h2 := congrArg (MvPolynomial.eval (![0, 0, 0] : Fin 3 → ℂ)) h0
    have hv2 : (![0, 0, 1] : Fin 3 → ℂ) 2 = 1 := rfl
    have hv1 : (![0, 0, 1] : Fin 3 → ℂ) 1 = 0 := rfl
    have hw2 : (![0, 0, 0] : Fin 3 → ℂ) 2 = 0 := rfl
    have hw1 : (![0, 0, 0] : Fin 3 → ℂ) 1 = 0 := rfl
    simp only [map_add, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C,
      map_zero, hv2, hv1, hw2, hw1] at h1 h2
    have hone : (1 : ℂ) = 0 := by linear_combination h1 - h2
    exact one_ne_zero hone
  · intro z
    have h0 : iteratedDeriv 0 (expShift a b c d k) z = expShift a b c d k z := by
      simp [iteratedDeriv_zero]
    have h1 : iteratedDeriv 1 (expShift a b c d k) z
        = a k * (expShift a b c d k z - d k) := by
      rw [iteratedDeriv_one, deriv_expShift]
    simp only [map_add, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [show (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expShift a b c d k) z) :
        Fin 3 → ℂ) 2 = iteratedDeriv 1 (expShift a b c d k) z from rfl,
      show (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (expShift a b c d k) z) :
        Fin 3 → ℂ) 1 = iteratedDeriv 0 (expShift a b c d k) z from rfl, h0, h1]
    ring

theorem transHom_towerMonomial (e : ℕ → ℂ) (k : ℕ) :
    transHom e (towerMonomial k)
      = ∏ j ∈ Finset.Icc 1 k, (MvPolynomial.X j + MvPolynomial.C (e j)) := by
  rw [towerMonomial, map_prod]
  exact Finset.prod_congr rfl (fun j _ => transHom_X e j)

/-! ## The derivative law of the cascade -/

theorem differentiable_expShiftCascade (a b c d : ℕ → ℂ) (k : ℕ) :
    Differentiable ℂ (entireCascade (expShift a b c d) k) := by
  induction k with
  | zero => simp [entireCascade]
  | succ k ih =>
      have hfun : entireCascade (expShift a b c d) (k + 1)
          = fun z => expShift a b c d k (entireCascade (expShift a b c d) k z) := rfl
      rw [hfun]
      exact (differentiable_expShift a b c d k).comp ih

theorem deriv_expShiftCascade (a b c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expShift a b c d) k) z
      = scaleWeight a k *
        ∏ j ∈ Finset.Icc 1 k,
          (entireCascade (expShift a b c d) j z - stateShift d j) := by
  induction k with
  | zero => simp [entireCascade]
  | succ k ih =>
      have hd : HasDerivAt (entireCascade (expShift a b c d) k)
          (deriv (entireCascade (expShift a b c d) k) z) z :=
        ((differentiable_expShiftCascade a b c d k) z).hasDerivAt
      have hf : HasDerivAt (expShift a b c d k)
          (a k * (expShift a b c d k (entireCascade (expShift a b c d) k z) - d k))
          (entireCascade (expShift a b c d) k z) := by
        rw [← deriv_expShift]
        exact ((differentiable_expShift a b c d k) _).hasDerivAt
      have hcomp : HasDerivAt (fun w => expShift a b c d k (entireCascade (expShift a b c d) k w))
          (a k * (expShift a b c d k (entireCascade (expShift a b c d) k z) - d k) *
            deriv (entireCascade (expShift a b c d) k) z) z := hf.comp z hd
      have hfun : entireCascade (expShift a b c d) (k + 1)
          = fun w => expShift a b c d k (entireCascade (expShift a b c d) k w) := rfl
      have hval : deriv (entireCascade (expShift a b c d) (k + 1)) z
          = a k * (entireCascade (expShift a b c d) (k + 1) z - d k) *
            deriv (entireCascade (expShift a b c d) k) z := by
        rw [hfun]
        exact hcomp.deriv
      rw [hval, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1), scaleWeight_succ]
      have hshift : stateShift d (k + 1) = d k := rfl
      rw [hshift]
      ring

/-- **The cascade's derivative law is the shifted model derivation.** -/
theorem law_expShiftCascade (a b c d : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    deriv (entireCascade (expShift a b c d) k) z
      = evalAt (fun j => entireCascade (expShift a b c d) j) z
        (shiftedDerivation a (fun j => -(stateShift d j)) (MvPolynomial.X k)) := by
  rw [deriv_expShiftCascade, shiftedDerivation_X, scaledDerivation_X, map_mul, transHom_C,
    transHom_towerMonomial]
  simp only [evalAt, map_mul, map_prod, map_add, MvPolynomial.eval_X, MvPolynomial.eval_C]
  congr 1


/-! ## The order statement -/

theorem pderiv_zero_shiftedJet {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (e : ℕ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (i : ℕ) :
    (MvPolynomial.pderiv 0)
        (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N))
      = 0 := by
  rw [pderiv_iterate_shiftedDerivation, pderiv_zero_scaledJet ha hN i, map_zero]

/-- **No low-order equation for a constant-coefficient first-order cascade.** -/
theorem not_differentiallyAlgebraicOfOrder_expShift {a b c d : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hc : ∀ k, c k ≠ 0) (m : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder (entireCascade (expShift a b c d) (m + 1)) m := by
  classical
  set e : ℕ → ℂ := fun j => -(stateShift d j) with hedef
  set v : Fin (m + 2) → MvPolynomial ℕ ℂ :=
    Fin.cons (MvPolynomial.X (0 : ℕ))
      (fun j : Fin (m + 1) => modelJet (shiftedDerivation a e) (m + 1) (j : ℕ)) with hv
  set M : Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial ℕ ℂ) :=
    Matrix.of fun i j => (MvPolynomial.pderiv ((i : ℕ))) (v j) with hM
  have hrow0 : ∀ j : Fin (m + 2), M 0 j = if j = 0 then 1 else 0 := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simp [hM, hv]
    · intro l
      have hne : (Fin.succ l : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero l
      simp only [hM, hv, Matrix.of_apply, Fin.cons_succ, Fin.val_zero]
      rw [modelJet, pderiv_zero_shiftedJet ha e (by omega)]
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
              (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
                (MvPolynomial.X (m + 1))) := by
      funext i j
      simp [hM, hv, Fin.succAbove_zero, modelJet]
    rw [hsub]
    exact shifted_jet_det_ne_zero ha e m
  refine not_differentiallyAlgebraicOfOrder_of_model (δ := shiftedDerivation a e)
    (fun k => differentiable_expShiftCascade a b c d k)
    (fun k z => law_expShiftCascade a b c d k z)
    (fun Q hQ => exists_evalAt_ne_zero_of_transcendental
      (fun i => transcendentalEntire_expShift ha hc i) hQ) ?_ rfl
  refine algebraicIndependent_of_domain_jacobian (K := ℂ) (R := MvPolynomial ℕ ℂ)
    v (fun i => fun P => (MvPolynomial.pderiv ((i : ℕ))) P) ?_ ?_ ?_ M hdetM ?_
  · intro i x y; simp
  · intro i x y
    rw [Derivation.leibniz]
    simp
  · intro i γ
    have hγ : (algebraMap ℂ (MvPolynomial ℕ ℂ)) γ = MvPolynomial.C γ := rfl
    rw [hγ]
    simp
  · intro i j; rfl

/-- **The unit-cost law for constant-coefficient first-order cascades.**  For any `a_k, c_k ≠ 0` and
any `b_k, d_k`, the length-`n` cascade of `w ↦ d_k + c_k·exp(a_k w + b_k)` has differential order
exactly `n`.  Unconditional. -/
theorem exactDifferentialOrder_expShiftCascade {a b c d : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hc : ∀ k, c k ≠ 0) (m : ℕ) :
    ExactDifferentialOrder (entireCascade (expShift a b c d) (m + 1)) (m + 1) := by
  have hall : ∀ i : ℕ, TranscendentalEntire (expShift a b c d i) :=
    fun i => transcendentalEntire_expShift ha hc i
  have h1 : ∀ k, k < m + 1 → DifferentiallyAlgebraicOfOrder (expShift a b c d k) 1 :=
    fun k _ => differentiallyAlgebraicOfOrder_one_expShift a b c d k
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hall h1, ?_⟩
  intro k hk hDA
  exact not_differentiallyAlgebraicOfOrder_expShift ha hc m (hDA.mono (by omega : k ≤ m))


/-! ## The earlier families are specialisations -/

theorem expShift_one_zero_one_zero_eq_exp (k : ℕ) :
    expShift (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) k = Complex.exp := by
  funext w
  simp [expShift]

theorem expShift_eq_expAffine (a b : ℕ → ℂ) (k : ℕ) :
    expShift a b (fun _ => 1) (fun _ => 0) k = expAffine a b k := by
  funext w
  simp [expShift, expAffine]

/-- The exponential tower is the constant-coefficient family at its simplest parameters. -/
theorem expTower_eq_expShiftCascade (n : ℕ) :
    expTower n
      = entireCascade (expShift (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0)) n := by
  have hf : (fun _ : ℕ => Complex.exp)
      = expShift (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) := by
    funext k
    exact (expShift_one_zero_one_zero_eq_exp k).symm
  rw [expTower, hf]

end GaloisForLFunctions.HTGeometry
