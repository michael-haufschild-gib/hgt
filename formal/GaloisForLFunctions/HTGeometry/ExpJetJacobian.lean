import GaloisForLFunctions.HTGeometry.ExpJetPolynomial
import GaloisForLFunctions.HTGeometry.LeibnizJetMatrix

/-!
# The jet map of an exponential is a submersion

Truncating the exponential jet polynomials at order `m` gives an explicit map
`v ↦ (exp(v_0)·B_l(v))_{l<m}` from the jets of an exponent to the jets of its exponential.  Its
Jacobian is triangular with constant diagonal `exp(v_0)`, because `B_l` is the top jet variable plus
terms of lower level and involves no zeroth jet variable.  So the map is a submersion everywhere,
which is what transports a codimension bound from the jets of a source to the jets of a gauge.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Linear functionals on a finite jet space -/

/-- A linear functional on the truncated jet space, given by its coefficient vector. -/
def dotLin (m : ℕ) (a : Fin m → ℂ) : (Fin m → ℂ) →ₗ[ℂ] ℂ where
  toFun w := ∑ k, a k * w k
  map_add' := by
    intro x y
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The same functional, as a continuous linear map. -/
def dotCLM (m : ℕ) (a : Fin m → ℂ) : (Fin m → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (dotLin m a)

@[simp] theorem dotCLM_apply (m : ℕ) (a w : Fin m → ℂ) :
    dotCLM m a w = ∑ k, a k * w k := rfl

theorem dotCLM_add (m : ℕ) (a b : Fin m → ℂ) :
    dotCLM m (a + b) = dotCLM m a + dotCLM m b := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [dotCLM_apply, ContinuousLinearMap.add_apply, dotCLM_apply, dotCLM_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp [add_mul]

theorem dotCLM_zero (m : ℕ) : dotCLM m 0 = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  simp

theorem hasFDerivAt_dotCLM (m : ℕ) (a v : Fin m → ℂ) :
    HasFDerivAt (fun w : Fin m → ℂ => ∑ k, a k * w k) (dotCLM m a) v :=
  (dotCLM m a).hasFDerivAt

/-! ### Evaluating a jet polynomial on a truncated jet vector -/

/-- A finite jet vector, read as a full jet vector by padding with zeros. -/
def expJetJacobianExtend (m : ℕ) (w : Fin m → ℂ) : ℕ → ℂ := fun k => if h : k < m then w ⟨k, h⟩ else 0

theorem expJetJacobianExtend_apply_lt {m : ℕ} (w : Fin m → ℂ) {k : ℕ} (h : k < m) :
    expJetJacobianExtend m w k = w ⟨k, h⟩ := dif_pos h

/-- The coefficient vector of one jet slot, zero above the truncation. -/
def jetCoordVec (m j : ℕ) : Fin m → ℂ := fun k => if (k : ℕ) = j then 1 else 0

theorem dot_jetCoordVec (m j : ℕ) (w : Fin m → ℂ) :
    ∑ k, jetCoordVec m j k * w k = expJetJacobianExtend m w j := by
  classical
  unfold jetCoordVec expJetJacobianExtend
  by_cases h : j < m
  · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin m)]
    · simp
    · intro b _ hb
      have hbj : (b : ℕ) ≠ j := fun hbj => hb (Fin.ext hbj)
      simp [hbj]
    · intro hcon
      exact absurd (Finset.mem_univ (⟨j, h⟩ : Fin m)) hcon
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hkj : (k : ℕ) ≠ j := fun hkj => h (hkj ▸ k.2)
    simp [hkj]

theorem hasFDerivAt_expJetJacobianExtend_coord (m j : ℕ) (v : Fin m → ℂ) :
    HasFDerivAt (fun w : Fin m → ℂ => expJetJacobianExtend m w j) (dotCLM m (jetCoordVec m j)) v := by
  have hfun : (fun w : Fin m → ℂ => expJetJacobianExtend m w j)
      = fun w : Fin m → ℂ => ∑ k, jetCoordVec m j k * w k := by
    funext w
    rw [dot_jetCoordVec]
  rw [hfun]
  exact hasFDerivAt_dotCLM m (jetCoordVec m j) v

/-- The gradient coefficient vector of a jet polynomial on the truncated jet space. -/
def jetGradVec (m : ℕ) (P : MvPolynomial ℕ ℂ) (v : Fin m → ℂ) : Fin m → ℂ :=
  fun k => MvPolynomial.eval (expJetJacobianExtend m v) (MvPolynomial.pderiv (k : ℕ) P)

theorem contDiff_evalJetExtend (m : ℕ) (P : MvPolynomial ℕ ℂ) :
    ContDiff ℂ ⊤ (fun w : Fin m → ℂ => MvPolynomial.eval (expJetJacobianExtend m w) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const (c := a) (𝕜 := ℂ) (E := (Fin m → ℂ))
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P j hP =>
      have hcoord : ContDiff ℂ ⊤ (fun w : Fin m → ℂ => expJetJacobianExtend m w j) := by
        have hfun : (fun w : Fin m → ℂ => expJetJacobianExtend m w j)
            = fun w : Fin m → ℂ => ∑ k, jetCoordVec m j k * w k := by
          funext w
          rw [dot_jetCoordVec]
        rw [hfun]
        exact (dotCLM m (jetCoordVec m j)).contDiff
      simpa only [map_mul, MvPolynomial.eval_X] using hP.mul hcoord

/-- **The gradient of a jet polynomial on the truncated jet space.** -/
theorem hasFDerivAt_evalJetExtend (m : ℕ) (P : MvPolynomial ℕ ℂ) (v : Fin m → ℂ) :
    HasFDerivAt (fun w : Fin m → ℂ => MvPolynomial.eval (expJetJacobianExtend m w) P)
      (dotCLM m (jetGradVec m P v)) v := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hz : jetGradVec m (MvPolynomial.C a) v = 0 := by
        funext k
        rw [jetGradVec, MvPolynomial.pderiv_C, map_zero]
        rfl
      rw [hz, dotCLM_zero]
      simpa only [MvPolynomial.eval_C] using (hasFDerivAt_const a v)
  | add P Q hP hQ =>
      have hsum : jetGradVec m (P + Q) v = jetGradVec m P v + jetGradVec m Q v := by
        funext k
        rw [jetGradVec, map_add, map_add]
        rfl
      have hfun : (fun w : Fin m → ℂ => MvPolynomial.eval (expJetJacobianExtend m w) (P + Q))
          = fun w : Fin m → ℂ => MvPolynomial.eval (expJetJacobianExtend m w) P
              + MvPolynomial.eval (expJetJacobianExtend m w) Q := by
        funext w
        rw [map_add]
      rw [hsum, dotCLM_add, hfun]
      exact hP.add hQ
  | mul_X P j hP =>
      have hcoord := hasFDerivAt_expJetJacobianExtend_coord m j v
      have hmul := hP.mul hcoord
      have hfun : (fun w : Fin m → ℂ => MvPolynomial.eval (expJetJacobianExtend m w) (P * MvPolynomial.X j))
          = fun w : Fin m → ℂ =>
            MvPolynomial.eval (expJetJacobianExtend m w) P * expJetJacobianExtend m w j := by
        funext w
        rw [map_mul, MvPolynomial.eval_X]
      rw [hfun]
      refine hmul.congr_fderiv ?_
      refine (ContinuousLinearMap.ext fun w => ?_).symm
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, dotCLM_apply, dotCLM_apply, dotCLM_apply]
      have hpd : ∀ k : Fin m, jetGradVec m (P * MvPolynomial.X j) v k
          = jetGradVec m P v k * expJetJacobianExtend m v j
            + MvPolynomial.eval (expJetJacobianExtend m v) P * jetCoordVec m j k := by
        intro k
        rw [jetGradVec, jetGradVec, jetCoordVec, MvPolynomial.pderiv_mul, map_add, map_mul,
          map_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_X]
        by_cases h : (k : ℕ) = j
        · rw [h, Pi.single_eq_same, if_pos rfl]
          simp
        · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]
          simp
      simp only [hpd, add_mul]
      rw [Finset.sum_add_distrib]
      have h1 : ∑ k : Fin m, jetGradVec m P v k * expJetJacobianExtend m v j * w k
          = (∑ k : Fin m, jetGradVec m P v k * w k) * expJetJacobianExtend m v j := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      have h2 : ∑ k : Fin m,
            MvPolynomial.eval (expJetJacobianExtend m v) P * jetCoordVec m j k * w k
          = MvPolynomial.eval (expJetJacobianExtend m v) P * ∑ k : Fin m, jetCoordVec m j k * w k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [h1, h2, dot_jetCoordVec]
      simp only [smul_eq_mul]
      ring

/-! ### The truncated exponential jet map -/

/-- The jets of an exponential, as a function of the jets of its exponent. -/
def expJetMap (m : ℕ) (v : Fin m → ℂ) : Fin m → ℂ :=
  fun l => Complex.exp (expJetJacobianExtend m v 0) *
    MvPolynomial.eval (expJetJacobianExtend m v) (expJetPoly (l : ℕ))

theorem contDiff_expJetMap (m : ℕ) : ContDiff ℂ ⊤ (expJetMap m) := by
  rw [contDiff_pi]
  intro l
  refine ContDiff.mul ?_ (contDiff_evalJetExtend m (expJetPoly (l : ℕ)))
  refine Complex.contDiff_exp.comp ?_
  have hfun : (fun w : Fin m → ℂ => expJetJacobianExtend m w 0)
      = fun w : Fin m → ℂ => ∑ k, jetCoordVec m 0 k * w k := by
    funext w
    rw [dot_jetCoordVec]
  rw [hfun]
  exact (dotCLM m (jetCoordVec m 0)).contDiff

theorem contDiff_real_expJetMap (m : ℕ) : ContDiff ℝ ⊤ (expJetMap m) :=
  (contDiff_expJetMap m).restrict_scalars ℝ

/-- A zeroth partial derivative kills the jet subalgebra. -/
theorem pderiv_zero_eq_zero_of_mem_jetSub {l : ℕ} {B : MvPolynomial ℕ ℂ}
    (hB : B ∈ jetSub l) : MvPolynomial.pderiv 0 B = 0 := by
  induction hB using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨i, ⟨h1, _⟩, rfl⟩ := hx
      rw [MvPolynomial.pderiv_X]
      exact Pi.single_eq_of_ne (by omega) _
  | algebraMap r =>
      have hC : (algebraMap ℂ (MvPolynomial ℕ ℂ) r) = MvPolynomial.C r := rfl
      rw [hC, MvPolynomial.pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [MvPolynomial.pderiv_mul, hx, hy, mul_zero, zero_mul, add_zero]

/-- No exponential jet polynomial involves the zeroth jet variable. -/
theorem pderiv_zero_expJetPoly (l : ℕ) : MvPolynomial.pderiv 0 (expJetPoly l) = 0 :=
  pderiv_zero_eq_zero_of_mem_jetSub (expJetPoly_mem_jetSub l)

/-- The Jacobian of the truncated exponential jet map. -/
def expJetJacobian (m : ℕ) (v : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun l k => Complex.exp (expJetJacobianExtend m v 0) *
    (MvPolynomial.eval (expJetJacobianExtend m v) (expJetPoly (l : ℕ)) * jetCoordVec m 0 k
      + jetGradVec m (expJetPoly (l : ℕ)) v k)

/-- The Jacobian as a continuous linear map. -/
def expJetJacobianCLM (m : ℕ) (v : Fin m → ℂ) : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun l => dotCLM m (expJetJacobian m v l)

theorem expJetJacobianCLM_apply (m : ℕ) (v w : Fin m → ℂ) :
    expJetJacobianCLM m v w = (expJetJacobian m v).mulVec w := by
  funext l
  rw [expJetJacobianCLM, ContinuousLinearMap.pi_apply, dotCLM_apply, Matrix.mulVec, dotProduct]

theorem hasFDerivAt_expJetMap (m : ℕ) (v : Fin m → ℂ) :
    HasFDerivAt (expJetMap m) (expJetJacobianCLM m v) v := by
  classical
  refine hasFDerivAt_pi.mpr fun l => ?_
  have hexp : HasFDerivAt (fun w : Fin m → ℂ => Complex.exp (expJetJacobianExtend m w 0))
      (Complex.exp (expJetJacobianExtend m v 0) • dotCLM m (jetCoordVec m 0)) v :=
    (hasFDerivAt_expJetJacobianExtend_coord m 0 v).cexp
  have hpoly := hasFDerivAt_evalJetExtend m (expJetPoly (l : ℕ)) v
  have hmul := hexp.mul hpoly
  refine hmul.congr_fderiv ?_
  refine (ContinuousLinearMap.ext fun w => ?_).symm
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    dotCLM_apply, dotCLM_apply, dotCLM_apply]
  simp only [expJetJacobian, smul_eq_mul]
  have hL : ∀ x : Fin m,
      Complex.exp (expJetJacobianExtend m v 0) *
          (MvPolynomial.eval (expJetJacobianExtend m v) (expJetPoly (l : ℕ)) * jetCoordVec m 0 x
            + jetGradVec m (expJetPoly (l : ℕ)) v x) * w x
        = MvPolynomial.eval (expJetJacobianExtend m v) (expJetPoly (l : ℕ))
              * Complex.exp (expJetJacobianExtend m v 0) * (jetCoordVec m 0 x * w x)
          + Complex.exp (expJetJacobianExtend m v 0) * (jetGradVec m (expJetPoly (l : ℕ)) v x * w x) :=
    fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => hL x), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

theorem expJetJacobian_blockTriangular (m : ℕ) (v : Fin m → ℂ) :
    (expJetJacobian m v).BlockTriangular (⇑OrderDual.toDual) := by
  intro l k hlk
  have hlt : (l : ℕ) < (k : ℕ) := by
    simpa [OrderDual.toDual_lt_toDual] using hlk
  have hk0 : (k : ℕ) ≠ 0 := by omega
  have hcoord : jetCoordVec m 0 k = 0 := by
    rw [jetCoordVec, if_neg hk0]
  have hgrad : jetGradVec m (expJetPoly (l : ℕ)) v k = 0 := by
    rw [jetGradVec, pderiv_expJetPoly_eq_zero hlt, map_zero]
  rw [expJetJacobian, hcoord, hgrad]
  simp

theorem expJetJacobian_diag (m : ℕ) (v : Fin m → ℂ) (l : Fin m) :
    expJetJacobian m v l l = Complex.exp (expJetJacobianExtend m v 0) := by
  rcases Nat.eq_zero_or_pos (l : ℕ) with hl | hl
  · have hcoord : jetCoordVec m 0 l = 1 := by rw [jetCoordVec, if_pos hl]
    have hgrad : jetGradVec m (expJetPoly (l : ℕ)) v l = 0 := by
      rw [jetGradVec, hl, pderiv_zero_expJetPoly, map_zero]
    rw [expJetJacobian, hcoord, hgrad, hl]
    simp
  · have hcoord : jetCoordVec m 0 l = 0 := by rw [jetCoordVec, if_neg (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, (l : ℕ) = j + 1 := ⟨(l : ℕ) - 1, by omega⟩
    have hgrad : jetGradVec m (expJetPoly (l : ℕ)) v l = 1 := by
      rw [jetGradVec, hj, pderiv_expJetPoly_self, map_one]
    rw [expJetJacobian, hcoord, hgrad]
    simp

theorem det_expJetJacobian (m : ℕ) (v : Fin m → ℂ) :
    (expJetJacobian m v).det = Complex.exp (expJetJacobianExtend m v 0) ^ m := by
  rw [Matrix.det_of_lowerTriangular _ (expJetJacobian_blockTriangular m v)]
  rw [Finset.prod_congr rfl (fun l _ => expJetJacobian_diag m v l)]
  simp

theorem det_expJetJacobian_ne_zero (m : ℕ) (v : Fin m → ℂ) :
    (expJetJacobian m v).det ≠ 0 := by
  rw [det_expJetJacobian]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

theorem surjective_mulVec_of_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.det ≠ 0) : Function.Surjective A.mulVec := by
  intro y
  refine ⟨A⁻¹.mulVec y, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    Matrix.one_mulVec]

/-- **The truncated exponential jet map is a submersion.** -/
theorem surjective_fderiv_expJetMap (m : ℕ) (v : Fin m → ℂ) :
    Function.Surjective (fderiv ℝ (expJetMap m) v) := by
  have hR := (hasFDerivAt_expJetMap m v).restrictScalars ℝ
  rw [hR.fderiv]
  intro y
  obtain ⟨w, hw⟩ := surjective_mulVec_of_det_ne_zero (det_expJetJacobian_ne_zero m v) y
  refine ⟨w, ?_⟩
  show expJetJacobianCLM m v w = y
  rw [expJetJacobianCLM_apply, hw]

end

end GaloisForLFunctions.HTGeometry
