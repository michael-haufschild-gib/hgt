import GaloisForLFunctions.HTGeometry.SpectralInversionGauge

/-!
# The spectral affine gauge: precomposition with `w ↦ a w + b`

Precomposing a family with an invertible affine change of the spectral variable multiplies the
`k`-th jet by `a ^ k` and replaces the spectral variable by `(z - b) / a`, which is again a
polynomial.  So the substitution stays inside the jet ring and is invertible, its inverse being the
substitution of the inverse affine map.

Together with the spectral inversion gauge this covers every Mobius change of the spectral
variable.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

section ChainRule

variable {m : ℕ} {U V : Set ℂ} {g : Fin m → ℂ → ℂ}

/-- **The chain rule through an affine change of the spectral variable.** -/
theorem deriv_eval_fullJetVec_affine (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) {a b w : ℂ} (hwU : a * w + b ∈ U)
    (P : MvPolynomial (FullJetIndex m) ℂ) :
    deriv (fun v => MvPolynomial.eval (fullJetVec g (a * v + b)) P) w
      = a * MvPolynomial.eval (fullJetVec g (a * w + b)) (fullJetDerivation m P) := by
  have hF : DifferentiableAt ℂ (fun z => MvPolynomial.eval (fullJetVec g z) P) (a * w + b) :=
    differentiableAt_eval_fullJetVec hUo hg hwU P
  have haff : DifferentiableAt ℂ (fun v : ℂ => a * v + b) w :=
    ((differentiableAt_id).const_mul a).add_const b
  have hcomp : (fun v : ℂ => MvPolynomial.eval (fullJetVec g (a * v + b)) P)
      = (fun z => MvPolynomial.eval (fullJetVec g z) P) ∘ (fun v : ℂ => a * v + b) := rfl
  have hderiv : deriv (fun v : ℂ => a * v + b) w = a := by
    have hd : HasDerivAt (fun v : ℂ => a * v + b) a w := by
      simpa using ((hasDerivAt_id w).const_mul a).add_const b
    exact hd.deriv
  rw [hcomp, deriv_comp w hF haff, hderiv, deriv_eval_fullJetVec hUo hg hwU P]
  ring

/-- **The affinely composed jets.**  Every jet of `g i (a w + b)` is `a ^ k` times the corresponding
jet of `g i` at `a w + b`. -/
theorem iteratedDeriv_comp_affine_eq (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V) {a b : ℂ}
    (hVU : ∀ v ∈ V, a * v + b ∈ U) (i : Fin m) (k : ℕ) :
    ∀ w ∈ V, iteratedDeriv k (fun v => g i (a * v + b)) w
      = a ^ k * iteratedDeriv k (g i) (a * w + b) := by
  induction k with
  | zero =>
      intro w _
      rw [iteratedDeriv_zero, iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
      intro w hw
      have hEq : (fun v => iteratedDeriv k (fun u => g i (a * u + b)) v)
          =ᶠ[nhds w] fun v => MvPolynomial.eval (fullJetVec g (a * v + b))
            (MvPolynomial.C (a ^ k) * MvPolynomial.X (Sum.inr (i, k))) := by
        filter_upwards [hVo.mem_nhds hw] with v hv
        rw [ih v hv, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, fullJetVec_inr]
      rw [iteratedDeriv_succ, hEq.deriv_eq,
        deriv_eval_fullJetVec_affine hUo hg (hVU w hw)
          (MvPolynomial.C (a ^ k) * MvPolynomial.X (Sum.inr (i, k)))]
      have hD : fullJetDerivation m
          (MvPolynomial.C (a ^ k) * MvPolynomial.X (Sum.inr (i, k)))
          = MvPolynomial.C (a ^ k) * MvPolynomial.X (Sum.inr (i, k + 1)) := by
        have hC : fullJetDerivation m (MvPolynomial.C (a ^ k)) = 0 := by
          have hCa : (MvPolynomial.C (a ^ k) : MvPolynomial (FullJetIndex m) ℂ)
              = algebraMap ℂ (MvPolynomial (FullJetIndex m) ℂ) (a ^ k) := rfl
          rw [hCa]
          exact (fullJetDerivation m).map_algebraMap _
        have hX : fullJetDerivation m (MvPolynomial.X (Sum.inr (i, k)))
            = MvPolynomial.X (Sum.inr (i, k + 1)) := by
          rw [fullJetDerivation, jetLikeDerivation_X, fullJetShift, Sum.elim_inr]
        rw [Derivation.leibniz, hC, hX, smul_zero, add_zero, smul_eq_mul]
      rw [hD, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, fullJetVec_inr,
        iteratedDeriv_succ]
      ring

end ChainRule

/-- The substitution attached to precomposing a family with an affine change of the spectral
variable. -/
def affSubst (m : ℕ) (a b : ℂ) : FullJetIndex m → MvPolynomial (FullJetIndex m) ℂ :=
  Sum.elim (fun _ => MvPolynomial.C a⁻¹ * (MvPolynomial.X (Sum.inl ()) - MvPolynomial.C b))
    (fun p => MvPolynomial.C (a ^ p.2) * MvPolynomial.X (Sum.inr p))

/-- The affine substitution as an algebra homomorphism. -/
def affAlgHom (m : ℕ) (a b : ℂ) :
    MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ] MvPolynomial (FullJetIndex m) ℂ :=
  MvPolynomial.aeval (affSubst m a b)

/-- The affine substitution is invertible: the inverse map's substitution undoes it. -/
theorem affAlgHom_comp_inv (m : ℕ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (MvPolynomial.aeval (Sum.elim
        (fun _ => MvPolynomial.C a * MvPolynomial.X (Sum.inl ()) + MvPolynomial.C b)
        (fun p : Fin m × ℕ => MvPolynomial.C (a⁻¹ ^ p.2) * MvPolynomial.X (Sum.inr p)) :
      FullJetIndex m → MvPolynomial (FullJetIndex m) ℂ)).comp (affAlgHom m a b)
      = AlgHom.id ℂ (MvPolynomial (FullJetIndex m) ℂ) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with u | ⟨i, k⟩
  · simp only [AlgHom.comp_apply, affAlgHom, MvPolynomial.aeval_X, affSubst, Sum.elim_inl,
      map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Sum.elim_inl,
      AlgHom.id_apply, MvPolynomial.algebraMap_eq]
    rw [add_sub_cancel_right, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  · simp only [AlgHom.comp_apply, affAlgHom, MvPolynomial.aeval_X, affSubst, Sum.elim_inr,
      map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Sum.elim_inr, AlgHom.id_apply,
      MvPolynomial.algebraMap_eq]
    rw [← mul_assoc, ← map_mul, ← mul_pow, mul_inv_cancel₀ ha, one_pow, map_one, one_mul]

theorem affAlgHom_injective (m : ℕ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    Function.Injective (affAlgHom m a b) := by
  intro P Q hPQ
  have h := affAlgHom_comp_inv m ha b
  have hP := congrArg (fun F : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ]
    MvPolynomial (FullJetIndex m) ℂ => F P) h
  have hQ := congrArg (fun F : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ]
    MvPolynomial (FullJetIndex m) ℂ => F Q) h
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at hP hQ
  rw [← hP, ← hQ, hPQ]

/-- **Evaluating the affine substitution.**  It computes the jets of the affinely composed family. -/
theorem eval_affAlgHom {m : ℕ} {U V : Set ℂ} {g : Fin m → ℂ → ℂ} (hUo : IsOpen U)
    (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V) {a b : ℂ} (ha : a ≠ 0)
    (hVU : ∀ v ∈ V, a * v + b ∈ U) {w : ℂ} (hw : w ∈ V) (P : MvPolynomial (FullJetIndex m) ℂ) :
    MvPolynomial.eval (fullJetVec g (a * w + b)) (affAlgHom m a b P)
      = MvPolynomial.eval (fullJetVec (fun i v => g i (a * v + b)) w) P := by
  have hcomp : (MvPolynomial.aeval (fullJetVec g (a * w + b))).comp (affAlgHom m a b)
      = MvPolynomial.aeval (fullJetVec (fun i v => g i (a * v + b)) w) := by
    have hself : ∀ x : ℂ, algebraMap ℂ ℂ x = x := fun _ => rfl
    refine MvPolynomial.algHom_ext fun v => ?_
    rcases v with u | ⟨i, k⟩
    · simp only [AlgHom.comp_apply, affAlgHom, MvPolynomial.aeval_X, affSubst, Sum.elim_inl,
        map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X, fullJetVec_inl, hself]
      field_simp
      ring
    · simp only [AlgHom.comp_apply, affAlgHom, MvPolynomial.aeval_X, affSubst, Sum.elim_inr,
        map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, fullJetVec_inr, hself]
      exact (iteratedDeriv_comp_affine_eq hUo hg hVo hVU i k w hw).symm
  have happ := congrArg (fun F : MvPolynomial (FullJetIndex m) ℂ →ₐ[ℂ] ℂ => F P) hcomp
  simp only [AlgHom.comp_apply] at happ
  exact happ

/-- **Independence transports through an affine change of the spectral variable.** -/
theorem fullJet_independent_comp_affine {m : ℕ} {U V W : Set ℂ} (hUo : IsOpen U)
    {g : Fin m → ℂ → ℂ} (hg : ∀ i, ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) z) (hVo : IsOpen V)
    {a b : ℂ} (ha : a ≠ 0) (hVU : ∀ v ∈ V, a * v + b ∈ U) {chi : ℂ → ℂ}
    (hchi : ∀ w ∈ W, chi w ∈ V)
    (hind : ∀ Q : MvPolynomial (FullJetIndex m) ℂ,
      (∀ w ∈ W, MvPolynomial.eval (fullJetVec g (a * chi w + b)) Q = 0) → Q = 0)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ w ∈ W,
      MvPolynomial.eval (fullJetVec (fun i v => g i (a * v + b)) (chi w)) P = 0) :
    P = 0 := by
  refine affAlgHom_injective m ha b ?_
  rw [map_zero]
  refine hind (affAlgHom m a b P) fun w hw => ?_
  rw [eval_affAlgHom hUo hg hVo ha hVU (hchi w hw) P]
  exact hP w hw

end

end GaloisForLFunctions.HTGeometry
