import GaloisForLFunctions.HTGeometry.ScaledExponentialCascade

/-!
# Exponential cascades with shifts

A transcendental entire solution of a constant-coefficient first-order linear equation is
`f(w) = d + c·exp(a w)`, and `f' = a·(f − d)`.  The cascade of such maps therefore satisfies

`δ Y_{k+1} = a_k·(Y_{k+1} − e_{k+1})·δ Y_k`,

which is the scaled model translated by the shifts.  Translation is an automorphism of the polynomial
ring commuting with every partial derivative, so the scaled model's observability determinant
transports unchanged.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The translation automorphism of the model. -/
noncomputable def transHom (e : ℕ → ℂ) : MvPolynomial ℕ ℂ →ₐ[ℂ] MvPolynomial ℕ ℂ :=
  MvPolynomial.aeval fun k => MvPolynomial.X k + MvPolynomial.C (e k)

@[simp] theorem transHom_X (e : ℕ → ℂ) (k : ℕ) :
    transHom e (MvPolynomial.X k) = MvPolynomial.X k + MvPolynomial.C (e k) := by
  simp [transHom]

@[simp] theorem transHom_C (e : ℕ → ℂ) (c : ℂ) :
    transHom e (MvPolynomial.C c) = MvPolynomial.C c := MvPolynomial.aeval_C _ _

theorem transHom_injective (e : ℕ → ℂ) : Function.Injective (transHom e) := by
  have hcomp : (transHom (fun k => -(e k))).comp (transHom e)
      = AlgHom.id ℂ (MvPolynomial ℕ ℂ) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, transHom_X, map_add, transHom_C, AlgHom.id_apply]
    rw [map_neg]
    ring
  intro x y hxy
  have h := congrArg (transHom (fun k => -(e k))) hxy
  rw [show (transHom (fun k => -(e k))) (transHom e x)
      = ((transHom (fun k => -(e k))).comp (transHom e)) x from rfl,
    show (transHom (fun k => -(e k))) (transHom e y)
      = ((transHom (fun k => -(e k))).comp (transHom e)) y from rfl, hcomp] at h
  simpa using h

/-- **Translation commutes with the partial derivatives.** -/
theorem pderiv_transHom (e : ℕ → ℂ) (k : ℕ) (P : MvPolynomial ℕ ℂ) :
    (MvPolynomial.pderiv k) (transHom e P) = transHom e ((MvPolynomial.pderiv k) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p j hp =>
      rw [map_mul, transHom_X, Derivation.leibniz, hp, Derivation.leibniz]
      by_cases hkj : k = j
      · subst hkj
        simp only [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_C, smul_eq_mul, map_add,
          map_mul, transHom_X, map_one, add_zero]
      · simp only [MvPolynomial.pderiv_X_of_ne (Ne.symm hkj), MvPolynomial.pderiv_C, smul_eq_mul,
          map_add, map_mul, transHom_X, mul_zero, add_zero, zero_add]

/-- The model derivation of a shifted exponential cascade. -/
noncomputable def shiftedDerivation (a e : ℕ → ℂ) :
    Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ fun k => transHom e (scaledDerivation a (MvPolynomial.X k))

@[simp] theorem shiftedDerivation_X (a e : ℕ → ℂ) (k : ℕ) :
    shiftedDerivation a e (MvPolynomial.X k)
      = transHom e (scaledDerivation a (MvPolynomial.X k)) :=
  MvPolynomial.mkDerivation_X ℂ _ k

/-- **The translation conjugates the scaled model into the shifted one.** -/
theorem shiftedDerivation_transHom (a e : ℕ → ℂ) (P : MvPolynomial ℕ ℂ) :
    shiftedDerivation a e (transHom e P) = transHom e (scaledDerivation a P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [transHom_C,
        show (MvPolynomial.C c : MvPolynomial ℕ ℂ) = algebraMap ℂ (MvPolynomial ℕ ℂ) c from rfl,
        (shiftedDerivation a e).map_algebraMap, (scaledDerivation a).map_algebraMap, map_zero]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p k hp =>
      have hc : shiftedDerivation a e (MvPolynomial.C (e k)) = 0 := by
        rw [show (MvPolynomial.C (e k) : MvPolynomial ℕ ℂ)
          = algebraMap ℂ (MvPolynomial ℕ ℂ) (e k) from rfl]
        exact (shiftedDerivation a e).map_algebraMap _
      rw [map_mul, transHom_X, Derivation.leibniz, map_add, hc, add_zero, hp,
        Derivation.leibniz]
      simp only [smul_eq_mul, map_add, map_mul, transHom_X, shiftedDerivation_X]

/-- **The conjugation on jets.** -/
theorem iterate_shiftedDerivation_transHom (a e : ℕ → ℂ) (P : MvPolynomial ℕ ℂ) (i : ℕ) :
    ((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (transHom e P)
      = transHom e (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) P) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, shiftedDerivation_transHom,
        Function.iterate_succ_apply']

/-- **The shifted jets are the scaled jets, translated.**  The two differ by a constant, which the
jets kill above order zero and the partial derivatives kill at order zero. -/
theorem pderiv_iterate_shiftedDerivation (a e : ℕ → ℂ) (k N i : ℕ) :
    (MvPolynomial.pderiv k)
        (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N))
      = transHom e ((MvPolynomial.pderiv k)
          (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
            (MvPolynomial.X N))) := by
  have hsplit : ((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
      (MvPolynomial.X N + MvPolynomial.C (e N))
      = ((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N)
        + ((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
          (MvPolynomial.C (e N)) := by
    induction i with
    | zero => simp
    | succ l ihl =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Function.iterate_succ_apply', ihl, map_add]
  have hshift : ((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
      (MvPolynomial.X N + MvPolynomial.C (e N))
      = transHom e (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
          (MvPolynomial.X N)) := by
    rw [← transHom_X]
    exact iterate_shiftedDerivation_transHom a e (MvPolynomial.X N) i
  have hconst : (MvPolynomial.pderiv k)
      (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i])
        (MvPolynomial.C (e N))) = 0 := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [hi]
      simp
    · obtain ⟨l, hl⟩ : ∃ l, i = l + 1 := ⟨i - 1, by omega⟩
      rw [hl, Function.iterate_succ_apply,
        show shiftedDerivation a e (MvPolynomial.C (e N)) = 0 from by
          rw [show (MvPolynomial.C (e N) : MvPolynomial ℕ ℂ)
            = algebraMap ℂ (MvPolynomial ℕ ℂ) (e N) from rfl]
          exact (shiftedDerivation a e).map_algebraMap _]
      simp
  have hmain := congrArg (MvPolynomial.pderiv k) (hsplit.symm.trans hshift)
  rw [map_add, hconst, add_zero] at hmain
  rw [hmain, pderiv_transHom]

/-- **The shifted model's output-jet determinant is nonzero.** -/
theorem shifted_jet_det_ne_zero {a : ℕ → ℂ} (ha : ∀ k, a k ≠ 0) (e : ℕ → ℂ) (m : ℕ) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (MvPolynomial.pderiv ((i : ℕ) + 1))
          (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
            (MvPolynomial.X (m + 1)))).det ≠ 0 := by
  classical
  have hmat : (Matrix.of fun i j : Fin (m + 1) =>
      (MvPolynomial.pderiv ((i : ℕ) + 1))
        (((shiftedDerivation a e : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
          (MvPolynomial.X (m + 1))))
      = (transHom e).toRingHom.mapMatrix
        (Matrix.of fun i j : Fin (m + 1) =>
          (MvPolynomial.pderiv ((i : ℕ) + 1))
            (((scaledDerivation a : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[(j : ℕ)])
              (MvPolynomial.X (m + 1)))) := by
    funext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact pderiv_iterate_shiftedDerivation a e ((i : ℕ) + 1) (m + 1) (j : ℕ)
  rw [hmat, ← RingHom.map_det]
  intro h0
  refine scaled_jet_det_ne_zero ha m (transHom_injective e ?_)
  rw [map_zero]
  simpa using h0

end GaloisForLFunctions.HTGeometry
