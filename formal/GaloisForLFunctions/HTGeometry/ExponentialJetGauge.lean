import GaloisForLFunctions.HTGeometry.ExponentialFamilyRealization

/-!
# The exponential jet substitution and its injectivity

The jets of an exponential family are the exponential values times universal polynomials in the
jets of the exponents.  Recording the exponential values as extra variables makes the substitution
polynomial: it maps the jet ring of the family into the jet ring of the exponents enlarged by one
variable per member.

The substitution kills nothing: every jet point whose zeroth jets are nonzero is realized by an
actual exponential family, so a polynomial in its kernel vanishes on the whole nonzero locus and is
therefore zero.  This is what will let a differential relation among exponentials be rewritten as a
linear relation in the exponential monomials with jet-polynomial coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The exponential jet substitution: each jet variable becomes the exponential value times the
universal exponential numerator. -/
def expSubst (m n : ℕ) : FamilyJetIndex m n → MvPolynomial (FamilyJetIndex m n ⊕ Fin m) ℂ :=
  Sum.elim (fun _ => MvPolynomial.X (Sum.inl (Sum.inl ())))
    (fun p => MvPolynomial.X (Sum.inr p.1) *
      MvPolynomial.rename Sum.inl (familyExpJetNum m n p.1 (p.2 : ℕ)))

/-- The exponential jet substitution as an algebra homomorphism. -/
def expSubstHom (m n : ℕ) :
    MvPolynomial (FamilyJetIndex m n) ℂ →ₐ[ℂ] MvPolynomial (FamilyJetIndex m n ⊕ Fin m) ℂ :=
  MvPolynomial.aeval (expSubst m n)

/-- The jet point of an exponential family, given the jets of the exponents and the exponential
values. -/
def expJetPoint {m n : ℕ} (x : FamilyJetIndex m n → ℂ) (u : Fin m → ℂ) :
    FamilyJetIndex m n → ℂ :=
  Sum.elim (fun _ => x (Sum.inl ()))
    (fun p => u p.1 * MvPolynomial.eval x (familyExpJetNum m n p.1 (p.2 : ℕ)))

/-- Evaluating the substitution is evaluating at the exponential jet point. -/
theorem eval_expSubstHom {m n : ℕ} (x : FamilyJetIndex m n → ℂ) (u : Fin m → ℂ)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    MvPolynomial.aeval (Sum.elim x u) (expSubstHom m n P)
      = MvPolynomial.aeval (expJetPoint x u) P := by
  rw [expSubstHom, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have hfun : (fun v => MvPolynomial.aeval (Sum.elim x u) (expSubst m n v))
      = expJetPoint x u := by
    funext v
    rcases v with ⟨⟩ | ⟨i, k⟩
    · simp [expSubst, expJetPoint]
    · rw [expSubst, Sum.elim_inr, expJetPoint, Sum.elim_inr, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.aeval_rename]
      rfl
  rw [hfun]

/-- The exponential jet point of a smooth family is the jet vector of the exponentials. -/
theorem expJetPoint_eq_familyJetVec {m n : ℕ} {U : Set ℂ} (hU : IsOpen U) {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w) {z : ℂ} (hz : z ∈ U) :
    expJetPoint (familyJetVec (n := n) sigma z) (fun i => Complex.exp (sigma i z))
      = familyJetVec (n := n) (fun i w => Complex.exp (sigma i w)) z := by
  funext v
  rcases v with ⟨⟩ | ⟨i, k⟩
  · rfl
  · rw [expJetPoint, Sum.elim_inr]
    exact (familyJetVec_exp_apply hU hs hz i k).symm

/-- **The exponential jet substitution is injective.**  Every jet point with nonzero zeroth jets is
the jet point of an actual exponential family. -/
theorem expSubstHom_injective (m n : ℕ) : Function.Injective (expSubstHom m n) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates
    (Finset.image (fun i : Fin m => Sum.inr (i, (0 : Fin (n + 1)))) Finset.univ) P ?_
  intro y hy
  have hy0 : ∀ i : Fin m, y (Sum.inr (i, (0 : Fin (n + 1)))) ≠ 0 := by
    intro i
    refine hy _ ?_
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  set z₀ : ℂ := y (Sum.inl ()) with hz₀
  set c : Fin m → ℕ → ℂ :=
    fun i k => if h : k < n + 1 then y (Sum.inr (i, ⟨k, h⟩)) else 1 with hc
  have hcne : ∀ i, c i 0 ≠ 0 := by
    intro i
    rw [hc]
    simp only [dif_pos (Nat.succ_pos n)]
    exact hy0 i
  obtain ⟨V, sigma, hVopen, hz₀V, hsmooth, hjets⟩ :=
    exists_expFamily_realizing_jets (m := m) n z₀ c hcne
  have hpoint : expJetPoint (familyJetVec (n := n) sigma z₀)
      (fun i => Complex.exp (sigma i z₀)) = y := by
    rw [expJetPoint_eq_familyJetVec hVopen hsmooth hz₀V]
    funext v
    rcases v with ⟨⟩ | ⟨i, k⟩
    · rfl
    · have hval : familyJetVec (n := n) (fun i w => Complex.exp (sigma i w)) z₀ (Sum.inr (i, k))
          = iteratedDeriv (k : ℕ) (fun w => Complex.exp (sigma i w)) z₀ := rfl
      rw [hval, hjets i (k : ℕ) (Nat.lt_succ_iff.mp k.2), hc]
      simp only [dif_pos k.2]
  have heval := eval_expSubstHom (familyJetVec (n := n) sigma z₀)
    (fun i => Complex.exp (sigma i z₀)) P
  rw [hpoint, hP, map_zero] at heval
  have hconv : MvPolynomial.aeval y P = MvPolynomial.eval y P := rfl
  rw [← hconv]
  exact heval.symm

end

end GaloisForLFunctions.HTGeometry
