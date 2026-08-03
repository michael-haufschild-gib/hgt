import GaloisForLFunctions.HTGeometry.FamilyJetChainRule
import GaloisForLFunctions.HTGeometry.ExponentialFamilyRealization

/-!
# The exponential substitution on full jets

The jets of `exp (sigma i)` are `exp (sigma i)` times universal polynomials in the jets of the
exponents.  Recording each exponential value as one extra variable makes the substitution
polynomial, with coefficients in the jet ring of the exponents:

`X_{i,k}  |->  U_i * B_{i,k}(jets sigma)`,   `X_z |-> X_z`.

The substitution kills nothing: any prescription of finitely many derivatives with nonzero value at
a point is realized by an actual exponential family, so a polynomial in the kernel vanishes on the
whole nonzero locus and is therefore zero.  This is the grouping which turns a differential relation
among exponentials into a linear relation in the exponential monomials.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The blockwise exponential numerator in the full jet ring. -/
def fullExpJetNum (m : ℕ) (i : Fin m) (k : ℕ) : MvPolynomial (FullJetIndex m) ℂ :=
  MvPolynomial.rename (fun j => Sum.inr (i, j)) (expJetNum k)

theorem eval_fullExpJetNum {m : ℕ} (sigma : Fin m → ℂ → ℂ) (z : ℂ) (i : Fin m) (k : ℕ) :
    MvPolynomial.eval (fullJetVec sigma z) (fullExpJetNum m i k)
      = MvPolynomial.eval (jetVec (sigma i) z) (expJetNum k) := by
  rw [fullExpJetNum, MvPolynomial.eval_rename]
  rfl

/-- **The jets of an exponential family.**  Every jet of `exp (sigma i)` is `exp (sigma i)` times the
blockwise exponential numerator evaluated on the jets of the exponents. -/
theorem fullJetVec_exp_apply {m : ℕ} {U : Set ℂ} (hU : IsOpen U) {sigma : Fin m → ℂ → ℂ}
    (hs : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (sigma i) w) {z : ℂ} (hz : z ∈ U) (i : Fin m)
    (k : ℕ) :
    fullJetVec (fun i w => Complex.exp (sigma i w)) z (Sum.inr (i, k))
      = Complex.exp (sigma i z)
        * MvPolynomial.eval (fullJetVec sigma z) (fullExpJetNum m i k) := by
  rw [fullJetVec_inr, eval_fullExpJetNum, iteratedDeriv_exp_eq_expJetNum_mul hU (hs i) k z hz]

/-- The jet ring of the exponents with one exponential variable per member. -/
abbrev FullExpRing (m : ℕ) := MvPolynomial (Fin m) (MvPolynomial (FullJetIndex m) ℂ)

/-- The exponential substitution on full jet coordinates. -/
def fullExpSubst (m : ℕ) : FullJetIndex m → FullExpRing m :=
  Sum.elim (fun _ => MvPolynomial.C (MvPolynomial.X (Sum.inl ())))
    (fun p => MvPolynomial.X p.1 * MvPolynomial.C (fullExpJetNum m p.1 p.2))

/-- The exponential substitution as a ring homomorphism. -/
def fullExpSubstHom (m : ℕ) : MvPolynomial (FullJetIndex m) ℂ →+* FullExpRing m :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (fullExpSubst m)

@[simp] theorem fullExpSubstHom_X {m : ℕ} (v : FullJetIndex m) :
    fullExpSubstHom m (MvPolynomial.X v) = fullExpSubst m v := by
  rw [fullExpSubstHom, MvPolynomial.eval₂Hom_X']

@[simp] theorem fullExpSubstHom_C {m : ℕ} (r : ℂ) :
    fullExpSubstHom m (MvPolynomial.C r) = MvPolynomial.C (MvPolynomial.C r) := by
  rw [fullExpSubstHom, MvPolynomial.eval₂Hom_C]
  rfl

/-- The jet point of an exponential family, given the jets of the exponents and the exponential
values. -/
def expFullJetPoint {m : ℕ} (x : FullJetIndex m → ℂ) (u : Fin m → ℂ) : FullJetIndex m → ℂ :=
  Sum.elim (fun _ => x (Sum.inl ()))
    (fun p => u p.1 * MvPolynomial.eval x (fullExpJetNum m p.1 p.2))

/-- Evaluating the substitution at a point of the enlarged ring is evaluating the original
polynomial at the corresponding exponential jet point. -/
theorem eval₂_fullExpSubstHom {m : ℕ} (x : FullJetIndex m → ℂ) (u : Fin m → ℂ)
    (P : MvPolynomial (FullJetIndex m) ℂ) :
    MvPolynomial.eval₂ (MvPolynomial.eval x) u (fullExpSubstHom m P)
      = MvPolynomial.eval (expFullJetPoint x u) P := by
  have hcomp : ((MvPolynomial.eval₂Hom (MvPolynomial.eval x) u : FullExpRing m →+* ℂ).comp
        (fullExpSubstHom m))
      = (MvPolynomial.eval (expFullJetPoint x u) : MvPolynomial (FullJetIndex m) ℂ →+* ℂ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · rw [RingHom.comp_apply, fullExpSubstHom_C, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C,
        MvPolynomial.eval_C]
    · rw [RingHom.comp_apply, fullExpSubstHom_X, MvPolynomial.eval_X]
      rcases v with u' | ⟨i, k⟩
      · rw [fullExpSubst, Sum.elim_inl, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_X]
        rfl
      · rw [fullExpSubst, Sum.elim_inr, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
        rfl
  exact congrArg (fun f : MvPolynomial (FullJetIndex m) ℂ →+* ℂ => f P) hcomp

/-- The largest jet index occurring in a full jet polynomial. -/
def fullJetOrder {m : ℕ} (P : MvPolynomial (FullJetIndex m) ℂ) : ℕ :=
  P.vars.sup (Sum.elim (fun _ => 0) (fun p : Fin m × ℕ => p.2))

theorem le_fullJetOrder {m : ℕ} {P : MvPolynomial (FullJetIndex m) ℂ} {i : Fin m} {k : ℕ}
    (h : Sum.inr (i, k) ∈ P.vars) : k ≤ fullJetOrder P :=
  Finset.le_sup (f := Sum.elim (fun _ => 0) (fun p : Fin m × ℕ => p.2)) h

/-- **The exponential substitution on full jets is injective.**  Every jet point with nonzero
exponential values is the jet point of an actual exponential family, so a polynomial in the kernel
vanishes on the whole nonzero locus. -/
theorem fullExpSubstHom_injective (m : ℕ) : Function.Injective (fullExpSubstHom m) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates
    (Finset.image (fun i : Fin m => (Sum.inr (i, 0) : FullJetIndex m)) Finset.univ) P ?_
  intro y hy
  have hy0 : ∀ i : Fin m, y (Sum.inr (i, 0)) ≠ 0 := fun i =>
    hy _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  set n : ℕ := fullJetOrder P with hn
  set z₀ : ℂ := y (Sum.inl ()) with hz₀
  set c : Fin m → ℕ → ℂ := fun i k => if k ≤ n then y (Sum.inr (i, k)) else 1 with hc
  have hcne : ∀ i, c i 0 ≠ 0 := by
    intro i
    rw [hc]
    simp only [Nat.zero_le, if_pos]
    exact hy0 i
  obtain ⟨V, sigma, hVopen, hz₀V, hsmooth, hjets⟩ :=
    exists_expFamily_realizing_jets (m := m) n z₀ c hcne
  set x : FullJetIndex m → ℂ := fullJetVec sigma z₀ with hx
  set u : Fin m → ℂ := fun i => Complex.exp (sigma i z₀) with hu
  have hpoint : ∀ v ∈ P.vars, expFullJetPoint x u v = y v := by
    intro v hv
    rcases v with u' | ⟨i, k⟩
    · rw [expFullJetPoint, Sum.elim_inl, hx, fullJetVec_inl]
    · have hk : k ≤ n := le_fullJetOrder hv
      have hexp : expFullJetPoint x u (Sum.inr (i, k))
          = fullJetVec (fun i w => Complex.exp (sigma i w)) z₀ (Sum.inr (i, k)) := by
        rw [fullJetVec_exp_apply hVopen hsmooth hz₀V i k, expFullJetPoint, Sum.elim_inr]
      rw [hexp]
      have hval : fullJetVec (fun i w => Complex.exp (sigma i w)) z₀ (Sum.inr (i, k))
          = iteratedDeriv k (fun w => Complex.exp (sigma i w)) z₀ := rfl
      rw [hval, hjets i k hk, hc]
      simp only [hk, if_pos]
  have hcongr : MvPolynomial.eval (expFullJetPoint x u) P = MvPolynomial.eval y P := by
    refine MvPolynomial.eval₂_congr _ _ _ ?_
    intro v d hvd hcoeff
    exact hpoint v ((MvPolynomial.mem_vars_iff_mem_support v).mpr
      ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hvd⟩)
  rw [← hcongr, ← eval₂_fullExpSubstHom x u P, hP]
  exact MvPolynomial.eval₂_zero _ _

/-! ## Truncated and full jet relations -/

/-- Truncated jet coordinates sit inside the full jet coordinates. -/
def jetEmbed (m n : ℕ) : FamilyJetIndex m n → FullJetIndex m :=
  Sum.elim (fun _ => Sum.inl ()) (fun p => Sum.inr (p.1, (p.2 : ℕ)))

theorem jetEmbed_injective (m n : ℕ) : Function.Injective (jetEmbed m n) := by
  rintro (⟨⟩ | ⟨i, j⟩) (⟨⟩ | ⟨i', j'⟩) h
  · rfl
  · exact absurd h (by simp [jetEmbed])
  · exact absurd h (by simp [jetEmbed])
  · simp only [jetEmbed, Sum.elim_inr, Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨hi, hj⟩ := h
    subst hi
    exact congrArg (fun b => Sum.inr (i, b)) (Fin.ext hj)

theorem fullJetVec_jetEmbed {m n : ℕ} (sigma : Fin m → ℂ → ℂ) (z : ℂ)
    (v : FamilyJetIndex m n) :
    fullJetVec sigma z (jetEmbed m n v) = familyJetVec (n := n) sigma z v := by
  rcases v with ⟨⟩ | ⟨i, j⟩ <;> rfl

theorem eval_rename_jetEmbed {m n : ℕ} (sigma : Fin m → ℂ → ℂ) (z : ℂ)
    (P : MvPolynomial (FamilyJetIndex m n) ℂ) :
    MvPolynomial.eval (fullJetVec sigma z) (MvPolynomial.rename (jetEmbed m n) P)
      = MvPolynomial.eval (familyJetVec (n := n) sigma z) P := by
  rw [MvPolynomial.eval_rename]
  have hfun : fullJetVec sigma z ∘ jetEmbed m n = familyJetVec (n := n) sigma z := by
    funext v
    exact fullJetVec_jetEmbed sigma z v
  rw [hfun]

/-- Full jet coordinates truncated at a given order. -/
def jetTrunc (m n : ℕ) : FullJetIndex m → FamilyJetIndex m n :=
  Sum.elim (fun _ => Sum.inl ())
    (fun p => Sum.inr (p.1, if h : p.2 < n + 1 then ⟨p.2, h⟩ else 0))

/-- Below the truncation order, evaluating after truncation is evaluating the full jet
polynomial. -/
theorem eval_jetTrunc_eq {m n : ℕ} (x : FullJetIndex m → ℂ) (w : FamilyJetIndex m n → ℂ)
    (hw : ∀ v : FamilyJetIndex m n, w v = x (jetEmbed m n v))
    (P : MvPolynomial (FullJetIndex m) ℂ) (hP : fullJetOrder P ≤ n) :
    MvPolynomial.eval (fun v => w (jetTrunc m n v)) P = MvPolynomial.eval x P := by
  classical
  refine MvPolynomial.eval₂_congr _ _ _ ?_
  intro v d hvd hcoeff
  have hv : v ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support v).mpr
    ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, hvd⟩
  rcases v with u | ⟨i, k⟩
  · rw [jetTrunc, Sum.elim_inl, hw]
    rfl
  · have hk : k < n + 1 := Nat.lt_succ_of_le (le_trans (le_fullJetOrder hv) hP)
    rw [jetTrunc, Sum.elim_inr, dif_pos hk, hw]
    rfl

/-- **Full jet independence from truncated independence.**  A family satisfying no truncated
differential relation satisfies no full jet relation either. -/
theorem fullJet_independent_of_not_familyDifferentiallyAlgebraicOn {m : ℕ} {U : Set ℂ}
    {sigma : Fin m → ℂ → ℂ} (hind : ¬ FamilyDifferentiallyAlgebraicOn sigma U)
    (P : MvPolynomial (FullJetIndex m) ℂ)
    (hP : ∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) : P = 0 := by
  classical
  by_contra hPne
  obtain ⟨y, hy⟩ : ∃ y : FullJetIndex m → ℂ, MvPolynomial.eval y P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hPne (mvPolynomial_eq_zero_of_eval_eq_zero_off_coordinates ∅ P fun y _ => hcon y)
  set n := fullJetOrder P with hn
  refine hind ⟨n, MvPolynomial.rename (jetTrunc m n) P, ?_, ?_⟩
  · intro hzero
    refine hy ?_
    have hval : MvPolynomial.eval (fun v => y (jetEmbed m n v))
        (MvPolynomial.rename (jetTrunc m n) P) = 0 := by
      rw [hzero, map_zero]
    rw [MvPolynomial.eval_rename] at hval
    rw [← eval_jetTrunc_eq y (fun v => y (jetEmbed m n v)) (fun v => rfl) P le_rfl]
    exact hval
  · intro z hz
    rw [MvPolynomial.eval_rename]
    rw [show (MvPolynomial.eval (familyJetVec (n := n) sigma z ∘ jetTrunc m n)) P
        = MvPolynomial.eval (fun v => familyJetVec (n := n) sigma z (jetTrunc m n v)) P from rfl,
      eval_jetTrunc_eq (fullJetVec sigma z) (familyJetVec (n := n) sigma z)
        (fun v => (fullJetVec_jetEmbed sigma z v).symm) P le_rfl]
    exact hP z hz


/-- **Full jet independence gives no truncated relation.**  The converse direction of the
truncation bridge. -/
theorem not_familyDifferentiallyAlgebraicOn_of_fullJet_independent {m : ℕ} {U : Set ℂ}
    {sigma : Fin m → ℂ → ℂ}
    (hind : ∀ P : MvPolynomial (FullJetIndex m) ℂ,
      (∀ z ∈ U, MvPolynomial.eval (fullJetVec sigma z) P = 0) → P = 0) :
    ¬ FamilyDifferentiallyAlgebraicOn sigma U := by
  rintro ⟨n, Q, hQne, hQ0⟩
  refine hQne (MvPolynomial.rename_injective _ (jetEmbed_injective m n) ?_)
  rw [map_zero]
  refine hind _ fun z hz => ?_
  rw [eval_rename_jetEmbed]
  exact hQ0 z hz

end

end GaloisForLFunctions.HTGeometry
