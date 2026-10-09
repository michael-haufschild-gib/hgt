import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Eliminating variables along a triangular system

In a polynomial ring `R[X_0, …, X_{m-1}]`, let `h_i = X_i − φ_i` where `φ_i` only involves the
variables `X_l` with `l > i`.  Substituting `X_0 ↦ φ_0`, then `X_1 ↦ φ_1`, …, then
`X_{j-1} ↦ φ_{j-1}` defines an `R`-algebra endomorphism `ε_j` whose kernel is exactly the ideal
`(h_0, …, h_{j-1})`: every polynomial is congruent to its substitution modulo these equations, and
the substitution kills them.  Hence `R[X] ⧸ (h_0, …, h_{j-1})` embeds into `R[X]`; over a domain it
is a domain, and `h_j` — which the substitution leaves untouched — is a nonzerodivisor on it.  So
`h_0, h_1, …` is a regular sequence of polynomials, one after another.

* `HTGeometry.triangularElim` : the iterated substitution.
* `HTGeometry.ker_triangularElim` : its kernel is `(h_0, …, h_{j-1})`.
* `HTGeometry.triangular_mem_nonZeroDivisors` : `h_j` is a nonzerodivisor modulo the earlier ones.
-/

namespace HTGeometry

open MvPolynomial

variable {R : Type*} [CommRing R] {m : ℕ} (φ : Fin m → MvPolynomial (Fin m) R)

/-- Substitution of a single variable. -/
noncomputable def substOneVar (i : Fin m) (ψ : MvPolynomial (Fin m) R) :
    MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R :=
  aeval fun l => if l = i then ψ else X l

/-- The equations of the triangular system. -/
noncomputable def triangularEq (i : Fin m) : MvPolynomial (Fin m) R := X i - φ i

/-- **The iterated substitution** of the first `j` variables. -/
noncomputable def triangularElim : ℕ → (MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R)
  | 0 => AlgHom.id R _
  | j + 1 => if h : j < m then (substOneVar ⟨j, h⟩ (φ ⟨j, h⟩)).comp (triangularElim j)
      else triangularElim j

/-- The ideal of the first `j` equations. -/
noncomputable def triangularIdeal (j : ℕ) : Ideal (MvPolynomial (Fin m) R) :=
  Ideal.span (triangularEq φ '' {i | (i : ℕ) < j})

theorem triangularIdeal_mono {j j' : ℕ} (h : j ≤ j') : triangularIdeal φ j ≤ triangularIdeal φ j' :=
  Ideal.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/-- A substitution of one variable fixes every polynomial not involving it. -/
theorem substOneVar_eq_self {i : Fin m} {ψ g : MvPolynomial (Fin m) R} (hg : i ∉ g.vars) :
    substOneVar i ψ g = g := by
  have h := MvPolynomial.hom_congr_vars (f₁ := (substOneVar i ψ).toRingHom)
    (f₂ := RingHom.id _) (p₁ := g) (p₂ := g) ?_ (fun l hl _ => ?_) rfl
  · exact h
  · ext r
    simp [substOneVar]
  · have hli : l ≠ i := fun h => hg (h ▸ hl)
    simp [substOneVar, hli]

/-- A substitution of one variable changes a polynomial by a multiple of its equation. -/
theorem substOneVar_sub_mem (i : Fin m) (ψ g : MvPolynomial (Fin m) R) :
    substOneVar i ψ g - g ∈ Ideal.span {X i - ψ} := by
  rw [← Ideal.Quotient.eq]
  have hmk : (Ideal.Quotient.mkₐ R (Ideal.span {X i - ψ})).comp (substOneVar i ψ)
      = Ideal.Quotient.mkₐ R (Ideal.span {X i - ψ}) := by
    refine MvPolynomial.algHom_ext fun l => ?_
    simp only [AlgHom.comp_apply, substOneVar, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    split_ifs with h
    · subst h
      exact (Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self _)).symm
    · rfl
  exact DFunLike.congr_fun hmk g

variable {φ}

/-- The triangular hypothesis: `φ_i` involves only variables beyond `i`. -/
def IsTriangular (φ : Fin m → MvPolynomial (Fin m) R) : Prop := ∀ i : Fin m, ∀ l ∈ (φ i).vars, i < l

/-- **The substitution of the first `j` variables fixes every polynomial in the remaining ones.** -/
theorem triangularElim_eq_self (j : ℕ) {g : MvPolynomial (Fin m) R}
    (hg : ∀ l ∈ g.vars, j ≤ (l : ℕ)) : triangularElim φ j g = g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [triangularElim]
    split_ifs with h
    · rw [AlgHom.comp_apply, ih fun l hl => (Nat.le_succ j).trans (hg l hl)]
      exact substOneVar_eq_self fun hl => by have := hg _ hl; simp at this
    · exact ih fun l hl => (Nat.le_succ j).trans (hg l hl)

theorem vars_triangularEq_ge (hφ : IsTriangular φ) (i : Fin m) :
    ∀ l ∈ (triangularEq φ i).vars, (i : ℕ) ≤ (l : ℕ) := by
  intro l hl
  classical
  have := MvPolynomial.vars_sub_subset (p := X i) (q := φ i) hl
  rw [Finset.mem_union] at this
  rcases this with h | h
  · rcases subsingleton_or_nontrivial R with hR | hR
    · have h0 : (X i : MvPolynomial (Fin m) R) = 0 := Subsingleton.elim _ _
      rw [h0, MvPolynomial.vars_0] at h
      exact absurd h (Finset.notMem_empty _)
    · rw [MvPolynomial.vars_X] at h
      rw [Finset.mem_singleton.mp h]
  · exact (hφ i l h).le

/-- **Every polynomial is congruent to its substitution** modulo the eliminated equations. -/
theorem triangularElim_sub_mem (j : ℕ) (g : MvPolynomial (Fin m) R) :
    triangularElim φ j g - g ∈ triangularIdeal φ j := by
  induction j with
  | zero => simp [triangularElim]
  | succ j ih =>
    rw [triangularElim]
    split_ifs with h
    · rw [AlgHom.comp_apply, show substOneVar ⟨j, h⟩ (φ ⟨j, h⟩) (triangularElim φ j g) - g
        = (substOneVar ⟨j, h⟩ (φ ⟨j, h⟩) (triangularElim φ j g) - triangularElim φ j g)
          + (triangularElim φ j g - g) by ring]
      refine Ideal.add_mem _ ?_ (triangularIdeal_mono φ (Nat.le_succ j) ih)
      refine Ideal.span_le.mpr ?_ (substOneVar_sub_mem _ _ _)
      rintro _ rfl
      exact Ideal.subset_span ⟨⟨j, h⟩, Nat.lt_succ_self j, rfl⟩
    · exact triangularIdeal_mono φ (Nat.le_succ j) ih

/-- **The substitution kills the eliminated equations.** -/
theorem triangularElim_eq_zero (hφ : IsTriangular φ) {j : ℕ} {i : Fin m} (hi : (i : ℕ) < j) :
    triangularElim φ j (triangularEq φ i) = 0 := by
  induction j with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ j ih =>
    rw [triangularElim]
    by_cases hj : j < m
    swap
    · rw [dif_neg hj]
      exact ih (lt_of_lt_of_le i.2 (not_lt.mp hj))
    rw [dif_pos hj, AlgHom.comp_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · rw [ih hlt, map_zero]
    · have hi' : i = ⟨j, hj⟩ := Fin.ext heq
      rw [triangularElim_eq_self j (fun l hl => heq ▸ vars_triangularEq_ge hφ i l hl)]
      subst hi'
      rw [triangularEq, map_sub, substOneVar_eq_self (fun h => (lt_irrefl _) (hφ _ _ h))]
      simp [substOneVar]

/-- **The kernel of the substitution is the ideal of the eliminated equations.** -/
theorem ker_triangularElim (hφ : IsTriangular φ) (j : ℕ) :
    RingHom.ker (triangularElim φ j) = triangularIdeal φ j := by
  apply le_antisymm
  · intro g hg
    have h := triangularElim_sub_mem (φ := φ) j g
    rw [RingHom.mem_ker.mp hg, zero_sub] at h
    exact neg_mem_iff.mp h
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    exact triangularElim_eq_zero hφ hi

/-- **Over a domain, each equation is a nonzerodivisor modulo the earlier ones.** -/
theorem triangular_mem_nonZeroDivisors [IsDomain R] (hφ : IsTriangular φ) (i : Fin m) :
    Ideal.Quotient.mk (triangularIdeal φ i) (triangularEq φ i) ∈
      nonZeroDivisors (MvPolynomial (Fin m) R ⧸ triangularIdeal φ i) := by
  haveI : IsDomain (MvPolynomial (Fin m) R ⧸ triangularIdeal φ i) := by
    have hinj : Function.Injective (Ideal.Quotient.lift (triangularIdeal φ i)
        (triangularElim φ i).toRingHom (fun g hg => by
          rw [← ker_triangularElim hφ] at hg; exact hg)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.lift_mk] at hx
      rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_triangularElim hφ]
      exact hx
    exact hinj.isDomain
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_triangularElim hφ, RingHom.mem_ker,
    triangularElim_eq_self i (vars_triangularEq_ge hφ i)] at h
  have h1 := congrArg (MvPolynomial.coeff (Finsupp.single i 1)) h
  rw [triangularEq, coeff_sub, coeff_X, coeff_zero] at h1
  have h2 : coeff (Finsupp.single i 1) (φ i) = 0 := by
    by_contra hne
    have hmem : i ∈ (φ i).vars := by
      rw [MvPolynomial.mem_vars_iff_mem_support]
      exact ⟨Finsupp.single i 1, MvPolynomial.mem_support_iff.mpr hne, by simp⟩
    exact lt_irrefl _ (hφ i i hmem)
  rw [h2, sub_zero, if_pos rfl] at h1
  exact one_ne_zero h1

end HTGeometry
