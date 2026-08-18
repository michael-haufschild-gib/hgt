import GaloisForLFunctions.HTGeometry.AutonomousSeparant
import GaloisForLFunctions.HTGeometry.DominantNeighborhood

/-!
# The autonomous relation as a function of the full jet

An autonomous annihilator is stored as a univariate polynomial whose coefficients are polynomials in
the lower jets and whose variable is the top jet.  Evaluating both at a point of `ℂ^(n+1)` turns it
into an ordinary function of the full jet, and the two descriptions of the separant agree: the
derivative of the stored polynomial in its variable is the partial derivative of the evaluated
relation in the top coordinate.

This is what lets Ritt's separant step — the separant does not vanish along the solution — feed the
quantitative dominance hypothesis of the implicit-function argument, which is stated for a function
of the full jet.
-/

namespace GaloisForLFunctions

open Polynomial

/-- The autonomous relation evaluated at a full jet. -/
noncomputable def jetRelation (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (y : Fin (n + 1) → ℂ) : ℂ :=
  Polynomial.eval₂ (MvPolynomial.eval fun j : Fin n => y j.castSucc) (y (Fin.last n)) P

/-- The stored notion of annihilation is evaluation of the relation along the jet of `f`. -/
theorem autonomousAnnihilator_iff_jetRelation {f : ℂ → ℂ} {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    AutonomousAnnihilator f n P ↔
      ∀ z : ℂ, jetRelation n P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) f z) = 0 := by
  constructor
  · intro h z
    have := h z
    simpa [jetRelation, Fin.val_last] using this
  · intro h z
    have := h z
    simpa [jetRelation, Fin.val_last] using this

/-- **The top partial derivative of the relation is its separant.**  Fixing the lower jets, the
relation is a univariate polynomial in the top jet, and its derivative there is the stored
separant. -/
theorem hasDerivAt_jetRelation_last (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (v : Fin n → ℂ) (w : ℂ) :
    HasDerivAt
      (fun x : ℂ => Polynomial.eval₂ (MvPolynomial.eval v) x P)
      (Polynomial.eval₂ (MvPolynomial.eval v) w (Polynomial.derivative P)) w := by
  have hfun : (fun x : ℂ => Polynomial.eval₂ (MvPolynomial.eval v) x P)
      = fun x : ℂ => Polynomial.eval x (P.map (MvPolynomial.eval v)) := by
    funext x
    rw [Polynomial.eval_map]
  have hval : Polynomial.eval₂ (MvPolynomial.eval v) w (Polynomial.derivative P)
      = Polynomial.eval w (P.map (MvPolynomial.eval v)).derivative := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
  rw [hfun, hval]
  exact (P.map (MvPolynomial.eval v)).hasDerivAt w

/-- The separant of a minimal autonomous equation is the top partial derivative of the evaluated
relation, and it does not vanish identically along the solution. -/
theorem exists_minimal_jetRelation_separant {f : ℂ → ℂ} {n : ℕ}
    (h : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ AutonomousAnnihilator f n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      AutonomousAnnihilator f n Q → Q.natDegree ≠ 0) :
    ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ P.natDegree ≠ 0 ∧
      (∀ z : ℂ, jetRelation n P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) f z) = 0) ∧
      ∃ z : ℂ, jetRelation n (Polynomial.derivative P)
        (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) f z) ≠ 0 := by
  obtain ⟨P, hP, hA, hdeg, hsep⟩ := exists_minimal_with_separant h horder
  refine ⟨P, hP, hdeg, (autonomousAnnihilator_iff_jetRelation P).mp hA, ?_⟩
  by_contra hcon
  refine hsep ((autonomousAnnihilator_iff_jetRelation (Polynomial.derivative P)).mpr fun z => ?_)
  by_contra hz
  exact hcon ⟨z, hz⟩


/-! ### The relation is a smooth function of the full jet -/

/-- Evaluating a multivariate polynomial at a moving point is smooth. -/
theorem contDiff_mvEval (n : ℕ) (Q : MvPolynomial (Fin n) ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun v : Fin n → ℂ => MvPolynomial.eval v Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ (⊤ : ℕ∞) fun _ : Fin n → ℂ => a)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
      have hrw : (fun v : Fin n → ℂ => MvPolynomial.eval v (p * MvPolynomial.X i))
          = fun v : Fin n → ℂ => (MvPolynomial.eval v p) * v i := by
        funext v
        simp
      rw [hrw]
      exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).contDiff)

theorem jetRelation_eq_sum (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (y : Fin (n + 1) → ℂ) :
    jetRelation n P y = ∑ i ∈ P.support,
      MvPolynomial.eval (fun j : Fin n => y j.castSucc) (P.coeff i) * (y (Fin.last n)) ^ i := by
  rw [jetRelation, Polynomial.eval₂_eq_sum, Polynomial.sum]

/-- **The relation is smooth in the full jet.**  It is a finite sum of products of polynomial
evaluations, so in particular its derivative is continuous — which is what a dominant convex
neighbourhood needs. -/
theorem contDiff_jetRelation (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    ContDiff ℂ (⊤ : ℕ∞) (jetRelation n P) := by
  have hrw : jetRelation n P = fun y : Fin (n + 1) → ℂ => ∑ i ∈ P.support,
      MvPolynomial.eval (fun j : Fin n => y j.castSucc) (P.coeff i) * (y (Fin.last n)) ^ i := by
    funext y
    exact jetRelation_eq_sum n P y
  rw [hrw]
  refine ContDiff.sum fun i _ => ?_
  refine ContDiff.mul ?_ ?_
  · have hproj : ContDiff ℂ (⊤ : ℕ∞) fun y : Fin (n + 1) → ℂ => fun j : Fin n => y j.castSucc := by
      refine contDiff_pi.mpr fun j => ?_
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
        j.castSucc).contDiff
    exact (contDiff_mvEval n (P.coeff i)).comp hproj
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
      (Fin.last n)).contDiff).pow i

theorem differentiable_jetRelation (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    Differentiable ℂ (jetRelation n P) :=
  (contDiff_jetRelation n P).differentiable (by simp)

theorem continuous_fderiv_jetRelation (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    Continuous (fun y => fderiv ℂ (jetRelation n P) y) :=
  (contDiff_jetRelation n P).continuous_fderiv (by simp)


/-! ### The top partial derivative of the evaluated relation -/

theorem jetRelation_update_last (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (y : Fin (n + 1) → ℂ) (t : ℂ) :
    jetRelation n P (Function.update y (Fin.last n) t)
      = Polynomial.eval₂ (MvPolynomial.eval fun j : Fin n => y j.castSucc) t P := by
  have hlow : ∀ j : Fin n, Function.update y (Fin.last n) t j.castSucc = y j.castSucc := by
    intro j
    exact Function.update_of_ne (Fin.ne_of_lt (Fin.castSucc_lt_last j)) _ _
  have hlast : Function.update y (Fin.last n) t (Fin.last n) = t := by simp
  have harg : (fun j : Fin n => Function.update y (Fin.last n) t j.castSucc)
      = fun j : Fin n => y j.castSucc := by
    funext j
    exact hlow j
  rw [jetRelation, hlast, harg]

/-- **The top partial coefficient of the derivative is the separant.**  This is the identification
that lets Ritt's separant step feed a dominance hypothesis stated for the full-jet relation. -/
theorem partialCoeff_fderiv_jetRelation_last (n : ℕ) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (y : Fin (n + 1) → ℂ) :
    partialCoeff (fderiv ℂ (jetRelation n P) y) (Fin.last n)
      = jetRelation n (Polynomial.derivative P) y := by
  set c : ℂ := y (Fin.last n) with hc
  set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 with he
  set L : ℂ → (Fin (n + 1) → ℂ) := fun t => Function.update y (Fin.last n) t with hL
  have hLc : L c = y := by
    funext k
    rw [hL]
    by_cases hk : k = Fin.last n
    · subst hk; simp [hc]
    · simp [Function.update_of_ne hk]
  have hLaff : L = fun t : ℂ => y + (t - c) • e := by
    funext t
    funext k
    by_cases hk : k = Fin.last n
    · subst hk
      simp [hL, he, hc]
    · simp [hL, he, hk]
  have hLderiv : HasDerivAt L e c := by
    rw [hLaff]
    have hbase : HasDerivAt (fun t : ℂ => (t - c) • e) e c := by
      simpa using ((hasDerivAt_id c).sub_const c).smul_const e
    simpa using hbase.const_add y
  -- the composite, differentiated two ways
  have hF : HasFDerivAt (jetRelation n P) (fderiv ℂ (jetRelation n P) y) (L c) := by
    rw [hLc]
    exact (differentiable_jetRelation n P y).hasFDerivAt
  have hcomp : HasDerivAt (fun t => jetRelation n P (L t))
      (fderiv ℂ (jetRelation n P) y e) c := hF.comp_hasDerivAt c hLderiv
  have hpoly : HasDerivAt (fun t => jetRelation n P (L t))
      (jetRelation n (Polynomial.derivative P) y) c := by
    have hrw : (fun t => jetRelation n P (L t))
        = fun t : ℂ => Polynomial.eval₂
          (MvPolynomial.eval fun j : Fin n => y j.castSucc) t P := by
      funext t
      rw [hL]
      exact jetRelation_update_last n P y t
    have hval : jetRelation n (Polynomial.derivative P) y
        = Polynomial.eval₂ (MvPolynomial.eval fun j : Fin n => y j.castSucc) c
            (Polynomial.derivative P) := rfl
    rw [hrw, hval]
    exact hasDerivAt_jetRelation_last n P (fun j : Fin n => y j.castSucc) c
  rw [partialCoeff, ← he]
  exact hcomp.unique hpoly

end GaloisForLFunctions
