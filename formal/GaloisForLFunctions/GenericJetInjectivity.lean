import Mathlib
import GaloisForLFunctions.FormalMahlerDescent
import GaloisForLFunctions.TaylorDerivativeCoefficient

/-!
# Injectivity of the generic jet substitution

A differential polynomial that annihilates the formal jets of **every** power series is zero
(`formalJets_substitution_injective`): the substitution of generic jets is injective.  The
proof is a divisibility induction with no analysis.  Annihilating all series forces the
point-slot variable to divide the polynomial — the constant coefficient of the jet
evaluation is the evaluation at the origin jets, and origin jets are arbitrary because a
finite Taylor polynomial realizes any finite jet — and the quotient again annihilates
everything since the series variable is regular; iterating makes the polynomial divisible by
every power of the point-slot variable, which bounds its degree from below by every natural
number.

This is the exactness of the generic-coefficient expansion: distinct differential
polynomials induce distinct universal coefficient identities.
-/

open MvPolynomial PowerSeries

namespace GaloisForLFunctions

/-- The constant coefficient of a jet evaluation is the evaluation at the origin jets. -/
theorem constantCoeff_aeval_formalJets (n : ℕ) (G : ℂ⟦X⟧)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    PowerSeries.constantCoeff (MvPolynomial.aeval (formalJets n G) Q)
      = MvPolynomial.eval (fun i => PowerSeries.constantCoeff (formalJets n G i)) Q := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left
    (PowerSeries.constantCoeff) (algebraMap ℂ ℂ⟦X⟧) (formalJets n G) Q]
  have hid : (PowerSeries.constantCoeff (R := ℂ)).comp (algebraMap ℂ ℂ⟦X⟧)
      = RingHom.id ℂ := by
    ext c
    simp
  rw [hid]
  rfl

/-- Origin jets of the truncated realization series recover prescribed values. -/
theorem constantCoeff_formalJets_realization (n : ℕ) (v : Fin (n + 1) → ℂ) :
    (fun i => PowerSeries.constantCoeff
      (formalJets n (PowerSeries.mk fun j =>
        if hj : j < n + 1 then v ⟨j, hj⟩ / (Nat.factorial j : ℂ) else 0) i))
      = Fin.cons 0 v := by
  funext i
  induction i using Fin.cases with
  | zero => simp [formalJets]
  | succ j =>
    have hslot : formalJets n (PowerSeries.mk fun j' =>
        if hj' : j' < n + 1 then v ⟨j', hj'⟩ / (Nat.factorial j' : ℂ) else 0) j.succ
        = (⇑(d⁄dX ℂ))^[(j : ℕ)] (PowerSeries.mk fun j' =>
        if hj' : j' < n + 1 then v ⟨j', hj'⟩ / (Nat.factorial j' : ℂ) else 0) := by
      simp [formalJets]
    rw [hslot, Fin.cons_succ, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_iterate_derivative _ (j : ℕ) 0]
    have hfac : ∏ i ∈ Finset.range (j : ℕ), ((0 + 1 + i : ℕ) : ℂ)
        = ((Nat.factorial (j : ℕ) : ℕ) : ℂ) := by
      rw [← Nat.cast_prod]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]
      exact Finset.prod_congr rfl fun i _ => by omega
    rw [hfac, PowerSeries.coeff_mk, dif_pos (by omega : (0 + (j : ℕ)) < n + 1)]
    have hne : ((Nat.factorial (j : ℕ) : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [show (⟨0 + (j : ℕ), by omega⟩ : Fin (n + 1)) = j from by
      ext; simp]
    simp only [Nat.zero_add]
    field_simp

/-- **Injectivity of the generic jet substitution**: a differential polynomial annihilating
the formal jets of every power series is zero. -/
theorem formalJets_substitution_injective {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ}
    (h : ∀ G : ℂ⟦X⟧, MvPolynomial.aeval (formalJets n G) P = 0) : P = 0 := by
  by_contra hP
  have hdvd : ∀ k : ℕ, (MvPolynomial.X 0 : MvPolynomial (Fin (n + 2)) ℂ) ^ k ∣ P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      have hQ0 : ∀ G : ℂ⟦X⟧, MvPolynomial.aeval (formalJets n G) Q = 0 := by
        intro G
        have hG := h G
        rw [hQ, map_mul, map_pow, MvPolynomial.aeval_X] at hG
        have hX0 : formalJets n G 0 = PowerSeries.X := by simp [formalJets]
        rw [hX0] at hG
        rcases mul_eq_zero.mp hG with h1 | h1
        · exact absurd h1 (pow_ne_zero k PowerSeries.X_ne_zero)
        · exact h1
      have hval : ∀ v : Fin (n + 1) → ℂ, MvPolynomial.eval (Fin.cons 0 v) Q = 0 := by
        intro v
        have h0 := congrArg (PowerSeries.constantCoeff (R := ℂ))
          (hQ0 (PowerSeries.mk fun j =>
            if hj : j < n + 1 then v ⟨j, hj⟩ / (Nat.factorial j : ℂ) else 0))
        rw [constantCoeff_aeval_formalJets, constantCoeff_formalJets_realization] at h0
        simpa using h0
      have hXdvd : Polynomial.X ∣ (MvPolynomial.finSuccEquiv ℂ (n + 1)) Q := by
        rw [Polynomial.X_dvd_iff]
        apply MvPolynomial.funext
        intro v
        rw [map_zero, Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.eval_zero_map,
          ← MvPolynomial.eval_eq_eval_mv_eval']
        exact hval v
      have hX0dvd : (MvPolynomial.X 0 : MvPolynomial (Fin (n + 2)) ℂ) ∣ Q := by
        have h1 := map_dvd (MvPolynomial.finSuccEquiv ℂ (n + 1)).symm hXdvd
        have h2 : (MvPolynomial.finSuccEquiv ℂ (n + 1)).symm Polynomial.X
            = MvPolynomial.X 0 := by
          rw [← MvPolynomial.finSuccEquiv_X_zero (R := ℂ) (n := n + 1)]
          exact AlgEquiv.symm_apply_apply _ _
        rwa [h2, AlgEquiv.symm_apply_apply] at h1
      obtain ⟨R, hR⟩ := hX0dvd
      exact ⟨R, by rw [hQ, hR]; ring⟩
  have heP : (MvPolynomial.finSuccEquiv ℂ (n + 1)) P ≠ 0 := fun h0 =>
    hP ((MvPolynomial.finSuccEquiv ℂ (n + 1)).injective (by rw [h0, map_zero]))
  set d := ((MvPolynomial.finSuccEquiv ℂ (n + 1)) P).natDegree with hd
  have hk := hdvd (d + 1)
  have hkP := map_dvd (MvPolynomial.finSuccEquiv ℂ (n + 1)) hk
  rw [map_pow, MvPolynomial.finSuccEquiv_X_zero] at hkP
  have hle := Polynomial.natDegree_le_of_dvd hkP heP
  rw [Polynomial.natDegree_X_pow] at hle
  omega

end GaloisForLFunctions
